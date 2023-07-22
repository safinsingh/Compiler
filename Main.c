#include <ctype.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#define ERROR (-1)
#define SUCCESS (0)
#define VEC_SZ (32)
#define INT_BASE (10)
#define DBG_BUF_LEN (128)
#define ERR_BUF_LEN (512)
#define MIN(a, b) ((a) > (b) ? (b) : (a))
#define MatchReturn(string, tokenType)                                                             \
	if (LexerMatchSymbol(lex, string)) return TokenNew(lex, tokenType);
char *CurrentFile = "<unknown>";
bool DEBUG = false;

/// UTIL ///

void AllocFailed(void) {
	perror("fatal: alloc failed");
	exit(EXIT_FAILURE);
}

void ICE(char *msg) {
	fprintf(stderr, "fatal: internal compiler error: %s", msg);
	exit(EXIT_FAILURE);
}

size_t ParseUintLiteral(const char *ptr, size_t len) {
	size_t out = 0;
	for (int off = 0; off < len; off++) {
		char raw = *(ptr + off);
		if (off == len - 1 && raw == 'u') {
			break;
		}
		int digit = raw - '0';
		out *= INT_BASE;
		out += digit;
	}
	return out;
}

size_t ParseIntLiteral(const char *ptr, size_t len) {
	size_t out = 0;
	bool neg = false;
	for (int off = 0; off < len; off++) {
		char raw = *(ptr + off);
		if (off == 0 && raw == '-') {
			neg = true;
			continue;
		}
		if (off == len - 1 && raw == 'i') {
			break;
		}
		int digit = raw - '0';
		out *= INT_BASE;
		out += digit;
	}
	return out * (neg ? -1 : 1);
}

typedef struct {
	void *data;
	size_t len;
	size_t cap;
	size_t itemSize;
} Vec;

void VecInit(Vec *vec, size_t itemSize) {
	vec->data = malloc(itemSize * VEC_SZ);
	if (!vec->data) {
		AllocFailed();
	}
	vec->len = 0;
	vec->cap = VEC_SZ;
	vec->itemSize = itemSize;
}

void VecResize(Vec *vec) {
	vec->data = realloc(vec->data, (vec->cap <<= 1) * vec->itemSize);
	if (!vec->data) {
		AllocFailed();
	}
}

void VecPush(Vec *vec, void *item) {
	if (vec->cap == vec->len + 1) {
		VecResize(vec);
	}
	void *slot = vec->data + vec->len * vec->itemSize;
	memcpy(slot, item, vec->itemSize);
	vec->len++;
}

void VecFree(Vec *vec) {
	free(vec->data);
	vec->cap = vec->len = 0;
	vec->itemSize = 0;
}

#define VecAsPtr(vec, TY) (TY *)vec.data

/// LEX ///

typedef enum {
	// ops, symbols
	TOK_PLUS,
	TOK_MINUS,
	TOK_MUL,
	TOK_DIV,
	TOK_MOD,
	TOK_LEQ,
	TOK_GEQ,
	TOK_GT,
	TOK_LT,
	TOK_BIT_AND,
	TOK_BIT_OR,
	TOK_BIT_NOT,
	TOK_AND,
	TOK_OR,
	TOK_NOT,
	TOK_ASSIGN,
	TOK_ADD_ASSIGN,
	TOK_SUB_ASSIGN,
	TOK_MUL_ASSIGN,
	TOK_DIV_ASSIGN,
	TOK_MOD_ASSIGN,
	TOK_BIT_AND_ASSIGN,
	TOK_BIT_OR_ASSIGN,
	TOK_BIT_NOT_ASSIGN,
	// TOK_AND_ASSIGN,
	// TOK_OR_ASSIGN,
	TOK_EQ,
	TOK_NEQ,
	TOK_LPAREN,
	TOK_RPAREN,
	TOK_LBRACE,
	TOK_RBRACE,
	TOK_LBRACKET,
	TOK_RBRACKET,
	TOK_COLON,
	TOK_COMMA,
	TOK_ARROW,

	// keywords
	TOK_TRUE,
	TOK_FALSE,
	TOK_PROC,
	TOK_MATCH,
	TOK_FOR,
	TOK_WHILE,
	TOK_VAL,
	TOK_RETURN,
	TOK_TYPE,

	// types
	TOK_INT,
	TOK_UINT,
	TOK_FLOAT,
	TOK_BOOL,
	TOK_STR,

	// literals
	TOK_SYM,
	TOK_INT_LIT,
	TOK_UINT_LIT,
	TOK_ARBITRARY_INT_LIT,
	TOK_STR_LIT,
	TOK_FLOAT_LIT,

	// misc
	TOK_NEWLINE,
	TOK_EOF
} TokenKind;

// clang-format off
static char* TOKEN_KIND_STR[] = {
	[TOK_PLUS] = "TOK_PLUS",
	[TOK_MINUS] = "TOK_MINUS",
	[TOK_MUL] = "TOK_MUL",
	[TOK_DIV] = "TOK_DIV",
	[TOK_MOD] = "TOK_MOD",
	[TOK_LEQ] = "TOK_LEQ",
	[TOK_GEQ] = "TOK_GEQ",
	[TOK_GT] = "TOK_GT",
	[TOK_LT] = "TOK_LT",
	[TOK_BIT_AND] = "TOK_BIT_AND",
	[TOK_BIT_OR] = "TOK_BIT_OR",
	[TOK_BIT_NOT] = "TOK_BIT_NOT",
	[TOK_AND] = "TOK_AND",
	[TOK_OR] = "TOK_OR",
	[TOK_NOT] = "TOK_NOT",
	[TOK_ASSIGN] = "TOK_ASSIGN",
	[TOK_ADD_ASSIGN] = "TOK_ADD_ASSIGN",
	[TOK_SUB_ASSIGN] = "TOK_SUB_ASSIGN",
	[TOK_MUL_ASSIGN] = "TOK_MUL_ASSIGN",
	[TOK_DIV_ASSIGN] = "TOK_DIV_ASSIGN",
	[TOK_MOD_ASSIGN] = "TOK_MOD_ASSIGN",
	[TOK_BIT_AND_ASSIGN] = "TOK_BIT_AND_ASSIGN",
	[TOK_BIT_OR_ASSIGN] = "TOK_BIT_OR_ASSIGN",
	[TOK_BIT_NOT_ASSIGN] = "TOK_BIT_NOT_ASSIGN",
	// TOK_AND_ASSIGN,
	// TOK_OR_ASSIGN,
	[TOK_EQ] = "TOK_EQ",
	[TOK_NEQ] = "TOK_NEQ",
	[TOK_LPAREN] = "TOK_LPAREN",
	[TOK_RPAREN] = "TOK_RPAREN",
	[TOK_LBRACE] = "TOK_LBRACE",
	[TOK_RBRACE] = "TOK_RBRACE",
	[TOK_LBRACKET] = "TOK_LBRACKET",
	[TOK_RBRACKET] = "TOK_RBRACKET",
	[TOK_COLON] = "TOK_COLON",
	[TOK_COMMA] = "TOK_COMMA",
	[TOK_ARROW] = "TOK_ARROW",

	// keywords
	[TOK_TRUE] = "TOK_TRUE",
	[TOK_FALSE] = "TOK_FALSE",
	[TOK_PROC] = "TOK_PROC",
	[TOK_MATCH] = "TOK_MATCH",
	[TOK_FOR] = "TOK_FOR",
	[TOK_WHILE] = "TOK_WHILE",
	[TOK_VAL] = "TOK_VAL",
	[TOK_RETURN] = "TOK_RETURN",
	[TOK_TYPE] = "TOK_TYPE",

	// types
	[TOK_INT] = "TOK_INT",
	[TOK_UINT] = "TOK_UINT",
	[TOK_FLOAT] = "TOK_FLOAT",
	[TOK_BOOL] = "TOK_BOOL",
	[TOK_STR] = "TOK_STR",

	// literals
	[TOK_SYM] = "TOK_SYM",
	[TOK_INT_LIT] = "TOK_INT_LIT",
	[TOK_UINT_LIT] = "TOK_UINT_LIT",
	[TOK_ARBITRARY_INT_LIT] = "TOK_ARBITRARY_INT_LIT",
	[TOK_STR_LIT] = "TOK_STR_LIT",
	[TOK_FLOAT_LIT] = "TOK_FLOAT_LIT",

	// misc
	[TOK_NEWLINE] = "TOK_NEWLINE",
	[TOK_EOF] = "TOK_EOF"
};
// clang-format on

typedef struct {
	const char *ptr;
	size_t len;
} SourcePtr;

typedef enum { STAGE_LEXER, STAGE_AST } CompilerStage;

// clang-format off
static char *COMPILER_STAGE_STR[] = {
	[STAGE_LEXER] = "LEXER", 
	[STAGE_AST] = "AST"
};
// clang-format on

typedef struct {
	TokenKind kind;
	SourcePtr loc;
	size_t line;
} Token;

void CompilerErrFatal(CompilerStage stage, SourcePtr src, SourcePtr loc, size_t line, char *raw) {
	const char *lineStart = NULL;
	for (const char *s = loc.ptr; s >= src.ptr; s--) {
		if (*s == '\n') {
			lineStart = s + 1;
			break;
		}
	}
	if (!lineStart) {
		lineStart = src.ptr;
	}
	const char *lineEnd = NULL;
	for (const char *s = loc.ptr + loc.len; s <= src.ptr + src.len - 1; s++) {
		if (*s == '\n') {
			lineEnd = s - 1;
			break;
		}
	}
	if (!lineEnd) {
		lineEnd = src.ptr + src.len;
	}
	fprintf(stderr,
	        "[%s] error: %s\n"
	        " --> %s\n"
	        "  |\n"
	        "%lu | ",
	        COMPILER_STAGE_STR[stage], raw, CurrentFile, line);
	for (const char *i = lineStart; i <= lineEnd; i++) {
		putc(*i, stderr);
	}
	fprintf(stderr, "\n  |%*c^\n", (int)(loc.ptr - lineStart + 1), ' ');
	exit(EXIT_FAILURE);
}

typedef struct {
	SourcePtr src;
	size_t currentLine;
	size_t start;
	size_t end;

	Token peek;
	bool validPeek;
} Lexer;

void LexerInit(Lexer *lex, SourcePtr src) {
	lex->src = src;
	lex->currentLine = 1;
	lex->start = lex->end = 0;
	lex->validPeek = false;
}

SourcePtr LexerGetSrcPtr(Lexer *lex) {
	return (SourcePtr){.ptr = lex->src.ptr + lex->start, .len = lex->end - lex->start};
}

Token TokenNew(Lexer *lex, TokenKind kind) {
	Token tok;
	tok.kind = kind;
	tok.line = lex->currentLine;
	tok.loc = LexerGetSrcPtr(lex);
	return tok;
}

void TokenDebug(Token *tok) {
	char buf[DBG_BUF_LEN] = {0};
	int head = sprintf(buf, "%s (line %lu) - \"", TOKEN_KIND_STR[tok->kind], tok->line);
	int sz = sizeof(buf) - head - 3; // '"\n' and NUL
	for (int i = 0; i < sz && i < tok->loc.len; i++) {
		sprintf(buf + strlen(buf), "%c", tok->loc.ptr[i]);
	}
	sprintf(buf + strlen(buf), "\"\n");
	fprintf(stderr, "%s", buf);
}

bool LexerStreamExhausted(Lexer *lex) { return lex->src.len == lex->end; }

char LexerPeekChar(Lexer *lex) {
	if (LexerStreamExhausted(lex)) {
		return 0;
	}
	return lex->src.ptr[lex->end];
}

void LexerShift(Lexer *lex) { lex->end++; }

char LexerNextChar(Lexer *lex) {
	char c = LexerPeekChar(lex);
	LexerShift(lex);
	return c;
}

void LexerSkipWhitespace(Lexer *lex) {
	char c;
	while (isspace(c = LexerPeekChar(lex))) {
		LexerShift(lex);
		if (c == '\n') {
			lex->currentLine++;
		}
	}
}

Token TokenMaybeDouble(Lexer *lex, char branch, TokenKind branchTrue, TokenKind branchFalse) {
	if (LexerPeekChar(lex) == branch) {
		LexerShift(lex);
		return TokenNew(lex, branchTrue);
	}
	return TokenNew(lex, branchFalse);
}

Token TokenMaybeDouble2(Lexer *lex,
                        char branch1,
                        TokenKind branch1True,
                        char branch2,
                        TokenKind branch2True,
                        TokenKind branchesFalse) {
	char c = LexerPeekChar(lex);
	if (c == branch1) {
		LexerShift(lex);
		return TokenNew(lex, branch1True);
	}
	if (c == branch2) {
		LexerShift(lex);
		return TokenNew(lex, branch2True);
	}
	return TokenNew(lex, branchesFalse);
}

Token LexerLexNumber(Lexer *lex, bool neg) {
	bool fl = false;
	char c;
	while ((c = LexerPeekChar(lex))) {
		if (isdigit(c)) {
			LexerShift(lex);
		} else if (!fl && c == '.') {
			LexerShift(lex);
		} else {
			break;
		}
	}

	if (fl) {
		return TokenNew(lex, TOK_FLOAT_LIT);
	}
	char suffix = LexerPeekChar(lex);
	switch (suffix) {
	case 'u':
		LexerShift(lex);
		if (neg) {
			CompilerErrFatal(STAGE_LEXER, lex->src, LexerGetSrcPtr(lex), lex->currentLine,
			                 "Unexpected '-' preceding unsigned integer literal");
		}
		return TokenNew(lex, TOK_UINT_LIT);
	case 'i': LexerShift(lex); return TokenNew(lex, TOK_INT_LIT);
	default: return TokenNew(lex, neg ? TOK_INT_LIT : TOK_ARBITRARY_INT_LIT);
	}
}

bool LexerMatchSymbol(Lexer *lex, char *sym) {
	if (lex->end - lex->start != strlen(sym)) {
		return false;
	}
	return memcmp(lex->src.ptr + lex->start, sym, lex->end - lex->start) == 0;
}

Token LexerLexSymbol(Lexer *lex) {
	char c;
	while ((c = LexerPeekChar(lex)) && (isalpha(c) || isdigit(c) || c == '_')) {
		LexerShift(lex);
	}

	// keywords
	MatchReturn("true", TOK_TRUE);
	MatchReturn("false", TOK_FALSE);
	MatchReturn("proc", TOK_PROC);
	MatchReturn("match", TOK_MATCH);
	MatchReturn("for", TOK_FOR);
	MatchReturn("while", TOK_WHILE);
	MatchReturn("val", TOK_VAL);
	MatchReturn("return", TOK_RETURN);
	MatchReturn("type", TOK_RETURN);

	// types
	MatchReturn("int", TOK_INT);
	MatchReturn("uint", TOK_UINT);
	MatchReturn("float", TOK_FLOAT);
	MatchReturn("bool", TOK_BOOL);
	MatchReturn("str", TOK_STR);

	return TokenNew(lex, TOK_SYM);
}

Token LexerLexStrLit(Lexer *lex) {
	char c;
	bool escaped = false;
	while ((c = LexerPeekChar(lex))) {
		switch (c) {
		case '\\':
			LexerShift(lex);
			if (LexerPeekChar(lex) == '"') {
				escaped = true;
			}
			break;
		case '"':
			LexerShift(lex);
			if (escaped) {
				escaped = false;
			} else {
				goto OUT;
			}
		default: LexerShift(lex);
		}
	}
OUT:
	return TokenNew(lex, TOK_STR_LIT);
}

// assume `buf` is DBG_BUF_LEN bytes long
void TokenSrcDebug(Token tok, char *buf) {
	int bytes = MIN(DBG_BUF_LEN - 1, tok.loc.len);
	memcpy(buf, tok.loc.ptr, bytes);
	buf[bytes] = '\0';
}

Token _LexerNextInner(Lexer *lex) {
	LexerSkipWhitespace(lex);

	lex->start = lex->end;
	char c = LexerNextChar(lex);

	if (isdigit(c)) {
		return LexerLexNumber(lex, false);
	}
	if (isalpha(c) || c == '_') {
		return LexerLexSymbol(lex);
	}

	switch (c) {
	case 0: return TokenNew(lex, TOK_EOF);
	case '"': return LexerLexStrLit(lex);
	case '+': return TokenMaybeDouble(lex, '=', TOK_ADD_ASSIGN, TOK_PLUS);
	case '-':
		if (isdigit(LexerPeekChar(lex))) {
			return LexerLexNumber(lex, true);
		}
		return TokenMaybeDouble2(lex, '=', TOK_SUB_ASSIGN, '>', TOK_ARROW, TOK_MINUS);
	case '*': return TokenMaybeDouble(lex, '=', TOK_MUL_ASSIGN, TOK_MUL);
	case '/': return TokenMaybeDouble(lex, '=', TOK_DIV_ASSIGN, TOK_DIV);
	case '%': return TokenMaybeDouble(lex, '=', TOK_MOD_ASSIGN, TOK_MOD);
	case '<': return TokenMaybeDouble(lex, '=', TOK_LEQ, TOK_LT);
	case '>': return TokenMaybeDouble(lex, '=', TOK_GEQ, TOK_GT);
	case '&': return TokenMaybeDouble2(lex, '&', TOK_AND, '=', TOK_BIT_AND_ASSIGN, TOK_BIT_AND);
	case '|': return TokenMaybeDouble2(lex, '|', TOK_OR, '=', TOK_BIT_OR_ASSIGN, TOK_BIT_OR);
	case '~': return TokenMaybeDouble(lex, '=', TOK_BIT_NOT_ASSIGN, TOK_BIT_NOT);
	case '!': return TokenMaybeDouble(lex, '=', TOK_NEQ, TOK_NOT);
	case '=': return TokenMaybeDouble(lex, '=', TOK_EQ, TOK_ASSIGN);
	case '(': return TokenNew(lex, TOK_LPAREN);
	case ')': return TokenNew(lex, TOK_RPAREN);
	case '{': return TokenNew(lex, TOK_LBRACE);
	case '}': return TokenNew(lex, TOK_RBRACE);
	case '[': return TokenNew(lex, TOK_LBRACKET);
	case ']': return TokenNew(lex, TOK_RBRACKET);
	case ':': return TokenNew(lex, TOK_COLON);
	case ',': return TokenNew(lex, TOK_COMMA);
	default:
		CompilerErrFatal(STAGE_LEXER, lex->src, LexerGetSrcPtr(lex), lex->currentLine,
		                 "Unexpected character");
	}

	// unreachable
	return TokenNew(lex, TOK_EOF);
}

/// AST ///

Token LexerPeekToken(Lexer *lex) {
	if (lex->validPeek) {
		return lex->peek;
	}
	lex->peek = _LexerNextInner(lex);
	lex->validPeek = true;
	return lex->peek;
}

Token LexerNext(Lexer *lex) {
	Token tok = lex->validPeek ? lex->peek : _LexerNextInner(lex);
	lex->validPeek = false;
	return tok;
}

bool TokenIsArithBinOp(TokenKind kind) {
	switch (kind) {
	case TOK_PLUS:
	case TOK_MINUS:
	case TOK_MUL:
	case TOK_DIV:
	case TOK_MOD:
	case TOK_LEQ:
	case TOK_GEQ:
	case TOK_LT:
	case TOK_GT:
	case TOK_BIT_AND:
	case TOK_BIT_OR:
	case TOK_BIT_NOT: return true;
	default: return false;
	}
}

typedef struct {
	Token type;
	Token ident;
} TypedCallParameter;

typedef enum {
	EXPR_BINOP,
	EXPR_UNOP,

	EXPR_FUNCALL,
	EXPR_BLOCK,
	EXPR_IF,

	// => ()
	EXPR_RETURN,
	EXPR_ASSIGN,
	EXPR_PROC,

	EXPR_INT_LIT,
	EXPR_UINT_LIT,
	EXPR_BOOL_LIT,
	EXPR_FLOAT_LIT,
	EXPR_SYM_LIT
} ExprTy;

// clang-format off
static char* EXPR_STR_LIT[] = {
	[EXPR_BINOP] = "EXPR_BINOP",
	[EXPR_UNOP] = "EXPR_UNOP",

	[EXPR_FUNCALL] = "EXPR_FUNCALL",
	[EXPR_BLOCK] = "EXPR_BLOCK",
	[EXPR_IF] = "EXPR_IF",

	[EXPR_RETURN] = "EXPR_RETURN",
	[EXPR_ASSIGN] = "EXPR_ASSIGN",
	[EXPR_PROC] = "EXPR_PROC",

	[EXPR_INT_LIT] = "EXPR_INT_LIT",
	[EXPR_UINT_LIT] = "EXPR_UINT_LIT",
	[EXPR_BOOL_LIT] = "EXPR_BOOL_LIT",
	[EXPR_FLOAT_LIT] = "EXPR_FLOAT_LIT",
	[EXPR_SYM_LIT] = "EXPR_SYM_LIT"
};
// clang-format off

typedef struct _Expr {
	ExprTy ty;
	union {
		struct {
			struct _Expr *lhs;
			struct _Expr *rhs;
			Token op;
		} BinaryExpr;
		struct {
			struct _Expr *rhs;
			Token op;
		} UnaryExpr;
		struct {
			Token proc;
			struct _Expr **args;
			size_t numArgs;
		} CallExpr;
		struct {
			struct _Expr **exprs;
			size_t numExprs;
		} BlockExpr;
		struct {
			struct _Expr *cond;
			struct _Expr **alt;
		} IfExpr;
		struct {
			struct Expr *value;
		} ReturnExpr;
		struct {
			Token ident;
			bool typed;
			Token type;
			struct _Expr *value;
		} AssignExpr;
		struct {
			TypedCallParameter *args;
			size_t argCount;
			Token proc;
			struct _Expr *body;
		} ProcExpr;
		struct {
			ssize_t value;
			bool flexibleType;
		} IntLiteral;
		struct {
			size_t value;
		} UIntLiteral;
		struct {
			bool value;
		} BooleanLiteral;
		struct {
			double value;
		} FloatLit;
		struct {
			Token ident;
		} SymbolLit;
	} inner;
} Expr;

Expr *ExprNew(ExprTy ty) {
	Expr *expr = malloc(sizeof(*expr));
	if (!expr) {
		AllocFailed();
	}
	expr->ty = ty;
	return expr;
}

Token LexerExpectToken(Lexer *lex, TokenKind kind) {
	Token tok = LexerNext(lex);
	if (tok.kind != kind) {
		char expected[ERR_BUF_LEN] = {0};
		sprintf(expected, "Expected token '%s', got '%s'", TOKEN_KIND_STR[kind],
		        TOKEN_KIND_STR[tok.kind]);
		CompilerErrFatal(STAGE_AST, lex->src, tok.loc, lex->currentLine, expected);
	}
	return tok;
}

Token LexerExpectTokenWith(Lexer *lex, bool (*fn)(TokenKind kind)) {
	Token tok = LexerNext(lex);
	if (!fn(tok.kind)) {
		char expected[ERR_BUF_LEN] = {0};
		sprintf(expected, "Unexpected token: '%s'", TOKEN_KIND_STR[tok.kind]);
		CompilerErrFatal(STAGE_AST, lex->src, tok.loc, lex->currentLine, expected);
	}
	return tok;
}

bool TokenIsTy(TokenKind kind) {
	return kind == TOK_INT || kind == TOK_UINT || kind == TOK_BOOL || kind == TOK_STR;
}

static Expr *Parse(Lexer *lex);

Expr *ParseProc(Lexer *lex) {
	Token name = LexerExpectToken(lex, TOK_SYM);
	LexerExpectToken(lex, TOK_LPAREN);

	Vec args;
	VecInit(&args, sizeof(TypedCallParameter));

	bool first = true;
	while (LexerPeekToken(lex).kind != TOK_RPAREN) {
		if (!first) {
			LexerExpectToken(lex, TOK_COMMA);
		}
		Token argName = LexerExpectToken(lex, TOK_SYM);
		LexerExpectToken(lex, TOK_COLON);
		Token ty = LexerExpectTokenWith(lex, TokenIsTy);

		TypedCallParameter param = {.ident = argName, .type = ty};
		VecPush(&args, &param);
		first = false;
	}

	LexerExpectToken(lex, TOK_RPAREN);
	Expr *body = Parse(lex);

	Expr *ret = ExprNew(EXPR_PROC);
	ret->inner.ProcExpr.args = VecAsPtr(args, TypedCallParameter);
	ret->inner.ProcExpr.argCount = args.len;
	ret->inner.ProcExpr.proc = name;
	ret->inner.ProcExpr.body = body;

	return ret;
}

Expr *ParseVal(Lexer *lex) {
	Token name = LexerExpectToken(lex, TOK_SYM);

	Token type;
	bool typed = false;
	if (LexerPeekToken(lex).kind == TOK_COLON) {
		type = LexerExpectTokenWith(lex, TokenIsTy);
		typed = true;
	}

	LexerExpectToken(lex, TOK_ASSIGN);
	Expr *value = Parse(lex);

	Expr *ret = ExprNew(EXPR_ASSIGN);
	ret->inner.AssignExpr.ident = name;
	ret->inner.AssignExpr.value = value;
	if (typed) {
		ret->inner.AssignExpr.typed = true;
		ret->inner.AssignExpr.type = type;
	} else {
		ret->inner.AssignExpr.typed = false;
	}

	return ret;
}

Expr *ParseFunCall(Lexer *lex, Token ident) {
	LexerExpectToken(lex, TOK_LPAREN);
	Expr *call = ExprNew(EXPR_FUNCALL);
	call->inner.CallExpr.proc = ident;

	Vec args;
	VecInit(&args, sizeof(Expr *));

	while (LexerPeekToken(lex).kind != TOK_RPAREN) {
		Expr *arg = Parse(lex);
		VecPush(&args, &arg);
		if (LexerPeekToken(lex).kind != TOK_COMMA) {
			break;
		}
		LexerNext(lex);
	}
	LexerExpectToken(lex, TOK_RPAREN);

	call->inner.CallExpr.args = VecAsPtr(args, Expr *);
	call->inner.CallExpr.numArgs = args.len;
	return call;
}

Expr *ParseUint(Token *tok) {
	Expr *uint = ExprNew(EXPR_UINT_LIT);
	uint->inner.UIntLiteral.value = ParseUintLiteral(tok->loc.ptr, tok->loc.len);
	return uint;
}

Expr *ParseInt(Token *tok, bool flexibleType) {
	Expr *num = ExprNew(EXPR_INT_LIT);
	num->inner.IntLiteral.value = ParseIntLiteral(tok->loc.ptr, tok->loc.len);
	num->inner.IntLiteral.flexibleType = flexibleType;
	return num;
}

Expr *ParseBool(bool value) {
	Expr *b = ExprNew(EXPR_BOOL_LIT);
	b->inner.BooleanLiteral.value = value;
	return b;
}

Expr *ParseSymLit(Token tok) {
	Expr *expr = ExprNew(EXPR_SYM_LIT);
	expr->inner.SymbolLit.ident = tok;
	return expr;
}

Expr *ParseBlock(Lexer *lex, bool astRoot) {
	Vec exprs;
	VecInit(&exprs, sizeof(Expr *));

	while (LexerPeekToken(lex).kind != TOK_RBRACE && LexerPeekToken(lex).kind != TOK_EOF) {
		Expr *expr = Parse(lex);
		VecPush(&exprs, &expr);
	}

	if (!astRoot) {
		LexerExpectToken(lex, TOK_RBRACE);
	}

	Expr *block = ExprNew(EXPR_BLOCK);
	block->inner.BlockExpr.exprs = VecAsPtr(exprs, Expr *);
	block->inner.BlockExpr.numExprs = exprs.len;

	return block;
}

Expr *Parse(Lexer *lex) {
	Token tok = LexerNext(lex);
	switch (tok.kind) {
	case TOK_PROC: return ParseProc(lex);
	case TOK_VAL: return ParseVal(lex);
	case TOK_UINT_LIT: return ParseUint(&tok);
	case TOK_INT_LIT: return ParseInt(&tok, false);
	case TOK_ARBITRARY_INT_LIT: return ParseInt(&tok, true);
	case TOK_TRUE: return ParseBool(true);
	case TOK_FALSE: return ParseBool(false);
	case TOK_LBRACE: return ParseBlock(lex, false);
	case TOK_SYM: {
		if (LexerPeekToken(lex).kind == TOK_LPAREN) {
			return ParseFunCall(lex, tok);
		}
		return ParseSymLit(tok);
	}
	default: {
		char err[ERR_BUF_LEN] = {0};
		sprintf(err, "Expected expression, got '%s'", TOKEN_KIND_STR[tok.kind]);
		CompilerErrFatal(STAGE_AST, lex->src, tok.loc, lex->currentLine, err);
		return NULL;
	}
	}
}

Expr *AST(Lexer *lex) { return ParseBlock(lex, true); }

void Tab(int indent) {
	if (indent) {
		fprintf(stderr, "%*c", indent * 4, ' ');
	}
}

void _ASTDumpInner(FILE *stream, Expr *node, int it, bool firstNeedsIndent) {
	if (firstNeedsIndent) {
		Tab(it);
	}
	switch (node->ty) {
	case EXPR_BLOCK:
		fprintf(stream, "BlockExpression [\n");
		for (int i = 0; i < node->inner.BlockExpr.numExprs; i++) {
			_ASTDumpInner(stream, node->inner.BlockExpr.exprs[i], it + 1, true);
		}
		Tab(it);
		fprintf(stream, "]\n");
		break;
	case EXPR_ASSIGN: {
		char ident[DBG_BUF_LEN];
		TokenSrcDebug(node->inner.AssignExpr.ident, ident);
		fprintf(stream, "AssignExpression \"%s\" ", ident);

		if (node->inner.AssignExpr.typed) {
			char type[DBG_BUF_LEN];
			TokenSrcDebug(node->inner.AssignExpr.type, type);
			fprintf(stream, "(%s) ", type);
		}

		fprintf(stream, "= ");
		_ASTDumpInner(stream, node->inner.AssignExpr.value, it, false);
		break;
	}
	case EXPR_BOOL_LIT:
		fprintf(stream, "BoolLiteral (%s)\n", node->inner.BooleanLiteral.value ? "true" : "false");
		break;
	case EXPR_SYM_LIT: {
		char sym[DBG_BUF_LEN];
		TokenSrcDebug(node->inner.SymbolLit.ident,sym);
		fprintf(stream, "SymbolLiteral (%s)\n", sym);
		break;
	}
	case EXPR_INT_LIT: fprintf(stream, "IntLiteral (%zd)\n", node->inner.IntLiteral.value); break;
	case EXPR_UINT_LIT:
		fprintf(stream, "UintLiteral (%lu)\n", node->inner.UIntLiteral.value);
		break;
	case EXPR_PROC: {
		char ident[DBG_BUF_LEN];
		TokenSrcDebug(node->inner.ProcExpr.proc, ident);
		fprintf(stream, "ProcExpression \"%s\" (", ident);
		for (int i = 0; i < node->inner.ProcExpr.argCount; i++) {
			if (i != 0) {
				fprintf(stream, ", ");
			}
			TypedCallParameter arg = node->inner.ProcExpr.args[i];
			char argbuf[DBG_BUF_LEN];
			char tybuf[DBG_BUF_LEN];
			TokenSrcDebug(arg.ident, argbuf);
			TokenSrcDebug(arg.type, tybuf);
			fprintf(stream, "%s: %s", argbuf, tybuf);
		}
		fprintf(stderr, ") [\n");
		_ASTDumpInner(stream, node->inner.ProcExpr.body, it + 1, true);
		Tab(it);
		fprintf(stream, "]\n");
		break;
	}
	case EXPR_FUNCALL: {
		char ident[DBG_BUF_LEN];
		TokenSrcDebug(node->inner.CallExpr.proc, ident);
		fprintf(stream, "CallExpression \"%s\" (\n", ident);
		for (int i = 0; i < node->inner.CallExpr.numArgs; i++) {
			Expr *arg = node->inner.CallExpr.args[i];
			_ASTDumpInner(stream, arg, it + 1, true);
		}
		Tab(it);
		fprintf(stream, ")\n");
		break;
	}
	}
}

void ASTDump(Expr *node) { _ASTDumpInner(stderr, node, 0, false); }

void ASTFree(Expr *node) {
	switch (node->ty) {
	case EXPR_BLOCK:
		for (int i = 0; i < node->inner.BlockExpr.numExprs; i++) {
			ASTFree(node->inner.BlockExpr.exprs[i]);
		}
		free(node->inner.BlockExpr.exprs);
		break;
	case EXPR_ASSIGN: ASTFree(node->inner.AssignExpr.value); break;
	case EXPR_PROC:
		free(node->inner.ProcExpr.args);
		ASTFree(node->inner.ProcExpr.body);
		break;
	case EXPR_FUNCALL:
		for (int i = 0; i < node->inner.CallExpr.numArgs; i++) {
			ASTFree(node->inner.CallExpr.args[i]);
		}
		free(node->inner.CallExpr.args);
		break;
	}
	free(node);
}

/// ARGS ///

typedef struct {
	char *long_;
	char *short_;
	char *desc;
	bool yes;
	bool ignoreOthers;
} Opt;

typedef struct {
	Opt *opts;
	size_t opts_sz;
	char *name;
	char *version;
	char *author;
	char *description;
	char *usage;
} App;

// clang-format off
typedef enum { OPT_HELP, OPT_DEBUG } Opts;
static Opt flags[] = {
	[OPT_HELP] = {.long_ = "help", .short_ = "h", .desc = "Display this message", .ignoreOthers = true},
	[OPT_DEBUG] = {.long_ = "debug", .short_ = "d", .desc = "Enable debug mode", .ignoreOthers = false}
};

static App app = {
	.opts = flags,
	.opts_sz = sizeof(flags) / sizeof(*flags),
	.name = "Compiler",
	.version = "v0.1.0",
	.author = "Safin Singh",
	.description = "Strongly-typed scripting language",
	.usage = "./bin [-h/-d] <file>"
};
// clang-format on

bool OptMatch(Opt *opt, char *arg) {
	switch (strlen(arg)) {
	case 0:
	case 1: return false;
	case 2: return *arg == '-' && *opt->short_ == *(arg + 1);
	default: {
		bool matchesDashes = memcmp(arg, "--", sizeof("--")) == 0;
		if (strlen(arg) != strlen(opt->long_)) {
			return false;
		}
		return matchesDashes && memcmp(arg + 2, opt->long_, strlen(arg) - 2);
	}
	}
}

void PrintHelp(void) {
	fprintf(stderr,
	        "%s %s: %s\n"
	        "By %s\n\n"
	        "Usage: %s\n",
	        app.name, app.version, app.description, app.author, app.usage);
	for (int i = 0; i < app.opts_sz; i++) {
		fprintf(stderr, "\t-%s, --%s\t%s\n", app.opts[i].short_, app.opts[i].long_,
		        app.opts[i].desc);
	}
	exit(EXIT_FAILURE);
}

void ParseArgs(int argc, char **argv) {
	if (argc < 2) {
		PrintHelp();
	}
	if (argc == 2) {
		CurrentFile = argv[1];
		return;
	}
	for (int i = 0; i < argc - 1; i++) {
		for (int j = 0; j < app.opts_sz; j++) {
			Opt *flag = &flags[j];
			if (OptMatch(flag, argv[i])) {
				flag->yes = true;
				if (flag->ignoreOthers) {
					goto EXIT;
				}
			}
		}
	}
EXIT:
	if (flags[OPT_HELP].yes) {
		PrintHelp();
	}
	if (flags[OPT_DEBUG].yes) {
		DEBUG = true;
	}
	CurrentFile = argv[argc - 1];
}

/// BIN ///

int MapFile(SourcePtr *outSource) {
	int fd = open(CurrentFile, O_RDONLY);
	if (fd < 0) {
		return ERROR;
	}

	struct stat sb;
	if (fstat(fd, &sb)) {
		return ERROR;
	}

	outSource->ptr = mmap(NULL, sb.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
	if (outSource->ptr == MAP_FAILED) {
		return ERROR;
	}

	outSource->len = sb.st_size;
	close(fd);

	return SUCCESS;
}

void UnmapFile(SourcePtr *file) { munmap((void *)file->ptr, file->len); }

int main(int argc, char **argv) {
	ParseArgs(argc, argv);

	SourcePtr file;
	if (MapFile(&file)) {
		perror("Failed to read file");
		PrintHelp();
	}

	Lexer lex;
	LexerInit(&lex, file);

	Expr *ast = AST(&lex);
	ASTDump(ast);

	ASTFree(ast);
	UnmapFile(&file);
}
