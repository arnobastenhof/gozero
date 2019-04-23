/*
 * Go/0 is a minimal subset of the Go programming language comparable to Wirth's
 * PL/0 in terms of expressivity, as presented in the 1976 book Algorithms +
 * Data Structures = Programs. Our aim, in particular, was to learn from
 * Wirth's materials through imitation, introducing minor variations by changing
 * both the compiler's implementation- and input languages in order instill the
 * exercise with a hint of novelty.
 *
 * Below we present the grammar for Go/0, borrowing heavily from the official
 * language specification. It should be noted, however, that strictly speaking
 * not all valid Go/0 programs would be accepted by other Go compilers, in that
 * we did not implement the usual restrictions on formatting. In addition,
 * Go/0 only supports ASCII-encoded source files, as opposed to UTF-8.
 *
 *   letter         = "a" | "b" | ... | "z" | "A" | "B" | ... | "Z" .
 *   digit          = "0" | "1" | ... | "9" .
 *   number         = digit { digit } .
 *   identifier     = letter { digit | letter } .
 *   IdentifierList = identifier { "," identifier } .
 *   SourceFile     = PackageClause ";" { TopLevelDecl ";" } .
 *   PackageClause  = "package" identifier .
 *   TopLevelDecl   = Declaration | FuncDecl .
 *   Declaration    = ConstDecl | VarDecl .
 *   ConstDecl      = "const" ( ConstSpec | "(" { ConstSpec ";" } ")" ) .
 *   ConstSpec      = identifier "=" number .
 *   VarDecl        = "var" ( VarSpec | "(" { VarSpec ";" } ")" ) .
 *   VarSpec        = IdentifierList "int" .
 *   FuncDecl       = "func" identifier "(" ")" Block .
 *   Block          = "{" { Statement ";" } "}" .
 *   Statement      = [ Declaration | Assignment | CallStmt | Block
 *                  | IfStmt | ForStmt ] .
 *   Assignment     = identifier "=" Expression .
 *   CallStmt       = identifier "(" ")" .
 *   IfStmt         = "if" Condition Block .
 *   ForStmt        = "for" Condition Block .
 *   Condition      = Expression rel_op Expression .
 *   rel_op         = "==" | "!=" | "<" | "<=" | ">" | ">=" .
 *   Expression     = [ "+" | "-" ] Term { ( "+" | "-" ) Term } .
 *   Term           = Factor { ( "*" | "/" | "%" ) Factor } .
 *   Factor         = identifier | number | "(" Expression ")" .
 *
 * In addition, all objects must be declared before they are referenced. In
 * particular, mutually recursive functions are not supported.
 *
 * Like with PL/0, we have kept the entire program to a single source file.
 */

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Various compile-time constants */
enum {
  kNumKw = 6,                 /* Number of keywords */
  kTxMax = 101,               /* Symbol table size (incl. sentinel) */
  kIdLen = 11,                /* Identifier length (incl. terminating '\0') */
  kAMax  = 4095,              /* Max value of an instruction's operand field */
  kCxMax = 201                /* Max value of the code allocation index */
};

/* Symbol sets */
typedef uint32_t symset_t;

/*
 * Individual symbols are defined as singleton symbol sets.
 */
typedef enum {
  kNul     = 0x0,             /* Invalid character */
  kPackage = 0x1,             /* Keyword "package" */
  kFunc    = 0x4,             /* Keyword "func" */
  kConst   = 0x8,             /* Keyword "const" */
  kVar     = 0x10,            /* Keyword "var" */
  kIf      = 0x20,            /* Keyword "if" */
  kFor     = 0x40,            /* Keyword "for" */
  kIdent   = 0x80,            /* Identifiers */
  kNumber  = 0x100,           /* Numbers */
  kLparen  = 0x200,           /* "(" */
  kMul     = 0x400,           /* "*" */
  kDiv     = 0x800,           /* "/" */
  kAdd     = 0x1000,          /* "+" */
  kSub     = 0x2000,          /* "-" */
  kMod     = 0x4000,          /* "%" */
  kAssign  = 0x8000,          /* "=" */
  kEq      = 0x10000,         /* "==" */
  kNeq     = 0x20000,         /* "!=" */
  kLt      = 0x40000,         /* "<" */
  kLe      = 0x80000,         /* "<=" */
  kGt      = 0x100000,        /* ">" */
  kGe      = 0x200000,        /* ">=" */
  kRparen  = 0x400000,        /* ")" */
  kLbrace  = 0x800000,        /* "{" */
  kSemicln = 0x1000000,       /* ";" */
  kRbrace  = 0x2000000,       /* "}" */
  kComma   = 0x4000000,       /* "," */
  kEof     = 0x8000000        /* end of file */
} symbol_t;

/* Various symbol sets */
enum {
  kFirstDecl = kConst | kVar | kFunc,
  kFirstStmt = kVar | kConst | kIdent | kLbrace | kIf | kFor,
  kFirstFctr = kIdent | kNumber | kLparen,
  kRelOp     = kEq | kNeq | kLt | kLe | kGt | kGe,
  kAddOp     = kAdd | kSub,
  kMulOp     = kMul | kDiv | kMod
};

/* Character kinds; defined not to overlap with symbols */
enum {
  kAlpha   = 0x10000000,      /* Letters a..z and A..Z */
  kDigit   = 0x20000000,      /* Digits 0..9 */
  kWhite   = 0x40000000       /* Whitespace */
};

/* Symbol table tags */
typedef enum {
  kVariable, kConstant, kFunction, kType
} object_t;

/*
 * Instructions contain a 3-bit opcode f, a modifier bit m and a 12-bit operand
 * a, which may be the identifier for a built-in operation (opr), a code address
 * (cal, jmp, jpc), a literal (lit), an increment (inc) or a displacement (lod,
 * sto). The modifier bit, in turn, is used with lod and sto to indicate whether
 * the referenced variable is global (1) or local (0). Finally, it should be
 * noted that the absence of a constant pool in the generated bytecode implies
 * all literals appearing in a source program must fit inside an instruction,
 * effectively instating an upper bound of 4095 on their value.
 *
 *   +-----+-----+------+
 *   |  f  |  m  |  a   |
 *   | (3) | (1) | (12) |
 *   +-----+-----+------+
 *
 */
typedef uint16_t insn_t;

/* Instruction bitmasks */
enum {
  kMmask = 0x1000,            /* Modifier bit */
  kAmask = 0xFFF              /* Operand field */
};

/* Opcodes */
typedef enum {
  kLit,                       /* lit 0, a: load literal */
  kOpr,                       /* opr 0, a: execute operation */
  kLod,                       /* lod m, a: load variable */
  kSto,                       /* sto m, a: store variable */
  kCal,                       /* cal 0, a: call function */
  kInc,                       /* inc 0, a: increment stack register */
  kJmp,                       /* jmp 0, a: unconditional jump */
  kJpc                        /* jpc 0, a: conditional jump */
} opcode_t;

/* Reserved words */
const char * const g_kw[kNumKw] = {
  "const", "for", "func", "if", "package", "var"
};

/* Keyword symbols */
const symbol_t g_kw_sym[kNumKw] = {
  kConst, kFor, kFunc, kIf, kPackage, kVar
};

/* Association of (ASCII) characters with their symbol and kind */
const uint32_t g_ch_traits[] = {
  kNul,    kNul,    kNul,    kNul,     kNul,    kNul,     kNul,    /*   0-6   */
  kNul,    kNul,    kWhite,  kWhite,   kWhite,  kWhite,   kWhite,  /*   7-13  */
  kNul,    kNul,    kNul,    kNul,     kNul,    kNul,     kNul,    /*  14-20  */
  kNul,    kNul,    kNul,    kNul,     kNul,    kNul,     kNul,    /*  21-27  */
  kNul,    kNul,    kNul,    kNul,     kWhite,  kNul,     kNul,    /*  28-34  */
  kNul,    kNul,    kMod,    kNul,     kNul,    kLparen,  kRparen, /*  35-41  */
  kMul,    kAdd,    kComma,  kSub,     kNul,    kDiv,     kDigit,  /*  42-48  */
  kDigit,  kDigit,  kDigit,  kDigit,   kDigit,  kDigit,   kDigit,  /*  49-55  */
  kDigit,  kDigit,  kNul,    kSemicln, kLt,     kAssign,  kGt,     /*  56-62  */
  kNul,    kNul,    kAlpha,  kAlpha,   kAlpha,  kAlpha,   kAlpha,  /*  63-69  */
  kAlpha,  kAlpha,  kAlpha,  kAlpha,   kAlpha,  kAlpha,   kAlpha,  /*  70-76  */
  kAlpha,  kAlpha,  kAlpha,  kAlpha,   kAlpha,  kAlpha,   kAlpha,  /*  77-83  */
  kAlpha,  kAlpha,  kAlpha,  kAlpha,   kAlpha,  kAlpha,   kAlpha,  /*  84-90  */
  kNul,    kNul,    kNul,    kNul,     kNul,    kNul,     kAlpha,  /*  91-97  */
  kAlpha,  kAlpha,  kAlpha,  kAlpha,   kAlpha,  kAlpha,   kAlpha,  /*  98-104 */
  kAlpha,  kAlpha,  kAlpha,  kAlpha,   kAlpha,  kAlpha,   kAlpha,  /* 105-111 */
  kAlpha,  kAlpha,  kAlpha,  kAlpha,   kAlpha,  kAlpha,   kAlpha,  /* 112-118 */
  kAlpha,  kAlpha,  kAlpha,  kAlpha,   kLbrace, kNul,     kRbrace, /* 119-125 */
  kNul,    kNul                                                    /* 126-127 */
};

/* Opcode mnemonics, indexed by the values of type opcode_t */
const char * const g_mnemonics[] = {
  "LIT", "OPR", "LOD", "STO", "CAL", "INC", "JMP", "JPC"
};

/* Forward declarations */
static void     Block(int * const, const symset_t);
static void     Expression(const symset_t);

/* Global state */
static FILE *   g_src;          /* Source file */
static int      g_ch = ' ';     /* Lookahead character */
static symbol_t g_sym = kNul;   /* Lookahead symbol */
static char     g_id[kIdLen];   /* Last parsed identifier */
static int32_t  g_num;          /* Last parsed number */
static char     g_line[81];     /* Line buffer (incl. terminating '\0') */
static int      g_cc = 0;       /* Character count */
static int      g_ll = 0;       /* Line length */
static uint32_t g_errs = 0;     /* Encountered errors (used as a bitset) */
static int      g_tx = 0;       /* Symbol table index */
static int      g_cx = 0;       /* Code allocation index */
static insn_t   g_code[kCxMax]; /* Code array */

/*
 * Symbol table. Note only a single namespace is supported, and that locals
 * can't hide globals. The following table describes the contents of an entry.
 *
 * kind       | val                    glb
 * -----------+------------------------------------------------------------
 * kVariable  | displacement address   whether declared globally or locally
 * kConstant  | numeric value          n.a.
 * kFunction  | code address           n.a.
 * kType      | n.a.                   n.a.
 */
static struct {
  char        name[kIdLen];
  object_t    kind;
  int         val;
  bool        glb;
} g_table[kTxMax];

/* Error marks an error in the source file */
static void
Error(const int errno)
{
  assert(errno >= 1 && errno <= 22);
  printf(" ****%*c^%d\n", g_cc-1, ' ', errno);
  g_errs |= (1 << (errno-1));
}

/* PrintErrors writes descriptive messages for encountered compilation errors */
static void
PrintErrors(void)
{
  /* 0:     sentinel
   * 1-2:   character-level errors
   * 3-15:  syntax errors
   * 16-22: semantic errors
   */
  static const char * const g_errmsg[] = {
    /*  0,1  */ "",                             "maximum line size exceeded",
    /*  2,3  */ "octal literals not supported", "= inserted",
    /*  4,5  */ "\"package\" inserted",         "identifier inserted",
    /*  6,7  */ "\";\" inserted",               "\"(\" inserted",
    /*  8,9  */ "\")\" inserted",               "\"{\" inserted",
    /* 10,11 */ "\"}\" inserted",               "EOF inserted",
    /* 12,13 */ "relop inserted",               "number inserted",
    /* 14,15 */ "changed to \"==\"",            "symbol deleted",
    /* 16,17 */ "not a type",                   "not a variable",
    /* 18,19 */ "not a function",               "not \"main\" package",
    /* 20,21 */ "assignment to non-variable",   "lookup failed",
    /* 22    */ "number too large"
  };
  int i;

  printf("  key words\n");
  for (i = 1; i <= 22; ++i) {
    if (g_errs & (1 << (i-1))) {
      printf("%*c%2d  %s\n", 9, ' ', i, g_errmsg[i]);
    }
  }
}

/* GetChar reads the lookahead character from the source file */
static void
GetChar()
{
  int ch;

  /* Once the EOF is reached, we don't expect requests for more characters */
  assert(g_ch != EOF);

  /* Time to refill the line buffer? */
  if (g_cc == g_ll) {
    assert(g_ch_traits[g_ch] & kWhite);
    printf("%5d ", g_cx);

    /* Echo each char in this line to stdout and append it to the line buffer */
    g_ll = 0;
    while ((ch = fgetc(g_src)) != '\n' && ch != EOF && g_ll < 80) {
      putchar(ch);
      g_line[g_ll++] = ch;
    }
    putchar('\n');

    /* Validate line length */
    if (ch != '\n' && ch != EOF && g_ll == 80) {
      Error(1);
      ungetc(ch, stdin);
      ch = '\n';
    }

    /* Append newline or EOF and reset character count to start of line */
    assert(ch == '\n' || ch == EOF);
    g_line[g_ll++] = ch;
    g_cc = 0;
  }

  /* Return next character from the current line */
  g_ch = g_line[g_cc++];
}

/* GetSymbol returns the next symbol to the parser */
static void
GetSymbol(void)
{
  int   i;    /* Index variable */

  /* Once the EOF is reached, we don't expect requests for more symbols */
  assert(g_sym != kEof);

  /* Skip whitespace */
  for (; g_ch_traits[g_ch] & kWhite; GetChar())
    ;

  if (g_ch_traits[g_ch] & kAlpha) { /* Identifiers */
    /* Read identifier into g_id */
    i = 0;
    do {
      /* Only the first kIdLen-1 characters are significant */
      if (i != kIdLen - 1) {
        g_id[i++] = g_ch;
      }
      GetChar();
    } while (g_ch_traits[g_ch] & (kAlpha | kDigit));
    g_id[i] = '\0';

    /* Keyword table lookup */
    for (i = 0; i != kNumKw && strcmp(g_kw[i], g_id); ++i)
      ;
    g_sym = (i == kNumKw) ? kIdent : g_kw_sym[i];
  } else if (g_ch_traits[g_ch] & kDigit) { /* Numbers */
    g_num = 0;
    if (g_ch == '0') {
      /* Octal literals are not supported */
      GetChar();
      if (g_ch_traits[g_ch] & kDigit) {
        Error(2);
        for (; g_ch == '0'; GetChar())
          ;
      }
    }
    while (g_ch_traits[g_ch] & kDigit) {
      /* Guard against overflow */
      if (g_num > (INT32_MAX - (g_ch - '0'))/10) {
        Error(22);
        g_num = 0;
      } else {
        g_num = (10 * g_num) + (g_ch - '0');
      }
      GetChar();
    }
    g_sym = kNumber;
  } else if (g_ch == '!') { /* != */
    GetChar();
    if (g_ch == '=') {
      GetChar();
      g_sym = kNeq;
    } else {
      g_sym = kNul;
    }
  } else if (g_ch == EOF) {
    g_sym = kEof;
  } else {
    /* Lookup symbol for single character */
    g_sym = g_ch_traits[g_ch] & ~(kAlpha | kDigit | kWhite);

    /* ==, <=, >= */
    if (g_ch == '=' || g_ch == '<' || g_ch == '>') {
      GetChar();
      if (g_ch == '=') {
        g_sym = g_sym << 1;
        GetChar();
      }
    } else {
      GetChar();
    }
  }
}

/* Gen emits an instruction */
static inline void
Gen(const opcode_t f, const bool m, const int a)
{
  assert(a >= 0 && a <= kAMax);
  if (g_cx == kCxMax) {
    fprintf(stderr, "program too large\n");
    exit(1);
  }
  g_code[g_cx++] = (f << 13) | (!!m << 12) | a;
}

/* ListCode prints the bytecode for the current block in assembly format */
static inline void
ListCode()
{
  int           cx0;
  insn_t        insn;
  const char *  f;
  int           m;
  int           a;

  for (cx0 = 0; cx0 < g_cx; ++cx0) {
    insn = g_code[cx0];
    f = g_mnemonics[insn >> 13];
    m = (insn & kMmask) >> 12;
    a = insn & kAmask;
    printf("%5d %3s %3d %5d\n", cx0, f, m, a);
  }
}

/* Enter adds an entry to the symbol table */
static void
Enter(const object_t kind)
{
  strcpy(g_table[g_tx].name, g_id);
  g_table[g_tx].kind = kind;
  if (kind == kFunction) {
    g_table[g_tx].val = g_cx;
  }
  /* If kind == kVariable, val is set by VarSpec */
  /* If kind == kConstant, val is set by ConstSpec */
  ++g_tx;
}

/* Position searches the symbol table, returning -1 in case of failure */
static int
Position(const char * const id)
{
  int i;

  for (i = g_tx-1; i >= 0 && strcmp(g_table[i].name, id); --i)
    ;
  return i;
}

/* Test brings the parser back in step after an unexpected lookahead symbol */
static void
Test(const symset_t fset)
{
  assert(kEof & fset);

  for (; !(g_sym & fset); GetSymbol()) {
    Error(15);
  }
}

/* Expect tests the last read symbol against an expected value */
static inline void
Expect(const symbol_t exp, const int errno)
{
  assert(errno >= 3 && errno <= 13);
  if (exp == g_sym) {
    GetSymbol();
  } else {
    Error(errno);
  }
}

/* ConstSpec = identifier "=" number . */
static void
ConstSpec(const symset_t fset)
{
  assert(g_sym & (kIdent | fset));
  if (g_sym == kIdent) {
    Enter(kConstant);
    GetSymbol();
  } else {
    Error(5);
    /* Add a dummy entry to the identifier table */
    strcpy(g_id, "dummy");
    Enter(kConstant);
  }
  Expect(kAssign, 3);
  if (g_sym == kNumber) {
    if (g_num > kAMax) {
      Error(22);
      g_num = 0;
    }
    GetSymbol();
  } else {
    Error(13);
    g_num = 0;
  }
  g_table[g_tx-1].val = g_num;
  Test(fset);
}

/* ConstDecl = "const" ( ConstSpec | "(" { ConstSpec ";" } ")" ) . */
static void
ConstDecl(const symset_t fset)
{
  assert(g_sym == kConst);
  GetSymbol();
  Test(kIdent | kLparen | fset);
  assert(!(kLparen & fset));
  if (g_sym == kIdent || g_sym & fset) {
    ConstSpec(fset);
  } else if (g_sym == kLparen) {
    GetSymbol();
    for (;;) {
      Test(kIdent | kRparen | fset);
      if (g_sym != kIdent) {
        break;
      }
      ConstSpec(kSemicln | kIdent | kRparen | fset);
      Expect(kSemicln, 6);
    }
    Expect(kRparen, 8);
    Test(fset);
  }
}

/* IdentifierList = identifier { "," identifier } . */
static int
IdentifierList(const object_t kind, const symset_t fset)
{
  int tx0 = g_tx;

  for (;;) {
    Test(kIdent | kComma | fset);
    if (g_sym == kIdent) {
      Enter(kind);
      GetSymbol();
    } else {
      Error(5);
    }
    Test(kComma | fset);
    if (g_sym != kComma) {
      break;
    }
    GetSymbol();
  }
  Test(fset);
  return tx0;
}

/* VarSpec = IdentifierList "int" . */
static void
VarSpec(int * const dx, const bool glb, const symset_t fset)
{
  int it;
  int pos;

  /* Parse variable names */
  it = IdentifierList(kVariable, kIdent | fset);

  /* Parse type */
  if (g_sym == kIdent) {
    if ((pos = Position(g_id)) >= 0 && g_table[pos].kind == kType) {
      /* Normally, we would save a representation for the parsed type in a local
      * variable at this point. However, since Go/0 only supports the integer
      * type, we omit this step here, contenting ourselves with an assertion.
      */
      assert(!strcmp(g_id, "int"));
    } else {
      Error(16);
    }
    GetSymbol();
    Test(fset);
  } else {
    Error(5);
    /* Continuing from the previous comment, had we chosen to store type
     * information in the symbol table (i.e., if "int" had not been the sole
     * supported type), we would have had to store a 'dummy' type at this point
     * inside a local variable to serve as a fallback.
     */
  }

  /* Set variable properties */
  for (; it != g_tx; ++it) {
    assert(g_table[it].kind == kVariable);
    g_table[it].val = (*dx)++;
    g_table[it].glb = glb;
    /* Here we would have set the type in g_table[it], had we reserved a field
     * for it.
     */
  }
}

/* VarDecl = "var" ( VarSpec | "(" { VarSpec ";" } ")" ) . */
static void
VarDecl(int * const dx, const bool glb, const symset_t fset)
{
  assert(g_sym == kVar);
  GetSymbol();
  Test(kIdent | kLparen | fset);
  assert(!(kLparen & fset));
  if (g_sym == kIdent || g_sym & fset) {
    VarSpec(dx, glb, fset);
  } else if (g_sym == kLparen) {
    GetSymbol();
    for (;;) {
      Test(kIdent | kRparen | fset);
      if (g_sym != kIdent) {
        break;
      }
      VarSpec(dx, glb, kSemicln | kIdent | kRparen | fset);
      Expect(kSemicln, 6);
    }
    Expect(kRparen, 8);
    Test(fset);
  }
}

/* Factor = identifier | number | "(" Expression ")" . */
static void
Factor(const symset_t fset)
{
  int       pos;
  object_t  kind;

  Test(kFirstFctr | fset);
  assert(!(fset & (kNumber | kLparen)));
  if (g_sym & (kIdent | fset)) {
    if (g_sym == kIdent) {
      if ((pos = Position(g_id)) == -1) {
        Error(21);
      } else if ((kind = g_table[pos].kind) == kVariable) {
        Gen(kLod, g_table[pos].glb, g_table[pos].val);
      } else if (kind == kConstant) {
        Gen(kLit, 0, g_table[pos].val);
      } else {
        Error(17);
      }
      GetSymbol();
    } else {
      Error(5);
    }
  } else if (g_sym == kNumber) {
    if (g_num > kAMax) {
      Error(22);
      g_num = 0;
    }
    Gen(kLit, 0, g_num);
    GetSymbol();

  } else if (g_sym == kLparen) {
    GetSymbol();
    Expression(kRparen | fset);
    Expect(kRparen, 8);
  }
  Test(fset);
}

/* Term = Factor { ( "*" | "/" | "%" ) Factor } . */
static void
Term(const symset_t fset)
{
  symbol_t  mulop;

  Factor(kMulOp | fset);
  for (;;) {
    Test(kMulOp | fset);
    if (!(g_sym & kMulOp)) {
      break;
    }
    mulop = g_sym;
    GetSymbol();
    Expression(kMulOp | fset);
    if (mulop == kMul) {
      Gen(kOpr, 0, 4);
    } else if (mulop == kDiv) {
      Gen(kOpr, 0, 5);
    } else {
      assert(mulop == kMod);
      Gen(kOpr, 0, 6);
    }
  }
  assert(g_sym & fset);
}

/* Expression = [ "+" | "-" ] Term { ( "+" | "-" ) Term } . */
static void
Expression(const symset_t fset)
{
  symbol_t  addop;

  if (g_sym & kAddOp) {
    addop = g_sym;
    GetSymbol();
  } else {
    addop = kAdd;
  }
  Term(kAddOp | fset);
  if (addop == kSub) {
    Gen(kOpr, 0, 1);
  }
  for (;;) {
    Test(kAddOp | fset);
    if (!(g_sym & kAddOp)) {
      break;
    }
    addop = g_sym;
    GetSymbol();
    Term(kAddOp | fset);
    if (addop == kAdd) {
      Gen(kOpr, 0, 2);
    } else {
      assert(addop == kSub);
      Gen(kOpr, 0, 3);
    }
  }
  assert(g_sym & fset);
}

/* Condition = Expression rel_op Expression . */
/* rel_op    = "==" | "!=" | "<" | "<=" | ">" | ">=" . */
static void
Condition(const symset_t fset)
{
  symbol_t relop = kNul;

  /* Though kAssign is not a follow symbol for Expression, in practice it is
   * frequently confused with the relop "==".
   */
  Expression(kRelOp | kAssign | fset);
  if (g_sym & (kRelOp | kAssign)) {
    if (g_sym == kAssign) {
      Error(14);
      relop = kEq;
    } else {
      relop = g_sym;
    }
    GetSymbol();
  } else {
    Error(12);
  }
  Expression(fset);
  switch (relop) {
  case kEq:  Gen(kOpr, 0, 8);  break;
  case kNeq: Gen(kOpr, 0, 9);  break;
  case kLt:  Gen(kOpr, 0, 10); break;
  case kLe:  Gen(kOpr, 0, 11); break;
  case kGt:  Gen(kOpr, 0, 12); break;
  case kGe:  Gen(kOpr, 0, 13); break;
  default:
    assert(relop == kNul);
  }
  assert(g_sym & fset);
}

/* IfStmt = "if" Condition Block . */
static void
IfStmt(int * const dx, const symset_t fset)
{
  int cx1;

  assert(g_sym == kIf);
  GetSymbol();
  Condition(kLbrace | fset);  /* Instructions for condition */
  cx1 = g_cx;
  Gen(kJpc, 0, 0);            /* Jump to L0 if condition evaluates to false */
  Block(dx, fset);            /* Instructions for body */
  g_code[cx1] |= g_cx;        /* L0 */
}

/* ForStmt = "for" Condition Block . */
static void
ForStmt(int * const dx, const symset_t fset)
{
  int cx1, cx2;

  assert(g_sym == kFor);
  GetSymbol();
  cx1 = g_cx;                 /* L0 */
  Condition(kLbrace | fset);  /* Instructions for condition */
  cx2 = g_cx;
  Gen(kJpc, 0, 0);            /* Jump to L1 if condition evaluates to false */
  Block(dx, fset);            /* Instructions for body */
  Gen(kJmp, 0, cx1);          /* Jump to L0 */
  g_code[cx2] |= g_cx;        /* L1 */
}

/* Statement  = [ Declaration | Assignment | CallStmt | Block
 *            | IfStmt | ForStmt ] .
 * Assignment = identifier "=" Expression .
 * CallStmt   = identifier "(" ")" .
 */
static void
Statement(int * const dx, const symset_t fset)
{
  int pos;    /* Symbol table index */

  if (g_sym == kVar) {
    VarDecl(dx, false, fset);
  } else if (g_sym == kConst) {
    ConstDecl(fset);
  } else if (g_sym == kIdent) {
    if ((pos = Position(g_id)) == -1) {
      Error(21);
    }
    GetSymbol();
    Test(kAssign | kLparen | fset);
    assert(!(fset & kLparen));
    if (g_sym == kAssign || g_sym & fset) {
      /* Assignment */
      object_t kind;
      if (g_sym != kAssign) {
        Error(3);
      }
      if ((kind = g_table[pos].kind) != kVariable) {
        Error(20);
      }
      if (g_sym == kAssign) {
        GetSymbol();
      }
      Expression(fset);
      if (kind == kVariable) {
        Gen(kSto, g_table[pos].glb, g_table[pos].val);
      }
    } else {
      /* CallStmt */
      assert(g_sym == kLparen);
      GetSymbol();
      if (g_sym == kRparen) {
        if (pos != -1) {
          if (g_table[pos].kind == kFunction) {
            Gen(kCal, 0, g_table[pos].val);
          } else {
            Error(18);
          }
        }
        GetSymbol();
      } else {
        Error(8);
      }
      Test(fset);
    }
  } else if (g_sym == kLbrace) {
    Block(dx, fset);
  } else if (g_sym == kIf) {
    IfStmt(dx, fset);
  } else if (g_sym == kFor) {
    ForStmt(dx, fset);
  }
  assert(g_sym & fset);
}

/* Block = "{" { Statement ";" } "}" . */
static void
Block(int * const dx, const symset_t fset)
{
  int tx0 = g_tx;

  Test(kLbrace | kFirstStmt | kRbrace | fset);
  Expect(kLbrace, 9);
  for (;;) {
    Test(kFirstStmt | kSemicln | kRbrace | fset);
    if (!(g_sym & (kFirstStmt | kSemicln))) {
      break;
    }
    Statement(dx, kSemicln | kFirstStmt | kRbrace | fset);
    Expect(kSemicln, 6);
  }
  Expect(kRbrace, 10);
  Test(fset);

  /* Make variables declared within the block go out of scope */
  g_tx = tx0;
}

/* FuncDecl = "func" identifier "(" ")" Block . */
static void
FuncDecl(const symset_t fset)
{
  int   dx = 2; /* A dynamic link and return address precede local vars */
  int   pc0;

  assert(g_sym == kFunc);
  GetSymbol();
  /* While not in accordance with Stirling's error recovery scheme, the FIRST
   * set for statements is here included with the call to Test to prevent
   * the parser from skipping entire function bodies.
   */
  Test(kIdent | kLparen | kRparen | kLbrace | kFirstStmt | fset);
  if (g_sym == kIdent) {
    Enter(kFunction);
    GetSymbol();
  } else {
    Error(5);
  }
  Expect(kLparen, 7);
  Expect(kRparen, 8);

  /* Variable declarations may appear anywhere inside a function body, in
   * particular following code for which instructions are to be generated.
   * At the same time, INC must be emitted first; i.e., before knowing how
   * much space actually has to be reserved on the stack for locals. To this
   * end, we first give INC a dummy argument of 0, and fix it later.
   */
  pc0 = g_cx;
  Gen(kInc, 0, 0);
  Block(&dx, fset);
  g_code[pc0] |= dx;

  /* Emit a return */
  Gen(kOpr, 0, 0);
}

/* TopLevelDecl = Declaration | FuncDecl . */
static void
TopLevelDecl(int * const dx, const symset_t fset) {
  if (g_sym == kConst) {
    ConstDecl(fset);
  } else if (g_sym == kVar) {
    VarDecl(dx, true, fset);
  } else {
    assert(g_sym == kFunc);
    FuncDecl(fset);
  }
}

/* PackageClause = "package" identifier . */
static void
PackageClause(const symset_t fset)
{
  Test(kPackage | kIdent | fset);
  Expect(kPackage, 4);
  if (g_sym == kIdent) {
    if (strcmp("main", g_id)) {
      Error(19);
    }
    GetSymbol();
  } else {
    Error(5);
  }
  Test(fset);
}

/* SourceFile = PackageClause ";" { TopLevelDecl ";" } . */
static void
SourceFile(void)
{
  int dx = 0;   /* displacement address for local variables */
  int pos;      /* position inside the symbol table */

  /* Parse package clause */
  GetSymbol();
  PackageClause(kSemicln | kFirstDecl | kEof);
  Expect(kSemicln, 6);

  /* Forward JMP to L0 (see below) */
  Gen(kJmp, 0, 0);

  /* Parse global declarations and emit instructions for functions */
  for (;;) {
    Test(kFirstDecl | kEof);
    if (!(g_sym & kFirstDecl)) {
      break;
    }
    TopLevelDecl(&dx, kSemicln | kFirstDecl | kEof);
    Expect(kSemicln, 6);
  }
  if (g_sym != kEof) {
    Error(11);
  }

  /* Emit instructions to call main and afterwards halt the interpreter */
  if ((pos = Position("main")) >= 0 && g_table[pos].kind == kFunction) {
    g_code[0] |= g_cx;               /* L0 */
    Gen(kInc, 0, dx);                /* INC stack ptr by no. of global vars */
    Gen(kCal, 0, g_table[pos].val);  /* CAL main */
    Gen(kJmp, 0, 0);                 /* JMP to 0 (ends interpretation) */
  }
}

/*
 * The interpreter features a stack along with a separate code area, as well as
 * three special-purpose registers: P (program counter), I (instruction
 * register), B (base register) and T (top-of-stack). P points at the next
 * instruction that is to be fetched from the code area and stored in I. B and
 * T, in contrast, point into the stack, as explained in the diagram below. In
 * short, the latter is organized into stack frames that are pushed and popped
 * with every function call, resp. any return therefrom. They are chained
 * together via dynamic chains, in addition storing a return address and any
 * local variables (incl. an operand stack).
 * 
 * highest address --> +------------------+ <-- T (top-of-stack register)
 *                     | local variables  |  }
 *                     +------------------+  }
 *                     |  return address  |  } callee
 *                     +------------------+  }
 *                 +---+-- dynamic link   |  }
 *                 |   +------------------+ <-- B (base register)
 *                 |   | local variables  |  }
 *                 |   +------------------+  }
 *                 |   |  return address  |  } caller
 *                 |   +------------------+  }
 *                 |   |   dynamic link   |  }
 *                 +-> +------------------+  }
 *                             :
 *                             :
 *                     +------------------+
 *                     | global variables |
 * lowest address ---> +------------------+
 *
 * Note that, in contrast to PL/0, Go/0 does not support nested functions,
 * eliminating the need for a static link.
 */
static void
Interpret(void)
{
  static int32_t  stack[500];
  int             p = 0;        /* program counter */
  int             b = 0;        /* base register */
  int             t = 0;        /* top-of-stack register */
  int             i;            /* instruction register */
  int             m;            /* modifier bit */
  int             a;            /* operand */

  do {
    /* fetch and decode */
    i = g_code[p++];
    m = i & kMmask;
    a = i & kAmask;

    /* execute */
    switch (i >> 13) {
    case kLit:
      stack[t++] = a;
      break;
    case kOpr:
      switch (a) {
      case 0: /* return */
        t = b;
        b = stack[t];
        p = stack[t+1];
        break;
      case 1:  stack[t-1] = -stack[t-1]; break;
      case 2:  stack[t-1] = stack[t-2] +  stack[t-1]; break;
      case 3:  stack[t-1] = stack[t-2] -  stack[t-1]; break;
      case 4:  stack[t-1] = stack[t-2] *  stack[t-1]; break;
      case 5:  stack[t-1] = stack[t-2] /  stack[t-1]; break;
      case 6:  stack[t-1] = stack[t-2] %  stack[t-1]; break;
      case 8:  stack[t-1] = stack[t-2] == stack[t-1]; break;
      case 9:  stack[t-1] = stack[t-2] != stack[t-1]; break;
      case 10: stack[t-1] = stack[t-2] <  stack[t-1]; break;
      case 11: stack[t-1] = stack[t-2] <= stack[t-1]; break;
      case 12: stack[t-1] = stack[t-2] >  stack[t-1]; break;
      case 13: stack[t-1] = stack[t-2] >= stack[t-1]; break;
      default:
        assert(0 && "illegal OPR operand");
      }
      break;
    case kLod:
      stack[t++] = stack[(m ? 0 : b) + a];
      break;
    case kSto:
      stack[(m ? 0 : b) + a] = stack[--t];
      printf("%d\n", stack[t]);
      break;
    case kCal:
      stack[t] = b;
      stack[t+1] = p;
      b = t;
      p = a;
      /* Note T is incremented by a separate INC, emitted after every CAL */
      break;
    case kInc:
      t += a;
      break;
    case kJmp:
      p = a;
      break;
    case kJpc:
      if (!stack[--t]) {
        p = a;
      }
      break;
    default:
      assert(0);
    }
  } while (p != 0);
}

static int
Run(void)
{
  int sc;

  assert(g_src != NULL);

  /* Initialize symbol table with a predeclared identifier for the int type */
  g_table[g_tx].kind = kType;
  strcpy(g_table[g_tx].name, "int");
  ++g_tx;

  /* Compile and list assembly */
  SourceFile();
  ListCode();

  /* Run interpreter if no compilation errors were encountered */
  if ((sc = g_errs != 0)) {
    printf("  errors in source file\n");
    PrintErrors();
  } else {
    Interpret();
    printf("  end go/0\n");
  }

  /* 0 indicates success, 1 failure */
  return sc;
}

int
main(int argc, char *argv[])
{
  int sc = 1;

  if (argc == 1) {
    g_src = stdin;
    sc = Run();
  } else if (argc == 2) {
    if ((g_src = fopen(argv[1], "r")) != NULL) {
      sc = Run();
      if (fclose(g_src) == EOF) {
        perror(argv[0]);
      }
    } else {
      perror(argv[0]);
    }
  } else {
    fprintf(stderr, "%s: too many arguments\n", argv[0]);
  }

  return sc;
}
