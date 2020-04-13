package wemelt;

import beaver.Symbol;
import wemelt.Parser.Terminals;

%%

%class Scanner
%extends beaver.Scanner
%function nextToken
%type Symbol
%yylexthrow Scanner.Exception

%eofval{
	return newToken(Terminals.EOF);
%eofval}

%line
%column

%{
    Symbol resolve(String name) {
      if (name.matches("r[0-9]+") || name.startsWith("r_")) {
          return newToken(Terminals.REG_ID, name);
      } else {
          return newToken(Terminals.ID,   name);
      }
    }

	Symbol newToken(short id)
	{
		return newToken(id, yytext());
	}

	Symbol newToken(short id, Object value)
	{
		return new Symbol(id, yyline + 1, yycolumn + 1, yylength(), value);
	}
%}

NL = \r|\n|\r\n
WS = {NL} | [ \t\f]

%%

<YYINITIAL> {

"//" .* {NL} {}
"#"  .* {NL} {}
"/*" [^*] ~"*/" | "/*" "*"+ "/" {}
{WS}+ {}

"("         { return newToken(Terminals.LPAREN);   }
")"         { return newToken(Terminals.RPAREN);   }
"["         { return newToken(Terminals.LBRACK);   }
"]"         { return newToken(Terminals.RBRACK);   }
"{"         { return newToken(Terminals.LBRACE);   }
"}"         { return newToken(Terminals.RBRACE);   }
//"++"        { return newToken(Terminals.INCR);     }
//"--"        { return newToken(Terminals.DECR);     }
//"."         { return newToken(Terminals.DOT);      }
"!"         { return newToken(Terminals.BANG);     }
"~"         { return newToken(Terminals.TILDE);    }
//"sizeof"    { return newToken(Terminals.SIZEOF);   }
"*"         { return newToken(Terminals.STAR);     }
"/"         { return newToken(Terminals.DIV);      }
"%"         { return newToken(Terminals.MOD);      }
"+"         { return newToken(Terminals.PLUS);     }
"-"         { return newToken(Terminals.MINUS);    }
"<<"        { return newToken(Terminals.SHL);      }
">>"        { return newToken(Terminals.SHR);      }
">>>"        { return newToken(Terminals.ASHR);      }
"<"         { return newToken(Terminals.LT);       }
"<="        { return newToken(Terminals.LE);       }
">="        { return newToken(Terminals.GE);       }
">"         { return newToken(Terminals.GT);       }
"=="        { return newToken(Terminals.EQ);       }
"!="        { return newToken(Terminals.NEQ);      }
"&"         { return newToken(Terminals.AMP);      }
"^"         { return newToken(Terminals.CARET);    }
"|"         { return newToken(Terminals.PIPE);     }
"&&"        { return newToken(Terminals.AND);      }
"||"        { return newToken(Terminals.OR);       }
//"?"         { return newToken(Terminals.QUESTION); }
":"         { return newToken(Terminals.COLON);    }
"="         { return newToken(Terminals.ASG); }

","         { return newToken(Terminals.COMMA);    }
";"         { return newToken(Terminals.SEMICOLON);}

"CAS"       { return newToken(Terminals.CAS);     }

//"break"     { return newToken(Terminals.BREAK);    }
//"return"    { return newToken(Terminals.RETURN);   }
//"continue"  { return newToken(Terminals.CONTINUE); }
"do"        { return newToken(Terminals.DO);       }
"while"     { return newToken(Terminals.WHILE);    }
//"for"       { return newToken(Terminals.FOR);      }
"if"        { return newToken(Terminals.IF);       }
"else"      { return newToken(Terminals.ELSE);     }

"fence"     { return newToken(Terminals.FENCE);    }
"cfence"     { return newToken(Terminals.CFENCE);    }
"_L"       { return newToken(Terminals.LPRED);      }
"_Mode"       { return newToken(Terminals.MODE);     }
"NoRW"      { return newToken(Terminals.NORW);    }
"NoW"      { return newToken(Terminals.NOW);    }
"RW"      { return newToken(Terminals.RW);    }
"_invariant" {return newToken(Terminals.INVARIANT);}
"_Gamma" {return newToken(Terminals.GAMMA);}
"_Gamma_0" {return newToken(Terminals.GAMMA_0);}
"_P_0" {return newToken(Terminals.P_0);}
"_Stable" {return newToken(Terminals.STABLE);}
"_var"      { return newToken(Terminals.VAR);     }
"_array"    { return newToken(Terminals.ARRAY);     }

"TRUE" { return newToken(Terminals.TRUE);    }
"FALSE" { return newToken(Terminals.FALSE);    }
"LOW"   { return newToken(Terminals.LOW);    }
"HIGH" { return newToken(Terminals.HIGH);    }

"->"        { return newToken(Terminals.MAPSTO);    }

[a-zA-Z_][a-zA-Z_0-9]*
            { return resolve(yytext()); }

[0-9]+      { return newToken(Terminals.NUM, new Integer(yytext())); }

[^]         { throw new Scanner.Exception("unexpected character '" + yytext() + "'"); }

}



