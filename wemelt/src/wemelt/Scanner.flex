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
        return newToken(Terminals.ID, name);
    }

    Symbol resolvePrime(String name) {
            return newToken(Terminals.PRIMEID, name);
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
    "!"         { return newToken(Terminals.BANG);     }
    "~"         { return newToken(Terminals.TILDE);    }
    "*"         { return newToken(Terminals.STAR);     }
    "/"         { return newToken(Terminals.DIV);      }
    "%"         { return newToken(Terminals.MOD);      }
    "+"         { return newToken(Terminals.PLUS);     }
    "-"         { return newToken(Terminals.MINUS);    }
    "<<"        { return newToken(Terminals.SHL);      }
    ">>"        { return newToken(Terminals.SHR);      }
    ">>>"       { return newToken(Terminals.ASHR);     }
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
    ":"         { return newToken(Terminals.COLON);    }
    "="         { return newToken(Terminals.ASG);      }


    //"<=>"       { return newToken(Terminals.EQV);      }
    //"==>"       { return newToken(Terminals.IMP);      }
    ","         { return newToken(Terminals.COMMA);    }
    ";"         { return newToken(Terminals.SEMICOLON);}
    //"::"        { return newToken(Terminals.DCOLON);   }

    "CAS"       { return newToken(Terminals.CAS);      }

    "do"        { return newToken(Terminals.DO);       }
    "while"     { return newToken(Terminals.WHILE);    }
    "if"        { return newToken(Terminals.IF);       }
    "else"      { return newToken(Terminals.ELSE);     }

    "fence"     { return newToken(Terminals.FENCE);    }
    "cfence"    { return newToken(Terminals.CFENCE);    }
    "_L"        { return newToken(Terminals.LPRED);      }
    "_L_G"      { return newToken(Terminals.LPREDGUAR);      }
    "_L_R"      { return newToken(Terminals.LPREDRELY);      }

    "_invariant"   {return newToken(Terminals.INVARIANT);}
    "_P_inv"    {return newToken(Terminals.P_INV);}
    "_R_var"    {return newToken(Terminals.R_VAR);}
    "_G_var"    {return newToken(Terminals.G_VAR);}
    //"_G"        {return newToken(Terminals.GUARANTEE);}
    "_Gamma"    {return newToken(Terminals.GAMMA);}
    "_Gamma_0"  {return newToken(Terminals.GAMMA_0);}
    "_P_0"      {return newToken(Terminals.P_0);}
    "_local var"      { return newToken(Terminals.LOCAL);     }
    "_global var"      { return newToken(Terminals.GLOBAL);     }
    //"_array"    { return newToken(Terminals.ARRAY);     }

    "TRUE"      { return newToken(Terminals.TRUE);    }
    "FALSE"     { return newToken(Terminals.FALSE);    }

    "->"        { return newToken(Terminals.MAPSTO);    }

    //"exists"    { return newToken(Terminals.EXISTS);   }
    //"forall"    { return newToken(Terminals.FORALL);   }

    [a-zA-Z_][a-zA-Z_0-9]*
                { return resolve(yytext()); }
    [a-zA-Z_][a-zA-Z_0-9]*[']
                { return resolvePrime(yytext()); }

    [0-9]+      { return newToken(Terminals.NUM, new Integer(yytext())); }

    [^]         { throw new Scanner.Exception("unexpected character '" + yytext() + "'"); }
}



