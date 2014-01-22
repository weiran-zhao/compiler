//----------------------------------------------------------------------------
// Lexical analysis part of cool compiler
// This project took me 5 ~ 6 hours to read lex, jlex manual, and figure out the
// relationship between each piece of code. After which, I know what to program
// and where to put the program. 
// It took me 6 hours to finish the code and 3 hours to debug the code according
// to the grading script.
// I would say this is a 15 to 20 hours of work for me.
//-----------
//References:
//-----------
// [1] http://www.cs.princeton.edu/~appel/modern/java/JLex/current/sample.lex
//      examples on how to handle comments
// [2] http://dinosaur.compilertools.net/lex/index.html
//      for some regular expression questions.
// [3] A thread in discussion forum called "Conflicting instructions regarding
// handling EOF in Java" (you will have to sign up for 2013,Feb session to see
//      for how to handle eof in string or comments
// [4] http://www.cs.princeton.edu/~appel/modern/java/JLex/current/manual.html
//      this is the jlex manual
// [5] http://docs.oracle.com/javase/1.5.0/docs/api/java/lang/StringBuffer.html
//      API of java's StringBuffer class
// [6] http://home.adelphi.edu/~sbloch/class/271/examples/lexyacc/
//      Even if I am using jlex, examples from lex can shead some lights
//============================================================
// Ryan (Weiran) Zhao 
// Started: 2 days before Tue,Jan 21th 2014 10:56:33 AM EST
// Modified: Tue,Jan 21th 2014 05:10:02 PM EST
//           handle comments and it took about 3 hours because the stupid way
//           I was thinking
// Modified: Tue,Jan 21th 2014 07:21:03 PM EST
//           figure out how to add string to inttable, idtable, stringtable
// Modified: Tue,Jan 21th 2014 10:01:39 PM EST
//           kind of ridiculous to find out java doesn't support vertical
//           whitespace '\v'
// Modified: Tue,Jan 21th 2014 11:01:36 PM EST 
//           It turns out the way to include vertical whitespace is to use octal 
//           number \13
// Last Modified: Wed,Jan 22th 2014 12:36:10 AM EST
//----------------------------------------------------------------------------
/*
 *  The scanner definition for COOL.
 */

import java_cup.runtime.Symbol;

%%

%{

/*  Stuff enclosed in %{ %} is copied verbatim to the lexer class
 *  definition, all the extra variables/functions you want to use in the
 *  lexer actions should go here.  Don't remove or modify anything that
 *  was there initially.  */

    // Max size of string constants
    static int MAX_STR_CONST = 1025;

    // For assembling string constants
    StringBuffer string_buf = new StringBuffer();

    private int curr_lineno = 1;
    int get_curr_lineno() {
        return curr_lineno;
    }

    private AbstractSymbol filename;

    void set_filename(String fname) {
        filename = AbstractTable.stringtable.addString(fname);
    }

    AbstractSymbol curr_filename() {
        return filename;
    }
%}

%init{

/*  Stuff enclosed in %init{ %init} is copied verbatim to the lexer
 *  class constructor, all the extra initialization you want to do should
 *  go here.  Don't remove or modify anything that was there initially. */

    // empty for now
%init}

%eofval{

/*  Stuff enclosed in %eofval{ %eofval} specifies java code that is
 *  executed when end-of-file is reached.  If you use multiple lexical
 *  states and want to do something special if an EOF is encountered in
 *  one of those states, place your code in the switch statement.
 *  Ultimately, you should return the EOF symbol, or your lexer won't
 *  work.  */

    switch(yy_lexical_state) {
        case YYINITIAL:
            /* nothing special to do in the initial state */
            break;
        // taking care of comment state 1 and 2
        case COMMENT1:
            yybegin(YYINITIAL);
            return new Symbol(TokenConstants.ERROR, new String("EOF in comment")); 
        case COMMENT2:
            break;
        case STRING:
            yybegin(YYINITIAL);
            return new Symbol(TokenConstants.ERROR, new String("EOF in string constant")); 

    }
    return new Symbol(TokenConstants.EOF);
%eofval}

%{
    // this is for nested comments "(* (*"
    private int cmtCnt = 0;
    private boolean string2long = false;
    private boolean stringhasnull = false;
    // whether backslash has been translated or not
    private boolean backslashEscaped = false;
%}

%class CoolLexer
%cup
%state COMMENT1
%state COMMENT2
%state STRING

Digit = [0-9]
Letter = [a-zA-Z]
WhiteSpace = [\t \n\r\f\13]+
NonNewlineWS = [\t \r\f\13]+

a= [aA]
b= [bB]
c= [cC]
d= [dD]
e= [eE]
f= [fF]
g= [gG]
h= [hH]
i= [iI]
j= [jJ]
k= [kK]
l= [lL]
m= [mM]
n= [nN]
o= [oO]
p= [pP]
q= [qQ]
r= [rR]
s= [sS]
t= [tT]
u= [uU]
v= [vV]
w= [wW]
x= [xX]
y= [yY]
z= [zZ]
%%
<YYINITIAL>\"
{   /* string */
    // clear string buffer
    string_buf.delete(0,string_buf.length());
    backslashEscaped = false;
    string2long = false;
    stringhasnull = false;
    yybegin(STRING); }

<STRING>\"
{   /* string end */
    // takes care of escaped string first
    if((string_buf.length()>0) && (string_buf.charAt(string_buf.length()-1) == '\\') && !backslashEscaped) {
        string_buf.setCharAt(string_buf.length()-1,'\"');
    } else {
        yybegin(YYINITIAL); 
        if(string2long) {
            return new Symbol(TokenConstants.ERROR, new String("String constant too long")); 
        }
        if(stringhasnull) {
            return new Symbol(TokenConstants.ERROR, new String("String contains null character")); 
        }
        // do remember to cast string_buf to String class
        //System.out.println(string_buf);
        return new Symbol(TokenConstants.STR_CONST, AbstractTable.stringtable.addString(string_buf.toString())); 
    }
}

<STRING>\n
{   /* check unescaped newline*/
    curr_lineno +=1;
    if(string_buf.length()== 0) {
        yybegin(YYINITIAL);
        return new Symbol(TokenConstants.ERROR, new String("Unterminated string constant")); 
    } else {
        char c = string_buf.charAt(string_buf.length()-1);
        if(c == '\\' && !backslashEscaped) {
            string_buf.setCharAt(string_buf.length()-1, '\n');
        } else { // unescaped newline happened
            yybegin(YYINITIAL);
            return new Symbol(TokenConstants.ERROR, new String("Unterminated string constant")); 
        }
    }
}


<STRING>[^\n]
{   /* process each character in a string */
    // check if string is too long
    if(string2long || stringhasnull) {
        /* do nothing */
    } else {
        // add character to string buffer depending on cases
        // check if there are nulls
        if(yytext().charAt(0) == '\0') {
            stringhasnull = true;
        } else {
        	int len=string_buf.length();
            // always need to look back to determine if a character is escaped
            if(len > 0 ) {
                // index is 1 smaller than length
                int idx=len-1;
                char c = string_buf.charAt(idx);
                if((c=='\\') && (!backslashEscaped)) {
                    switch(yytext().charAt(0)) {
                        // four sepecial cases defined in cool manual of page 15
                        case 'b':
                            string_buf.setCharAt(idx, '\b');
                            break;
                        case 't':
                            string_buf.setCharAt(idx, '\t');
                            break;
                        case 'n':
                            string_buf.setCharAt(idx, '\n');
                            break;
                        case 'f':
                            string_buf.setCharAt(idx, '\f');
                            break;
                            // sepcial care of '\\'
                        case '\\':
                            string_buf.setCharAt(idx, yytext().charAt(0));
                            backslashEscaped = true;
                            // otherwise, the '\x' is 'x'
                        default:
                            string_buf.setCharAt(idx, yytext().charAt(0));
                            break;
                    }
                } else { // just append current yytext()
                    if(yytext().charAt(0) == '\\') {
                        backslashEscaped = false;
                    }
                    string_buf.append(yytext());
                }
            } else { // this is the first element, just add in
                string_buf.append(yytext());
            }
        }
        // check the length of string
        if(string_buf.length() >= MAX_STR_CONST) {
            string2long = true;
        }
    }
}

<YYINITIAL>{Digit}+
{   /* integer */ 
    return new Symbol(TokenConstants.INT_CONST, AbstractTable.inttable.addString(yytext())); }

<YYINITIAL>t{r}{u}{e}
{   /* true */
    return new Symbol(TokenConstants.BOOL_CONST,new Boolean(true)); }

<YYINITIAL>f{a}{l}{s}{e}
{   /* false */
    return new Symbol(TokenConstants.BOOL_CONST,new Boolean(false)); }

<YYINITIAL>"(*"
{   /* let's handle comments */
    yybegin(COMMENT1); 
    cmtCnt = 1; }

<YYINITIAL>"*)"
{   /* unmatched "*)" */
    return new Symbol(TokenConstants.ERROR, new String("Unmatched *)")); }

<COMMENT1>"(*"
{   /* nested comment */
    cmtCnt+=1; }

<COMMENT1>"*)"
{   /* in comment state, "*)" ends comments, if cmtCnt=0 */
    cmtCnt -=1;
    if(cmtCnt==0) {
        yybegin(YYINITIAL);
    } 
}

<YYINITIAL,COMMENT1>\n
{   /* newline */
    curr_lineno += 1; }

<COMMENT1>[^\n]
{   /* comment text */ }

<YYINITIAL>"--"
{   /* another kind of comment */
    yybegin(COMMENT2); }

<COMMENT2>\n
{   /* one way to end comment */
    curr_lineno+=1;
    yybegin(YYINITIAL); }

<COMMENT2>.
{   /* comment text */ }

<YYINITIAL>{c}{l}{a}{s}{s}
{   /* class */
    return new Symbol(TokenConstants.CLASS); }

<YYINITIAL>{i}{n}
{   /* in */
    return new Symbol(TokenConstants.IN); }

<YYINITIAL>{i}{n}{h}{e}{r}{i}{t}{s}
{   /* inherits */
    return new Symbol(TokenConstants.INHERITS); }

<YYINITIAL>{i}{s}{v}{o}{i}{d}
{   /* isvoid */
    return new Symbol(TokenConstants.ISVOID); }

<YYINITIAL>{l}{e}{t}
{   /* let */
    return new Symbol(TokenConstants.LET); }

<YYINITIAL>{n}{e}{w}
{   /* new */
    return new Symbol(TokenConstants.NEW); }

<YYINITIAL>{o}{f}
{   /* of */
    return new Symbol(TokenConstants.OF); }

<YYINITIAL>{n}{o}{t}
{   /* not */
    return new Symbol(TokenConstants.NOT); }

<YYINITIAL>{l}{o}{o}{p}
{   /* loop */
    return new Symbol(TokenConstants.LOOP); }

<YYINITIAL>{p}{o}{o}{l}
{   /* pool */
    return new Symbol(TokenConstants.POOL); }

<YYINITIAL>{c}{a}{s}{e}
{   /* case */
    return new Symbol(TokenConstants.CASE); }

<YYINITIAL>{e}{s}{a}{c}
{   /* esac */
    return new Symbol(TokenConstants.ESAC); }

<YYINITIAL>{i}{f}
{   /* if */
    return new Symbol(TokenConstants.IF); }

<YYINITIAL>{t}{h}{e}{n}
{   /* then */
    return new Symbol(TokenConstants.THEN); }

<YYINITIAL>{e}{l}{s}{e}
{   /* else */
    return new Symbol(TokenConstants.ELSE); }

<YYINITIAL>{f}{i}
{   /* fi */
    return new Symbol(TokenConstants.FI); }

<YYINITIAL>{w}{h}{i}{l}{e}
{   /* while */
    return new Symbol(TokenConstants.WHILE); }

<YYINITIAL>"=>"	
{   /* ==> */
    return new Symbol(TokenConstants.DARROW); }

<YYINITIAL>"<-"	
{   /* assign */
    return new Symbol(TokenConstants.ASSIGN); }

<YYINITIAL>"<="	
{   /* less than or equal */
    return new Symbol(TokenConstants.LE); }

<YYINITIAL>"+"
{    /* plus */
    return new Symbol(TokenConstants.PLUS); }

<YYINITIAL>"-"
{    /* minus */
    return new Symbol(TokenConstants.MINUS); }

<YYINITIAL>"*"
{    /* multiply */
    return new Symbol(TokenConstants.MULT); }

<YYINITIAL>"/"
{    /* divide */
    return new Symbol(TokenConstants.DIV); }

<YYINITIAL>"("
{    /* left parenthesis */
    return new Symbol(TokenConstants.LPAREN); }

<YYINITIAL>")"
{    /* right parenthesis*/
    return new Symbol(TokenConstants.RPAREN); }

<YYINITIAL>"{"
{    /* left brace */
    return new Symbol(TokenConstants.LBRACE); }

<YYINITIAL>"}"
{    /* right brace*/
    return new Symbol(TokenConstants.RBRACE); }

<YYINITIAL>"."
{    /* dot */
    return new Symbol(TokenConstants.DOT); }

<YYINITIAL>":"
{    /* colon */
    return new Symbol(TokenConstants.COLON); }

<YYINITIAL>","
{    /* comma */
    return new Symbol(TokenConstants.COMMA); }

<YYINITIAL>";"
{    /* semi colon */
    return new Symbol(TokenConstants.SEMI); }

<YYINITIAL>"="
{    /* equal */
    return new Symbol(TokenConstants.EQ); }

<YYINITIAL>"~"
{    /* negate */
    return new Symbol(TokenConstants.NEG); }

<YYINITIAL>"<"
{    /* less than */
    return new Symbol(TokenConstants.LT); }

<YYINITIAL>"@"
{    /* at */
    return new Symbol(TokenConstants.AT); }

<YYINITIAL>[A-Z]({Digit}|{Letter}|_)*
{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }

<YYINITIAL>[a-z]({Digit}|{Letter}|_)*
{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
    
<YYINITIAL>{NonNewlineWS}
{    /*do nothing*/ }

<YYINITIAL>[^\n]
{ /* This rule should be the very last
     in your lexical specification and
     will match match everything not
     matched by other lexical rules. */
    return new Symbol(TokenConstants.ERROR, new String(yytext())); 
}
