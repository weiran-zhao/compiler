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


class CoolLexer implements java_cup.runtime.Scanner {
	private final int YY_BUFFER_SIZE = 512;
	private final int YY_F = -1;
	private final int YY_NO_STATE = -1;
	private final int YY_NOT_ACCEPT = 0;
	private final int YY_START = 1;
	private final int YY_END = 2;
	private final int YY_NO_ANCHOR = 4;
	private final int YY_BOL = 128;
	private final int YY_EOF = 129;

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

    // this is for nested comments "(* (*"
    private int cmtCnt = 0;
    private boolean string2long = false;
    private boolean stringhasnull = false;
    // whether backslash has been translated or not
    private boolean backslashEscaped = false;
	private java.io.BufferedReader yy_reader;
	private int yy_buffer_index;
	private int yy_buffer_read;
	private int yy_buffer_start;
	private int yy_buffer_end;
	private char yy_buffer[];
	private boolean yy_at_bol;
	private int yy_lexical_state;

	CoolLexer (java.io.Reader reader) {
		this ();
		if (null == reader) {
			throw (new Error("Error: Bad input stream initializer."));
		}
		yy_reader = new java.io.BufferedReader(reader);
	}

	CoolLexer (java.io.InputStream instream) {
		this ();
		if (null == instream) {
			throw (new Error("Error: Bad input stream initializer."));
		}
		yy_reader = new java.io.BufferedReader(new java.io.InputStreamReader(instream));
	}

	private CoolLexer () {
		yy_buffer = new char[YY_BUFFER_SIZE];
		yy_buffer_read = 0;
		yy_buffer_index = 0;
		yy_buffer_start = 0;
		yy_buffer_end = 0;
		yy_at_bol = true;
		yy_lexical_state = YYINITIAL;

/*  Stuff enclosed in %init{ %init} is copied verbatim to the lexer
 *  class constructor, all the extra initialization you want to do should
 *  go here.  Don't remove or modify anything that was there initially. */
    // empty for now
	}

	private boolean yy_eof_done = false;
	private final int STRING = 3;
	private final int YYINITIAL = 0;
	private final int COMMENT2 = 2;
	private final int COMMENT1 = 1;
	private final int yy_state_dtrans[] = {
		0,
		58,
		79,
		83
	};
	private void yybegin (int state) {
		yy_lexical_state = state;
	}
	private int yy_advance ()
		throws java.io.IOException {
		int next_read;
		int i;
		int j;

		if (yy_buffer_index < yy_buffer_read) {
			return yy_buffer[yy_buffer_index++];
		}

		if (0 != yy_buffer_start) {
			i = yy_buffer_start;
			j = 0;
			while (i < yy_buffer_read) {
				yy_buffer[j] = yy_buffer[i];
				++i;
				++j;
			}
			yy_buffer_end = yy_buffer_end - yy_buffer_start;
			yy_buffer_start = 0;
			yy_buffer_read = j;
			yy_buffer_index = j;
			next_read = yy_reader.read(yy_buffer,
					yy_buffer_read,
					yy_buffer.length - yy_buffer_read);
			if (-1 == next_read) {
				return YY_EOF;
			}
			yy_buffer_read = yy_buffer_read + next_read;
		}

		while (yy_buffer_index >= yy_buffer_read) {
			if (yy_buffer_index >= yy_buffer.length) {
				yy_buffer = yy_double(yy_buffer);
			}
			next_read = yy_reader.read(yy_buffer,
					yy_buffer_read,
					yy_buffer.length - yy_buffer_read);
			if (-1 == next_read) {
				return YY_EOF;
			}
			yy_buffer_read = yy_buffer_read + next_read;
		}
		return yy_buffer[yy_buffer_index++];
	}
	private void yy_move_end () {
		if (yy_buffer_end > yy_buffer_start &&
		    '\n' == yy_buffer[yy_buffer_end-1])
			yy_buffer_end--;
		if (yy_buffer_end > yy_buffer_start &&
		    '\r' == yy_buffer[yy_buffer_end-1])
			yy_buffer_end--;
	}
	private boolean yy_last_was_cr=false;
	private void yy_mark_start () {
		yy_buffer_start = yy_buffer_index;
	}
	private void yy_mark_end () {
		yy_buffer_end = yy_buffer_index;
	}
	private void yy_to_mark () {
		yy_buffer_index = yy_buffer_end;
		yy_at_bol = (yy_buffer_end > yy_buffer_start) &&
		            ('\r' == yy_buffer[yy_buffer_end-1] ||
		             '\n' == yy_buffer[yy_buffer_end-1] ||
		             2028/*LS*/ == yy_buffer[yy_buffer_end-1] ||
		             2029/*PS*/ == yy_buffer[yy_buffer_end-1]);
	}
	private java.lang.String yytext () {
		return (new java.lang.String(yy_buffer,
			yy_buffer_start,
			yy_buffer_end - yy_buffer_start));
	}
	private int yylength () {
		return yy_buffer_end - yy_buffer_start;
	}
	private char[] yy_double (char buf[]) {
		int i;
		char newbuf[];
		newbuf = new char[2*buf.length];
		for (i = 0; i < buf.length; ++i) {
			newbuf[i] = buf[i];
		}
		return newbuf;
	}
	private final int YY_E_INTERNAL = 0;
	private final int YY_E_MATCH = 1;
	private java.lang.String yy_error_string[] = {
		"Error: Internal error.\n",
		"Error: Unmatched input.\n"
	};
	private void yy_error (int code,boolean fatal) {
		java.lang.System.out.print(yy_error_string[code]);
		java.lang.System.out.flush();
		if (fatal) {
			throw new Error("Fatal Error.\n");
		}
	}
	private int[][] unpackFromString(int size1, int size2, String st) {
		int colonIndex = -1;
		String lengthString;
		int sequenceLength = 0;
		int sequenceInteger = 0;

		int commaIndex;
		String workString;

		int res[][] = new int[size1][size2];
		for (int i= 0; i < size1; i++) {
			for (int j= 0; j < size2; j++) {
				if (sequenceLength != 0) {
					res[i][j] = sequenceInteger;
					sequenceLength--;
					continue;
				}
				commaIndex = st.indexOf(',');
				workString = (commaIndex==-1) ? st :
					st.substring(0, commaIndex);
				st = st.substring(commaIndex+1);
				colonIndex = workString.indexOf(':');
				if (colonIndex == -1) {
					res[i][j]=Integer.parseInt(workString);
					continue;
				}
				lengthString =
					workString.substring(colonIndex+1);
				sequenceLength=Integer.parseInt(lengthString);
				workString=workString.substring(0,colonIndex);
				sequenceInteger=Integer.parseInt(workString);
				res[i][j] = sequenceInteger;
				sequenceLength--;
			}
		}
		return res;
	}
	private int yy_acpt[] = {
		/* 0 */ YY_NOT_ACCEPT,
		/* 1 */ YY_NO_ANCHOR,
		/* 2 */ YY_NO_ANCHOR,
		/* 3 */ YY_NO_ANCHOR,
		/* 4 */ YY_NO_ANCHOR,
		/* 5 */ YY_NO_ANCHOR,
		/* 6 */ YY_NO_ANCHOR,
		/* 7 */ YY_NO_ANCHOR,
		/* 8 */ YY_NO_ANCHOR,
		/* 9 */ YY_NO_ANCHOR,
		/* 10 */ YY_NO_ANCHOR,
		/* 11 */ YY_NO_ANCHOR,
		/* 12 */ YY_NO_ANCHOR,
		/* 13 */ YY_NO_ANCHOR,
		/* 14 */ YY_NO_ANCHOR,
		/* 15 */ YY_NO_ANCHOR,
		/* 16 */ YY_NO_ANCHOR,
		/* 17 */ YY_NO_ANCHOR,
		/* 18 */ YY_NO_ANCHOR,
		/* 19 */ YY_NO_ANCHOR,
		/* 20 */ YY_NO_ANCHOR,
		/* 21 */ YY_NO_ANCHOR,
		/* 22 */ YY_NO_ANCHOR,
		/* 23 */ YY_NO_ANCHOR,
		/* 24 */ YY_NO_ANCHOR,
		/* 25 */ YY_NO_ANCHOR,
		/* 26 */ YY_NO_ANCHOR,
		/* 27 */ YY_NO_ANCHOR,
		/* 28 */ YY_NO_ANCHOR,
		/* 29 */ YY_NO_ANCHOR,
		/* 30 */ YY_NO_ANCHOR,
		/* 31 */ YY_NO_ANCHOR,
		/* 32 */ YY_NO_ANCHOR,
		/* 33 */ YY_NO_ANCHOR,
		/* 34 */ YY_NO_ANCHOR,
		/* 35 */ YY_NO_ANCHOR,
		/* 36 */ YY_NO_ANCHOR,
		/* 37 */ YY_NO_ANCHOR,
		/* 38 */ YY_NO_ANCHOR,
		/* 39 */ YY_NO_ANCHOR,
		/* 40 */ YY_NO_ANCHOR,
		/* 41 */ YY_NO_ANCHOR,
		/* 42 */ YY_NO_ANCHOR,
		/* 43 */ YY_NO_ANCHOR,
		/* 44 */ YY_NO_ANCHOR,
		/* 45 */ YY_NO_ANCHOR,
		/* 46 */ YY_NO_ANCHOR,
		/* 47 */ YY_NO_ANCHOR,
		/* 48 */ YY_NO_ANCHOR,
		/* 49 */ YY_NO_ANCHOR,
		/* 50 */ YY_NO_ANCHOR,
		/* 51 */ YY_NO_ANCHOR,
		/* 52 */ YY_NO_ANCHOR,
		/* 53 */ YY_NO_ANCHOR,
		/* 54 */ YY_NO_ANCHOR,
		/* 55 */ YY_NO_ANCHOR,
		/* 56 */ YY_NO_ANCHOR,
		/* 57 */ YY_NO_ANCHOR,
		/* 58 */ YY_NOT_ACCEPT,
		/* 59 */ YY_NO_ANCHOR,
		/* 60 */ YY_NO_ANCHOR,
		/* 61 */ YY_NO_ANCHOR,
		/* 62 */ YY_NO_ANCHOR,
		/* 63 */ YY_NO_ANCHOR,
		/* 64 */ YY_NO_ANCHOR,
		/* 65 */ YY_NO_ANCHOR,
		/* 66 */ YY_NO_ANCHOR,
		/* 67 */ YY_NO_ANCHOR,
		/* 68 */ YY_NO_ANCHOR,
		/* 69 */ YY_NO_ANCHOR,
		/* 70 */ YY_NO_ANCHOR,
		/* 71 */ YY_NO_ANCHOR,
		/* 72 */ YY_NO_ANCHOR,
		/* 73 */ YY_NO_ANCHOR,
		/* 74 */ YY_NO_ANCHOR,
		/* 75 */ YY_NO_ANCHOR,
		/* 76 */ YY_NO_ANCHOR,
		/* 77 */ YY_NO_ANCHOR,
		/* 78 */ YY_NO_ANCHOR,
		/* 79 */ YY_NOT_ACCEPT,
		/* 80 */ YY_NO_ANCHOR,
		/* 81 */ YY_NO_ANCHOR,
		/* 82 */ YY_NO_ANCHOR,
		/* 83 */ YY_NOT_ACCEPT,
		/* 84 */ YY_NO_ANCHOR,
		/* 85 */ YY_NO_ANCHOR,
		/* 86 */ YY_NO_ANCHOR,
		/* 87 */ YY_NO_ANCHOR,
		/* 88 */ YY_NO_ANCHOR,
		/* 89 */ YY_NO_ANCHOR,
		/* 90 */ YY_NO_ANCHOR,
		/* 91 */ YY_NO_ANCHOR,
		/* 92 */ YY_NO_ANCHOR,
		/* 93 */ YY_NO_ANCHOR,
		/* 94 */ YY_NO_ANCHOR,
		/* 95 */ YY_NO_ANCHOR,
		/* 96 */ YY_NO_ANCHOR,
		/* 97 */ YY_NO_ANCHOR,
		/* 98 */ YY_NO_ANCHOR,
		/* 99 */ YY_NO_ANCHOR,
		/* 100 */ YY_NO_ANCHOR,
		/* 101 */ YY_NO_ANCHOR,
		/* 102 */ YY_NO_ANCHOR,
		/* 103 */ YY_NO_ANCHOR,
		/* 104 */ YY_NO_ANCHOR,
		/* 105 */ YY_NO_ANCHOR,
		/* 106 */ YY_NO_ANCHOR,
		/* 107 */ YY_NO_ANCHOR,
		/* 108 */ YY_NO_ANCHOR,
		/* 109 */ YY_NO_ANCHOR,
		/* 110 */ YY_NO_ANCHOR,
		/* 111 */ YY_NO_ANCHOR,
		/* 112 */ YY_NO_ANCHOR,
		/* 113 */ YY_NO_ANCHOR,
		/* 114 */ YY_NO_ANCHOR,
		/* 115 */ YY_NO_ANCHOR,
		/* 116 */ YY_NO_ANCHOR,
		/* 117 */ YY_NO_ANCHOR,
		/* 118 */ YY_NO_ANCHOR,
		/* 119 */ YY_NO_ANCHOR,
		/* 120 */ YY_NO_ANCHOR,
		/* 121 */ YY_NO_ANCHOR,
		/* 122 */ YY_NO_ANCHOR,
		/* 123 */ YY_NO_ANCHOR,
		/* 124 */ YY_NO_ANCHOR,
		/* 125 */ YY_NO_ANCHOR,
		/* 126 */ YY_NO_ANCHOR,
		/* 127 */ YY_NO_ANCHOR,
		/* 128 */ YY_NO_ANCHOR,
		/* 129 */ YY_NO_ANCHOR,
		/* 130 */ YY_NO_ANCHOR,
		/* 131 */ YY_NO_ANCHOR,
		/* 132 */ YY_NO_ANCHOR,
		/* 133 */ YY_NO_ANCHOR,
		/* 134 */ YY_NO_ANCHOR,
		/* 135 */ YY_NO_ANCHOR,
		/* 136 */ YY_NO_ANCHOR,
		/* 137 */ YY_NO_ANCHOR,
		/* 138 */ YY_NO_ANCHOR,
		/* 139 */ YY_NO_ANCHOR,
		/* 140 */ YY_NO_ANCHOR,
		/* 141 */ YY_NO_ANCHOR,
		/* 142 */ YY_NO_ANCHOR,
		/* 143 */ YY_NO_ANCHOR,
		/* 144 */ YY_NO_ANCHOR,
		/* 145 */ YY_NO_ANCHOR,
		/* 146 */ YY_NO_ANCHOR,
		/* 147 */ YY_NO_ANCHOR,
		/* 148 */ YY_NO_ANCHOR,
		/* 149 */ YY_NO_ANCHOR,
		/* 150 */ YY_NO_ANCHOR,
		/* 151 */ YY_NO_ANCHOR,
		/* 152 */ YY_NO_ANCHOR,
		/* 153 */ YY_NO_ANCHOR,
		/* 154 */ YY_NO_ANCHOR,
		/* 155 */ YY_NO_ANCHOR,
		/* 156 */ YY_NO_ANCHOR,
		/* 157 */ YY_NO_ANCHOR,
		/* 158 */ YY_NO_ANCHOR,
		/* 159 */ YY_NO_ANCHOR,
		/* 160 */ YY_NO_ANCHOR,
		/* 161 */ YY_NO_ANCHOR,
		/* 162 */ YY_NO_ANCHOR,
		/* 163 */ YY_NO_ANCHOR,
		/* 164 */ YY_NO_ANCHOR,
		/* 165 */ YY_NO_ANCHOR,
		/* 166 */ YY_NO_ANCHOR
	};
	private int yy_cmap[] = unpackFromString(1,130,
"17:9,60,2,60:2,3,17:18,60,17,1,17:5,13,15,14,32,38,16,36,33,4:10,37,39,31,2" +
"9,30,17,41,42,43,44,45,46,27,43,47,48,43:2,49,43,50,51,52,43,53,54,22,55,56" +
",57,43:3,17:4,59,17,10,58,18,25,8,9,58,21,19,58:2,11,58,20,24,28,58,6,12,5," +
"7,23,26,58:3,34,17,35,40,17,0:2")[0];

	private int yy_rmap[] = unpackFromString(1,167,
"0,1:3,2,3,4,5,6,1,7,1,8,9,10,1:10,11,1:3,11,12,11,1:3,11:15,1:8,13,14,15,16" +
":2,17,16:14,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38," +
"39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,16,11,61," +
"62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86," +
"87,88,89,90,91,92,93,94,11,16,95,96,97,98,99,100,101,102")[0];

	private int yy_nxt[][] = unpackFromString(103,61,
"1,2,3,4,5,6,157:2,159,59,157,114,157,7,8,9,10,11,161,80,116,157,12,157,84,1" +
"57,163,60,165,13,11,14,15,16,17,18,19,20,21,22,23,24,158:2,160,158,162,158," +
"81,115,117,85,164,158:4,166,157,11,4,-1:64,4,-1:56,4,-1:4,5,-1:60,157:2,118" +
",157:6,-1:5,157:3,120,157:7,-1:13,157:5,120,157:5,118,157:5,122,-1:15,26,-1" +
":61,27,-1:61,28,-1:48,158:9,-1:5,158:3,119,158:7,-1:13,158:5,119,158:11,121" +
",-1:31,32,-1:46,33,-1:12,34,-1:35,157:9,-1:5,157:11,-1:13,157:17,122,-1:5,1" +
"57:9,-1:5,157:3,148,157:7,-1:13,157:5,148,157:11,122,-1,1,50,3,50:10,78,82," +
"50:46,-1:4,157:6,128,157:2,-1:5,157,25,157:9,-1:13,128,157:5,25,157:10,122," +
"-1:5,158:9,-1:5,158,61,158:9,-1:13,158:6,61,158:10,121,-1:5,158:9,-1:5,158:" +
"11,-1:13,158:17,121,-1:5,158:9,-1:5,158:3,143,158:7,-1:13,158:5,143,158:11," +
"121,-1:15,51,-1:46,1,53,54,-1,53:57,-1:4,157:5,29,157:2,136,-1:5,157:2,30,1" +
"57:6,29,157,-1:13,157:8,30,157:3,136,157:4,122,-1:5,158:5,62,158:2,131,-1:5" +
",158:2,63,158:6,62,158,-1:13,158:8,63,158:3,131,158:4,121,-1:16,52,-1:45,1," +
"55,56,57:58,-1:4,157:5,31,157:3,-1:5,157:9,31,157,-1:13,157:17,122,-1:5,158" +
":5,64,158:3,-1:5,158:9,64,158,-1:13,158:17,121,-1:5,157,35,157:7,-1:5,157:4" +
",35,157:6,-1:13,157:17,122,-1:5,158,65,158:7,-1:5,158:4,65,158:6,-1:13,158:" +
"17,121,-1:5,157:9,-1:5,157:8,36,157:2,-1:13,157:15,36,157,122,-1:5,158:9,-1" +
":5,158:8,66,158:2,-1:13,158:15,66,158,121,-1:5,157,37,157:7,-1:5,157:4,37,1" +
"57:6,-1:13,157:17,122,-1:5,158,67,158:7,-1:5,158:4,67,158:6,-1:13,158:17,12" +
"1,-1:5,157:4,38,157:4,-1:5,157:11,-1:13,157:4,38,157:12,122,-1:5,158:9,-1:5" +
",158:2,68,158:8,-1:13,158:8,68,158:8,121,-1:5,157:9,-1:5,157:2,39,157:8,-1:" +
"13,157:8,39,157:8,122,-1:5,158:4,72,158:4,-1:5,158:11,-1:13,158:4,72,158:12" +
",121,-1:5,157:4,40,157:4,-1:5,157:11,-1:13,157:4,40,157:12,122,-1:5,158:4,6" +
"9,158:4,-1:5,158:11,-1:13,158:4,69,158:12,121,-1:5,157:9,-1:5,41,157:10,-1:" +
"13,157:2,41,157:14,122,-1:5,158:9,-1:5,70,158:10,-1:13,158:2,70,158:14,121," +
"-1:5,157:9,-1:5,157:10,42,-1:13,157:10,42,157:6,122,-1:5,158:9,-1:5,158:10," +
"71,-1:13,158:10,71,158:6,121,-1:5,157:4,43,157:4,-1:5,157:11,-1:13,157:4,43" +
",157:12,122,-1:5,158:7,73,158,-1:5,158:11,-1:13,158:7,73,158:9,121,-1:5,157" +
":7,44,157,-1:5,157:11,-1:13,157:7,44,157:9,122,-1:5,158:8,74,-1:5,158:11,-1" +
":13,158:12,74,158:4,121,-1:5,157:4,45,157:4,-1:5,157:11,-1:13,157:4,45,157:" +
"12,122,-1:5,158:4,75,158:4,-1:5,158:11,-1:13,158:4,75,158:12,121,-1:5,157:8" +
",46,-1:5,157:11,-1:13,157:12,46,157:4,122,-1:5,158:9,-1:5,158:7,76,158:3,-1" +
":13,158:3,76,158:13,121,-1:5,157:4,47,157:4,-1:5,157:11,-1:13,157:4,47,157:" +
"12,122,-1:5,158:8,77,-1:5,158:11,-1:13,158:12,77,158:4,121,-1:5,157:9,-1:5," +
"157:7,48,157:3,-1:13,157:3,48,157:13,122,-1:5,157:8,49,-1:5,157:11,-1:13,15" +
"7:12,49,157:4,122,-1:5,157:4,86,157:4,-1:5,157:6,130,157:4,-1:13,157:4,86,1" +
"57:4,130,157:7,122,-1:5,158:4,87,158:4,-1:5,158:6,133,158:4,-1:13,158:4,87," +
"158:4,133,158:7,121,-1:5,157:4,88,157:4,-1:5,157:6,90,157:4,-1:13,157:4,88," +
"157:4,90,157:7,122,-1:5,158:4,89,158:4,-1:5,158:6,91,158:4,-1:13,158:4,89,1" +
"58:4,91,158:7,121,-1:5,157:3,92,157:5,-1:5,157:11,-1:13,157:13,92,157:3,122" +
",-1:5,158:4,93,158:4,-1:5,158:11,-1:13,158:4,93,158:12,121,-1:5,157:4,94,15" +
"7:4,-1:5,157:11,-1:13,157:4,94,157:12,122,-1:5,158:8,95,-1:5,158:11,-1:13,1" +
"58:12,95,158:4,121,-1:5,157:8,96,-1:5,157:11,-1:13,157:12,96,157:4,122,-1:5" +
",158:6,139,158:2,-1:5,158:11,-1:13,139,158:16,121,-1:5,157:6,98,157:2,-1:5," +
"157:11,-1:13,98,157:16,122,-1:5,158:8,97,-1:5,158:11,-1:13,158:12,97,158:4," +
"121,-1:5,157:7,142,157,-1:5,157:11,-1:13,157:7,142,157:9,122,-1:5,158:6,99," +
"158:2,-1:5,158:11,-1:13,99,158:16,121,-1:5,157:9,-1:5,157:6,100,157:4,-1:13" +
",157:9,100,157:7,122,-1:5,158:9,-1:5,158:5,141,158:5,-1:13,158:14,141,158:2" +
",121,-1:5,157:8,102,-1:5,157:11,-1:13,157:12,102,157:4,122,-1:5,158:9,-1:5," +
"158:6,101,158:4,-1:13,158:9,101,158:7,121,-1:5,157:6,144,157:2,-1:5,157:11," +
"-1:13,144,157:16,122,-1:5,158:9,-1:5,158:6,103,158:4,-1:13,158:9,103,158:7," +
"121,-1:5,157:9,-1:5,157:5,146,157:5,-1:13,157:14,146,157:2,122,-1:5,158:9,-" +
"1:5,158,145,158:9,-1:13,158:6,145,158:10,121,-1:5,157:9,-1:5,157,150,157:9," +
"-1:13,157:6,150,157:10,122,-1:5,158:8,105,-1:5,158:11,-1:13,158:12,105,158:" +
"4,121,-1:5,157:9,-1:5,157:6,104,157:4,-1:13,157:9,104,157:7,122,-1:5,158:9," +
"-1:5,158:6,147,158:4,-1:13,158:9,147,158:7,121,-1:5,157:8,106,-1:5,157:11,-" +
"1:13,157:12,106,157:4,122,-1:5,158:4,149,158:4,-1:5,158:11,-1:13,158:4,149," +
"158:12,121,-1:5,157:8,108,-1:5,157:11,-1:13,157:12,108,157:4,122,-1:5,158:7" +
",107,158,-1:5,158:11,-1:13,158:7,107,158:9,121,-1:5,157:9,-1:5,157:6,152,15" +
"7:4,-1:13,157:9,152,157:7,122,-1:5,158:9,-1:5,158,109,158:9,-1:13,158:6,109" +
",158:10,121,-1:5,157:4,154,157:4,-1:5,157:11,-1:13,157:4,154,157:12,122,-1:" +
"5,158:2,151,158:6,-1:5,158:11,-1:13,158:11,151,158:5,121,-1:5,157:7,110,157" +
",-1:5,157:11,-1:13,157:7,110,157:9,122,-1:5,158:9,-1:5,158,153,158:9,-1:13," +
"158:6,153,158:10,121,-1:5,157:9,-1:5,157,112,157:9,-1:13,157:6,112,157:10,1" +
"22,-1:5,158,111,158:7,-1:5,158:4,111,158:6,-1:13,158:17,121,-1:5,157:2,155," +
"157:6,-1:5,157:11,-1:13,157:11,155,157:5,122,-1:5,157:9,-1:5,157,156,157:9," +
"-1:13,157:6,156,157:10,122,-1:5,157,113,157:7,-1:5,157:4,113,157:6,-1:13,15" +
"7:17,122,-1:5,157:7,124,126,-1:5,157:11,-1:13,157:7,124,157:4,126,157:4,122" +
",-1:5,158:6,123,125,158,-1:5,158:11,-1:13,123,158:6,125,158:9,121,-1:5,157:" +
"6,132,134,157,-1:5,157:11,-1:13,132,157:6,134,157:9,122,-1:5,158:7,127,129," +
"-1:5,158:11,-1:13,158:7,127,158:4,129,158:4,121,-1:5,157:9,-1:5,157:3,138,1" +
"57:7,-1:13,157:5,138,157:11,122,-1:5,158:9,-1:5,158:6,135,158:4,-1:13,158:9" +
",135,158:7,121,-1:5,157:9,-1:5,157:6,140,157:4,-1:13,157:9,140,157:7,122,-1" +
":5,158:9,-1:5,158:3,137,158:7,-1:13,158:5,137,158:11,121,-1");

	public java_cup.runtime.Symbol next_token ()
		throws java.io.IOException {
		int yy_lookahead;
		int yy_anchor = YY_NO_ANCHOR;
		int yy_state = yy_state_dtrans[yy_lexical_state];
		int yy_next_state = YY_NO_STATE;
		int yy_last_accept_state = YY_NO_STATE;
		boolean yy_initial = true;
		int yy_this_accept;

		yy_mark_start();
		yy_this_accept = yy_acpt[yy_state];
		if (YY_NOT_ACCEPT != yy_this_accept) {
			yy_last_accept_state = yy_state;
			yy_mark_end();
		}
		while (true) {
			if (yy_initial && yy_at_bol) yy_lookahead = YY_BOL;
			else yy_lookahead = yy_advance();
			yy_next_state = YY_F;
			yy_next_state = yy_nxt[yy_rmap[yy_state]][yy_cmap[yy_lookahead]];
			if (YY_EOF == yy_lookahead && true == yy_initial) {

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
			}
			if (YY_F != yy_next_state) {
				yy_state = yy_next_state;
				yy_initial = false;
				yy_this_accept = yy_acpt[yy_state];
				if (YY_NOT_ACCEPT != yy_this_accept) {
					yy_last_accept_state = yy_state;
					yy_mark_end();
				}
			}
			else {
				if (YY_NO_STATE == yy_last_accept_state) {
					throw (new Error("Lexical Error: Unmatched Input."));
				}
				else {
					yy_anchor = yy_acpt[yy_last_accept_state];
					if (0 != (YY_END & yy_anchor)) {
						yy_move_end();
					}
					yy_to_mark();
					switch (yy_last_accept_state) {
					case 1:
						
					case -2:
						break;
					case 2:
						{   /* string */
    // clear string buffer
    string_buf.delete(0,string_buf.length());
    backslashEscaped = false;
    string2long = false;
    stringhasnull = false;
    yybegin(STRING); }
					case -3:
						break;
					case 3:
						{   /* newline */
    curr_lineno += 1; }
					case -4:
						break;
					case 4:
						{    /*do nothing*/ }
					case -5:
						break;
					case 5:
						{   /* integer */ 
    return new Symbol(TokenConstants.INT_CONST, AbstractTable.inttable.addString(yytext())); }
					case -6:
						break;
					case 6:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -7:
						break;
					case 7:
						{    /* left parenthesis */
    return new Symbol(TokenConstants.LPAREN); }
					case -8:
						break;
					case 8:
						{    /* multiply */
    return new Symbol(TokenConstants.MULT); }
					case -9:
						break;
					case 9:
						{    /* right parenthesis*/
    return new Symbol(TokenConstants.RPAREN); }
					case -10:
						break;
					case 10:
						{    /* minus */
    return new Symbol(TokenConstants.MINUS); }
					case -11:
						break;
					case 11:
						{ /* This rule should be the very last
     in your lexical specification and
     will match match everything not
     matched by other lexical rules. */
    return new Symbol(TokenConstants.ERROR, new String(yytext())); 
}
					case -12:
						break;
					case 12:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -13:
						break;
					case 13:
						{    /* equal */
    return new Symbol(TokenConstants.EQ); }
					case -14:
						break;
					case 14:
						{    /* less than */
    return new Symbol(TokenConstants.LT); }
					case -15:
						break;
					case 15:
						{    /* plus */
    return new Symbol(TokenConstants.PLUS); }
					case -16:
						break;
					case 16:
						{    /* divide */
    return new Symbol(TokenConstants.DIV); }
					case -17:
						break;
					case 17:
						{    /* left brace */
    return new Symbol(TokenConstants.LBRACE); }
					case -18:
						break;
					case 18:
						{    /* right brace*/
    return new Symbol(TokenConstants.RBRACE); }
					case -19:
						break;
					case 19:
						{    /* dot */
    return new Symbol(TokenConstants.DOT); }
					case -20:
						break;
					case 20:
						{    /* colon */
    return new Symbol(TokenConstants.COLON); }
					case -21:
						break;
					case 21:
						{    /* comma */
    return new Symbol(TokenConstants.COMMA); }
					case -22:
						break;
					case 22:
						{    /* semi colon */
    return new Symbol(TokenConstants.SEMI); }
					case -23:
						break;
					case 23:
						{    /* negate */
    return new Symbol(TokenConstants.NEG); }
					case -24:
						break;
					case 24:
						{    /* at */
    return new Symbol(TokenConstants.AT); }
					case -25:
						break;
					case 25:
						{   /* fi */
    return new Symbol(TokenConstants.FI); }
					case -26:
						break;
					case 26:
						{   /* let's handle comments */
    yybegin(COMMENT1); 
    cmtCnt = 1; }
					case -27:
						break;
					case 27:
						{   /* unmatched "*)" */
    return new Symbol(TokenConstants.ERROR, new String("Unmatched *)")); }
					case -28:
						break;
					case 28:
						{   /* another kind of comment */
    yybegin(COMMENT2); }
					case -29:
						break;
					case 29:
						{   /* if */
    return new Symbol(TokenConstants.IF); }
					case -30:
						break;
					case 30:
						{   /* in */
    return new Symbol(TokenConstants.IN); }
					case -31:
						break;
					case 31:
						{   /* of */
    return new Symbol(TokenConstants.OF); }
					case -32:
						break;
					case 32:
						{   /* ==> */
    return new Symbol(TokenConstants.DARROW); }
					case -33:
						break;
					case 33:
						{   /* assign */
    return new Symbol(TokenConstants.ASSIGN); }
					case -34:
						break;
					case 34:
						{   /* less than or equal */
    return new Symbol(TokenConstants.LE); }
					case -35:
						break;
					case 35:
						{   /* let */
    return new Symbol(TokenConstants.LET); }
					case -36:
						break;
					case 36:
						{   /* new */
    return new Symbol(TokenConstants.NEW); }
					case -37:
						break;
					case 37:
						{   /* not */
    return new Symbol(TokenConstants.NOT); }
					case -38:
						break;
					case 38:
						{   /* true */
    return new Symbol(TokenConstants.BOOL_CONST,new Boolean(true)); }
					case -39:
						break;
					case 39:
						{   /* then */
    return new Symbol(TokenConstants.THEN); }
					case -40:
						break;
					case 40:
						{   /* else */
    return new Symbol(TokenConstants.ELSE); }
					case -41:
						break;
					case 41:
						{   /* esac */
    return new Symbol(TokenConstants.ESAC); }
					case -42:
						break;
					case 42:
						{   /* loop */
    return new Symbol(TokenConstants.LOOP); }
					case -43:
						break;
					case 43:
						{   /* case */
    return new Symbol(TokenConstants.CASE); }
					case -44:
						break;
					case 44:
						{   /* pool */
    return new Symbol(TokenConstants.POOL); }
					case -45:
						break;
					case 45:
						{   /* false */
    return new Symbol(TokenConstants.BOOL_CONST,new Boolean(false)); }
					case -46:
						break;
					case 46:
						{   /* class */
    return new Symbol(TokenConstants.CLASS); }
					case -47:
						break;
					case 47:
						{   /* while */
    return new Symbol(TokenConstants.WHILE); }
					case -48:
						break;
					case 48:
						{   /* isvoid */
    return new Symbol(TokenConstants.ISVOID); }
					case -49:
						break;
					case 49:
						{   /* inherits */
    return new Symbol(TokenConstants.INHERITS); }
					case -50:
						break;
					case 50:
						{   /* comment text */ }
					case -51:
						break;
					case 51:
						{   /* nested comment */
    cmtCnt+=1; }
					case -52:
						break;
					case 52:
						{   /* in comment state, "*)" ends comments, if cmtCnt=0 */
    cmtCnt -=1;
    if(cmtCnt==0) {
        yybegin(YYINITIAL);
    } 
}
					case -53:
						break;
					case 53:
						{   /* comment text */ }
					case -54:
						break;
					case 54:
						{   /* one way to end comment */
    curr_lineno+=1;
    yybegin(YYINITIAL); }
					case -55:
						break;
					case 55:
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
					case -56:
						break;
					case 56:
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
					case -57:
						break;
					case 57:
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
					case -58:
						break;
					case 59:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -59:
						break;
					case 60:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -60:
						break;
					case 61:
						{   /* fi */
    return new Symbol(TokenConstants.FI); }
					case -61:
						break;
					case 62:
						{   /* if */
    return new Symbol(TokenConstants.IF); }
					case -62:
						break;
					case 63:
						{   /* in */
    return new Symbol(TokenConstants.IN); }
					case -63:
						break;
					case 64:
						{   /* of */
    return new Symbol(TokenConstants.OF); }
					case -64:
						break;
					case 65:
						{   /* let */
    return new Symbol(TokenConstants.LET); }
					case -65:
						break;
					case 66:
						{   /* new */
    return new Symbol(TokenConstants.NEW); }
					case -66:
						break;
					case 67:
						{   /* not */
    return new Symbol(TokenConstants.NOT); }
					case -67:
						break;
					case 68:
						{   /* then */
    return new Symbol(TokenConstants.THEN); }
					case -68:
						break;
					case 69:
						{   /* else */
    return new Symbol(TokenConstants.ELSE); }
					case -69:
						break;
					case 70:
						{   /* esac */
    return new Symbol(TokenConstants.ESAC); }
					case -70:
						break;
					case 71:
						{   /* loop */
    return new Symbol(TokenConstants.LOOP); }
					case -71:
						break;
					case 72:
						{   /* case */
    return new Symbol(TokenConstants.CASE); }
					case -72:
						break;
					case 73:
						{   /* pool */
    return new Symbol(TokenConstants.POOL); }
					case -73:
						break;
					case 74:
						{   /* class */
    return new Symbol(TokenConstants.CLASS); }
					case -74:
						break;
					case 75:
						{   /* while */
    return new Symbol(TokenConstants.WHILE); }
					case -75:
						break;
					case 76:
						{   /* isvoid */
    return new Symbol(TokenConstants.ISVOID); }
					case -76:
						break;
					case 77:
						{   /* inherits */
    return new Symbol(TokenConstants.INHERITS); }
					case -77:
						break;
					case 78:
						{   /* comment text */ }
					case -78:
						break;
					case 80:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -79:
						break;
					case 81:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -80:
						break;
					case 82:
						{   /* comment text */ }
					case -81:
						break;
					case 84:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -82:
						break;
					case 85:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -83:
						break;
					case 86:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -84:
						break;
					case 87:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -85:
						break;
					case 88:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -86:
						break;
					case 89:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -87:
						break;
					case 90:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -88:
						break;
					case 91:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -89:
						break;
					case 92:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -90:
						break;
					case 93:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -91:
						break;
					case 94:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -92:
						break;
					case 95:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -93:
						break;
					case 96:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -94:
						break;
					case 97:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -95:
						break;
					case 98:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -96:
						break;
					case 99:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -97:
						break;
					case 100:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -98:
						break;
					case 101:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -99:
						break;
					case 102:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -100:
						break;
					case 103:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -101:
						break;
					case 104:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -102:
						break;
					case 105:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -103:
						break;
					case 106:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -104:
						break;
					case 107:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -105:
						break;
					case 108:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -106:
						break;
					case 109:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -107:
						break;
					case 110:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -108:
						break;
					case 111:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -109:
						break;
					case 112:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -110:
						break;
					case 113:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -111:
						break;
					case 114:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -112:
						break;
					case 115:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -113:
						break;
					case 116:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -114:
						break;
					case 117:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -115:
						break;
					case 118:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -116:
						break;
					case 119:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -117:
						break;
					case 120:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -118:
						break;
					case 121:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -119:
						break;
					case 122:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -120:
						break;
					case 123:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -121:
						break;
					case 124:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -122:
						break;
					case 125:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -123:
						break;
					case 126:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -124:
						break;
					case 127:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -125:
						break;
					case 128:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -126:
						break;
					case 129:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -127:
						break;
					case 130:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -128:
						break;
					case 131:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -129:
						break;
					case 132:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -130:
						break;
					case 133:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -131:
						break;
					case 134:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -132:
						break;
					case 135:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -133:
						break;
					case 136:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -134:
						break;
					case 137:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -135:
						break;
					case 138:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -136:
						break;
					case 139:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -137:
						break;
					case 140:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -138:
						break;
					case 141:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -139:
						break;
					case 142:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -140:
						break;
					case 143:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -141:
						break;
					case 144:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -142:
						break;
					case 145:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -143:
						break;
					case 146:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -144:
						break;
					case 147:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -145:
						break;
					case 148:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -146:
						break;
					case 149:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -147:
						break;
					case 150:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -148:
						break;
					case 151:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -149:
						break;
					case 152:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -150:
						break;
					case 153:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -151:
						break;
					case 154:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -152:
						break;
					case 155:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -153:
						break;
					case 156:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -154:
						break;
					case 157:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -155:
						break;
					case 158:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -156:
						break;
					case 159:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -157:
						break;
					case 160:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -158:
						break;
					case 161:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -159:
						break;
					case 162:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -160:
						break;
					case 163:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -161:
						break;
					case 164:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -162:
						break;
					case 165:
						{   /* object identifier */
    //System.out.println(curr_lineno+" "+yytext());
    return new Symbol(TokenConstants.OBJECTID, AbstractTable.idtable.addString(yytext())); }
					case -163:
						break;
					case 166:
						{   /* type identifier */
    return new Symbol(TokenConstants.TYPEID, AbstractTable.idtable.addString(yytext())); }
					case -164:
						break;
					default:
						yy_error(YY_E_INTERNAL,false);
					case -1:
					}
					yy_initial = true;
					yy_state = yy_state_dtrans[yy_lexical_state];
					yy_next_state = YY_NO_STATE;
					yy_last_accept_state = YY_NO_STATE;
					yy_mark_start();
					yy_this_accept = yy_acpt[yy_state];
					if (YY_NOT_ACCEPT != yy_this_accept) {
						yy_last_accept_state = yy_state;
						yy_mark_end();
					}
				}
			}
		}
	}
}
