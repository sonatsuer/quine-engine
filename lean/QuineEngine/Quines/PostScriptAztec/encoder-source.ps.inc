/cat{1 index length 1 index length add string dup 0 4 index putinterval dup 3 index length 3 index putinterval 3 1 roll pop pop}def
/Q{/s exch def /S 151 def /C 75 def
/b 20048 array def /bn 0 def
/p{/n exch def /V exch def n 1 sub -1 0{V exch neg bitshift 1 and b bn 3 -1 roll put /bn bn 1 add def}for}def
0 2078 s length 1 sub{/i exch def /g s i s length i sub 2078 2 copy gt{exch}if pop getinterval def /l g length def
 31 5 p l 32 lt{l 5 p}{0 5 p l 31 sub 11 p}ifelse g{8 p}forall}for
/w 1664 array def /wn 0 def /i 0 def
{i bn ge{exit}if /V 0 def 0 1 11{/j exch def /V V 2 mul i j add bn ge{1}{b i j add get}ifelse add def}for
 /m V -2 and def m 4094 eq{w wn m put /i i 11 add def}{m 0 eq{w wn 1 put /i i 11 add def}{w wn V put /i i 12 add def}ifelse}ifelse
 /wn wn 1 add def}loop
wn 0 eq{w 0 4094 put /wn 1 def}if
/k 1664 wn sub def k 3 lt{stop}if
/G{/q exch def /n exch def /N 1 n bitshift 1 sub def /e N 2 mul array def /L N 1 add array def /x 1 def
 0 1 N 1 sub{/i exch def e i x put e i N add x put L x i put /x x 1 bitshift def x N gt{/x x q xor def}if}for}def
/F{2 copy mul 0 eq{pop pop 0}{L exch get exch L exch get add e exch get}ifelse}def
/R{/q exch def /n exch def /k exch def /d exch def n q G /y [1] def
 1 1 k{/i exch def /z [y length 1 add{0}repeat] def
  0 1 y length 1 sub{/j exch def z j z j get y j get xor put z j 1 add z j 1 add get y j get e i get F xor put}for /y z def}for
 /r [k{0}repeat] def
 d{r 0 get xor /f exch def /r [r 1 k 1 sub getinterval aload pop 0] def 0 1 k 1 sub{/j exch def r j r j get y j 1 add get f F xor put}for}forall r}def
/W w 0 wn getinterval def
/bn 0 def W{12 p}forall W k 12 4201 R{12 p}forall
/x 31 2048 mul wn 1 sub add def /d [x -12 bitshift x -8 bitshift 15 and x -4 bitshift 15 and x 15 and] def
d{4 p}forall d 6 4 19 R{4 p}forall
/Z S S mul string def /h{S mul add Z exch 1 put}def
/A 142 array def 0 1 70{/i exch def /t i i 15 idiv add def A 70 i sub C t sub 1 sub put A 71 i add C t add 1 add put}for
/r 0 def 0 1 31{/i exch def /q 32 i sub 4 mul 12 add def 0 1 q 1 sub{/j exch def 0 1 1{/l exch def /t j 2 mul def
 b r t add l add get 1 eq{A i 2 mul l add get A i 2 mul j add get h}if
 b r q 2 mul add t add l add get 1 eq{A i 2 mul j add get A 141 i 2 mul sub l sub get h}if
 b r q 4 mul add t add l add get 1 eq{A 141 i 2 mul sub l sub get A 141 i 2 mul sub j sub get h}if
 b r q 6 mul add t add l add get 1 eq{A 141 i 2 mul sub j sub get A i 2 mul l add get h}if}for}for /r r q 8 mul add def}for
0 1 9{/i exch def /t C 5 sub i add i 5 idiv add def b 19968 i add get 1 eq{t C 7 sub h}if b 19978 i add get 1 eq{C 7 add t h}if
 b 19997 i sub get 1 eq{t C 7 add h}if b 20007 i sub get 1 eq{C 7 sub t h}if}for
0 2 6{/i exch def C i sub 1 C i add{/j exch def j C i sub h j C i add h C i sub j h C i add j h}for}for
C 7 sub C 7 sub h C 6 sub C 7 sub h C 7 sub C 6 sub h C 7 add C 7 sub h C 7 add C 6 sub h C 7 add C 6 add h
0 15 69{15 idiv 16 mul /j exch def C 2 mod 2 S 1 sub{/l exch def C j sub l h C j add l h l C j sub h l C j add h}for}for
20 140 translate 3 3 scale 4 4 translate S S scale /g S S mul string def 0 1 S S mul 1 sub{/i exch def g i 1 Z i get sub 255 mul put}for
S S 8 [S 0 0 S neg 0 S]{g}image}def
