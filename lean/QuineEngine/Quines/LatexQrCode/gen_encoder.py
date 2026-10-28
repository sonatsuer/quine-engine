#!/usr/bin/env python3
r"""Write the three fixed pieces of the LaTeX quine, which `LatexQrCode.lean` embeds with
`include_str`. Run from this folder:

    python3 gen_encoder.py

The quine is `PRE x |` with `x = \iffalse PRE \fi LIB EPI`:

- `pre.inc`, the prefix PRE: sets up the page, defines `\grab`, sets the special characters to
  catcode 12 and starts `\grab`, which reads `x` verbatim into `\v`;
- `library.inc`, LIB: the drawing definitions (plain TeX), then, in expl3, the QR encoder of
  `encoder-source.tex` and the color drawing routine;
- `epilogue.inc`, EPI: the template. It rebuilds the file from `\v`, splits it into thirds,
  encodes each third, and draws the three codes as one color QR code.

`encoder-source.tex` stays readable. The expl3 code is golfed here: names are shortened, long
functions get two-letter aliases, and spaces that expl3 ignores are dropped.
"""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))

# The page holds 185 x 185 cells of 2.6pt: the symbol and its 4-cell quiet zone.
GEO = "paperwidth=175mm,paperheight=185mm,margin=.3mm,headheight=0pt,headsep=0pt,footskip=0pt"

# `\grab\relax#1|` takes `x`. Its body was tokenized when it was defined, so it can restore the
# catcodes and run `\v`. `\afterassignment` starts `\grab` once backslash is at catcode 12, and
# `\grab` takes the pushed-back `\relax` as its delimiter. `^^7c` keeps `|` out of PRE.
PRE = (r"\documentclass{article}\usepackage[" + GEO + r"]{geometry}\pagestyle{empty}"
       r"\begin{document}\makeatletter\topskip0pt"
       r"\long\def\grab\relax#1^^7c{\def\v{#1}\catcode92=0\catcode32=10\catcode123=1"
       r"\catcode125=2\catcode35=6\endlinechar-1\scantokens\expandafter{\v}\end{document}}"
       r"\catcode`\#=12\catcode`\&=12\catcode`\$=12\catcode`\_=12\catcode`\^=12"
       r"\catcode`\{=12\catcode`\}=12\catcode`\%=12\catcode32=12"
       r"\afterassignment\grab\catcode92=12\relax")
assert "|" not in PRE

# Plain TeX: the cell size, the two math fonts, the 16 symbols, and the fill color (`\F`) and
# symbol tint (`\T`) of a cell with color `c`. Bit k of c means code k is dark there, so channel k
# is 0 in the fill and 0.3 in the tint; a light channel is 1 in the fill and 0.82 in the tint.
DRAW = (r"\newdimen\cw \cw=2.6pt "
        r"\font\mi=cmmi5 at2.1pt \font\sy=cmsy5 at2.1pt "
        r"\def\putsym#1{\raise.45pt\hbox{\ifcase#1 "
        r"\mi\char11\or\mi\char12\or\mi\char13\or\mi\char14\or\mi\char25\or\mi\char27\or"
        r"\mi\char30\or\mi\char32\or\mi\char33\or\mi\char18\or\mi\char21\or\mi\char22\or"
        r"\mi\char64\or\sy\char49\or\sy\char8\or\sy\char10\fi}}"
        r"\def\F#1{\pdfliteral direct{\ifcase#1 1 1 1\or0 1 1\or1 0 1\or0 0 1\or1 1 0\or"
        r"0 1 0\or1 0 0\or0 0 0\fi\space rg}}"
        r"\def\T#1{\pdfliteral direct{\ifcase#1 .82 .82 .82\or.3 .82 .82\or.82 .3 .82\or"
        r".3 .3 .82\or.82 .82 .3\or.3 .82 .3\or.82 .3 .3\or.3 .3 .3\fi\space rg}}")

with open(os.path.join(HERE, "encoder-source.tex")) as f:
    ENC = " ".join(ln.strip() for ln in f if ln.strip())

# expl3: `\drawpanel` draws the color matrix `\gC` row by row. A cell gets a rule in its fill
# color, unless it is white. Unless it is a function module, it also gets a symbol in its tint.
DRAWEXPL = (
    r"\int_new:N\l_rr \int_new:N\l_cc \int_new:N\l_third \tl_new:N\l_full_tl "
    r"\intarray_new:Nn\gC{31329} "
    r"\cs_new:Npn\drawpanel{\offinterlineskip"
    r"\int_step_inline:nnnn{1}{1}{4}{\hbox{\vrule height\cw depth0pt width0pt}}"
    r"\int_step_inline:nnnn{0}{1}{176}{\int_set:Nn\l_rr{##1}"
    r"\hbox{\vrule height\cw depth0pt width0pt\kern4\cw"
    r"\int_step_inline:nnnn{1}{1}{177}"
    r"{\int_set:Nn\l_cc{\intarray_item:Nn\gC{\l_rr*177+####1}}"
    r"\int_compare:nNnT{\l_cc}>{0}{\F\l_cc\vrule height\cw depth0pt width\cw\kern-\cw}"
    r"\int_compare:nNnTF{\intarray_item:Nn\gF{\l_rr*177+####1}}={0}"
    r"{\T\l_cc\hb@xt@\cw{\hss"
    r"\exp_args:Nx\putsym{\int_eval:n{\int_mod:nn{\l_rr+####1}{16}}}\hss}}{\kern\cw}}}}"
    r"\int_step_inline:nnnn{1}{1}{4}{\hbox{\vrule height\cw depth0pt width0pt}}}")

# The template. `\v` holds `x`, whose characters 9..8+|PRE| are the copy of PRE. Code k's matrix
# is added into `\gC` with weight 2^k.
EPI_RAW = (
    r"\tl_set:Nx\l_full_tl{\tl_range:Nnn\v{9}{" + str(8 + len(PRE)) + r"}"
    r"\v\char_generate:nn{124}{12}}"
    r"\int_set:Nn\l_third{\int_div_truncate:nn{\tl_count:N\l_full_tl+2}{3}}"
    r"\int_step_inline:nnnn{0}{1}{2}{\tl_set:Nx\l_src_tl{\tl_range:Nnn\l_full_tl"
    r"{\int_eval:n{#1*\l_third+1}}{\int_eval:n{(#1+1)*\l_third}}}\runenc:"
    r"\int_step_inline:nnnn{1}{1}{31329}{\intarray_gset:Nnn\gC{##1}"
    r"{\intarray_item:Nn\gC{##1}+\intarray_item:Nn\gM{##1}*\pw:n{#1}}}}"
    r"\drawpanel\ExplSyntaxOff")

WORD = r"(?![A-Za-z_:@])"
FUNCS = [r"\int_step_inline:nnnn", r"\intarray_gset:Nnn", r"\int_set:Nn", r"\intarray_item:Nn",
         r"\int_compare:nNnTF", r"\int_div_truncate:nn", r"\int_eval:n", r"\int_mod:nn",
         r"\intarray_new:Nn", r"\int_new:N", r"\int_compare_p:nNn", r"\seq_put_right:Nx",
         r"\cs_new:Npn", r"\int_zero:N", r"\int_incr:N"]
RENAME = {r"\l_tmpa_seq": r"\Vs", r"\l_tmpb_int": r"\Vt", r"\l_full_tl": r"\Vf",
          r"\l_src_tl": r"\Vu", r"\l_third": r"\Vh", r"\l_len": r"\Vn", r"\l_rr": r"\Vw",
          r"\l_cc": r"\Vy", r"\sm:nnn": r"\Ws", r"\fd:nnnn": r"\Wf", r"\xr:nn": r"\Wx",
          r"\pw:n": r"\Wp", r"\gf:nn": r"\Wg", r"\cpair:n": r"\Wc", r"\runenc:": r"\Wr",
          r"\drawpanel": r"\Wd"}
for v in "abcdepqgkr":
    RENAME["\\l_" + v] = "\\V" + v


def golf(t):
    """Shorten names, alias long functions, and drop the spaces that expl3 ignores."""
    for a, b in RENAME.items():
        t = re.sub(re.escape(a) + WORD, lambda m: b, t)
    head = r"\seq_new:N\Vs\int_new:N\Vt"
    for i, f in enumerate(FUNCS):
        alias = "\\Q" + "abcdefghijklmnopqrstuvwxyz"[i]
        t = re.sub(re.escape(f) + WORD, lambda m: alias, t)
        head += r"\cs_new_eq:NN" + alias + f
    # A space matters only between two letters (a control word followed by a letter).
    return re.sub(r" (?![A-Za-z_:@])|(?<![A-Za-z_:@]) ", "", head + t)


LIB_EXPL, EPI = golf(ENC + " " + DRAWEXPL + "SPLITHERE" + EPI_RAW).split("SPLITHERE")
LIB = DRAW + r" \ExplSyntaxOn " + LIB_EXPL

for name, text in [("pre.inc", PRE), ("library.inc", LIB), ("epilogue.inc", EPI)]:
    with open(os.path.join(HERE, name), "w") as f:
        f.write(text)
    print("wrote %s (%d bytes)" % (name, len(text)))
print("the quine: %d bytes (capacity 8859)" % (2 * len(PRE) + 12 + len(LIB) + len(EPI)))
