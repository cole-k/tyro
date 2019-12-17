(TeX-add-style-hook
 "typing"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("wasysym" "nointegrals")))
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "ebproof"
    "amsmath"
    "amssymb"
    "graphicx"
    "lmodern"
    "upgreek"
    "amsthm"
    "wasysym"
    "xcolor")
   (TeX-add-symbols
    '("deduct" ["argument"] 2)
    '("eva" ["argument"] 0)
    '("lookup" 5)
    '("instR" 4)
    '("instL" 4)
    '("subsumes" 4)
    '("presynth" 6)
    '("synth" 4)
    '("declLookup" 4)
    '("declApSynth" 4)
    '("declCheck" 3)
    '("declSynth" 3)
    '("subtypes" 3)
    '("wf" 2)
    '("rcons" 2)
    '("apply" 1)
    '("marker" 1)
    '("rcd" 1)
    '("code" 1)
    '("consider" 1)
    '("todo" 1)
    '("ignore" 1)
    "declCtx"
    "B"
    "C"
    "D"
    "rowall"
    "rowvar"
    "bottom"
    "define"
    "subsume"
    "synthesizes"
    "app"
    "prjSymbol"
    "prj"
    "instLSymbol"
    "instRSymbol"
    "ev"
    "spc"
    "evb"
    "rnil"
    "subtype"
    "extends")
   (LaTeX-add-environments
    '("manuallemma" 1))
   (LaTeX-add-amsthm-newtheorems
    "thm"
    "prop"
    "lem"
    "manuallemmainner"))
 :latex)

