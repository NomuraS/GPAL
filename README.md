An automated theorem prover of a labelled sequent calculus for Public Announcement Logic, GPAL.

(1) Install ghc, a compiler for Haskell.

(2) ghc --make GPAL

(3) ./GPAL

(4) Input a formula A which you want to prove. 
    A ::= p | ~A | (A & A) | (A v A) | (A -> A) | (A <-> A) | #aA | $aA | [A]A | <A>A 
    For example, A->(B->A). 

(5) After the proof, LaTeX form of output is also available (for typesetting the file, proof.sty is required).
    The file named "figureTeX.tex" appears in the present directory.
