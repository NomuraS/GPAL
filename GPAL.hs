module Main where 

import Data.Tree
import Data.List
import BasisDec
import System.IO
import System.Process
--- parser 
import Data.Char
--import Data.List
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Char
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language
import Control.Applicative hiding((<|>))


infixr 3 +++
a +++ b  = a++ " "++b

main = do
    putStrLn opMessage 
    f <- getLine
    prove f
    a <- ask "Output its LaTeX file? yes/no"
    do  
     (if a 
      then tex0 f
      else putStrLn "done")

opMessage =
  "\nInput Formula A"++"\n"++
  "A ::= p | ~A | (A & A) | (A v A) | (A -> A) | (A <-> A) | #aA | $aA | [A]A | <A>A " ++"\n"++
  "ex1. A->(B->A)"++"\n"++
  "ex2. [A]#a B->(A->#a[A]B)"++"\n"


ask :: String -> IO Bool
ask q = do
          putStrLn q
          x <- getLine
          return (x == "yes")

--classical axioms
ca1 = "A->(B->A)"
ca2 = "(A->(B->C)) -> ((A->B)->(A->C))"
ca3 = "(~B->~A)->(A->B)"
ca123 = "(A->(B->A)) & (((A->(B->C))->((A->B)->(A->C))) & ((~B->~A)->(A->B)))"     -- o 

--modal axioms
axK = "#a(A->B)->(#aA->#aB)" -- o 
axT = "#a A-> A"             -- (needs refl)
ax4 = "#aA<-> (#a#aA)"       -- (needs tran & refl)
ax5 = "~#aA -> #a~#cA"       -- (needs eucl & refl)  (loop)
axB = "A-> #a$aA"            -- (needs symm)

--reduction axioms
ra1  = "[A]q <-> (A->q)"            -- o 
ra2  = "[A](B->C) <-> ([A]B->[A]C)" -- o 
ra3  = "[A]~B <-> (A->~[A]B)"       -- o 
ra4  = "[A]#aB <-> (A->#a[A]B)"     -- o 
ra5  = "[A][B]C <-> [A&[A]B]C"      -- o (need Rcmp)

-- propositions
prop1   = "[A&A]B <-> [A]B"       -- x needs lemma
prop1p  = "[p&p]q <-> [p]q"       -- o atom 
prop2   = "[A][B](#a C & D) <-> [A & [A]B](#a C & D)"   -- o Rcmp 
prop3   = "[A]B <-> ~<A>~B"         -- o 

--H. van Ditmarsh et al "Dynamic Epistemic Logic", p.78
prop419a  = "[A]#aB <-> (A -> #a[A]B)"      -- o 
prop419b  = "<A>#aB <-> (A & #a(A-><A>B))"  -- o 
prop419c  = "(<A>$aB) <-> (A & $a<A>B)"     -- o 
prop421   = "<A & ~#b A>($a$b ~A)"          -- x (invalid) 
prop425   = "(A & ~<A>B) <-> (<A>~B)"       -- o


----------------------------------------------------------------------------------------------
-- inference Rules
----------------------------------------------------------------------------------------------
systemPAL :: [InferenceRule]
systemPAL = ruleClassic ++ruleGPAL++ruleK-- ++ modalKT4B

modalKT   = ruleT
modalS4   = ruleT++rule4 
modalTB   = ruleT++ruleB 
modalS5   = ruleT++rule5 
modalKT4B = ruleT++rule4 ++ruleB -- S5
----------------------------------------------------------------------------------------------
-- tree
----------------------------------------------------------------------------------------------
type Label = Int
type Agent = String
type InferenceRule = (Int, String, Sequent -> Maybe [Sequent])

----------------------------------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------------------------------

data Formula = Atom String              -- p
             | AnyF String              -- A
             | Top                      -- T
             | Bottom                   -- _|_
             | Neg  Formula             -- ~A
             | Box Agent [Label] Formula     -- #a A
             | Dia Agent [Label] Formula     -- $a A 　     
             | Conj Formula Formula     -- A & B
             | Disj Formula Formula     -- A v B
             | Impl Formula Formula     -- A -> B
             | Impl2 Formula Formula     -- A -> B
             | Equi Formula Formula    -- A <-> B
             | Announce Formula Formula  -- A+B
             | Announce2 Formula Formula  -- A^B
                 deriving (Eq,Show,Ord)
--PAL   
data LabelExp = LabelForm ([Formula],Label,Formula)
               | RelAtom (Agent,[Formula],Label,Label)
                 deriving (Eq,Show,Ord)

type Sequent = ([LabelExp],[LabelExp])

data Proof =  Proof String Sequent [Proof]
               deriving (Eq,Show,Ord)

relAtom1 (RelAtom (ag,_,_,_)) = ag
relAtom2 (RelAtom (_,annf,_,_)) = annf
relAtom3 (RelAtom (_,_,w1,_)) = w1
relAtom4 (RelAtom (_,_,_,w2)) = w2                        
        
labelForm1 (LabelForm (annf,_,_))= annf
labelForm2 (LabelForm (_,w,_))= w
labelForm3 (LabelForm (_,_,p))= p

proof1st (Proof s _ _) = s
proof2nd (Proof _ s _) = s
proof3rd (Proof _ _ s) = s 

-- initial sequents --------------------------------------------------------------------------------------------

axiomRule  :: [InferenceRule] 
axiomRule =[
  (0, "init", \ (left,right) -> case left of 
                    p:rest | p `elem` right -> Just [] 
                    otherwise                                     -> Nothing), 
  (0, "init2", \ (left,right) -> case left of 
                    LabelForm(annf, la, Bottom):rest  -> Just []
                    otherwise                                 -> Nothing),
  (0, "end", \ (left,right) -> if   (forall systemPAL (\x->  forall [(b,c)|b<-rotate left, c<-rotate right] (\y->(thrd3 x) y == Nothing ))) 
                                 && forall left (\x -> forall right (\y ->　x/=y)) 
                           then Just []
                           else Nothing)]
-- classical rules --------------------------------------------------------------------------------------------

ruleClassic  :: [InferenceRule] 
ruleClassic =[

  (1, "L~", \ (left,right) -> case left of
                LabelForm (annf, la, Neg p):rest -> Just [{-1-}(rest,(LabelForm (annf, la, p)):right)]
                otherwise             -> Nothing),
  (1, "R~", \ (left,right) -> case right of
                   LabelForm(annf, la, Neg p):rest -> Just [{-1-}(LabelForm(annf, la, p):left,rest)]
                   otherwise             -> Nothing),
  (1, "L&", \ (left,right) -> case left of
                LabelForm (annf, la, (Conj p q)):rest -> Just [({-1-}LabelForm (annf, la, p):LabelForm (annf, la, q):rest,right)]
                otherwise             -> Nothing), 
  (5, "R&", \ (left,right) -> case right of
                LabelForm(annf, la, (Conj p q)):rest -> Just [{-1-}(left,LabelForm(annf, la, p):rest),
                                                              {-2-}(left,LabelForm(annf, la, q):rest)]
                otherwise             -> Nothing),
  (5, "Lv", \ (left,right) -> case left of
                LabelForm (annf, la, (Disj p q)):rest -> Just [{-1-}(LabelForm(annf, la, p):rest,right), 
                                                               {-2-}(LabelForm(annf, la, q):rest,right)]
                otherwise             -> Nothing),
  (1, "Rv", \ (left,right) -> case right of
                LabelForm(annf, la, (Disj p q)):rest -> Just [{-1-}(left, LabelForm(annf, la, p):LabelForm(annf, la, q):rest)]
                otherwise             -> Nothing),
  (6, "L->", \ (left,right) -> case left of
                LabelForm(annf, la, (Impl p q)):rest -> Just [{-1-}(rest,LabelForm(annf, la, p):right), 
                                                              {-2-}     (LabelForm(annf, la, q):rest,right)]
                otherwise             -> Nothing),
  (1, "R->", \ (left,right) -> case right of
                LabelForm(annf, la, (Impl p q)):rest -> Just [{-1-}(LabelForm(annf, la, p):left, LabelForm(annf, la, q):rest)]
                otherwise             -> Nothing),

  (6, "L->2", \ (left,right) -> case left of
                LabelForm(annf, la, (Impl2 p q)):rest -> Just [ {-1-}(rest,LabelForm(annf, la, q):right), 
                                                                {-2-} (LabelForm(annf, la, p):rest,right)]
                otherwise             -> Nothing),
  (1, "R->2", \ (left,right) -> case right of
                LabelForm(annf, la, (Impl2 p q)):rest -> Just [{-1-}(LabelForm(annf, la, q):left, LabelForm(annf, la, p):rest)]
                otherwise             -> Nothing),

  (1, "L<->", \ (left,right) -> case left of
                LabelForm(annf, la, (Equi p q)):rest -> Just [{-1-}(LabelForm(annf, la, Conj (Impl p q)  (Impl q p) ):rest,right)] 
                otherwise             -> Nothing),
  (1, "R<->", \ (left,right) -> case right of
                LabelForm(annf, la, (Equi p q)):rest -> Just [{-1-}(left,LabelForm(annf, la, Conj (Impl p q)  (Impl q p) ):rest)]
                otherwise             -> Nothing)]


-- PAL rules --------------------------------------------------------------------------------------------

ruleGPAL  :: [InferenceRule] 
ruleGPAL =[
  (8, "Lat", \ (left,right)  -> case left of
                   LabelForm (k:restw, la, Atom p):restl -> Just [{-1-}(LabelForm (restw,la, k):LabelForm (restw,la, Atom p):restl, right)]
                   otherwise          -> Nothing ) , 
  (8, "Rat", \ (left,right) -> case right of
                   LabelForm(k:restw, la, Atom p):restr  -> Just [{-1-}(left, (LabelForm (restw,la, Atom p)):restr), 
                                                                  {-2-}(left,(LabelForm(restw,la, k)):restr)]
                   otherwise            -> Nothing),{--}
  (4, "L[.]", \ (left,right)  -> case left of
                LabelForm(annf, la, (Announce p q)):rest -> Just [{-1-}(rest,LabelForm(annf, la, p):right), 
                                                                  {-2-} (LabelForm(p:annf, la, q):rest,right)]
                otherwise                              -> Nothing),
  (2, "R[.]", \ (left,right)  -> case right of
                LabelForm(annf, la, (Announce p q)):rest -> Just [{-1-}(LabelForm(annf, la, p):left, LabelForm(p:annf, la, q):rest)]
                otherwise             -> Nothing),
  (2, "R<.>", \ (left,right)  -> case right of
                LabelForm(annf, la, (Announce2 p q)):restr -> Just [{-1-}(left,LabelForm(annf, la, p):restr), 
                                                                    {-2-} (left, LabelForm(p:annf, la, q):restr)]
                otherwise                                  -> Nothing),
  (4, "L<.>", \ (left,right)  -> case left of
                LabelForm(annf, la, (Announce2 p q)):restl -> Just [{-1-}(LabelForm(annf, la, p):LabelForm(p:annf, la, q):restl, right)]
                otherwise             -> Nothing),
  (2, "Lrel", \ (left,right) -> case left of
                RelAtom (ag, (x:annf), w1, w2):restl  -> Just [{-1-}((LabelForm (annf,w1, x)):(LabelForm (annf,w2, x)):(RelAtom (ag, annf, w1, w2)):restl, right)]
                otherwise             -> Nothing),
  (5, "Rrel", \ (left,right) -> case right of
                RelAtom (ag, (x:annf), w1, w2):restr  -> Just [ {-1-}(left, (LabelForm (annf,w1, x)):restr), 
                                                                {-2-}(left, (LabelForm (annf,w2, x)):restr), 
                                                                {-3-}(left, RelAtom (ag, annf, w1, w2):restr)]
                otherwise             -> Nothing),
  (4, "Lcmp", \ (left,right)  -> case left of
                LabelForm(p `Conj` (Announce p' q):annf, w,r):restl| p==p'
                               -> Just [(LabelForm( (q:p:annf), w,r):restl,right)] 
                otherwise              -> Nothing),
  (4, "Rcmp", \ (left,right)  -> case right of
                LabelForm( (p `Conj` (Announce p' q)):annf,w,r):restr| p==p'
                               -> Just [(left,LabelForm( q:p:annf,w,r):restr )]
                otherwise              -> Nothing) ]


ruleK  :: [InferenceRule] 
ruleK =[
  (6, "R#", \  (left,right) -> case right of
                LabelForm (annf,la, Box ag hist p):restr  -> Just [({-1-}RelAtom (ag,annf,la, label1):left, LabelForm (annf, label1, p):restr)]
                                                        where label1 = freshLabel (left,right)  
                otherwise          -> Nothing),
  (9, "L#", \  (left,right) -> case left of
                LabelForm (annf, la, Box ag hist p):restl ->  if not $ null (difference (wholeLabel (left,right)) hist) 
                                                              then Just [{-1-} (LabelForm (annf, la, Box ag (nub (label2:hist)) p):restl,RelAtom (ag, annf, la, label2):right), 
                                                                         {-2-} (LabelForm (annf, la, Box ag (nub (label2:hist)) p):LabelForm (annf, label2, p):   restl,right)]
                                                              else  Nothing
                                                        where label2 = head $ rvsort $ difference (wholeLabel (left,right)) hist
                otherwise          -> Nothing){--},
  (6, "L$", \  (left,right) -> case left of
                LabelForm (annf, la, Dia ag hist p):restl -> Just [{-1-}(LabelForm (annf, la, Neg (Box ag hist (Neg p))):restl, right)]
                otherwise          -> Nothing),
  (6, "R$", \  (left,right) -> case right of
                LabelForm (annf, la, Dia ag hist p):restr -> Just [{-1-}(left,LabelForm (annf, la, Neg (Box ag hist (Neg p))):restr)]
                otherwise          -> Nothing)]


-- modal rules --------------------------------------------------------------------------------------------

ruleT ::  [InferenceRule] 
ruleT = [
  (8, "ref", \ (left,right) -> 
                if  nub left /= nub (left ++ [RelAtom (ag,[],w1, w1)|ag <- (wholeAgent (left,right)), w1<- (wholeLabel (left,right))])
                then Just [(left++ [RelAtom (ag,[],w1, w1)|ag <- (wholeAgent (left,right)), w1<- (wholeLabel (left,right))],right)]
                else Nothing)]


rule4  :: [InferenceRule] 
rule4 =[
  (8, "tra", \ (left,right) -> if (not$null$ tran left)   &&    (nub$sort$ tran left++left) /= (nub$sort left)
                              then  Just [((tran left++left),right)] 
                              else  Nothing)]

tran (rs) = if not$null (rs) then tran1 (head rs) (tail rs) else []
tran1 (RelAtom (ag,annf,w1, w2))   rs = if not$null rs then 
                                               case  head rs of 
                                               (RelAtom (ag,annf,w2', w4))|w2==w2'&& w1/=w4 -> [(RelAtom (ag,annf,w1, w4))] 
                                               otherwise      -> tran1 (RelAtom (ag,annf,w1, w2))  (tail rs)
                                        else []
tran1 x rs = []


rule5  :: [InferenceRule] 
rule5 =[
  (8, "euc", \ (left,right) -> if (not$null$ ecul left)   &&    (nub$sort$ ecul left++left) /= (nub$sort left)
                              then  Just [((ecul left++left),right)] 
                              else  Nothing)]

ecul (rs) = if not$null (rs) then ecul1 (head rs) (tail rs) else []
ecul1 (RelAtom (ag,annf,w2,w1))   rs = if not$null rs then 
                                               case  head rs of 
                                               (RelAtom (ag,annf,w2', w4))|w2==w2' {--}-> [(RelAtom (ag,annf,w1, w4))] 
                                               otherwise      -> ecul1 (RelAtom (ag,annf, w2,w1))  (tail rs)
                                        else []
ecul1 x rs = []



ruleB  :: [InferenceRule] 
ruleB =[
  (8, "sym", \ (left,right) -> if (not$null$ symm left)   &&    (nub$sort$ symm left++left) /= (nub$sort left)
                              then  Just [((symm left++left),right)] 
                              else  Nothing)]

symm rs = if not$null rs then symm1 (head rs) (tail rs) else []

symm1 x rs = if not$null rs then case x of  
                 (RelAtom (ag,annf,w1,w2)) -> [(RelAtom (ag,annf,w2, w1))] 
                 otherwise  -> symm1 (head rs) (tail rs)

                 else []

-- functions --------------------------------------------------------------------------------------------

freshLabel :: Sequent->Label
freshLabel sq = head[x|x<-[1..],x `notElem` (wholeLabel sq)]

wholeLabel :: Sequent->[Int]
wholeLabel sq =  nub(  [w | LabelForm (_,w,_) <-(fst sq)++(snd sq)]
                    ++ [w | RelAtom (_,_,w,v) <-(fst sq)++(snd sq)] 
                    ++ [v | RelAtom (_,_,w,v) <-(fst sq)++(snd sq)] )


wholeAgent :: Sequent->[Agent]
wholeAgent (left,right) = nub $ concat[ agentL x [] | x  <-left++right]

agentF x li = case  x of 
      Box ag hist p ->  agentF p (ag:li)
      Dia ag hist p -> agentF p (ag:li)
      Neg p -> (agentF p li)
      Conj p q -> (agentF p li) ++ (agentF q li)
      Disj p q -> (agentF p li) ++ (agentF q li)
      Impl p q -> (agentF p li) ++ (agentF q li)
      Impl2 p q -> (agentF p li) ++ (agentF q li)
      Equi p q -> (agentF p li) ++ (agentF q li)
      Announce p q -> (agentF p li) ++ (agentF q li)
      Announce2 p q -> (agentF p li) ++ (agentF q li)
      otherwise -> li

agentL x li = case  x of 
      LabelForm (annf,la, y)      -> agentF y li
      RelAtom (ag, annf, w1, w2)  -> (ag:li)

--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------


applicableRules ::Sequent -> [(Sequent,InferenceRule,[Sequent])]
applicableRules (left,right) = [ ((left,right),(num, r,ab),justList ab (left,right)) | (num, r,ab) <- (systemPAL++axiomRule), justTrue ab (left,right)]

sortRule ::   [(Sequent,InferenceRule,[Sequent])] ->[(Sequent,InferenceRule,[Sequent])]
sortRule []= []
sortRule (x:xs) =
   let smallerOrEqual = [a | a <- xs , fst3 (list2nd a) <= fst3 (list2nd x)]
       larger = [a | a <- xs , fst3 (list2nd a) > fst3 (list2nd  x)]
   in sortRule smallerOrEqual ++ [x] ++ sortRule larger

applyRule :: Sequent -> [Proof] 
applyRule (l1,r1) = [(head  [Proof ( name) (sort$nub l3, sort$nub r3) prf2 | ((l3,r3),(num,name,ab),ss) <- e,
                                                                                      prf2   <- combinations $ map applyRule ss])]
 where e = sortRule $ concat[applicableRules (l2, r2)|l2<-rotate l1, r2<-rotate r1] 


--------------------------------------------------------------------------------------------
-- Parser(output)
--------------------------------------------------------------------------------------------

--parseForm :: (Num a, Ord a) => a -> Formula -> String
parseForm n f = case f of
    Atom i   -> i
    AnyF i   -> i
    Top          -> "T"
    Bottom          -> "_|_"
    Neg  a          -> "~" ++ parseForm 3 a
    Box ag  hist a          -> "#" ++ag++show hist++ parseForm 3 a
    Dia ag hist a          -> "$"  ++ag++show hist++ parseForm 3 a
    Announce a b    -> parIf 3 ("["  ++parseForm 3 a ++ "]"  ++ parseForm 3 b)
    Announce2 a b   -> parIf 3 ("<"  ++parseForm 3 a ++ ">"  ++ parseForm 3 b)
    Conj a b        -> parIf 2 (parseForm 3 a +++ "&"  +++ parseForm 3 b)
    Disj a b        -> parIf 2 (parseForm 3 a +++ "v"  +++ parseForm 3 b)
    Impl a b        -> parIf 1 (parseForm 2 a +++ "->" +++ parseForm 2 b)
    Equi a b       -> parIf 1 (parseForm 2 a +++ "<->" +++ parseForm 2 b)
   where
    parIf k s = if n > k then "(" ++ s ++ ")" else s

outParseLabelExp :: Int -> LabelExp -> String
outParseLabelExp n f = case f of 
                 LabelForm(annf,la,f)   -> (show la)++"("++concat2 (reverse [parseForm n ff|ff<-annf])++"):"++(parseForm n f)
                 RelAtom(ag, annf,w1,w2)-> (show w1)++"R" ++ag ++ "("++concat2[parseForm n ff|ff<-annf]++")"++(show w2)

outParseSequent :: Sequent -> String
outParseSequent br =  prTList ", " (map (outParseLabelExp 1) (fst br)) +++
                  "==>" +++ 
                  prTList ", " (map (outParseLabelExp 1) (snd br))

concat2 :: [String] -> String
concat2 a = case a of 
            [] -> []
            x:xs -> x ++ concat2' xs
             where concat2' [] = ""
                   concat2' xs = ","++ (concat2 xs)


prTList t ss =
 case ss of
   []   -> ""
   [s]  -> s
   s:ss -> s ++ t ++ prTList t ss

drawProof1 :: Proof -> Tree [Char]
drawProof1 pr = Node ("["++(proof1st ( pr))++"]  " ++ outParseSequent(proof2nd ( pr))) 
          [drawProof1 x |x <-(proof3rd pr)]

drawProof2 :: Tree String -> IO ()
drawProof2 = putStrLn.drawTree

--------------------------------------------------------------------------------------------
-- Parser(output/ TeX)
--------------------------------------------------------------------------------------------
  
drawTexS :: Sequent -> String
drawTexS (left,right) = (words2 [drawTexL x|x<-left] )++"\\Rightarrow " ++(words2 [drawTexL x|x<-right] )

drawTexL l = case l of 
            LabelForm ([], w, f) -> (show w )++ "{:}^{\\epsilon}"++ (drawTexF 1 f)
            LabelForm (annf, w, f) -> (show w )++ "{:}^{" ++ (forml (reverse annf) )++ "}"++ (drawTexF 1 f)
            RelAtom (ag, [], w1,w2) -> show w1 ++ "\\mathsf{R}^{\\epsilon}_"++ag++ show w2
            RelAtom (ag, annf, w1,w2) -> show w1 ++ "\\mathsf{R}^{"++ (forml annf )++ "}_"++ag++ show w2
  where forml fs = words2[ drawTexF 1 f| f<-fs]

drawTexF n f = case f of
    Atom i   -> i
    AnyF i   -> i
    Top             -> " \\top "
    Bottom             -> " \\bot "
    Neg  a          -> " \\neg " ++ drawTexF 3 a
    Box ag  hist a          -> "\\mathcal{K}_{" ++ag++ "}" ++ drawTexF 3 a
    Dia ag hist a          -> "\\mathcal{\\widehat{K}}_{" ++ag++ "}" ++ drawTexF 3 a
    Announce a b    -> kakko 3 ("["  ++drawTexF 3 a ++ "]"  ++ drawTexF 3 b)
    Announce2 a b   -> kakko 3 ("\\langle "  ++drawTexF 3 a ++ "\\rangle "  ++ drawTexF 3 b)
    Conj a b        -> kakko 2 ("("++drawTexF 3 a +++ "\\wedge"  +++ drawTexF 3 b++")")
    Disj a b        -> kakko 2 ("("++drawTexF 3 a +++ "\\vee"  +++ drawTexF 3 b++")")
    Impl a b        -> kakko 1 (drawTexF 2 a +++ "\\to" +++ drawTexF 2 b)
    Equi a b        -> kakko 1 (drawTexF 2 a +++ "\\leftrightarrow" +++ drawTexF 2 b)
   where
    kakko k s = if n > k then "(" ++ s ++ ")" else s


drawTexP [(Proof rule sq next)]   = case next of 
  [] -> "\\infer[\\mbox{($" ++ (texRule rule) ++"$)}]{"++ drawTexS sq ++"}{}"
  [(Proof rule2 sq2 pr2)] -> "\\infer[\\mbox{($" ++  (texRule rule)  ++"$)}]{"++ drawTexS sq ++"}"++ "{"++ drawTexP [(Proof  rule2 sq2 pr2)] ++"}"
  [(Proof rule2 sq2 pr2),(Proof rule3 sq3 pr3)] -> "\\infer[\\mbox{($" ++ (texRule rule)  ++"$)}]{"++ drawTexS sq ++"}"++ "{"++ drawTexP [(Proof rule2 sq2 pr2)] ++ "&"++ drawTexP [(Proof rule3 sq3 pr3)] ++"}"
  [(Proof rule2 sq2 pr2),(Proof rule3 sq3 pr3),(Proof rule4 sq4 pr4)] -> "\\infer[\\mbox{($" ++ (texRule rule)  ++"$)}]{"++ drawTexS sq ++"}"++ "{"++ drawTexP [(Proof rule2 sq2 pr2)] ++ "&"++ drawTexP [(Proof rule3 sq3 pr3)]++ "&"++ drawTexP [(Proof rule4 sq4 pr4)] ++"}"

writeP  x= writeFile "figureTeX.tex" ("\\documentclass[landscape,a0b,final]{article}\n\\usepackage{amsmath, amssymb,amsthm}\n\\usepackage{proof}\n\\usepackage[truedimen,b4j,landscape,dvipdfm]{geometry}\n\\begin{document}\\tiny{" 
  ++ x ++ "}\\end{document}")

texRule r = case   r of 
       "R~" -> "R\\neg "
       "L~" -> "L\\neg "
       "R&" -> "R\\wedge "
       "L&" -> "L\\wedge "
       "Rv" -> "R\\vee "
       "Lv" -> "L\\vee "
       "R->" -> "R\\to "
       "L->"  -> "L\\to "
       "R<->" -> "R\\leftrightarrow "
       "L<->" -> "L\\leftrightarrow "
       "R<.>" -> "L\\langle . \\rangle "
       "L<.>" -> "R\\langle . \\rangle "
       "R#" -> "R\\mathcal{K} "
       "L#" -> "L\\mathcal{K} "
       "R$" -> "R\\mathcal{\\widehat{K}} "
       "L$" -> "L\\mathcal{\\widehat{K}} "
       x -> x

tex0 x = do 
       (writeP.drawTexP.listing.kaku2.kaku1) x

tex x = do 
       (writeP.drawTexP.listing.kaku2.kaku1) x
       system "latex figureTeX.tex"
       system "open figureTeX.tex"

tex2 x = do 
       (writeP.drawTexP.listing.kaku2) x
       system "latex figureTeX.tex"
       system "open figureTeX.tex"

--------------------------------------------------------------------------------------------
-- Parser(input)
--------------------------------------------------------------------------------------------

------ shoud be revised ----------------------------
replace :: Char -> String -> String-> String 
replace x y str = str >>= (\c -> if c == x then y else [c])

rep x = replace ']' ")+" (replace '[' "(" x)

addRirightarrow x = "==>" ++ x
----------------------------------

aa  = "(A->q)->[A]q"               -- o 

inParseSeq :: String -> Sequent
inParseSeq  = makeSeq.pF{--}.addRirightarrow-- .rep 


makeSeq [x,y] = ([LabelForm([],0,a)|a<-x],[LabelForm([],0,b)|b<-y])

pF x = case inParseForm x of 
               Right s -> s  

inParseForm :: String -> Either ParseError [[Formula]]
inParseForm x = parse sequent0 "error" (deletes ' ' x) 

sequent0   = (sepBy formulas0 (string "==>")) 
formulas0  = sepBy form0 (char ',')

form0 :: Parser Formula
form0 = do
      f1 <-form1
      (Equi f1 <$> (string "<->" *> form0)) <|> pure f1

form1 :: Parser Formula
form1 = do
      f1 <-form1a
      (Impl f1 <$> (string "->" *> form1))  <|> pure f1

form1a :: Parser Formula
form1a = do
      f1 <-form1b
      (Announce f1 <$> (string "+" *> form1a))  <|> pure f1{--}

form1b :: Parser Formula
form1b = do
      f1 <-form2
      (Announce2 f1 <$> (string "^" *> form1b))  <|> pure f1

form2 :: Parser Formula
form2 = do
      f1 <-form3 
      (Conj f1 <$> (char '&' *> form2)) <|> pure f1

form3 :: Parser Formula
form3 = do
      f1 <-annP<|>annP2<|>kakko<|> negP<|> boxP<|> form6    -- バイナリーオペレーター最後のオペレーターにはform4~6のシングルオペレーターのルールを全て加える. 
      (Disj f1 <$> (char 'v' *> form3)) <|> pure f1


negP :: Parser Formula
negP = do 
     char '~'
     f1 <- annP<|>annP2<|>kakko<|> form0 --カッコの提示は必須。そうしないとカッコよりも~などが優先される。
     return (Neg (f1))

boxP :: Parser Formula
boxP = do 
     string "#"
     ag  <- agent
     f1 <- annP<|>annP2<|>kakko<|> form0
     return (Box ag [] (f1))

form6:: Parser Formula
form6 = do 
     string "$"
     ag  <- agent
     f1 <- annP<|>annP2<|>kakko<|> form0
     return (Dia ag [] (f1))


kakko :: Parser Formula
kakko =  do 
        char '('
        f1 <-form0
        char ')'
        return f1
       <|> anyForm <|> atom1 -- カッコとアトムは最後

atom1 :: Parser Formula
atom1 = do  
    f1 <- oneOf ['f'..'z']
    return (Atom [f1])

anyForm :: Parser Formula
anyForm = do  
    f1 <- oneOf ['A'..'Z']
    return (AnyF [f1])

agent :: Parser String
agent = do 
     c <- oneOf ['a'..'e']
     return [c]  

annP :: Parser Formula
annP = do
      char '['
      f1 <-form1b
      (Announce (f1) <$> (char ']' *> form3))  <|> pure f1

annP2 :: Parser Formula
annP2 = do
      char '<'
      f1 <-form1b
      (Announce2 (f1) <$> (char '>' *> form3))  <|> pure f1
----------------------------------------------------------------------------------------------
-- main functions
----------------------------------------------------------------------------------------------
--make a proof figure
kaku1 :: String -> Sequent
kaku1 = inParseSeq

{-makeLabelForm :: [Formula] -> Sequent
makeLabelForm x = ([],[LabelForm([],0,head x)])-}

kaku2 :: Sequent -> Proof
kaku2 sq =  head (applyRule sq)

prove :: String -> IO ()
prove = drawProof2.drawProof1.kaku2.kaku1

prove2 = drawProof2.drawProof1.kaku2

proofCal :: [Proof] -> Int
proofCal pr = case  pr of 
  [] -> 0
  [Proof a b c]-> 1 + (proofCal c)
  [Proof a b c,Proof a2 b2 c2]-> 2 + (proofCal c)+(proofCal c2)
  [Proof a b c,Proof a2 b2 c2,Proof a3 b3 c3]-> 3 + (proofCal c)+(proofCal c2)+(proofCal c3)

proofcal = proofCal.listing.kaku2.kaku1
