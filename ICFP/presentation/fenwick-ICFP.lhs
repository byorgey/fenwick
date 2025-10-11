% -*- mode: LaTeX; compile-command: "./build.sh" -*-

\documentclass[xcolor={usenames,dvipsnames,svgnames,table},12pt,aspectratio=169]{beamer}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\let\Bbbk\undefined  % https://github.com/kosmikus/lhs2tex/issues/82
%include polycode.fmt

%subst pragma a = "\texttt{\string{-\#" a "\#-\string}}"

%format :--:   = "\mathrel{:\!\text{---}\!:}"
%format `inR`  = "\in"
%format inR    = "(" `inR` ")"
%format `subR` = "\subseteq"
%format subR   = "(" `subR` ")"

%format <>     = "\oplus "
%format mempty = "0 "

%format lo1
%format lo2
%format hi1
%format hi2

%format ++ = "+\!+"
%format `interleave` = "\interleaveop"
%format interleave = "(" `interleave` ")"
%format `find` = "\gnab"
%format find = "(" `find` ")"

%format pow (a) (b) = a "^ {" b "}"

%format * = "\cdot"

%format invBit = "\neg"
%format .+. = "\oplus"
%format .&. = "\land"
%format .|. = "\lor"
%format .&&. = "\owedge"
%format :. = "\mathrel{:\!.}"

%format not = "not"

%format ul(x) = "\underline{" x "}"

%format len(x) = "|" x "|"


\mode<presentation>
{
  \usetheme{default}                          % use a default (plain) theme

  \setbeamertemplate{navigation symbols}{}    % don't show navigation
                                              % buttons along the
                                              % bottom
  \setbeamerfont{normal text}{family=\sffamily}

%  \setbeamertemplate{footline}[frame number]

  \AtBeginSection[]
  {
    \begin{frame}<beamer>
      \frametitle{}
      \begin{center}
        {\Huge \insertsectionhead}

        % \vspace{0.25in}
        % \includegraphics[width=2in]{\secimage}
      \end{center}
    \end{frame}
  }
}

\newenvironment{xframe}[1][]
  {\begin{frame}[fragile,environment=xframe,#1]}
  {\end{frame}}

% uncomment me to get 4 slides per page for printing
% \usepackage{pgfpages}
% \pgfpagesuselayout{4 on 1}[uspaper, border shrink=5mm]

% \setbeameroption{show only notes}

% \usepackage[english]{babel}
\usepackage[T1]{fontenc}
\usepackage{graphicx}
\graphicspath{{images/}}

\usepackage{ulem}
\usepackage{url}
\usepackage{fancyvrb}

\usepackage[backend=pgf, input, extension=pgf, outputdir=diagrams]{diagrams-latex}
\usepackage{sproof}

\usepackage{minted}

\usepackage{amsmath}

\newtheorem{thm}{Theorem}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\interleaveop}{\curlyvee}

\newcommand{\toB}{\mathit{toBinary}}
\newcommand{\fromB}{\mathit{fromBinary}}
\newcommand{\ftb}{\ensuremath{\mathit{f2b}}}
\newcommand{\btf}{\ensuremath{\mathit{b2f}}}
\newcommand{\set}[1]{\mathit{set}\;{#1}}
\newcommand{\unset}[1]{\mathit{unset}\;{#1}}
\newcommand{\while}[2]{\mathit{while}\;{#1}\;{#2}}
\newcommand{\even}{\mathit{even}}
\newcommand{\odd}{\mathit{odd}}
\newcommand{\shl}{\mathit{shl}}
\newcommand{\shr}{\mathit{shr}}
\newcommand{\activeParent}{\mathit{activeParent}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Todo: include picture of Fenwick tree on title slide

\title{You Could Have Invented Fenwick Trees!}
\date{ICFP, 13 October 2025}
\author{Brent Yorgey}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\maketitle

% TODO: drawArray a_1 ... a_8 as section image
% \def\secimage{array}
\section{Motivation}

\begin{xframe}{Sequence operations}
\note{foo}
\begin{center}
\begin{diagram}[width=150]
import FenwickDiagrams

dia = vsep 0.5
  [ drawArray (draw . ("a_"++) . show) [1 :: Int .. 8]
  , mconcat
    [ arrowV unit_Y
    , text "update" # fontSizeL 0.5 # translate (1.5 ^& (-0.5))
    ]
    # translateX (3*leafWidth)
  , drawArray draw2 [1 :: Int .. 8]
  , rangeBracket 2 5
  , mconcat
    [ arrowV unit_Y
    , text "range query" # fontSizeL 0.5 # translate (2.2 ^& (-0.5))
    ]
    # translateX (2.5 * leafWidth)
  , text "$a_2 + a_3 + v + a_5$" # fontSizeL 0.6
    # translateX (2.5 * leafWidth)
  ]
  where
    draw2 4 = draw "v"
    draw2 n = draw ("a_" ++ show n)
\end{diagram}
\end{center}
\end{xframe}

% IFTIME: use colors for ranges instead of brackets
% \begin{xframe}{Prefix queries}
% \begin{center}
% \begin{diagram}[width=150]
% import FenwickDiagrams

% dia = vsep 0.5
%   [ drawArray draw (map (("a_"++) . show) [1 :: Int .. 8])
%   , rangeBracket 3 6
%   , text "=" # translateX (3.5 * leafWidth) <> strutY 1
%   , drawArray draw (map (("a_"++) . show) [1 :: Int .. 8])
%   , rangeBracket 1 6
%   , text "-" # translateX (3.5 * leafWidth) <> strutY 1
%   , drawArray draw (map (("a_"++) . show) [1 :: Int .. 8])
%   , rangeBracket 1 2
%   ]
%   # fontSizeL 0.7
% \end{diagram}
% \end{center}
% \end{xframe}

\begin{xframe}{Solutions}
  \begin{center}
  \begin{tabular}{ccc}
    approach & update & range query \\ \hline
    \onslide<2->{just store sequence & $O(1)$ & $O(n)$ \\}
    \onslide<3->{segment tree & $O(\lg n)$ & $O(\lg n)$ \\}
    \onslide<4->{Fenwick tree & $O(\lg n)$ & $O(\lg n)$}
  \end{tabular}

  \onslide<3>{$P[i] = a_1 + \dots + a_i$ \\ $RQ(i,j) = P[j] - P[i-1]$}
  \end{center}
\end{xframe}

\begin{xframe}{Segment trees}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree

  dia :: Diagram B
  dia = sampleArray
    # mkSegTree
    # fmap getSum
    # drawSegTree def
\end{diagram}

(assume $n = 2^k$)
\end{center}
\end{xframe}

\begin{xframe}{Updating a segment tree}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***))

  dia :: Diagram B
  dia = sampleArray
    # map ((,) (Any False))
    # mkSegTree
    # update 5 (Any True, Sum 3)
    # fmap (getAny *** getSum)
    # drawSegTree (mkSTOpts showUpdateOpts)
\end{diagram}
\end{center}
\end{xframe}

\begin{xframe}{Prefix query on a segment tree}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), second)

  dia :: Diagram B
  dia = vsep 0.7
    [ sampleArray
      # mkSegTree
      # rq' i j
      # fst
      # drawSegTree (mkSTOpts showRangeOpts)
    , (fst (leafX i n) ^& 0) ~~ (snd (leafX j n) ^& 0)
      # lc green
      # applyStyle defRangeStyle
    ]
    where
      i = 1
      j = 11
      n = length sampleArray
\end{diagram}
\end{center}
\end{xframe}

\begin{xframe}{Fenwick trees}
  \begin{center}
    \begin{minipage}{0.45\textwidth}
      \raisebox{-0.5\height}{\includegraphics[height=3in]{fenwick-p1}}
    \end{minipage}
    \hspace{0.25in}
    \begin{minipage}{0.45\textwidth}
      Peter Fenwick, 1994 \medskip

      A New Data Structure for Cumulative Frequency Tables \bigskip

      \onslide<2->{\& Boris Ryabko, 1989: A fast on-line code}
    \end{minipage}
  \end{center}
\end{xframe}

% \begin{xframe}{Ryabko trees?}
%   \begin{center}
%     \includegraphics[width=3.5in]{Ryabko}

%     \vspace{0.25in}
%   \end{center}
% \end{xframe}

\begin{xframe}{Implementing Fenwick trees}
  \inputminted[fontsize=\footnotesize]{java}{FenwickTree.java}
\end{xframe}

\section{Deriving Fenwick Trees}

% TODO: get rid of range bars in this diagram
\begin{xframe}{Thinning segment trees}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), first, second)

  dia :: Diagram B
  dia = sampleArray
    # mkSegTree
    # fmap getSum
    # drawSegTree def { drawNode = drawNode' def { rangeStyle = const (mempty # lw none) } }

\end{diagram}
\end{center}
\end{xframe}

\begin{xframe}{Thinning segment trees}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), first, second)

  dia :: Diagram B
  dia = sampleArray
    # mkSegTree
    # deactivate
    # drawSegTree (mkSTOpts (showInactiveOpts False))
\end{diagram}
\end{center}
\end{xframe}

% TODO: picture showing how any prefix corresponds to a specific
% collection of active nodes?

\begin{xframe}{Storing a thinned segment tree}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), first, second)

  dia :: Diagram B
  dia = vsep 0.5
    [ sampleArray
      # mkSegTree
      # deactivate
      # drawSegTree opts
    , arrowV (2 *^ unit_Y)
    , sampleArray
    # mkFenwickArray
    # drawArray (draw . getSum)
    # centerX
    ]

  opts = (mkSTOpts (showInactiveOpts False))
    { drawEdge = drawSlidingEdges }
\end{diagram}
\end{center}
\end{xframe}

\begin{xframe}{Fenwick tree = right-leaning, thinned segment tree}
  \begin{center}
\begin{diagram}[width=300]
{-# LANGUAGE LambdaCase #-}
import FenwickDiagrams
import SegTree

dia :: Diagram B
dia = sampleArray
  # mkSegTree
  # deactivate
  # drawSegTree stOpts

stOpts = (mkSTOpts nOpts)
  { leanRight = True }

nOpts = (showInactiveOpts False)
  { leanRightN = True
  , rangeStyle = \case { (_, Active) -> defRangeStyle; _ -> mempty # lw none }
  }
\end{diagram}

\vspace{1em}

\onslide<2>{\dots but how to move around?}
  \end{center}
\end{xframe}

\begin{xframe}{Indexing full binary trees}
  \begin{center}
  \begin{diagram}[width=250]
import Diagrams.Prelude hiding (Empty)
import Diagrams.TwoD.Layout.Tree
import Data.Maybe (fromJust)

-- bt depth root
bt :: Int -> Int -> BTree Int
bt 0 _ = Empty
bt d r = BNode r (bt (d-1) (2*r)) (bt (d-1) (2*r+1))

dia = bt 4 1
  # symmLayoutBin' (with & slHSep .~ 4 & slVSep .~ 4)
  # fromJust
  # renderTree dn (~~)

dn i = text ("$" ++ show i ++ "$") <> circle 1 # fc white
  \end{diagram}
  \end{center}
\end{xframe}

\begin{xframe}{Indexing full binary trees}
  \begin{center}
  \begin{diagram}[width=250]
import Diagrams.Prelude hiding (Empty)
import Diagrams.TwoD.Layout.Tree
import Data.Maybe (fromJust)

-- bt depth root
bt :: Int -> Int -> BTree Int
bt 0 _ = Empty
bt d r = BNode r (bt (d-1) (2*r)) (bt (d-1) (2*r+1))

dia = bt 4 2
  # symmLayoutBin' (with & slHSep .~ 4 & slVSep .~ 4)
  # fromJust
  # renderTree dn (~~)

dn i = text ("$" ++ show i ++ "$") <> circle 1 # fc white
  \end{diagram}
  \end{center}
\end{xframe}

\begin{xframe}{Indexing full binary trees, in binary}
  \begin{center}
  \begin{diagram}[width=250]
import Diagrams.Prelude hiding (Empty)
import Diagrams.TwoD.Layout.Tree
import Data.Maybe (fromJust)
import Numeric

-- bt depth root
bt :: Int -> Int -> BTree Int
bt 0 _ = Empty
bt d r = BNode r (bt (d-1) (2*r)) (bt (d-1) (2*r+1))

dia = bt 4 2
  # symmLayoutBin' (with & slHSep .~ 4 & slVSep .~ 4)
  # fromJust
  # renderTree dn (~~)
  # fontSizeL 0.8

dn i = text ("$" ++ showIntAtBase 2 ("01"!!) i "" ++ "$") <> circle 1 # fc white # lw none
  \end{diagram}
  \end{center}
\end{xframe}

\begin{xframe}{The Plan}
  \begin{itemize}
  \item Derive Fenwick tree $\leftrightarrow$ binary
    tree index conversions $\ftb$, $\btf$
  \item Compute motion through a Fenwick tree (array) as \[ \btf
    \circ \mathit{binaryTreeMotion} \circ \ftb \]
  \item Fuse
  \item \dots
  \item Profit!
  \end{itemize} \bigskip

  \onslide<2->{We're going to need some kind of DSL for
    manipulating numbers in binary\dots}
\end{xframe}

\section{Binary EDSL}

\begin{xframe}{Bits}
  \begin{code}
data Bit = O | I

invBit :: Bit -> Bit
invBit O = I
invBit I = O

(.&.), (.|.) :: Bit -> Bit -> Bit
O  .&. _  = O
I  .&. b  = b

I  .|. _  = I
O  .|. b  = b
  \end{code}
\end{xframe}

\begin{xframe}{2's complement}
  \begin{center}
  \begin{tabular}{cc}
    \dots 000101 & 5\\
    \dots 000100 & 4\\
    \dots 000011 & 3\\
    \dots 000010 & 2\\
    \dots 000001 & 1\\
    \dots 000000 & 0\\
    \onslide<2->{\dots 111111 & -1 \\}
    \onslide<3->{\dots 111110 & -2 \\}
    \onslide<4->{\dots 111101 & -3 \\}
  \end{tabular}
  \end{center}
\end{xframe}

\begin{xframe}{Encoding infinite 2's complement bit strings?}
  \begin{code}
type Bits = [Bit] ?
\end{code}
\onslide<2>{
\begin{itemize}
\item No decidable equality, can't convert |Bits -> Int|
\item ``Junk'' values like |cycle [O,I] = [O,I,O,I,O,I, ...]|
\end{itemize}
}
\end{xframe}

\begin{xframe}{Encoding infinite 2's complement bit strings}
  Valid bit strings must have some finite part followed by an infinite
  tail of all 0's or all 1's.
  \begin{code}
data Bits where
  Rep   :: Bit -> Bits
  (:.)  :: Bits -> Bit -> Bits  -- see paper for real details
  \end{code}

Examples:
\begin{itemize}
\item $2 = \dots 000010$ = |Rep O :. I :. O|
\item $-5 = \dots 1111011$ = |Rep I :. O :. I :. I|
\end{itemize}
\end{xframe}

\begin{xframe}{Operations on infinite bit strings}
  \begin{code}
(.&&.) :: Bits -> Bits -> Bits
Rep x .&&. Rep y = Rep (x .&. y)
(xs :. x) .&&. (ys :. y) = (xs .&&. ys) :. (x .&. y)
  \end{code}
\end{xframe}

\begin{xframe}{Operations on infinite bit strings}
\begin{code}
inc :: Bits -> Bits
inc (Rep I)    = Rep O
inc (bs :. O)  = bs :. I
inc (bs :. I)  = inc bs :. O

inv :: Bits -> Bits
inv (Rep b) = Rep (invBit b)
inv (bs :. b) = inv bs :. invBit b

neg :: Bits -> Bits
neg = inc . inv
\end{code}
\end{xframe}

\begin{xframe}{LSB}
  \begin{code}
lsb :: Bits -> Bits
lsb (_ :. I)   = Rep O :. I
lsb (bs :. O)  = lsb bs :. O
lsb (Rep O)    = Rep O
  \end{code}
\onslide<2->{
  \inputminted[fontsize=\footnotesize,firstline=15,lastline=15]{java}{FenwickTree.java}
}
\bigskip
\onslide<3->{
  \begin{center}
    |lsb x = x .&&. neg x|

    Proof: induction on |x|.
  \end{center}
}
\end{xframe}

\begin{xframe}{Other operations on |Bits|}
  \begin{code}
set, clear
test, even, odd
shl, shr

while :: (a -> Bool) -> (a -> a) -> a -> a
while p f x
  | p x        = while p f (f x)
  | otherwise  = x
\end{code}

\onslide<2->{\& various rewriting lemmas, e.g. |inc . while odd shr = while even shr . inc|}
\end{xframe}

\section{Fenwick/binary conversion}

\begin{xframe}{\ftb}
  \begin{center}
  \begin{diagram}[width=250]
import FenwickDiagrams
import Control.Monad.State (evalState)

dia :: Diagram B
dia = evalState (bt 4 2 True) 1 # drawRightLeaning dn
  \end{diagram}
  \vspace{0.25in}

  \begin{tabular}{cccccccc}
    \textcolor{blue}{1} & \textcolor{blue}{2} & \textcolor{blue}{3}  & \textcolor{blue}{4} & \textcolor{blue}{5} & \textcolor{blue}{6} & \textcolor{blue}{7} & \textcolor{blue}{8} \\
    16 & 8 & 18 & 4 & 20 & 10 & 22 & 2
  \end{tabular}
  \end{center}

\end{xframe}

\begin{xframe}{\ftb}
  \begin{center}
  \begin{diagram}[width=300]
import FenwickDiagrams
import Control.Monad.State (evalState)

dia :: Diagram B
dia = evalState (bt 5 2 True) 1 # drawRightLeaning dn
  \end{diagram}
  \vspace{0.25in}

  \begingroup
  \setlength{\tabcolsep}{4pt}
  \begin{tabular}{cccccccccccccccc}
  \textcolor{blue}{1} & \textcolor{blue}{2} & \textcolor{blue}{3} & \textcolor{blue}{4} & \textcolor{blue}{5} & \textcolor{blue}{6} & \textcolor{blue}{7} & \textcolor{blue}{8} & \textcolor{blue}{9} & \textcolor{blue}{10} & \textcolor{blue}{11} & \textcolor{blue}{12} & \textcolor{blue}{13} & \textcolor{blue}{14} & \textcolor{blue}{15} & \textcolor{blue}{16}
  \\
  32 & \textcolor{green}{16} & 34 & \textcolor{green}{8} & 36 & \textcolor{green}{18} & 38 & \textcolor{green}{4} & 40 & \textcolor{green}{20} & 42 & \textcolor{green}{10} & 44 & \textcolor{green}{22} & 46 & \textcolor{green}{2}
  \end{tabular}
  \endgroup
  \end{center}

\end{xframe}

\begin{xframe}{\ftb}
  \begin{code}
interleave :: [a] -> [a] -> [a]
[]        `interleave` _   = []
(x : xs)  `interleave` ys  = x : (ys `interleave` xs)
  \end{code}

  \begin{code}
b :: Int -> [Int]
b 0  = [2]
b n  = map (2*) [pow 2 n .. pow 2 n + pow 2 (n-1) - 1] `interleave` b (n-1)
  \end{code}

\[ |f2b n k = b n ! k| = \begin{cases} |f2b (n-1) (k/2)| & k \text{ even} \\ 2^{n+1}
    + k - 1 & k \text{ odd} \end{cases} \]

  % \begin{align*}
  %   [] \inter \_ &= [] \\
  %   (x::xs) \inter ys &= x :: (ys \inter xs) \\ \\
  %   b_0 &= [2] \\
  %   b_n &= map\; (2 \times)\; [2^n, \dots, 2^n + 2^{n-1}-1] \inter b_{n-1} \\ \\
  %   \ftb_n\; k &= b\;n\;!\;k \qquad \text{(1-indexed)}
  % \end{align*}
\end{xframe}

% \begin{xframe}{Interleaving lemmas}
%   \begin{align*}
%     (xs \inter ys)\; ! \; 2k &= ys\;!\;k \\
%     (xs \inter ys)\; ! \; (2k - 1) &= xs\;!\;k
%   \end{align*}
% \end{xframe}

% \begin{xframe}{Simplifying \ftb}
% \begin{sproof}
%   \stmt{|f2b n (2*j)|}
%   \reason{=}{Definition of |f2b|}
%   \stmt{|b n ! (2 * j)|}
%   \reason{=}{Definition of |b|}
%   \stmt{|(map (2*) [pow 2 n .. pow 2 n + pow 2 (n-1) - 1] `interleave` b (n-1)) ! (2 * j)|}
%   \reason{=}{|`interleave`-!| lemma}
%   \stmt{|b (n-1) ! j|}
%   \reason{=}{Definition of |f2b|}
%   \stmt{|f2b (n-1) j|.}
% \end{sproof}
% \end{xframe}

% \begin{xframe}{\ftb}
% \begin{sproof}
%   \stmt{|f2b n (2*j-1)|}
%   \reason{=}{Definition of |f2b|}
%   \stmt{|b n ! (2 * j-1)|}
%   \reason{=}{Definition of |b|}
%   \stmt{|(map (2*) [pow 2 n .. pow 2 n + pow 2 (n-1) - 1] `interleave` b (n-1)) ! (2*j-1)|}
%   \reason{=}{|`interleave`-!| lemma}
%   \stmt{|map (2*) [pow 2 n .. pow 2 n + pow 2 (n-1) - 1] ! j|}
%   \reason{=}{Definition of |map|, algebra}
%   \stmt{|2 * (pow 2 n + j - 1)|}
%   \reason{=}{algebra}
%   \stmt{|pow 2 (n+1) + 2j-2|}
% \end{sproof}
% \end{xframe}

\begin{xframe}{\ftb}
  \[ |f2b n k| = \begin{cases} |f2b (n-1) (k/2)| & k \text{ even} \\ 2^{n+1}
    + k - 1 & k \text{ odd} \end{cases} \]

\begin{center}
\onslide<2->{
\begin{code}
f2b n = dec . while even shr . set (n+1)
\end{code}%
}%
\onslide<3->{%
\begin{code}
b2f n = clear (n+1) . while (not . test (n+1)) shl . inc
\end{code}
}
\end{center}
\end{xframe}

\begin{xframe}{update via |activeParent|}
\begin{center}
\begin{diagram}[width=300]
{-# LANGUAGE LambdaCase #-}
import FenwickDiagrams
import SegTree

dia :: Diagram B
dia = sampleArray
  # mkSegTree
  # deactivate
  # drawSegTree stOpts

stOpts = (mkSTOpts nOpts)
  { leanRight = True }

nOpts = (showInactiveOpts False)
  { leanRightN = True
  , rangeStyle = \case { (_, Active) -> defRangeStyle; _ -> mempty # lw none }
  }
\end{diagram} \bigskip

\onslide<2->{|activeParent = b2f . while odd shr . shr . f2b|}
\end{center}
% TODO: make picture with arrows pointing up the tree, showing how
% finding the active parent in BT corresponds to finding parent (shl), then
% finding parents until reaching an even node
\end{xframe}

\begin{xframe}{Calculating |activeParent|}
  \begin{sproof}
    \stmt{|activeParent = b2f . while odd shr . shr . f2b|}
    \reason{=}{inline + rewrite\dots}
    \stmt{|clear (n+1) . while (not . test (n+1)) shl . inc . while even shr . set (n+1)|}
  \end{sproof}

\begin{center}
\begin{diagram}[width=50]
  import Fenwick
  import Diagrams.Prelude hiding (Empty)
  import Prelude hiding (even)

  type FBits = (Int, [Style V2 Double], Bits)

  drawBits :: FBits -> Diagram B
  drawBits (0, _, _) = mempty
  drawBits (n, [], bs :. b) = drawBits (n-1, [], bs) |||||| drawBit mempty b
  drawBits (n, (s:ss), bs :. b) = drawBits (n-1, ss, bs) |||||| drawBit s b

  bitColor O = grey
  bitColor I = blue

  drawBit :: Style V2 Double -> Bit -> Diagram B
  drawBit s b = mconcat
    [ text (show (fromEnum b)) # applyStyle s # fc (bitColor b) # fontSizeL 0.8
    , square 1
    ]

  drawSteps :: [(FBits, Maybe String)] -> Diagram B
  drawSteps = vsep 0.5 . map drawStep

  drawStep :: (FBits, Maybe String) -> Diagram B
  drawStep (bs, Nothing) = drawBits bs # centerX
  drawStep (bs, Just s) = vsep 0.5
    [ drawBits bs # centerX
    , hsep 0.5
      [ arrowV unit_Y # centerY
      , alignedText 0 0.5 s # fontSizeL 0.8
      ]
      # alignL
    ]

  sentinelStyle n = replicate (n-1) mempty ++ [mempty # fc red]

  dia = drawSteps
    [ ((8, [], toBits 52), Just "set sentinel bit")
    , ((8, sentinelStyle 8, toBits 52 .+. toBits (2^7)), Just "shift right")
    , ((8, sentinelStyle 6, while even shr (toBits 52 .+. toBits (2^7))), Just "increment")
    , ((8, sentinelStyle 6, inc (while even shr (toBits 52 .+. toBits (2^7)))), Just "shift left")
    , ((8, sentinelStyle 8, toBits 56 .+. toBits (2^7)), Just "unset sentinel bit")
    , ((8, [], toBits 56), Nothing)
    ]
\end{diagram}
\end{center}
\end{xframe}

\begin{xframe}{update}
  \begin{center}
    |activeParent = ... = \x -> x + lsb x|
  \end{center}
  \vspace{1em}

  \onslide<2->{\inputminted[fontsize=\footnotesize,firstline=8,lastline=10]{java}{FenwickTree.java}}
\end{xframe}

\begin{xframe}
  More in the paper:
  \begin{itemize}
  \item More pictures!
  \item Proofs!
  \item Deriving \mintinline{java}{prefix} (subtracting LSB)!
  \end{itemize}

\begin{center}
\begin{diagram}[width=200]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), second)

  dia :: Diagram B
  dia = vsep 0.7
    [ sampleArray
      # mkSegTree
      # rq' i j
      # fst
      # drawSegTree opts
    , (fst (leafX i n) ^& 0) ~~ (snd (leafX j n) ^& 0)
      # lc green
      # applyStyle defRangeStyle
    ]
      <> (arrowBetween' arrOpts (5 ^& (-2)) (0 ^& (-2))) # lw veryThick
      <> (arrowBetween' arrOpts (3.5 ^& (-6)) (1.5 ^& (-6))) # lw veryThick
    where
      i = 1
      j = 11
      n = length sampleArray

      de (_, (Recurse, _)) x _ y
        || location x ^. _x > location y ^. _x =
             beneath (arrowBetween' arrOpts (location y) (location x) # lw veryThick
                      <> (location x ~~ location y))
      de _ x _ y = beneath (location x ~~ location y)

      arrOpts = with & gaps .~ local 0.5

      opts :: SegTreeOpts (Visit, Sum Int) B
      opts = (mkSTOpts (showRangeOpts' False False) :: SegTreeOpts (Visit, Sum Int) B)
        { drawEdge = de
        }
\end{diagram}
\end{center}
\end{xframe}

\begin{xframe}{}
  \begin{center}
    {\Huge Thanks!}
  \end{center}
\end{xframe}

\begin{xframe}
  \begin{code}
data Bits where
  Rep   :: Bit -> Bits
  Snoc  :: !Bits -> Bit -> Bits

toSnoc :: Bits -> Bits
toSnoc (Rep a) = Snoc (Rep a) a
toSnoc as = as

pattern (:.) :: Bits -> Bit -> Bits
pattern (:.) bs b <- (toSnoc -> Snoc bs b)
  where
    Rep b :. b' | b == b' = Rep b
    bs :. b = Snoc bs b

{-# COMPLETE (:.) #-}
  \end{code}
\end{xframe}


% \begin{xframe}{Simplifying toBinary}
%     \[ \toB_n(j) = \begin{cases}
%         \toB_{n-1}(j/2) & \text{$j$ even} \\ 2^n + j - 1
%         & \text{$j$ odd} \end{cases} \] \bigskip

%   Let $k = 2^a b$ where $b$ is odd.  Then
%   \[ \toB_n(2^a b) = \toB_{n-a}(b) =
%     2^{n-a} + b - 1. \]
% \end{xframe}

% \begin{xframe}{toBinary as bit operations?}
%   \[ \toB_n(2^a b) = 2^{n-a} + b - 1 \]

%   Given $k = 2^a b < 2^n$ ($2^n \to 1$ is special case):
%   \begin{itemize}
%   \item set $2^n$ bit ($2^n + 2^a b$)
%   \item shift right until final bit is $1$  ($2^{n-a} + b$)
%   \item set final bit to $0$ ($2^{n-a} + b - 1$)
%   \end{itemize} \medskip

%   \[ \toB_n = \unset 0 \circ \while{\even}{\shr} \circ
%     \set{n} \]

%   \onslide<2->{Question: what is the right DSL for expressing this bit
%     manipulation procedure?}

%     % TODO: express this using a little bit DSL
% \end{xframe}

% \begin{xframe}{fromBinary}
%   \[ \toB_n = \unset 0 \circ \while{\even}{\shr} \circ
%     \set{n} \]

%   $\fromB_n$ ($1 \to 2^n$ is special case):
%   \begin{itemize}
%   \item set final bit to $1$
%   \item shift left until MSB is $2^n$
%   \item set $2^n$ bit to 0
%   \end{itemize} \medskip

%   \[ \fromB_n = \unset n \circ \while{(< 2^n)}{\shl} \circ \set 0 \]
% \end{xframe}

% \begin{xframe}{$\fromB_n \circ \toB_n$ example}
%   \begin{sproof}
%     \stmt{00110100}
%     \reason{\to}{$\set n$}
%     \stmt{10110100}
%     \reason{\to}{$\while{\even}{\shr}$}
%     \stmt{00101101}
%     \reason{\to}{$\unset 0$}
%     \stmt{00101100}
%     \reason{\to}{$\set 0$}
%     \stmt{00101101}
%     \reason{\to}{$\while{(< 2^n)}{\shl}$}
%     \stmt{10110100}
%     \reason{\to}{$\unset n$}
%     \stmt{00110100}
%   \end{sproof}
% \end{xframe}

% \begin{xframe}{Update}
%   \begin{center}
% \begin{diagram}[width=300]
% import Diagrams.Prelude hiding (Empty)
% import Diagrams.TwoD.Layout.Tree
% import Data.Maybe (fromJust)
% import Control.Monad.State
% import Control.Monad (when)

% -- bt depth root left?
% bt :: Int -> Int -> Bool -> State Int (BTree (Int, Maybe Int))
% bt 0 _ _ = return Empty
% bt d r left = do
%   lt <- bt (d-1) (2*r) True
%   rt <- bt (d-1) (2*r+1) False
%   l <- get
%   when left (modify (+1))
%   return (BNode (r, if left then Just l else Nothing) lt rt)

% dia = evalState (bt 5 1 True) 1
%   # symmLayoutBin' (with & slHSep .~ 4 & slVSep .~ 4)
%   # fromJust
%   # renderTree dn (~~)

% dn :: (Int, Maybe Int) -> Diagram B
% dn (i,ml) = mconcat
%   [ text ("$" ++ show i ++ "$") # translateX (-0.7)
%   , vrule 3
%   , circle 1.5
%   , case ml of
%       Nothing -> arc' 1.5 (direction unit_Y) ((1/2) @@ turn)
%                  # closeTrail # strokeT # translateY (-1.5)
%                  # fc grey # lw none
%       Just l  -> text ("$" ++ show l ++ "$") # fc blue # translateX 0.7
%                  # fontSizeL 0.9
%   , circle 1.5 # fc (case ml of { Just 6 -> lgr ; Just 8 -> lgr ; _ -> white })
%                # lw none
%   ]
%   # fontSizeL 0.7
%   where
%     lgr = lightgreen
% \end{diagram}

% \onslide<2->{
%   \[ \activeParent = \while{\odd}{\shr} \circ \shr \]
% }
% \end{center}
% \end{xframe}

% \begin{xframe}{Update}
%   \begin{align*}
%     \mathit{nextUpdate_n}
%     &= \fromB_n \circ \activeParent \circ \toB_n \\
%     &= \unset n \circ \while{(< 2^n)}{\shl} \circ \set 0 \\
%     &\qquad\circ \while{\odd}{\shr} \circ \shr \\
%     &\qquad\circ \unset 0 \circ \while{\even}{\shr} \circ \set{n} \\
%     &= \unset n \circ \while{(< 2^n)}{\shl} \\
%     &\qquad\circ \set 0 \circ \while{\odd}{\shr} \circ
%       \while{\even}{\shr} \\
%     &\qquad\circ \set{n} \\
%     &= \dots \; ? \; \dots \\
%     &= \lambda x. x + \mathit{LSB}\;x
%   \end{align*}
% \end{xframe}

% \begin{xframe}{Update example}
%   \begin{sproof}
%     \stmt{00110}
%     \reason{\to}{$\set n$}
%     \stmt{10110}
%     \reason{\to}{$\while{\even}{\shr}$}
%     \stmt{01011}
%     \reason{\to}{$\while{\odd}{\shr}$}
%     \stmt{00010}
%     \reason{\to}{$\set 0$}
%     \stmt{00011}
%     \reason{\to}{$\while{(< 2^n)}{\shl}$}
%     \stmt{11000}
%     \reason{\to}{$\unset n$}
%     \stmt{01000}
%   \end{sproof}
% \end{xframe}

\end{document}

% XXX working here!  Motivate goals, then add section heading, do 2's
% complement DSL.

% IF TIME, show why this definition of LSB works.
% Otherwise leave it as exercise.  2's complement, to negate we flip
% all the bits then increment.  This means -x has all opposite bits as
% x up to the LSB, then is the same from the LSB onwards.

% \begin{xframe}{LSB = Least Significant Bit}
%   \[ \mathrm{LSB}(01101100) = 00000100 \]
%   \bigskip

%   \onslide<2->{
%     $\mathrm{LSB}(x) = x \mathbin{\&} (-x)$?  Hint: in 2's complement,
%     $(-x) = \overline{x} + 1$.
%   }
% \end{xframe}

