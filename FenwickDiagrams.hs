{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module FenwickDiagrams where

import Control.Monad (when)
import Control.Monad.State
import Data.Typeable
import Diagrams.Prelude hiding (Empty)
import Diagrams.TwoD.Text
import Diagrams.TwoD.Layout.Tree
import SegTree

sampleArray :: [Sum Int]
sampleArray = map (Sum . negate) [0, -4, -1, -1, -1, 2, -6, 4, 1, -6, 2, -5, 6, -2, -8, -3]

sampleArray4 :: [Sum Int]
sampleArray4 = map Sum (replicate 64 0)

drawArray :: _ => (a -> Diagram b) -> [a] -> Diagram b
drawArray nd = hcat . map (beneath squareNodeShape . nd)

rangeBracket :: _ => Int -> Int -> Diagram b
rangeBracket i j =
  fromOffsets
  [ -0.2 *^ unitY
  , (fromIntegral (j - i) * leafWidth + boxWidth) *^ unitX
  , 0.2 *^ unitY
  ]
  # translateX (-boxWidth / 2 + leafWidth * fromIntegral (i - 1))

data SegTreeOpts a b = STOpts
  {
    -- | Node drawing function: takes value of node (marked as leaf or
    --   internal) leaves and Right for internal nodes, along with
    --   interval endpoints the node covers.
    drawNode :: SegNode a -> Int -> Int -> Diagram b

    -- | Edge drawing function: takes value, location, and drawings of two nodes,
    --   produces diagram /transformation/ (so e.g. it can decide
    --   whether to draw under or over it).
  , drawEdge ::
      SegNode a -> Subdiagram b (V b) (N b) Any ->
      SegNode a -> Subdiagram b (V b) (N b) Any ->
      Diagram b -> Diagram b

    -- | Vertical separation between levels.
  , stVSep   :: Double

    -- | Should we draw the tree leaning to the right?
  , leanRight :: Bool
  }

instance (N b ~ Double, V b ~ V2
         , Drawable b a, Renderable (Path V2 Double) b, Renderable (Text Double) b
         , Show a) =>
  Default (SegTreeOpts a b) where
  def = STOpts { drawNode = drawNodeDef, drawEdge = drawEdgeDef, stVSep = 1, leanRight = False }

alignTo :: (Metric v, Semigroup m, Floating n, Ord n, IsName nm) =>
  nm -> QDiagram b v n m -> QDiagram b v n m
alignTo nm = withName nm $ moveOriginTo . location

drawSegTree :: _ =>

  -- | Options controlling how to draw the tree
  SegTreeOpts a b ->

  -- | The segment tree to draw
  SegmentTree a ->
  Diagram b

drawSegTree o@(STOpts f _ _  rt) (Leaf a i)         = f (LeafNode, a) i i
drawSegTree o@(STOpts f e vs rt) (Branch a i j l r) = localize $ vsep vs
  [ f (InternalNode, a) i j # named "root"
  , ((drawSegTree o l # named "left") ||| (drawSegTree o r # named "right"))
    # if rt then alignTo "right" else centerX
  ]
  # withNames ["root", "left", "right"]
  ( \[al, ll, rl] ->
      applyAll
      [ e (InternalNode, a) al
          (getRootNode l)   ll
      , e (InternalNode, a) al
          (getRootNode r)   rl
      ]
  )

boxWidth, leafSep, leafWidth :: Double
boxWidth = 1
leafSep = 0.2
leafWidth = boxWidth + leafSep

-- leafX l n computes the start and end offsets for leaf l in a tree
-- with n total leaf nodes.
leafX :: Int -> Int -> (Double, Double)
leafX l n =
  ( fi (l - 1 - n `div` 2) * leafWidth + (leafWidth - 1)/2
  , fi (l - n `div` 2) * leafWidth
  )

fi = fromIntegral

data DrawNodeOpts a b = DNOpts
  { drawNodeData :: a -> Diagram b
  , nodeStyle    :: a -> Style V2 Double
  , rangeStyle   :: a -> Style V2 Double
  , nodeShape    :: NodeType -> Diagram b
  , leanRightN   :: Bool
  }

class Drawable b a where
  draw :: a -> Diagram b

instance (V b ~ V2, TypeableFloat (N b), Renderable (Text (N b)) b) => Drawable b Int where
  draw = fontSizeL 0.6 . text . show

instance (V b ~ V2, TypeableFloat (N b), Renderable (Text (N b)) b) => Drawable b String where
  draw = fontSizeL 0.6 . text . mathify

instance Drawable b a => Drawable b (Sum a) where
  draw = draw . getSum

mathify = ("$"++) . (++"$")

instance
  ( N b ~ Double, V b ~ V2
  , Renderable (Text (N b)) b, Renderable (Path V2 Double) b
  , Drawable b a) =>
  Default (DrawNodeOpts a b) where
  def = DNOpts
    { drawNodeData = draw
    , nodeStyle    = const defNodeStyle
    , rangeStyle   = const defRangeStyle
    , nodeShape    = defNodeShape
    , leanRightN   = False
    }

defNodeStyle :: Style V2 Double
defNodeStyle = mempty # fc white

defRangeStyle :: Style V2 Double
defRangeStyle = mempty
  # lw veryThick
  # lc grey
  # lineCap LineCapRound

defNodeShape ::
  (V b ~ V2, N b ~ Double, Renderable (Path V2 Double) b) =>
  NodeType -> Diagram b
defNodeShape LeafNode     = squareNodeShape
defNodeShape InternalNode = circleNodeShape

squareNodeShape, circleNodeShape ::
  (V b ~ V2, N b ~ Double, Renderable (Path V2 Double) b) =>
  Diagram b
squareNodeShape = square boxWidth       <> strutX leafWidth
circleNodeShape = circle (boxWidth / 2) <> strutX leafWidth

drawEdgeDef ::
  (V b ~ V2, N b ~ Double, Renderable (Path V2 Double) b) =>
  SegNode a -> Subdiagram b V2 Double Any ->
  SegNode a -> Subdiagram b V2 Double Any ->
  Diagram b -> Diagram b
drawEdgeDef _ x _ y = beneath (location x ~~ location y)

drawNodeDef ::
  ( V b ~ V2, N b ~ Double, Renderable (Path V2 Double) b, Renderable (Text Double) b
  , Drawable b a) =>
  SegNode a -> Int -> Int -> Diagram b
drawNodeDef = drawNode' def

drawNode' ::
  (V b ~ V2, N b ~ Double, Renderable (Path V2 Double) b, Renderable (Text Double) b) =>
  DrawNodeOpts a b -> SegNode a -> Int -> Int -> Diagram b
drawNode' (DNOpts dn nsty _ shp _) (LeafNode, a) _ _
  = dn a <> shp LeafNode # applyStyle (nsty a)

drawNode' (DNOpts dn nsty rsty shp rt) (InternalNode, a) i j = mconcat
  [ dn a <> shp InternalNode # applyStyle (nsty a)
  , hrule ((fromIntegral j - fromIntegral i) * leafWidth + leafWidth/2)
    # applyStyle (rsty a)
    # if rt then (translateX (leafWidth/4) . alignR) else id
  ]

-- (j - i + 1) * leafWidth - (leafWidth - 1)
-- = (j - i) * leafWidth + 1
--
-- then subtract extra 0.5 just to leave a bit more gap

------------------------------------------------------------

updateColor :: Colour Double
updateColor = blend 0.5 red white

mkSTOpts :: _ => DrawNodeOpts a b -> SegTreeOpts a b
mkSTOpts dnOpts = STOpts { drawNode = drawNode' dnOpts, drawEdge = drawEdgeDef, stVSep = 1, leanRight = False }

showUpdateOpts :: _ => DrawNodeOpts (Bool, Int) b
showUpdateOpts =
  DNOpts
  { drawNodeData = drawNodeData def . snd
  , nodeStyle    = \(u,_) ->
      defNodeStyle <> case u of { False -> mempty; True -> mempty # fc updateColor }
  , rangeStyle   = const defRangeStyle
  , nodeShape    = defNodeShape
  , leanRightN   = False
  }

showRangeOpts :: (V b ~ V2, N b ~ Double, _) => DrawNodeOpts (Visit, a) b
showRangeOpts = showRangeOpts' True True

showRangeOpts' :: (V b ~ V2, N b ~ Double, _) => Bool -> Bool -> DrawNodeOpts (Visit, a) b
showRangeOpts' showNumbers showRangeBars =
  DNOpts
  { drawNodeData = case showNumbers of
                     True  -> drawNodeData def . snd
                     False -> const mempty
  , nodeStyle    = \(u,_) ->
      defNodeStyle <> mempty # case u of
      { NoVisit -> lc grey
      ; Zero    -> fc grey
      ; Stop    -> lc green . fc (blend 0.5 green white)
      ; Recurse -> lc blue  . fc (blend 0.5 blue white)
      }
  , rangeStyle   = \(u,_) ->
      mconcat
      [ defRangeStyle
      , mempty # case (u,showRangeBars) of
          { (Stop, _)  -> lc green
          ; (_, False) -> lw none
          ; _          -> lw medium
          }
      ]
  , nodeShape = defNodeShape
  , leanRightN = False
  }

-- data NodeState = Active | Inactive

showInactiveOpts :: (V b ~ V2, N b ~ Double, _) => Bool -> DrawNodeOpts (a, NodeState) b
showInactiveOpts showInactiveData =
  DNOpts
  { drawNodeData = \(a,s) ->
      case s of
        Active   -> drawNodeData def a
        Inactive ->
          if showInactiveData
            then drawNodeData def a # fc (blend 0.5 black darkgrey)
            else mempty
  , nodeStyle    = \(_,s) ->
      defNodeStyle <> mempty # case s of
        Active   -> mempty
        Inactive -> fc lightgrey
  , rangeStyle   = const (mempty # lw none)
  , nodeShape    = defNodeShape
  , leanRightN   = False
  }

------------------------------------------------------------

drawSlidingEdges ::
  (V b ~ V2, N b ~ Double, Renderable (Path V2 Double) b) =>
  SegNode (a, NodeState) -> Subdiagram b V2 Double Any ->
  SegNode (a, NodeState) -> Subdiagram b V2 Double Any ->
  Diagram b -> Diagram b
drawSlidingEdges _ s1 (_, (_, Inactive)) s2 = beneath $ mconcat
  [ location s1 ~~ location s2
  , arrowBetween' arrowOpts (location s1 .+^ 0.5 *^ edgeV) (location s2 .-^ 0.5 *^ edgeV)
    # translate ((0.4 *^) . perp $ edgeV)
  ]
  where
    edgeV = normalize $ location s2 .-. location s1
    arrowOpts = with & headLength .~ local 0.3

drawSlidingEdges _ s1 _ s2 = beneath (location s1 ~~ location s2)

------------------------------------------------------------

-- bt depth root left?
bt :: Int -> Int -> Bool -> State Int (BTree (Int, Maybe Int))
bt 0 _ _ = return Empty
bt d r left = do
  lt <- bt (d-1) (2*r) True
  rt <- bt (d-1) (2*r+1) False
  l <- get
  when left (modify (+1))
  return (BNode (r, if left then Just l else Nothing) lt rt)

dn :: _ => (Int, Maybe Int) -> Diagram b
dn (i,ml) = mconcat
  [ text ("$" ++ show i ++ "$") # translateX (-0.7)
  , vrule 3
  , circle 1.5
  , case ml of
      Nothing -> arc' 1.5 (direction unit_Y) ((1/2) @@ turn)
                 # closeTrail # strokeT # translateY (-1.5)
                 # fc (blend 0.4 black white) # lw none
      Just l  -> text ("$" ++ show l ++ "$") # fc blue # translateX 0.7
                 # fontSizeL 0.9
  , circle 1.5 # fc white # lw none
  ]
  # fontSizeL 0.8

drawRightLeaning :: _ => (a -> Diagram b) -> BTree a -> Diagram b
drawRightLeaning node (BNode x Empty Empty) = node x
drawRightLeaning node (BNode x l r) = localize $ vsep 2
  [ node x # named "root"
  , (drawRightLeaning node l # named "left" ||| strutX 2 ||| drawRightLeaning node r # named "right")
    # alignTo "right"
  ]
  # withNames ["root", "left", "right"]
  ( \[al, ll, rl] ->
     applyAll
     [ beneath (location al ~~ location ll), beneath (location al ~~ location rl) ]
  )
