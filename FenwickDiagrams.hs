{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module FenwickDiagrams where

import           Data.Typeable

import           Diagrams.Prelude
import           Diagrams.TwoD.Text

import           SegTree

data NodeType = LeafNode | InternalNode
type SegNode a = (NodeType, a)

sampleArray :: [Sum Int]
sampleArray = map (Sum . negate) [0, -4, -1, -1, -1, 2, -6, 4, 1, -6, 2, -5, 6, -2, -8, -3]

data SegTreeOpts a b = STOpts
  {
    -- | Node drawing function: takes value of node (marked as leaf or
    --   internal) leaves and Right for internal nodes, along with
    --   interval endpoints the node covers
    drawNode :: SegNode a -> Int -> Int -> Diagram b

  }

instance (N b ~ Double, V b ~ V2
         , Renderable (Path V2 Double) b, Renderable (Text Double) b
         , Show a) =>
  Default (SegTreeOpts a b) where
  def = STOpts { drawNode = drawNodeDef }

drawSegTree :: _ =>

  -- | Options controlling how to draw the tree
  SegTreeOpts a b ->

  -- | The segment tree to draw
  SegmentTree a ->
  Diagram b

drawSegTree o@(STOpts f) (Leaf a i)         = f (LeafNode, a) i i
drawSegTree o@(STOpts f) (Branch a i j l r) = localize $ vsep 1
  [ f (InternalNode, a) i j # named "root"
  , ((drawSegTree o l # named "left") ||| (drawSegTree o r # named "right")) # centerX
  ]
  # withNames ["root", "left", "right"]
  ( \[x, l, r] ->
      applyAll [ beneath (location x ~~ location l), beneath (location x ~~ location r) ]
  )

leafWidth :: Double
leafWidth = 1.2

-- XXX need to generalize the below node-drawing code.
-- Want to be able to draw

data DrawNodeOpts a b = DNOpts
  { drawNodeData :: a -> Diagram b
  , nodeStyle    :: a -> Style V2 Double
  }

instance (TypeableFloat (N b), V b ~ V2, Renderable (Text (N b)) b, Show a) =>
  Default (DrawNodeOpts a b) where
  def = DNOpts
    { drawNodeData = fontSizeL 0.6 . text . show
    , nodeStyle    = const defNodeStyle
    }

defNodeStyle :: Style V2 Double
defNodeStyle = mempty # fc white

drawNodeDef :: _ => SegNode a -> Int -> Int -> Diagram b
drawNodeDef = drawNode' def

drawNode' :: _ => DrawNodeOpts a b -> SegNode a -> Int -> Int -> Diagram b

drawNode' (DNOpts dn nsty) (LeafNode, a) _ _
  = dn a <> (square 1 <> strutX leafWidth) # applyStyle (nsty a)

drawNode' (DNOpts dn nsty) (InternalNode, a) i j = mconcat
  [ dn a <> circle 0.5 # applyStyle (nsty a)
  , hrule ((fromIntegral j - fromIntegral i) * leafWidth + 0.5)
    # lw veryThick
    # lc grey
    # lineCap LineCapRound
  ]

-- (j - i + 1) * leafWidth - (leafWidth - 1)
-- = (j - i) * leafWidth + 1
--
-- then subtract extra 0.5 just to leave a bit more gap

------------------------------------------------------------

showUpdateOpts :: _ => SegTreeOpts (Bool, Int) b
showUpdateOpts = STOpts
  { drawNode = drawNode'
      (DNOpts
        { drawNodeData = drawNodeData def . snd
        , nodeStyle    = \(u,x) ->
            defNodeStyle <> case u of { False -> mempty; True -> mempty # lc red }
        }
      )
  }
