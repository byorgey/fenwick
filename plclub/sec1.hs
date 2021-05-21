import           Diagrams.Backend.Rasterific.CmdLine
import           Diagrams.Prelude
import           FenwickDiagrams

main = mainWith dia

dia :: Diagram B
dia = drawArray (draw . ("a_"++) . show) [1 :: Int .. 8]
