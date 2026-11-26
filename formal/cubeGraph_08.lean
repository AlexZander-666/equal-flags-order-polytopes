import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_8 :
    FastTriples.advancedRow cubeGraph 25 8 = 1260 := by decide +kernel
#print axioms cubeGraph_row_8

theorem cubeGraph_row_9 :
    FastTriples.advancedRow cubeGraph 25 9 = 1262 := by decide +kernel
#print axioms cubeGraph_row_9

theorem cubeGraph_row_10 :
    FastTriples.advancedRow cubeGraph 25 10 = 1212 := by decide +kernel
#print axioms cubeGraph_row_10

theorem cubeGraph_row_11 :
    FastTriples.advancedRow cubeGraph 25 11 = 1163 := by decide +kernel
#print axioms cubeGraph_row_11
