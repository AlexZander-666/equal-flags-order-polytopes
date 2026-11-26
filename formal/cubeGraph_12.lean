import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_12 :
    FastTriples.advancedRow cubeGraph 25 12 = 1116 := by decide +kernel
#print axioms cubeGraph_row_12

theorem cubeGraph_row_13 :
    FastTriples.advancedRow cubeGraph 25 13 = 1071 := by decide +kernel
#print axioms cubeGraph_row_13

theorem cubeGraph_row_14 :
    FastTriples.advancedRow cubeGraph 25 14 = 1025 := by decide +kernel
#print axioms cubeGraph_row_14

theorem cubeGraph_row_15 :
    FastTriples.advancedRow cubeGraph 25 15 = 981 := by decide +kernel
#print axioms cubeGraph_row_15
