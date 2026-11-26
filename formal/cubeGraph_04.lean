import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_4 :
    FastTriples.advancedRow cubeGraph 25 4 = 1463 := by decide +kernel
#print axioms cubeGraph_row_4

theorem cubeGraph_row_5 :
    FastTriples.advancedRow cubeGraph 25 5 = 1412 := by decide +kernel
#print axioms cubeGraph_row_5

theorem cubeGraph_row_6 :
    FastTriples.advancedRow cubeGraph 25 6 = 1360 := by decide +kernel
#print axioms cubeGraph_row_6

theorem cubeGraph_row_7 :
    FastTriples.advancedRow cubeGraph 25 7 = 1310 := by decide +kernel
#print axioms cubeGraph_row_7
