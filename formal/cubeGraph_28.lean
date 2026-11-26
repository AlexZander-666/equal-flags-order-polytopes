import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_28 :
    FastTriples.advancedRow cubeGraph 25 28 = 499 := by decide +kernel
#print axioms cubeGraph_row_28

theorem cubeGraph_row_29 :
    FastTriples.advancedRow cubeGraph 25 29 = 470 := by decide +kernel
#print axioms cubeGraph_row_29

theorem cubeGraph_row_30 :
    FastTriples.advancedRow cubeGraph 25 30 = 441 := by decide +kernel
#print axioms cubeGraph_row_30

theorem cubeGraph_row_31 :
    FastTriples.advancedRow cubeGraph 25 31 = 412 := by decide +kernel
#print axioms cubeGraph_row_31
