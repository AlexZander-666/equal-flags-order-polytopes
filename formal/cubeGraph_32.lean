import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_32 :
    FastTriples.advancedRow cubeGraph 25 32 = 384 := by decide +kernel
#print axioms cubeGraph_row_32

theorem cubeGraph_row_33 :
    FastTriples.advancedRow cubeGraph 25 33 = 385 := by decide +kernel
#print axioms cubeGraph_row_33

theorem cubeGraph_row_34 :
    FastTriples.advancedRow cubeGraph 25 34 = 357 := by decide +kernel
#print axioms cubeGraph_row_34

theorem cubeGraph_row_35 :
    FastTriples.advancedRow cubeGraph 25 35 = 332 := by decide +kernel
#print axioms cubeGraph_row_35
