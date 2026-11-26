import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_16 :
    FastTriples.advancedRow cubeGraph 25 16 = 939 := by decide +kernel
#print axioms cubeGraph_row_16

theorem cubeGraph_row_17 :
    FastTriples.advancedRow cubeGraph 25 17 = 896 := by decide +kernel
#print axioms cubeGraph_row_17

theorem cubeGraph_row_18 :
    FastTriples.advancedRow cubeGraph 25 18 = 855 := by decide +kernel
#print axioms cubeGraph_row_18

theorem cubeGraph_row_19 :
    FastTriples.advancedRow cubeGraph 25 19 = 814 := by decide +kernel
#print axioms cubeGraph_row_19
