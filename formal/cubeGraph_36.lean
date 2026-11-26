import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_36 :
    FastTriples.advancedRow cubeGraph 25 36 = 307 := by decide +kernel
#print axioms cubeGraph_row_36

theorem cubeGraph_row_37 :
    FastTriples.advancedRow cubeGraph 25 37 = 283 := by decide +kernel
#print axioms cubeGraph_row_37

theorem cubeGraph_row_38 :
    FastTriples.advancedRow cubeGraph 25 38 = 259 := by decide +kernel
#print axioms cubeGraph_row_38

theorem cubeGraph_row_39 :
    FastTriples.advancedRow cubeGraph 25 39 = 237 := by decide +kernel
#print axioms cubeGraph_row_39
