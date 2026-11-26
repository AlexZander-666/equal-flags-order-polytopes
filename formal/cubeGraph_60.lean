import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_60 :
    FastTriples.advancedRow cubeGraph 25 60 = 3 := by decide +kernel
#print axioms cubeGraph_row_60

theorem cubeGraph_row_61 :
    FastTriples.advancedRow cubeGraph 25 61 = 1 := by decide +kernel
#print axioms cubeGraph_row_61

theorem cubeGraph_row_62 :
    FastTriples.advancedRow cubeGraph 25 62 = 0 := by decide +kernel
#print axioms cubeGraph_row_62

theorem cubeGraph_row_63 :
    FastTriples.advancedRow cubeGraph 25 63 = 0 := by decide +kernel
#print axioms cubeGraph_row_63
