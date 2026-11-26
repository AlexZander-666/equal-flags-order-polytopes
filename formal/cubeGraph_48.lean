import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_48 :
    FastTriples.advancedRow cubeGraph 25 48 = 83 := by decide +kernel
#print axioms cubeGraph_row_48

theorem cubeGraph_row_49 :
    FastTriples.advancedRow cubeGraph 25 49 = 72 := by decide +kernel
#print axioms cubeGraph_row_49

theorem cubeGraph_row_50 :
    FastTriples.advancedRow cubeGraph 25 50 = 63 := by decide +kernel
#print axioms cubeGraph_row_50

theorem cubeGraph_row_51 :
    FastTriples.advancedRow cubeGraph 25 51 = 51 := by decide +kernel
#print axioms cubeGraph_row_51
