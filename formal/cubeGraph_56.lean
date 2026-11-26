import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_56 :
    FastTriples.advancedRow cubeGraph 25 56 = 15 := by decide +kernel
#print axioms cubeGraph_row_56

theorem cubeGraph_row_57 :
    FastTriples.advancedRow cubeGraph 25 57 = 15 := by decide +kernel
#print axioms cubeGraph_row_57

theorem cubeGraph_row_58 :
    FastTriples.advancedRow cubeGraph 25 58 = 10 := by decide +kernel
#print axioms cubeGraph_row_58

theorem cubeGraph_row_59 :
    FastTriples.advancedRow cubeGraph 25 59 = 6 := by decide +kernel
#print axioms cubeGraph_row_59
