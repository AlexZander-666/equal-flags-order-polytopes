import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_52 :
    FastTriples.advancedRow cubeGraph 25 52 = 43 := by decide +kernel
#print axioms cubeGraph_row_52

theorem cubeGraph_row_53 :
    FastTriples.advancedRow cubeGraph 25 53 = 34 := by decide +kernel
#print axioms cubeGraph_row_53

theorem cubeGraph_row_54 :
    FastTriples.advancedRow cubeGraph 25 54 = 27 := by decide +kernel
#print axioms cubeGraph_row_54

theorem cubeGraph_row_55 :
    FastTriples.advancedRow cubeGraph 25 55 = 21 := by decide +kernel
#print axioms cubeGraph_row_55
