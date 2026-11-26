import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_44 :
    FastTriples.advancedRow cubeGraph 25 44 = 144 := by decide +kernel
#print axioms cubeGraph_row_44

theorem cubeGraph_row_45 :
    FastTriples.advancedRow cubeGraph 25 45 = 126 := by decide +kernel
#print axioms cubeGraph_row_45

theorem cubeGraph_row_46 :
    FastTriples.advancedRow cubeGraph 25 46 = 111 := by decide +kernel
#print axioms cubeGraph_row_46

theorem cubeGraph_row_47 :
    FastTriples.advancedRow cubeGraph 25 47 = 97 := by decide +kernel
#print axioms cubeGraph_row_47
