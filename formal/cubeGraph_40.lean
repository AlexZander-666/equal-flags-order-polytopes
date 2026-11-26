import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_40 :
    FastTriples.advancedRow cubeGraph 25 40 = 217 := by decide +kernel
#print axioms cubeGraph_row_40

theorem cubeGraph_row_41 :
    FastTriples.advancedRow cubeGraph 25 41 = 196 := by decide +kernel
#print axioms cubeGraph_row_41

theorem cubeGraph_row_42 :
    FastTriples.advancedRow cubeGraph 25 42 = 177 := by decide +kernel
#print axioms cubeGraph_row_42

theorem cubeGraph_row_43 :
    FastTriples.advancedRow cubeGraph 25 43 = 159 := by decide +kernel
#print axioms cubeGraph_row_43
