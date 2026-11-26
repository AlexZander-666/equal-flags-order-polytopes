import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_24 :
    FastTriples.advancedRow cubeGraph 25 24 = 630 := by decide +kernel
#print axioms cubeGraph_row_24

theorem cubeGraph_row_25 :
    FastTriples.advancedRow cubeGraph 25 25 = 595 := by decide +kernel
#print axioms cubeGraph_row_25

theorem cubeGraph_row_26 :
    FastTriples.advancedRow cubeGraph 25 26 = 563 := by decide +kernel
#print axioms cubeGraph_row_26

theorem cubeGraph_row_27 :
    FastTriples.advancedRow cubeGraph 25 27 = 531 := by decide +kernel
#print axioms cubeGraph_row_27
