import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_20 :
    FastTriples.advancedRow cubeGraph 25 20 = 776 := by decide +kernel
#print axioms cubeGraph_row_20

theorem cubeGraph_row_21 :
    FastTriples.advancedRow cubeGraph 25 21 = 738 := by decide +kernel
#print axioms cubeGraph_row_21

theorem cubeGraph_row_22 :
    FastTriples.advancedRow cubeGraph 25 22 = 702 := by decide +kernel
#print axioms cubeGraph_row_22

theorem cubeGraph_row_23 :
    FastTriples.advancedRow cubeGraph 25 23 = 665 := by decide +kernel
#print axioms cubeGraph_row_23
