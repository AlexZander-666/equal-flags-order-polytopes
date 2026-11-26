import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem cubeGraph_row_0 :
    FastTriples.advancedRow cubeGraph 25 0 = 1857 := by decide +kernel
#print axioms cubeGraph_row_0

theorem cubeGraph_row_1 :
    FastTriples.advancedRow cubeGraph 25 1 = 1627 := by decide +kernel
#print axioms cubeGraph_row_1

theorem cubeGraph_row_2 :
    FastTriples.advancedRow cubeGraph 25 2 = 1571 := by decide +kernel
#print axioms cubeGraph_row_2

theorem cubeGraph_row_3 :
    FastTriples.advancedRow cubeGraph 25 3 = 1517 := by decide +kernel
#print axioms cubeGraph_row_3
