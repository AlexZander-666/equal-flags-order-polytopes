import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_4 :
    FastTriples.advancedRow hexGraph 25 4 = 1464 := by decide +kernel
#print axioms hexGraph_row_4

theorem hexGraph_row_5 :
    FastTriples.advancedRow hexGraph 25 5 = 1412 := by decide +kernel
#print axioms hexGraph_row_5

theorem hexGraph_row_6 :
    FastTriples.advancedRow hexGraph 25 6 = 1360 := by decide +kernel
#print axioms hexGraph_row_6

theorem hexGraph_row_7 :
    FastTriples.advancedRow hexGraph 25 7 = 1165 := by decide +kernel
#print axioms hexGraph_row_7
