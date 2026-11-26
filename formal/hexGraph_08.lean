import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_8 :
    FastTriples.advancedRow hexGraph 25 8 = 1313 := by decide +kernel
#print axioms hexGraph_row_8

theorem hexGraph_row_9 :
    FastTriples.advancedRow hexGraph 25 9 = 1262 := by decide +kernel
#print axioms hexGraph_row_9

theorem hexGraph_row_10 :
    FastTriples.advancedRow hexGraph 25 10 = 1211 := by decide +kernel
#print axioms hexGraph_row_10

theorem hexGraph_row_11 :
    FastTriples.advancedRow hexGraph 25 11 = 1165 := by decide +kernel
#print axioms hexGraph_row_11
