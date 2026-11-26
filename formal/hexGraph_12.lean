import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_12 :
    FastTriples.advancedRow hexGraph 25 12 = 1118 := by decide +kernel
#print axioms hexGraph_row_12

theorem hexGraph_row_13 :
    FastTriples.advancedRow hexGraph 25 13 = 1071 := by decide +kernel
#print axioms hexGraph_row_13

theorem hexGraph_row_14 :
    FastTriples.advancedRow hexGraph 25 14 = 1027 := by decide +kernel
#print axioms hexGraph_row_14

theorem hexGraph_row_15 :
    FastTriples.advancedRow hexGraph 25 15 = 983 := by decide +kernel
#print axioms hexGraph_row_15
