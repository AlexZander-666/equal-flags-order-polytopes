import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_56 :
    FastTriples.advancedRow hexGraph 25 56 = 21 := by decide +kernel
#print axioms hexGraph_row_56

theorem hexGraph_row_57 :
    FastTriples.advancedRow hexGraph 25 57 = 15 := by decide +kernel
#print axioms hexGraph_row_57

theorem hexGraph_row_58 :
    FastTriples.advancedRow hexGraph 25 58 = 10 := by decide +kernel
#print axioms hexGraph_row_58

theorem hexGraph_row_59 :
    FastTriples.advancedRow hexGraph 25 59 = 6 := by decide +kernel
#print axioms hexGraph_row_59
