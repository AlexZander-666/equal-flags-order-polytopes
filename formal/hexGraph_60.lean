import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_60 :
    FastTriples.advancedRow hexGraph 25 60 = 3 := by decide +kernel
#print axioms hexGraph_row_60

theorem hexGraph_row_61 :
    FastTriples.advancedRow hexGraph 25 61 = 1 := by decide +kernel
#print axioms hexGraph_row_61

theorem hexGraph_row_62 :
    FastTriples.advancedRow hexGraph 25 62 = 0 := by decide +kernel
#print axioms hexGraph_row_62

theorem hexGraph_row_63 :
    FastTriples.advancedRow hexGraph 25 63 = 0 := by decide +kernel
#print axioms hexGraph_row_63
