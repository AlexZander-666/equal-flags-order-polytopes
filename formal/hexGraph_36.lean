import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_36 :
    FastTriples.advancedRow hexGraph 25 36 = 308 := by decide +kernel
#print axioms hexGraph_row_36

theorem hexGraph_row_37 :
    FastTriples.advancedRow hexGraph 25 37 = 283 := by decide +kernel
#print axioms hexGraph_row_37

theorem hexGraph_row_38 :
    FastTriples.advancedRow hexGraph 25 38 = 262 := by decide +kernel
#print axioms hexGraph_row_38

theorem hexGraph_row_39 :
    FastTriples.advancedRow hexGraph 25 39 = 238 := by decide +kernel
#print axioms hexGraph_row_39
