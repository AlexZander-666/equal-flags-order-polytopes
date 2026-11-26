import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_16 :
    FastTriples.advancedRow hexGraph 25 16 = 939 := by decide +kernel
#print axioms hexGraph_row_16

theorem hexGraph_row_17 :
    FastTriples.advancedRow hexGraph 25 17 = 898 := by decide +kernel
#print axioms hexGraph_row_17

theorem hexGraph_row_18 :
    FastTriples.advancedRow hexGraph 25 18 = 857 := by decide +kernel
#print axioms hexGraph_row_18

theorem hexGraph_row_19 :
    FastTriples.advancedRow hexGraph 25 19 = 816 := by decide +kernel
#print axioms hexGraph_row_19
