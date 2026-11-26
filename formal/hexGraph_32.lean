import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_32 :
    FastTriples.advancedRow hexGraph 25 32 = 416 := by decide +kernel
#print axioms hexGraph_row_32

theorem hexGraph_row_33 :
    FastTriples.advancedRow hexGraph 25 33 = 384 := by decide +kernel
#print axioms hexGraph_row_33

theorem hexGraph_row_34 :
    FastTriples.advancedRow hexGraph 25 34 = 361 := by decide +kernel
#print axioms hexGraph_row_34

theorem hexGraph_row_35 :
    FastTriples.advancedRow hexGraph 25 35 = 332 := by decide +kernel
#print axioms hexGraph_row_35
