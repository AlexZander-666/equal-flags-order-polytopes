import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_28 :
    FastTriples.advancedRow hexGraph 25 28 = 501 := by decide +kernel
#print axioms hexGraph_row_28

theorem hexGraph_row_29 :
    FastTriples.advancedRow hexGraph 25 29 = 471 := by decide +kernel
#print axioms hexGraph_row_29

theorem hexGraph_row_30 :
    FastTriples.advancedRow hexGraph 25 30 = 442 := by decide +kernel
#print axioms hexGraph_row_30

theorem hexGraph_row_31 :
    FastTriples.advancedRow hexGraph 25 31 = 413 := by decide +kernel
#print axioms hexGraph_row_31
