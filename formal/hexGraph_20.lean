import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_20 :
    FastTriples.advancedRow hexGraph 25 20 = 778 := by decide +kernel
#print axioms hexGraph_row_20

theorem hexGraph_row_21 :
    FastTriples.advancedRow hexGraph 25 21 = 740 := by decide +kernel
#print axioms hexGraph_row_21

theorem hexGraph_row_22 :
    FastTriples.advancedRow hexGraph 25 22 = 702 := by decide +kernel
#print axioms hexGraph_row_22

theorem hexGraph_row_23 :
    FastTriples.advancedRow hexGraph 25 23 = 667 := by decide +kernel
#print axioms hexGraph_row_23
