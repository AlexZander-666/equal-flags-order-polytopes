import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_24 :
    FastTriples.advancedRow hexGraph 25 24 = 631 := by decide +kernel
#print axioms hexGraph_row_24

theorem hexGraph_row_25 :
    FastTriples.advancedRow hexGraph 25 25 = 598 := by decide +kernel
#print axioms hexGraph_row_25

theorem hexGraph_row_26 :
    FastTriples.advancedRow hexGraph 25 26 = 565 := by decide +kernel
#print axioms hexGraph_row_26

theorem hexGraph_row_27 :
    FastTriples.advancedRow hexGraph 25 27 = 532 := by decide +kernel
#print axioms hexGraph_row_27
