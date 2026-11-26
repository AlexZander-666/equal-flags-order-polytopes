import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_48 :
    FastTriples.advancedRow hexGraph 25 48 = 85 := by decide +kernel
#print axioms hexGraph_row_48

theorem hexGraph_row_49 :
    FastTriples.advancedRow hexGraph 25 49 = 73 := by decide +kernel
#print axioms hexGraph_row_49

theorem hexGraph_row_50 :
    FastTriples.advancedRow hexGraph 25 50 = 62 := by decide +kernel
#print axioms hexGraph_row_50

theorem hexGraph_row_51 :
    FastTriples.advancedRow hexGraph 25 51 = 53 := by decide +kernel
#print axioms hexGraph_row_51
