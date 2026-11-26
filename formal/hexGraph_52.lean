import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_52 :
    FastTriples.advancedRow hexGraph 25 52 = 43 := by decide +kernel
#print axioms hexGraph_row_52

theorem hexGraph_row_53 :
    FastTriples.advancedRow hexGraph 25 53 = 35 := by decide +kernel
#print axioms hexGraph_row_53

theorem hexGraph_row_54 :
    FastTriples.advancedRow hexGraph 25 54 = 28 := by decide +kernel
#print axioms hexGraph_row_54

theorem hexGraph_row_55 :
    FastTriples.advancedRow hexGraph 25 55 = 21 := by decide +kernel
#print axioms hexGraph_row_55
