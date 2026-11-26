import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_40 :
    FastTriples.advancedRow hexGraph 25 40 = 217 := by decide +kernel
#print axioms hexGraph_row_40

theorem hexGraph_row_41 :
    FastTriples.advancedRow hexGraph 25 41 = 197 := by decide +kernel
#print axioms hexGraph_row_41

theorem hexGraph_row_42 :
    FastTriples.advancedRow hexGraph 25 42 = 179 := by decide +kernel
#print axioms hexGraph_row_42

theorem hexGraph_row_43 :
    FastTriples.advancedRow hexGraph 25 43 = 160 := by decide +kernel
#print axioms hexGraph_row_43
