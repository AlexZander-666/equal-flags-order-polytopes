import PolytopalProducts.Codim3Data
import PolytopalProducts.FastTriples

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem hexGraph_row_44 :
    FastTriples.advancedRow hexGraph 25 44 = 143 := by decide +kernel
#print axioms hexGraph_row_44

theorem hexGraph_row_45 :
    FastTriples.advancedRow hexGraph 25 45 = 127 := by decide +kernel
#print axioms hexGraph_row_45

theorem hexGraph_row_46 :
    FastTriples.advancedRow hexGraph 25 46 = 112 := by decide +kernel
#print axioms hexGraph_row_46

theorem hexGraph_row_47 :
    FastTriples.advancedRow hexGraph 25 47 = 98 := by decide +kernel
#print axioms hexGraph_row_47
