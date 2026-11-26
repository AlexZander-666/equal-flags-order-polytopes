import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_44 : FastTriples.advancedRow graph 25 44 = 143 := by decide +kernel
#print axioms row_44

theorem row_45 : FastTriples.advancedRow graph 25 45 = 127 := by decide +kernel
#print axioms row_45

theorem row_46 : FastTriples.advancedRow graph 25 46 = 112 := by decide +kernel
#print axioms row_46

theorem row_47 : FastTriples.advancedRow graph 25 47 = 97 := by decide +kernel
#print axioms row_47

end PolytopalProducts.Truncated
