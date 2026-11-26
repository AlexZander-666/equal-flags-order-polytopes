import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_40 : FastTriples.advancedRow graph 25 40 = 219 := by decide +kernel
#print axioms row_40

theorem row_41 : FastTriples.advancedRow graph 25 41 = 199 := by decide +kernel
#print axioms row_41

theorem row_42 : FastTriples.advancedRow graph 25 42 = 178 := by decide +kernel
#print axioms row_42

theorem row_43 : FastTriples.advancedRow graph 25 43 = 160 := by decide +kernel
#print axioms row_43

end PolytopalProducts.Truncated
