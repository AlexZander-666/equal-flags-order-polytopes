import PolytopalProducts.TruncatedRows.C00
import PolytopalProducts.TruncatedRows.C04
import PolytopalProducts.TruncatedRows.C08
import PolytopalProducts.TruncatedRows.C12
import PolytopalProducts.TruncatedRows.C16
import PolytopalProducts.TruncatedRows.C20
import PolytopalProducts.TruncatedRows.C24
import PolytopalProducts.TruncatedRows.C28
import PolytopalProducts.TruncatedRows.C32
import PolytopalProducts.TruncatedRows.C36
import PolytopalProducts.TruncatedRows.C40
import PolytopalProducts.TruncatedRows.C44
import PolytopalProducts.TruncatedRows.C48
import PolytopalProducts.TruncatedRows.C52
import PolytopalProducts.TruncatedRows.C56
import PolytopalProducts.TruncatedRows.C60
namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def expectedRows : Vector Nat 64 := #v[1857, 1573, 1519, 1466, 1465, 1415, 1363, 1312, 1312, 1262, 1211, 1165, 1118, 1073, 1026, 983, 940, 898, 857, 817, 778, 739, 701, 667, 632, 597, 565, 532, 502, 472, 442, 413, 415, 387, 360, 334, 307, 282, 260, 237, 219, 199, 178, 160, 143, 127, 112, 97, 85, 72, 62, 53, 43, 35, 28, 21, 21, 15, 10, 6, 3, 1, 0, 0]
theorem exact_rows (i : Fin 64) : FastTriples.advancedRow graph 25 i = expectedRows[i.val] := by
  fin_cases i
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16
  · exact row_17
  · exact row_18
  · exact row_19
  · exact row_20
  · exact row_21
  · exact row_22
  · exact row_23
  · exact row_24
  · exact row_25
  · exact row_26
  · exact row_27
  · exact row_28
  · exact row_29
  · exact row_30
  · exact row_31
  · exact row_32
  · exact row_33
  · exact row_34
  · exact row_35
  · exact row_36
  · exact row_37
  · exact row_38
  · exact row_39
  · exact row_40
  · exact row_41
  · exact row_42
  · exact row_43
  · exact row_44
  · exact row_45
  · exact row_46
  · exact row_47
  · exact row_48
  · exact row_49
  · exact row_50
  · exact row_51
  · exact row_52
  · exact row_53
  · exact row_54
  · exact row_55
  · exact row_56
  · exact row_57
  · exact row_58
  · exact row_59
  · exact row_60
  · exact row_61
  · exact row_62
  · exact row_63
theorem numerical_sum : (∑ i : Fin 64, FastTriples.advancedRow graph 25 i) = 35944 := by
  calc
    _ = ∑ i : Fin 64, expectedRows[i.val] := Finset.sum_congr rfl (fun i _ ↦ exact_rows i)
    _ = _ := by decide +kernel
#print axioms numerical_sum
end PolytopalProducts.Truncated
