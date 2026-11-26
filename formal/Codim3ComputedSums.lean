import cubeGraph_00
import cubeGraph_04
import cubeGraph_08
import cubeGraph_12
import cubeGraph_16
import cubeGraph_20
import cubeGraph_24
import cubeGraph_28
import cubeGraph_32
import cubeGraph_36
import cubeGraph_40
import cubeGraph_44
import cubeGraph_48
import cubeGraph_52
import cubeGraph_56
import cubeGraph_60
import hexGraph_00
import hexGraph_04
import hexGraph_08
import hexGraph_12
import hexGraph_16
import hexGraph_20
import hexGraph_24
import hexGraph_28
import hexGraph_32
import hexGraph_36
import hexGraph_40
import hexGraph_44
import hexGraph_48
import hexGraph_52
import hexGraph_56
import hexGraph_60

open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def cubeExpected : Vector Nat 64 := #v[1857,1627,1571,1517,1463,1412,1360,1310,1260,1262,1212,1163,1116,1071,1025,981,939,896,855,814,776,738,702,665,630,595,563,531,499,470,441,412,384,385,357,332,307,283,259,237,217,196,177,159,144,126,111,97,83,72,63,51,43,34,27,21,15,15,10,6,3,1,0,0]

theorem cube_numerical_rows (i : Fin 64) :
    FastTriples.advancedRow cubeGraph 25 i = cubeExpected[i.val] := by
  fin_cases i
  · exact cubeGraph_row_0
  · exact cubeGraph_row_1
  · exact cubeGraph_row_2
  · exact cubeGraph_row_3
  · exact cubeGraph_row_4
  · exact cubeGraph_row_5
  · exact cubeGraph_row_6
  · exact cubeGraph_row_7
  · exact cubeGraph_row_8
  · exact cubeGraph_row_9
  · exact cubeGraph_row_10
  · exact cubeGraph_row_11
  · exact cubeGraph_row_12
  · exact cubeGraph_row_13
  · exact cubeGraph_row_14
  · exact cubeGraph_row_15
  · exact cubeGraph_row_16
  · exact cubeGraph_row_17
  · exact cubeGraph_row_18
  · exact cubeGraph_row_19
  · exact cubeGraph_row_20
  · exact cubeGraph_row_21
  · exact cubeGraph_row_22
  · exact cubeGraph_row_23
  · exact cubeGraph_row_24
  · exact cubeGraph_row_25
  · exact cubeGraph_row_26
  · exact cubeGraph_row_27
  · exact cubeGraph_row_28
  · exact cubeGraph_row_29
  · exact cubeGraph_row_30
  · exact cubeGraph_row_31
  · exact cubeGraph_row_32
  · exact cubeGraph_row_33
  · exact cubeGraph_row_34
  · exact cubeGraph_row_35
  · exact cubeGraph_row_36
  · exact cubeGraph_row_37
  · exact cubeGraph_row_38
  · exact cubeGraph_row_39
  · exact cubeGraph_row_40
  · exact cubeGraph_row_41
  · exact cubeGraph_row_42
  · exact cubeGraph_row_43
  · exact cubeGraph_row_44
  · exact cubeGraph_row_45
  · exact cubeGraph_row_46
  · exact cubeGraph_row_47
  · exact cubeGraph_row_48
  · exact cubeGraph_row_49
  · exact cubeGraph_row_50
  · exact cubeGraph_row_51
  · exact cubeGraph_row_52
  · exact cubeGraph_row_53
  · exact cubeGraph_row_54
  · exact cubeGraph_row_55
  · exact cubeGraph_row_56
  · exact cubeGraph_row_57
  · exact cubeGraph_row_58
  · exact cubeGraph_row_59
  · exact cubeGraph_row_60
  · exact cubeGraph_row_61
  · exact cubeGraph_row_62
  · exact cubeGraph_row_63

theorem cube_numerical_sum : (∑ i : Fin 64, FastTriples.advancedRow cubeGraph 25 i) = 35948 := by
  calc
    _ = ∑ i : Fin 64, cubeExpected[i.val] := Finset.sum_congr rfl (fun i _ ↦ cube_numerical_rows i)
    _ = _ := by decide +kernel

#print axioms cube_numerical_sum

def hexExpected : Vector Nat 64 := #v[1857,1627,1571,1517,1464,1412,1360,1165,1313,1262,1211,1165,1118,1071,1027,983,939,898,857,816,778,740,702,667,631,598,565,532,501,471,442,413,416,384,361,332,308,283,262,238,217,197,179,160,143,127,112,98,85,73,62,53,43,35,28,21,21,15,10,6,3,1,0,0]

theorem hex_numerical_rows (i : Fin 64) :
    FastTriples.advancedRow hexGraph 25 i = hexExpected[i.val] := by
  fin_cases i
  · exact hexGraph_row_0
  · exact hexGraph_row_1
  · exact hexGraph_row_2
  · exact hexGraph_row_3
  · exact hexGraph_row_4
  · exact hexGraph_row_5
  · exact hexGraph_row_6
  · exact hexGraph_row_7
  · exact hexGraph_row_8
  · exact hexGraph_row_9
  · exact hexGraph_row_10
  · exact hexGraph_row_11
  · exact hexGraph_row_12
  · exact hexGraph_row_13
  · exact hexGraph_row_14
  · exact hexGraph_row_15
  · exact hexGraph_row_16
  · exact hexGraph_row_17
  · exact hexGraph_row_18
  · exact hexGraph_row_19
  · exact hexGraph_row_20
  · exact hexGraph_row_21
  · exact hexGraph_row_22
  · exact hexGraph_row_23
  · exact hexGraph_row_24
  · exact hexGraph_row_25
  · exact hexGraph_row_26
  · exact hexGraph_row_27
  · exact hexGraph_row_28
  · exact hexGraph_row_29
  · exact hexGraph_row_30
  · exact hexGraph_row_31
  · exact hexGraph_row_32
  · exact hexGraph_row_33
  · exact hexGraph_row_34
  · exact hexGraph_row_35
  · exact hexGraph_row_36
  · exact hexGraph_row_37
  · exact hexGraph_row_38
  · exact hexGraph_row_39
  · exact hexGraph_row_40
  · exact hexGraph_row_41
  · exact hexGraph_row_42
  · exact hexGraph_row_43
  · exact hexGraph_row_44
  · exact hexGraph_row_45
  · exact hexGraph_row_46
  · exact hexGraph_row_47
  · exact hexGraph_row_48
  · exact hexGraph_row_49
  · exact hexGraph_row_50
  · exact hexGraph_row_51
  · exact hexGraph_row_52
  · exact hexGraph_row_53
  · exact hexGraph_row_54
  · exact hexGraph_row_55
  · exact hexGraph_row_56
  · exact hexGraph_row_57
  · exact hexGraph_row_58
  · exact hexGraph_row_59
  · exact hexGraph_row_60
  · exact hexGraph_row_61
  · exact hexGraph_row_62
  · exact hexGraph_row_63

theorem hex_numerical_sum : (∑ i : Fin 64, FastTriples.advancedRow hexGraph 25 i) = 35946 := by
  calc
    _ = ∑ i : Fin 64, hexExpected[i.val] := Finset.sum_congr rfl (fun i _ ↦ hex_numerical_rows i)
    _ = _ := by decide +kernel

#print axioms hex_numerical_sum
