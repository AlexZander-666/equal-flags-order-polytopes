import PolytopalProducts.TruncatedData

namespace PolytopalProducts.Truncated
open Finset

def coord (i : Fin 7) := coordinates[i.val]
def listed (j : Fin 28) (i : Fin 7) : Bool := masks[j.val].testBit i.val
def contains (m : Fin 128) (i : Fin 7) : Bool := m.val.testBit i.val
def certWeight (w : Vector ℤ 7) (i : Fin 7) := w[i.val]

def Obstruction (m : Fin 128) (w : Vector ℤ 7) : Prop :=
  (∑ i, certWeight w i) = 0 ∧
  (∑ i, certWeight w i * (coord i).1) = 0 ∧
  (∑ i, certWeight w i * (coord i).2.1) = 0 ∧
  (∑ i, certWeight w i * (coord i).2.2) = 0 ∧
  (∀ i, contains m i = false → 0 ≤ certWeight w i) ∧
  ∃ i, contains m i = false ∧ 0 < certWeight w i

instance (m : Fin 128) (w : Vector ℤ 7) : Decidable (Obstruction m w) := by
  unfold Obstruction; infer_instance

def Valid (m : Fin 128) : Decision → Prop
  | .face j => ∀ i, contains m i = listed j i
  | .excluded w => Obstruction m w

instance (m : Fin 128) (d : Decision) : Decidable (Valid m d) := by
  cases d <;> unfold Valid <;> infer_instance

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 32768 in
theorem decisions_valid : ∀ m : Fin 128, Valid m decisions[m.val] := by decide +kernel

def encode (f : Fin 7 → Bool) : Fin 128 :=
  Fin.ofNat 128 (∑ i : Fin 7, if f i then 2^i.val else 0)

set_option maxHeartbeats 12000000 in
theorem encode_exact : ∀ (f : Fin 7 → Bool) (i : Fin 7), contains (encode f) i = f i := by
  decide +kernel

def integerScore (u : ℤ×ℤ×ℤ×ℤ) (i : Fin 7) : ℤ :=
  u.1*(coord i).1 + u.2.1*(coord i).2.1 + u.2.2.1*(coord i).2.2

set_option maxHeartbeats 4000000 in
theorem exposing_valid : ∀ (j : Fin 28) (i : Fin 7),
    if listed j i then integerScore exposing[j.val] i = exposing[j.val].2.2.2
    else integerScore exposing[j.val] i < exposing[j.val].2.2.2 := by decide +kernel

theorem faces_distinct : ∀ j k : Fin 28, (∀ i, listed j i = listed k i) → j=k := by
  decide +kernel

theorem singletons_listed : ∀ i : Fin 7, ∃ j : Fin 28, ∀ t : Fin 7, listed j t = decide (t=i) := by
  decide +kernel

theorem empty_code : ∀ i : Fin 7, listed 0 i = false := by decide +kernel

noncomputable section

def score (a b c : ℝ) (i : Fin 7) : ℝ :=
  a*(coord i).1 + b*(coord i).2.1 + c*(coord i).2.2

theorem deficient_impossible {m : Fin 128} {w : Vector ℤ 7} (ob : Obstruction m w)
    {a b c h : ℝ} (active : ∀ i, if contains m i then score a b c i=h else score a b c i<h) :
    False := by
  obtain ⟨tot,x,y,z,nonneg,⟨j,inactive,pos⟩⟩ := ob
  let v (i : Fin 7) := (certWeight w i : ℝ)
  have zero : ∑ i, v i * (h-score a b c i)=0 := by
    have ht : ∑ i, v i = 0 := by dsimp only [v]; exact_mod_cast tot
    have hx : ∑ i, v i*((coord i).1:ℝ) = 0 := by dsimp only [v]; exact_mod_cast x
    have hy : ∑ i, v i*((coord i).2.1:ℝ) = 0 := by dsimp only [v]; exact_mod_cast y
    have hz : ∑ i, v i*((coord i).2.2:ℝ) = 0 := by dsimp only [v]; exact_mod_cast z
    calc
      _ = ∑ i, (v i*h - (v i*(coord i).1*a + v i*(coord i).2.1*b + v i*(coord i).2.2*c)) := by
        apply sum_congr rfl; intro i _; unfold score; ring
      _ = 0 := by rw [sum_sub_distrib,sum_add_distrib,sum_add_distrib,
                        ← sum_mul,← sum_mul,← sum_mul,← sum_mul,ht,hx,hy,hz]; ring
  have positive : 0 < ∑ i, v i*(h-score a b c i) := by
    apply sum_pos'
    · intro i _
      cases hbit : contains m i with
      | true => have eq := active i; simp only [hbit,ite_true] at eq; simp [eq]
      | false =>
        have lt := active i
        simp [hbit] at lt
        exact mul_nonneg (by dsimp only [v]; exact_mod_cast nonneg i hbit) (sub_nonneg.mpr lt.le)
    · have lt := active j
      simp [inactive] at lt
      exact ⟨j,mem_univ _,mul_pos (by dsimp only [v]; exact_mod_cast pos) (sub_pos.mpr lt)⟩
  linarith

theorem classified {a b c h : ℝ} (f : Fin 7 → Bool)
    (active : ∀ i, if f i then score a b c i=h else score a b c i<h) :
    ∃ j : Fin 28, ∀ i, f i = listed j i := by
  let m := encode f
  have bits (i : Fin 7) : contains m i = f i := encode_exact f i
  have valid := decisions_valid m
  cases d : decisions[m.val] with
  | face j =>
    rw [d] at valid
    exact ⟨j,fun i ↦ (bits i).symm.trans (valid i)⟩
  | excluded w =>
    rw [d] at valid
    exact (deficient_impossible valid (fun i ↦ by rw [bits]; exact active i)).elim

#print axioms classified
#print axioms exposing_valid
end
end PolytopalProducts.Truncated
