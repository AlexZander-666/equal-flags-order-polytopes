import PolytopalProducts.FastTriplesSound

/-! The first three tight cover indices can be read by a binary prefix. -/

namespace PolytopalProducts.Codim3.FastTriples

open PolytopalProducts.OrderFaces

variable {n m : ℕ}

def tightWord (g : GraphData n m) (r : Vector Nat n) : ℕ :=
  mask (tight g r) (fun _ ↦ true) Fin.val

theorem tight_sorted (g : GraphData n m) (r : Vector Nat n) : (tight g r).SortedLT :=
  List.sortedLT_iff_pairwise.mpr ((List.sortedLT_finRange m).pairwise.filter _)

theorem tightWord_indices (g : GraphData n m) (r : Vector Nat n) :
    (tightWord g r).bitIndices = (tight g r).map Fin.val := by
  have hsort : ((tight g r).map Fin.val).SortedLT := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_map]
    exact (tight_sorted g r).pairwise
  apply Nat.bitIndices_sorted.eq_of_mem_iff hsort
  intro k
  rw [Nat.mem_bitIndices, tightWord, testBit_mask, List.mem_map]
  simp only [true_and]

private theorem bitIndices_mod (word bound : ℕ) :
    (word % 2^bound).bitIndices = word.bitIndices.filter (· < bound) := by
  apply Nat.bitIndices_sorted.eq_of_mem_iff
    (List.sortedLT_iff_pairwise.mpr (Nat.bitIndices_sorted.pairwise.filter _))
  intro i
  simp only [Nat.mem_bitIndices, List.mem_filter, Nat.testBit_mod_two_pow, Bool.and_eq_true,
    decide_eq_true_eq, and_comm]

private theorem filter_prefix {l : List Nat} (hl : l.SortedLT) (c : ℕ) :
    l.filter (· ≤ c) <+: l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hc : x ≤ c
    · rw [List.filter_cons_of_pos (of_decide_eq_true (by simp [hc]))]
      obtain ⟨ys, hys⟩ := ih (List.sortedLT_iff_pairwise.mpr (List.pairwise_cons.mp hl.pairwise).2)
      exact ⟨ys, by simp [hys]⟩
    · have hf : xs.filter (· ≤ c) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        have hxy := (List.pairwise_cons.mp hl.pairwise).1 y hy
        simpa using (show ¬y ≤ c by omega)
      rw [List.filter_cons_of_neg (by simpa using hc), hf]
      exact List.nil_prefix

private theorem take_three_eq_filter {l : List Nat} (hl : l.SortedLT)
    {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    l.take 3 = [a,b,c] ↔ l.filter (· ≤ c) = [a,b,c] := by
  constructor
  · intro h
    have he : l = [a,b,c] ++ l.drop 3 := by
      rw [← h, List.take_append_drop]
    have hs : ([a,b,c] ++ l.drop 3).Pairwise (· < ·) := he ▸ hl.pairwise
    have hf : (l.drop 3).filter (· ≤ c) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro y hy
      have hcy := (List.pairwise_append.mp hs).2.2 c (by simp) y hy
      have hn : ¬y ≤ c := not_le_of_gt hcy
      simpa using hn
    conv_lhs => rw [he]
    rw [List.filter_append, hf]
    simp [hab.le.trans hbc.le, hbc.le]
  · intro h
    obtain ⟨rest, hr⟩ := filter_prefix hl c
    rw [h] at hr
    rw [← hr]
    simp

theorem tightWord_prefix (g : GraphData n m) (r : Vector Nat n)
    {i j k : Fin m} (hij : i < j) (hjk : j < k) :
    tightWord g r % 2^(k.val+1) = 2^i.val+2^j.val+2^k.val ↔
      canonical g r = [i,j,k] := by
  have horder : [i.val,j.val,k.val].SortedLT := by
    simp [List.sortedLT_iff_pairwise, hij, hjk, hij.trans hjk]
  have he : (2^i.val+2^j.val+2^k.val).bitIndices = [i.val,j.val,k.val] := by
    have h := Nat.bitIndices_sum_map_two_pow horder
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc] using h
  have hmod :
      tightWord g r % 2^(k.val+1) = 2^i.val+2^j.val+2^k.val ↔
        ((tightWord g r).bitIndices.filter (· ≤ k.val)) = [i.val,j.val,k.val] := by
    simp only [← Nat.lt_succ_iff]
    rw [← he, ← bitIndices_mod]
    exact ⟨congrArg Nat.bitIndices, fun hw ↦ by
        have hv := congrArg (fun v : List Nat ↦ (v.map fun i ↦ 2^i).sum) hw
        simpa only [Nat.sum_map_two_pow_bitIndices] using hv⟩
  rw [hmod, ← take_three_eq_filter Nat.bitIndices_sorted hij hjk, tightWord_indices, ← List.map_take]
  change (canonical g r).map Fin.val = [i,j,k].map Fin.val ↔ _
  exact List.map_inj_right (fun _ _ h ↦ Fin.ext h)

/-- The tight-word update consists of the old tight word and the covers within
the interval being contracted. -/
theorem tightWord_add {V : Type*} [PartialOrder V] {g : GraphData n m}
    (model : GraphRealization V g) (s : List (Fin m)) (e : Fin n × Fin n) :
    let r := close g s
    let c := commonMask (fun v ↦ r[v.val]) (predecessors r) e
    tightWord g (add r e) = tightWord g r |||
      (collectSide c.bitIndices (bySource g) &&& collectSide c.bitIndices (byTarget g)) := by
  let r := close g s
  let c := commonMask (fun v ↦ r[v.val]) (predecessors r) e
  let arcs := collectSide c.bitIndices (bySource g) &&& collectSide c.bitIndices (byTarget g)
  change tightWord g (add r e) = tightWord g r ||| arcs
  have hmask (r : Vector Nat n) (x : Fin m) : (tightWord g r).testBit x.val = true ↔ x ∈ tight g r := by
    rw [← Nat.mem_bitIndices, tightWord_indices, List.mem_map]
    constructor
    · rintro ⟨i, hi, he⟩
      rwa [Fin.ext he] at hi
    · exact fun h ↦ ⟨x,h,rfl⟩
  have off (xs : List (Fin m)) (p : Fin m → Bool) {k : ℕ} (hk : m ≤ k) :
      (mask xs p Fin.val).testBit k = false := by
    apply Bool.eq_false_iff.mpr
    simp only [ne_eq, testBit_mask]
    rintro ⟨a, -, -, ha⟩
    exact (not_lt_of_ge hk) (ha ▸ a.isLt)
  have offS (v k : ℕ) (hk : m ≤ k) : (bySource g v).testBit k = false := by
    unfold bySource
    exact off _ _ hk
  have offA (l : List ℕ) (k : ℕ) (hk : m ≤ k) :
      (collectSide l (bySource g)).testBit k = false := by
    induction l with
    | nil => simp [collectSide]
    | cons x xs ih =>
      change (bySource g x ||| collectSide xs (bySource g)).testBit k = false
      rw [Nat.testBit_or, offS _ _ hk, ih]
      rfl
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < m
  · let x : Fin m := ⟨k,hk⟩
    apply Bool.eq_iff_iff.mpr
    change (tightWord g (add r e)).testBit x.val = true ↔ _
    rw [hmask, Nat.testBit_or, Bool.or_eq_true]
    change x ∈ tight g (add r e) ↔ (tightWord g r).testBit x.val = true ∨
      (collectSide c.bitIndices (bySource g) &&& collectSide c.bitIndices (byTarget g)).testBit x.val = true
    rw [hmask, intervalArcMask_testBit, commonMask_testBit, commonMask_testBit]
    exact tight_add_iff model s e x
  · have h := le_of_not_gt hk
    have hword (p : Vector Nat n) : (tightWord g p).testBit k = false := by
      unfold tightWord
      exact off _ _ h
    rw [hword, Nat.testBit_or, hword]
    change false = (false ||
      (collectSide c.bitIndices (bySource g) &&& collectSide c.bitIndices (byTarget g)).testBit k)
    rw [Nat.testBit_and, offA _ _ h]
    rfl

theorem pins_add {V : Type*} [PartialOrder V] {g : GraphData n m}
    (model : GraphRealization V g) (s : List (Fin m)) (e : Fin n × Fin n) :
    let r := close g s
    let c := commonMask (fun v ↦ r[v.val]) (predecessors r) e
    arrow (add r e) g.high g.low =
      (arrow r g.high g.low || (c.testBit g.high.val && c.testBit g.low.val)) := by
  let r := close g s
  let c := commonMask (fun v ↦ r[v.val]) (predecessors r) e
  change arrow (add r e) g.high g.low =
    (arrow r g.high g.low || (c.testBit g.high.val && c.testBit g.low.val))
  let R := matrixRelation r
  have hlow : R g.low g.high := (close_matches model s _ _).mpr
    (reach_of_le _ (by rw [model.low]; exact bot_le))
  have hAnt : addArrow R e.2 e.1 g.low g.high := Or.inl hlow
  have he := equivalentIn_addArrow_iff (matrixRelation_trans model s)
    (a := e.1) (b := e.2) (x := g.high) (y := g.low)
  change (addArrow R e.2 e.1 g.high g.low ∧ addArrow R e.2 e.1 g.low g.high) ↔
    (R g.high g.low ∧ R g.low g.high) ∨ _ at he
  simp only [hAnt, hlow, and_true] at he
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true, Bool.and_eq_true]
  change matrixRelation (add r e) g.high g.low ↔ R g.high g.low ∨ _
  rw [matrixRelation_add, commonMask_testBit, commonMask_testBit, mem_intervalIndices, mem_intervalIndices]
  exact he

end PolytopalProducts.Codim3.FastTriples
