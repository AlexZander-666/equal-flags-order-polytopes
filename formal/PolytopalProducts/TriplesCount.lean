import PolytopalProducts.CanonicalTriples
import PolytopalProducts.TightMask

/-! Counting sorted triples once, using the actual geometric seed condition. -/

noncomputable section

namespace PolytopalProducts.Codim3

open scoped Classical
open PolytopalProducts.OrderFaces PolytopalProducts.Codim3.FastTriples

variable {n m : ℕ}

/-- The index set of triples in strictly increasing order that are canonical seeds. -/
def acceptedTriples (g : GraphData n m) (d : ℕ) : Finset (Fin m × (Fin m × Fin m)) :=
  Finset.univ.filter fun t ↦
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ ({t.1,t.2.1,t.2.2} : Finset (Fin m)) ∈ canonicalSeeds g d

private def tripleSet (t : Fin m × (Fin m × Fin m)) : Finset (Fin m) := {t.1,t.2.1,t.2.2}

private theorem pair_eq_of_tripleSet_eq {t u : Fin m × (Fin m × Fin m)}
    (ht₁ : t.1 < t.2.1) (ht₂ : t.2.1 < t.2.2)
    (hu₁ : u.1 < u.2.1) (hu₂ : u.2.1 < u.2.2)
    (h : tripleSet t = tripleSet u) : t = u := by
  have hs₁ : [t.1,t.2.1,t.2.2].SortedLT := by
    simp [List.sortedLT_iff_pairwise, ht₁, ht₂, ht₁.trans ht₂]
  have hs₂ : [u.1,u.2.1,u.2.2].SortedLT := by
    simp [List.sortedLT_iff_pairwise, hu₁, hu₂, hu₁.trans hu₂]
  have hl : [t.1,t.2.1,t.2.2] = [u.1,u.2.1,u.2.2] :=
    hs₁.eq_of_mem_iff hs₂ fun a ↦ by
      have he : a ∈ tripleSet t ↔ a ∈ tripleSet u := by rw [h]
      simpa only [tripleSet, List.mem_cons, List.not_mem_nil, or_false,
        Finset.mem_insert, Finset.mem_singleton] using he
  have he : t.1 = u.1 ∧ t.2.1 = u.2.1 ∧ t.2.2 = u.2.2 := by simpa using hl
  exact Prod.ext he.1 (Prod.ext he.2.1 he.2.2)

theorem card_canonicalSeeds_eq_card_acceptedTriples (g : GraphData n m) (d : ℕ) :
    (canonicalSeeds g d).card = (acceptedTriples g d).card := by
  have himage : (acceptedTriples g d).image tripleSet = canonicalSeeds g d := by
    ext s
    constructor
    · intro hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact (Finset.mem_filter.mp ht).2.2.2
    · intro hs
      have hcard : s.card = 3 :=
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1).2
      let l := s.sort
      have hlen : l.length = 3 := by simpa [l] using hcard
      have hsort : l.SortedLT := s.sortedLT_sort
      have hback : l.toFinset = s := s.sort_toFinset (· ≤ ·)
      have hexists : ∃ i j k, l = [i,j,k] := by
        rcases l with _ | ⟨i,l⟩ <;> simp at hlen
        rcases l with _ | ⟨j,l⟩ <;> simp at hlen
        rcases l with _ | ⟨k,l⟩ <;> simp at hlen
        exact ⟨i,j,k,by simp [hlen]⟩
      obtain ⟨i,j,k,hh⟩ := hexists
      have ho : i < j ∧ j < k := by
        rw [hh, List.sortedLT_iff_pairwise] at hsort
        have hh := List.pairwise_cons.mp hsort
        exact ⟨hh.1 j (by simp), (List.pairwise_cons.mp hh.2).1 k (by simp)⟩
      have htriple : tripleSet (i,j,k) = s := by
        rw [hh] at hback
        simpa [tripleSet] using hback
      exact Finset.mem_image.mpr ⟨(i,j,k),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho.1, ho.2, by
          change tripleSet (i,j,k) ∈ canonicalSeeds g d
          rwa [htriple]⟩, htriple⟩
  rw [← himage]
  apply Finset.card_image_of_injOn
  intro t ht u hu h
  have ht' := (Finset.mem_filter.mp ht).2
  have hu' := (Finset.mem_filter.mp hu).2
  exact pair_eq_of_tripleSet_eq ht'.1 ht'.2.1 hu'.1 hu'.2.1 h

theorem card_acceptedTriples_sum (g : GraphData n m) (d : ℕ) :
    (acceptedTriples g d).card =
      ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
        if i < j ∧ j < k ∧ ({i,j,k} : Finset (Fin m)) ∈ canonicalSeeds g d then 1 else 0 := by
  simp only [acceptedTriples, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]

/-- For increasing indices the accepted triple is exactly the recovered ordered prefix. -/
theorem sorted_triple_spec {V : Type*} [PartialOrder V] {g : GraphData n m}
    (model : GraphRealization V g) {d : ℕ} (hd : 0 < d)
    {i j k : Fin m} (hi : i < j) (hj : j < k) :
    ({i,j,k} : Finset (Fin m)) ∈ canonicalSeeds g d ↔
      let r := close g [k,j,i]
      arrow r g.high g.low = false ∧ (rowSet r).card = d+2 ∧ canonical g r = [i,j,k] := by
  let s : Finset (Fin m) := {i,j,k}
  let r := close g [k,j,i]
  have hEq : close g s.toList = r := by
    apply close_eq_of_same_seed model
    ext x
    simp [s, or_comm, or_left_comm]
  have hcard : s.card = 3 := by
    simp [s, hi.ne, hj.ne, (hi.trans hj).ne]
  have hcanon : (canonical g r).toFinset = s ↔ canonical g r = [i,j,k] := by
    constructor
    · intro h
      have hsort : (canonical g r).SortedLT :=
        List.sortedLT_iff_pairwise.mpr (tight_sorted g r).pairwise.take
      have hsort' : [i,j,k].SortedLT := by
        simp [List.sortedLT_iff_pairwise, hi, hj, hi.trans hj]
      apply hsort.eq_of_mem_iff hsort'
      intro x
      rw [← List.mem_toFinset, h]
      simp [s]
    · intro h
      rw [h]
      ext x
      simp [s]
  change s ∈ canonicalSeeds g d ↔ _ 
  rw [canonicalSeeds, Finset.mem_filter]
  change (s ∈ seeds g d ∧ (canonical g (close g s.toList)).toFinset = s) ↔ _
  simp only [seeds, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
    hcard, and_self, true_and, hEq, hcanon]
  constructor
  · rintro ⟨⟨hp,hr⟩,hc⟩
    refine ⟨hp, ?_, hc⟩
    change (rowSet r).card = d+2
    omega
  · rintro ⟨hp,hr,hc⟩
    refine ⟨⟨hp, ?_⟩, hc⟩
    change (rowSet r).card = d+2 at hr
    omega

/-- Parity of the ranks in the certified cube numbering. -/
def cubeColor (i : Fin 30) : Bool :=
  i.val == 1 || (10 ≤ i.val && i.val ≤ 21) || i.val == 28

/-- Parity of the ranks in the certified hexagonal-pyramid numbering. -/
def hexColor (i : Fin 30) : Bool :=
  i.val == 1 || (9 ≤ i.val && i.val ≤ 20) || i.val == 28

def cubeOrderedBipartite : OrderedBipartite cubeGraph where
  color := cubeColor
  oriented := by decide +kernel
  color_ne := by decide +kernel

def hexOrderedBipartite : OrderedBipartite hexGraph where
  color := hexColor
  oriented := by decide +kernel
  color_ne := by decide +kernel

end PolytopalProducts.Codim3
