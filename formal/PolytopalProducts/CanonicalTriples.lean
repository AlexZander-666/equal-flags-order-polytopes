import PolytopalProducts.Codim3Readout
import PolytopalProducts.FastTriplesSound
import PolytopalProducts.ThreeDistinctEdges

/-! Every accepted face has exactly one canonical three-cover seed for bipartite covers. -/

noncomputable section

namespace PolytopalProducts.Codim3

open PolytopalProducts.OrderFaces PolytopalProducts.Codim3.FastTriples
open scoped Classical

variable {n m : ℕ} {V : Type*} [PartialOrder V] [Fintype V] {g : GraphData n m}

/-- The index order respects covers, with the two colors certifying that no
triangle of augmented covers can occur. -/
structure OrderedBipartite (g : GraphData n m) where
  color : Fin n → Bool
  oriented : ∀ e : Fin m, g.arcs[e.val].1 < g.arcs[e.val].2
  color_ne : ∀ e : Fin m, color g.arcs[e.val].1 ≠ color g.arcs[e.val].2

omit [Fintype V] in
private theorem card_rows_add_discarded (model : GraphRealization V g) (s : List (Fin m)) :
    let key (i : Fin n) := (close g s)[i.val]
    (rowSet (close g s)).card + (discarded key).card = n := by
  let k (i : Fin n) := (close g s)[i.val]
  let L := classLeaders (matrixRelation (close g s))
  have hL : L.card = (rowSet (close g s)).card :=
    by
      rw [← representatives_length model s]
      exact (leaders_length (close g s)).symm
  have he : discarded k = Finset.univ \ L := by
    ext v
    simp only [discarded, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, L, mem_classLeaders, equivalentIn, matrixRelation]
    push Not
    have hu (u : Fin n) : k v = k u ↔
        arrow (close g s) v u = true ∧ arrow (close g s) u v = true :=
      (same_row_iff model s v u).trans
        (and_congr (close_matches model s v u) (close_matches model s u v)).symm
    simp only [hu]
  change (rowSet (close g s)).card + (discarded k).card = n
  rw [he, ← hL, Finset.card_sdiff_of_subset (Finset.subset_univ L), Finset.card_univ, Fintype.card_fin]
  have hl := Finset.card_le_card (Finset.subset_univ L)
  simp only [Finset.card_univ, Fintype.card_fin] at hl
  omega

omit [Fintype V] in
private theorem rows_of_three_le (model : GraphRealization V g) (coloring : OrderedBipartite g)
    {s : Finset (Fin m)} (hcard : s.card = 3) :
    (rowSet (close g s.toList)).card ≤ n - 3 := by
  obtain ⟨i, j, k, hij, hik, hjk, hs⟩ := Finset.card_eq_three.mp hcard
  let r := close g s.toList
  let key (v : Fin n) := r[v.val]
  have ht (a : Fin m) (ha : a ∈ s) :
      key g.arcs[a.val].1 = key g.arcs[a.val].2 := by
    apply (same_row_iff model s.toList _ _).mpr
    have he : (model.arc a).val.1 ≤ (model.arc a).val.2 := (model.arc a).property.le
    have hmem : model.arc a ∈ actualSeed model s.toList := by
      exact Finset.mem_map.mpr ⟨a, by simpa using ha, rfl⟩
    obtain hrev := reach_reverse (actualSeed model s.toList) hmem
    rw [model.endpoints a] at he hrev
    exact ⟨reach_of_le _ he, hrev⟩
  have hinj (a b : Fin m) (he : g.arcs[a.val] = g.arcs[b.val]) : a = b := by
    apply model.arc.injective
    apply Subtype.ext
    rw [model.endpoints a, model.endpoints b, he]
  have hh := discarded_at_least_three key coloring.color g.arcs[i.val] g.arcs[j.val] g.arcs[k.val]
    (fun h ↦ hij (hinj _ _ h)) (fun h ↦ hik (hinj _ _ h)) (fun h ↦ hjk (hinj _ _ h))
    (coloring.oriented i) (coloring.oriented j) (coloring.oriented k)
    (ht i (by simp [hs])) (ht j (by simp [hs])) (ht k (by simp [hs]))
    (coloring.color_ne i) (coloring.color_ne j) (coloring.color_ne k)
  have hsum := card_rows_add_discarded model s.toList
  change 3 ≤ (discarded (fun v : Fin n ↦ (close g s.toList)[v.val])).card at hh
  omega

private theorem seededFace_eq_of_subset_of_finrank_le {s t : Finset (Arc V)}
    (hn : (seededFace s).Nonempty) (he : seededFace s ⊆ seededFace t)
    (hr : Module.finrank ℝ (vectorSpan ℝ (seededFace t)) ≤
      Module.finrank ℝ (vectorSpan ℝ (seededFace s))) :
    seededFace s = seededFace t := by
  have hv := Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ he) hr
  refine Set.Subset.antisymm he ?_
  intro y hy
  obtain ⟨x, hx⟩ := hn
  have hdiff : y - x ∈ vectorSpan ℝ (seededFace t) :=
    vsub_mem_vectorSpan ℝ hy (he hx)
  rw [← hv, vectorSpan_seededFace s ⟨x, hx⟩] at hdiff
  refine ⟨hy.1, ?_⟩
  intro e hmem
  have hcoords := hdiff e.val.1 e.val.2
    ⟨reach_of_le s e.property.le, reach_reverse s hmem⟩
  change coord V e.val.1 (y - x) = coord V e.val.2 (y - x) at hcoords
  rw [map_sub, map_sub] at hcoords
  have hx' := (form_eq_iff V x e).mp (hx.2 e hmem)
  apply (form_eq_iff V y e).mpr
  unfold value at *
  linarith

/-- Any three distinct tight covers generate a face of codimension three
if the starting face already has that codimension. -/
theorem accepted_three_of_tight (model : GraphRealization V g) (coloring : OrderedBipartite g)
    {d : ℕ} (hd : d + 5 = n) {s t : Finset (Fin m)}
    (hs : s ∈ seeds g d) (ht : t.card = 3) (htight : t ⊆ signature g s) :
    t ∈ seeds g d ∧ signature g t = signature g s := by
  have hstart := (Finset.mem_filter.mp hs).2
  have hnon := (nonempty_iff_accepted_pins model s.toList).mpr hstart.1
  have hrel : actualSeed model t.toList ⊆ tightArcs (actualSeed model s.toList) := by
    rw [← signature_matches model s]
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_map.mpr ⟨a, htight (by simpa using ha), rfl⟩
  have hsubset : seededFace (actualSeed model s.toList) ⊆ seededFace (actualSeed model t.toList) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro e he
    have hmem := hrel he
    rw [← active_seededFace _ hnon, Halfspaces.mem_active] at hmem
    exact hmem x hx
  have htNon := hnon.mono hsubset
  have hUpper := rows_of_three_le model coloring ht
  have hfin1 := finrank_eq_rows model s.toList hnon
  have hfin2 := finrank_eq_rows model t.toList htNon
  have hle : Module.finrank ℝ (vectorSpan ℝ (seededFace (actualSeed model t.toList))) ≤
      Module.finrank ℝ (vectorSpan ℝ (seededFace (actualSeed model s.toList))) := by
    rw [hfin1, hfin2, hstart.2]
    omega
  have he := seededFace_eq_of_subset_of_finrank_le hnon hsubset hle
  have hr : (rowSet (close g t.toList)).card - 2 = d := by
    rw [← hfin2, ← he, hfin1]
    exact hstart.2
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ht⟩,
    (nonempty_iff_accepted_pins model t.toList).mp htNon, hr⟩, ?_⟩
  apply Finset.map_injective model.arc.toEmbedding
  rw [signature_matches, signature_matches]
  exact (seededFace_eq_iff_tightArcs_eq htNon hnon).mp he.symm

def canonicalSelection (g : GraphData n m) (s : Finset (Fin m)) : Finset (Fin m) :=
  (canonical g (close g s.toList)).toFinset

def canonicalSeeds (g : GraphData n m) (d : ℕ) : Finset (Finset (Fin m)) :=
  (seeds g d).filter fun s ↦ canonicalSelection g s = s

theorem mem_tight_iff_mem_signature (s : Finset (Fin m)) (i : Fin m) :
    i ∈ tight g (close g s.toList) ↔ i ∈ signature g s := by
  simp [tight, signature]

omit [Fintype V] in
theorem seed_subset_signature (model : GraphRealization V g) (s : Finset (Fin m)) :
    s ⊆ signature g s := by
  intro i hi
  have hm : model.arc i ∈ actualSeed model s.toList :=
    Finset.mem_map.mpr ⟨i, by simpa using hi, rfl⟩
  obtain hr := reach_reverse (actualSeed model s.toList) hm
  rw [model.endpoints i] at hr
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (close_matches model _ _ _).mpr hr⟩

theorem canonicalSelection_subset (s : Finset (Fin m)) :
    canonicalSelection g s ⊆ signature g s := by
  intro i hi
  apply (mem_tight_iff_mem_signature s i).mp
  exact List.mem_of_mem_take (List.mem_toFinset.mp hi)

omit [Fintype V] in
theorem card_canonicalSelection (model : GraphRealization V g) (s : Finset (Fin m))
    (hs : s.card = 3) : (canonicalSelection g s).card = 3 := by
  have hlen := Finset.card_le_card (seed_subset_signature model s)
  have htight : (tight g (close g s.toList)).toFinset = signature g s := by
    ext i
    exact List.mem_toFinset.trans (mem_tight_iff_mem_signature s i)
  rw [hs, ← htight, List.toFinset_card_of_nodup] at hlen
  · have hn := (List.nodup_finRange m).filter
      (fun e ↦ arrow (close g s.toList) g.arcs[e.val].2 g.arcs[e.val].1)
    change ((tight g (close g s.toList)).take 3).toFinset.card = 3
    have hnTake : ((tight g (close g s.toList)).take 3).Nodup := hn.take
    rw [List.toFinset_card_of_nodup hnTake, List.length_take, min_eq_left hlen]
  · exact (List.nodup_finRange m).filter _

theorem canonicalSelection_congr {s t : Finset (Fin m)} (h : signature g s = signature g t) :
    canonicalSelection g s = canonicalSelection g t := by
  unfold canonicalSelection canonical
  congr 2
  unfold tight
  apply List.filter_congr
  intro e _
  apply Bool.eq_iff_iff.mpr
  have hh : e ∈ signature g s ↔ e ∈ signature g t := by rw [h]
  simpa only [signature, Finset.mem_filter, Finset.mem_univ, true_and] using hh

theorem card_signatures_eq_canonicalSeeds (model : GraphRealization V g)
    (coloring : OrderedBipartite g) {d : ℕ} (hd : d+5=n) :
    (signatures g d).card = (canonicalSeeds g d).card := by
  classical
  have himage : (canonicalSeeds g d).image (signature g) = signatures g d := by
    ext x
    constructor
    · rintro hx
      obtain ⟨s, hs, hsx⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨s, (Finset.mem_filter.mp hs).1, hsx⟩
    · rintro hx
      obtain ⟨s, hs, hsx⟩ := Finset.mem_image.mp hx
      let c := canonicalSelection g s
      have hsCard : s.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2
      obtain ⟨hc, hcSig⟩ :=
        accepted_three_of_tight model coloring hd hs (card_canonicalSelection model s hsCard)
          (canonicalSelection_subset (g := g) s)
      refine Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, ?_⟩, hcSig.trans hsx⟩
      exact canonicalSelection_congr hcSig
  rw [← himage]
  apply Finset.card_image_of_injOn
  intro s hs t ht h
  exact ((Finset.mem_filter.mp hs).2).symm.trans
    ((canonicalSelection_congr h).trans (Finset.mem_filter.mp ht).2)

end PolytopalProducts.Codim3
