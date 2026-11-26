import PolytopalProducts.IndexedClosures
import PolytopalProducts.CoefficientTransport
import PolytopalProducts.CubeGeometry

/-! The exact finite signature count for a genuine geometric face coefficient. -/

noncomputable section

namespace PolytopalProducts.Codim3

open PolytopalProducts.OrderFaces
open scoped Classical

variable {n m : ℕ} {V : Type*} [PartialOrder V] [Fintype V] {g : GraphData n m}

/-- Three independent equalities are enough to generate every codimension-three face.
The seed acceptance test checks that the pins remain distinct and exactly the desired
number of free equality classes survives. -/
def seeds (g : GraphData n m) (d : ℕ) : Finset (Finset (Fin m)) :=
  ((Finset.univ : Finset (Fin m)).powersetCard 3).filter fun s ↦
    arrow (close g s.toList) g.high g.low = false ∧
    (rowSet (close g s.toList)).card - 2 = d

/-- Signature of every equality forced among the defining Hasse inequalities. -/
def signature (g : GraphData n m) (s : Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun e ↦ arrow (close g s.toList) g.arcs[e.val].2 g.arcs[e.val].1 = true

/-- Each duplicate signature in the image represents the same actual face. -/
def signatures (g : GraphData n m) (d : ℕ) : Finset (Finset (Fin m)) :=
  (seeds g d).image (signature g)

theorem signature_matches (model : GraphRealization V g) (s : Finset (Fin m)) :
    (signature g s).map model.arc.toEmbedding = tightArcs (actualSeed model s.toList) := by
  ext e
  let i := model.arc.symm e
  have hi : model.arc i = e := model.arc.apply_symm_apply e
  have hep : (model.point g.arcs[i.val].1, model.point g.arcs[i.val].2) = e.val :=
    (model.endpoints i).symm.trans (congrArg Subtype.val hi)
  constructor
  · intro he
    obtain ⟨j, hj, hej⟩ := Finset.mem_map.mp he
    have hji : j = i := model.arc.injective (hej.trans hi.symm)
    subst j
    have ht := (Finset.mem_filter.mp hj).2
    have hc := (close_matches model s.toList g.arcs[i.val].2 g.arcs[i.val].1).mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [← hep] using hc⟩
  · intro he
    have hc := (Finset.mem_filter.mp he).2
    refine Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
    exact (close_matches model s.toList g.arcs[i.val].2 g.arcs[i.val].1).mpr
      (by simpa only [← hep] using (show reach _ _ _ from
        (show reach (actualSeed model s.toList) (e.val).2 (e.val).1 from hc)))

private def faceOfSeed (model : GraphRealization V g) {d : ℕ} (s : seeds g d) :
    FacesOfDimension V d := by
  have hs := (Finset.mem_filter.mp s.property).2
  have hn := (nonempty_iff_accepted_pins model s.val.toList).mpr hs.1
  refine ⟨seededFace (actualSeed model s.val.toList), ?_, hn, ?_⟩
  · rw [← body_eq_orderPolytope V]
    exact Halfspaces.face_isExposed _ _ _
  · exact (finrank_eq_rows model s.val.toList hn).trans hs.2

private theorem faceOfSeed_eq_iff (model : GraphRealization V g) {d : ℕ} (s t : seeds g d) :
    faceOfSeed model s = faceOfSeed model t ↔ signature g s.val = signature g t.val := by
  have h :=
    seededFace_eq_iff_tightArcs_eq (faceOfSeed model s).property.2.1
      (faceOfSeed model t).property.2.1
  rw [← signature_matches model s.val, ← signature_matches model t.val] at h
  change ((faceOfSeed model s).val = (faceOfSeed model t).val ↔ _) at h
  exact ⟨fun e ↦ Finset.map_injective _ (h.mp (congrArg Subtype.val e)),
    fun e ↦ Subtype.ext (h.mpr (congrArg (Finset.map model.arc.toEmbedding) e))⟩

private theorem faceOfSeed_surjective (model : GraphRealization V g) {d : ℕ}
    (hd : d + 3 = Fintype.card V) : Function.Surjective (faceOfSeed model (d := d)) := by
  intro F
  obtain ⟨t, hF, hcard⟩ := exists_seed V F
  change F.val = seededFace t at hF
  let s := t.map model.arc.symm.toEmbedding
  have hs : actualSeed model s.toList = t := by
    change s.toList.toFinset.map model.arc.toEmbedding = t
    ext e
    simp [s]
  have hn : (seededFace (actualSeed model s.toList)).Nonempty := by
    rw [hs, ← hF]
    exact F.property.2.1
  have hr := finrank_eq_rows model s.toList hn
  have hfd := F.property.2.2
  rw [hs, ← hF, hfd] at hr
  have hmem : s ∈ seeds g d := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [Finset.card_map]
      omega
    · exact ⟨(nonempty_iff_accepted_pins model s.toList).mp hn, hr.symm⟩
  exact ⟨⟨s, hmem⟩, Subtype.ext (by change seededFace _ = F.val; rw [hs, ← hF])⟩

private def witness {d : ℕ} (a : signatures g d) : seeds g d :=
  ⟨(Finset.mem_image.mp a.property).choose, (Finset.mem_image.mp a.property).choose_spec.1⟩

private theorem signature_witness {d : ℕ} (a : signatures g d) :
    signature g (witness a).val = a.val :=
  (Finset.mem_image.mp a.property).choose_spec.2

theorem fCoefficient_eq_card_signatures (model : GraphRealization V g) {d : ℕ}
    (hd : d + 3 = Fintype.card V) : fCoefficient V d = (signatures g d).card := by
  let f (s : signatures g d) : FacesOfDimension V d := faceOfSeed model (witness s)
  have hinj : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact (signature_witness s).symm.trans
      (((faceOfSeed_eq_iff model _ _).mp h).trans (signature_witness t))
  have hsurj : Function.Surjective f := by
    intro F
    obtain ⟨s, hs⟩ := faceOfSeed_surjective model hd F
    let a : signatures g d := ⟨signature g s.val, Finset.mem_image.mpr ⟨s.val, s.property, rfl⟩⟩
    exact ⟨a, ((faceOfSeed_eq_iff model _ _).mpr (signature_witness a)).trans hs⟩
  change Nat.card (FacesOfDimension V d) = _
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_coe]

open PolytopalProducts.Geometry

theorem cube_fCoefficient_eq_signatures :
    fCoefficient (ExposedFace cube) 25 = (signatures cubeGraph 25).card := by
  rw [← fCoefficient_iso cubeFaceIso]
  apply fCoefficient_eq_card_signatures cubeGraphRealization
  have hc := card_pinnedCube
  change Fintype.card (Option (Option CubeFace)) = 30 at hc
  simp only [Fintype.card_option] at hc
  omega

theorem hex_pyramid_fCoefficient_eq_signatures :
    fCoefficient (ExposedFace hexagonalPyramid) 25 = (signatures hexGraph 25).card := by
  rw [← fCoefficient_iso hexagonalPyramidFaceIso]
  exact fCoefficient_eq_card_signatures hexGraphRealization (by rw [card_pyramid])

end PolytopalProducts.Codim3
