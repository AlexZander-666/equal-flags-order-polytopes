import PolytopalProducts.Halfspaces

/-! Order-polytope halfspaces on the augmented Hasse diagram. -/

noncomputable section

namespace PolytopalProducts.OrderFaces

open Set ContinuousLinearMap
open scoped Classical

variable (V : Type*)

/-- The original polytope's coordinate indices and two artificial endpoints. -/
abbrev Pinned := WithBot (WithTop V)

/-- A single artificial lower point, the ordinary coordinates, and a single upper point. -/
def interior (v : V) : Pinned V := (↑(v : WithTop V) : WithBot (WithTop V))

def high : Pinned V := (↑(⊤ : WithTop V) : WithBot (WithTop V))

lemma interior_le_interior [PartialOrder V] (a b : V) :
    interior V a ≤ interior V b ↔ a ≤ b :=
  WithBot.coe_le_coe.trans WithTop.coe_le_coe

lemma le_high [PartialOrder V] (p : Pinned V) : p ≤ high V := by
  cases p using WithBot.recBotCoe
  · exact bot_le
  · exact WithBot.coe_le_coe.mpr le_top

/-- The independent linear coordinate of an index, zero at either pin. -/
def coord : Pinned V → StrongDual ℝ (V → ℝ) :=
  WithBot.recBotCoe 0 (WithTop.recTopCoe 0 fun v ↦ ContinuousLinearMap.proj v)

/-- The affine offset of each index, one precisely at the upper pin. -/
def offset : Pinned V → ℝ :=
  WithBot.recBotCoe 0 (WithTop.recTopCoe 1 fun _ ↦ 0)

def value (z : V → ℝ) (p : Pinned V) : ℝ := coord V p z + offset V p

@[simp] lemma value_bot (z : V → ℝ) : value V z ⊥ = 0 := by
  simp [value, coord, offset]

@[simp] lemma value_high (z : V → ℝ) : value V z (high V) = 1 := by
  simp only [value, coord, offset, high, WithBot.recBotCoe_coe, WithTop.recTopCoe_top,
    zero_apply, zero_add]

@[simp] lemma value_interior (z : V → ℝ) (v : V) : value V z (interior V v) = z v := by
  simp [value, coord, offset, interior]

variable [PartialOrder V]
/-- The finite family of actual Hasse covers on the augmented index set. -/
abbrev Arc := {p : Pinned V × Pinned V // p.1 ⋖ p.2}

instance [Fintype V] : Fintype (Arc V) := Fintype.ofFinite _

def form (p : Arc V) : StrongDual ℝ (V → ℝ) :=
  coord V p.val.1 - coord V p.val.2

def rhs (p : Arc V) : ℝ := offset V p.val.2 - offset V p.val.1

theorem form_le_iff (z : V → ℝ) (p : Arc V) :
    form V p z ≤ rhs V p ↔ value V z p.val.1 ≤ value V z p.val.2 := by
  simp only [form, rhs, value, sub_apply]
  constructor <;> intro h <;> linarith

theorem form_eq_iff (z : V → ℝ) (p : Arc V) :
    form V p z = rhs V p ↔ value V z p.val.1 = value V z p.val.2 := by
  simp only [form, rhs, value, sub_apply]
  constructor <;> intro h <;> linarith

theorem form_lt_iff (z : V → ℝ) (p : Arc V) :
    form V p z < rhs V p ↔ value V z p.val.1 < value V z p.val.2 := by
  simp only [form, rhs, value, sub_apply]
  constructor <;> intro h <;> linarith

variable [Fintype V]

theorem body_iff_monotone (z : V → ℝ) :
    z ∈ Halfspaces.body (form V) (rhs V) ↔ Monotone (value V z) := by
  let : LocallyFiniteOrder (Pinned V) := LocallyFiniteOrder.ofFiniteIcc
    (fun _ _ ↦ Set.toFinite _)
  rw [monotone_iff_forall_covBy]
  exact ⟨fun h a b hab ↦ (form_le_iff V z ⟨(a, b), hab⟩).mp (h _),
    fun h p ↦ (form_le_iff V z p).mpr (h _ _ p.property)⟩

/-- The Hasse cover inequalities describe exactly the original real order polytope. -/
theorem body_eq_orderPolytope :
    Halfspaces.body (form V) (rhs V) = Polygon.Ehrhart.orderPolytope (· ≤ · : V → V → Prop) := by
  ext z
  rw [body_iff_monotone]
  change Monotone (value V z) ↔ (∀ v, 0 ≤ z v ∧ z v ≤ 1) ∧ ∀ a b : V, a ≤ b → z a ≤ z b
  constructor
  · intro h
    exact ⟨fun v ↦ ⟨by simpa using h (bot_le : (⊥ : Pinned V) ≤ interior V v),
      by simpa using h (le_high V (interior V v))⟩,
      fun a b hab ↦ by simpa using h ((interior_le_interior V a b).mpr hab)⟩
  · rintro ⟨bounds, mono⟩ a b hab
    cases a using WithBot.recBotCoe with
    | bot =>
      cases b using WithBot.recBotCoe with
      | bot => exact le_rfl
      | coe b =>
        cases b using WithTop.recTopCoe with
        | top =>
          change value V z ⊥ ≤ value V z (high V)
          simp
        | coe b =>
          change value V z ⊥ ≤ value V z (interior V b)
          simpa only [value_bot, value_interior] using (bounds b).1
    | coe a =>
      cases b using WithBot.recBotCoe with
      | bot => exact (WithBot.not_coe_le_bot a hab).elim
      | coe b =>
        have hab' := WithBot.coe_le_coe.mp hab
        cases a using WithTop.recTopCoe with
        | top =>
          have he : b = ⊤ := le_antisymm le_top hab'
          subst b
          exact le_rfl
        | coe a =>
          cases b using WithTop.recTopCoe with
          | top =>
            change value V z (interior V a) ≤ value V z (high V)
            simpa only [value_interior, value_high] using (bounds a).2
          | coe b =>
            change value V z (interior V a) ≤ value V z (interior V b)
            simpa only [value_interior] using mono a b (WithTop.coe_le_coe.mp hab')

/-- Faces of a specified affine dimension in the genuine order polytope. -/
abbrev FacesOfDimension (d : ℕ) :=
  {F : Set (V → ℝ) // IsExposed ℝ (Polygon.Ehrhart.orderPolytope
    (· ≤ · : V → V → Prop)) F ∧ F.Nonempty ∧ Module.finrank ℝ (vectorSpan ℝ F) = d}

/-- The actual nonempty face coefficient. -/
def fCoefficient (d : ℕ) : ℕ := Nat.card (FacesOfDimension V d)

/-- Every actual face of a given dimension comes from the corresponding number of covers. -/
theorem exists_seed {d : ℕ} (F : FacesOfDimension V d) :
    ∃ s : Finset (Arc V), F.val = Halfspaces.face (form V) (rhs V) s ∧
      s.card + d = Fintype.card V := by
  let S : Set (V → ℝ) := F.val
  have hFactual : IsExposed ℝ (Polygon.Ehrhart.orderPolytope (· ≤ · : V → V → Prop)) S :=
    F.property.1
  have he : IsExposed ℝ (Halfspaces.body (form V) (rhs V)) S := by
    simpa only [body_eq_orderPolytope V] using hFactual
  obtain ⟨s, hs, hcard⟩ :=
    Halfspaces.exists_face_eq_card_codim (form V) (rhs V) he F.property.2.1
  have h := hcard
  rw [F.property.2.2, Module.finrank_pi_fintype] at h
  simpa using (show ∃ s, F.val = Halfspaces.face (form V) (rhs V) s ∧
    s.card + d = Fintype.card V from ⟨s, hs, by simpa using h⟩)

end PolytopalProducts.OrderFaces

