import PolytopalProducts.TruncatedRank

namespace PolytopalProducts.Truncated
open PolytopalProducts.OrderFaces PolytopalProducts.Codim3

def Slot {X : Type} (p : ℕ → X → Prop) : Option ℕ → Type
  | none => Unit
  | some r => {x : X // p r x}

def selected {X : Type} {p : ℕ → X → Prop} : (r : Option ℕ) → Slot p r → Option X
  | none, _ => none
  | some _, x => some x.val

def compatible {X : Type} (rel : X → X → Prop) : Option X → Option X → Prop
  | some i, some j => rel i j
  | _, _ => True

def tripleProperty {X : Type} (p : ℕ → X → Prop) (rel : X → X → Prop) (a b c : Option ℕ)
    (t : Slot p a × Slot p b × Slot p c) : Prop :=
  compatible rel (selected a t.1) (selected b t.2.1) ∧
  compatible rel (selected a t.1) (selected c t.2.2) ∧
  compatible rel (selected b t.2.1) (selected c t.2.2)

def RankFlag {X : Type} (p : ℕ → X → Prop) (rel : X → X → Prop) (a b c : Option ℕ) :=
  {t : Slot p a × Slot p b × Slot p c // tripleProperty p rel a b c t}

private def slotEquiv {X Y : Type} {p : ℕ → X → Prop} {q : ℕ → Y → Prop}
    (e : X ≃ Y) (h : ∀ r x, p r x ↔ q r (e x)) : (r : Option ℕ) → Slot p r ≃ Slot q r
  | none => Equiv.refl _
  | some r => e.subtypeEquiv (h r)

private theorem selected_map {X Y : Type} {p : ℕ → X → Prop} {q : ℕ → Y → Prop}
    (e : X ≃ Y) (h : ∀ r x, p r x ↔ q r (e x)) (r : Option ℕ) (x : Slot p r) :
    selected r (slotEquiv e h r x) = (selected r x).map e := by cases r <;> rfl

private theorem compatible_map {X Y : Type} {R : X → X → Prop} {S : Y → Y → Prop}
    (e : X ≃ Y) (h : ∀ a b, R a b ↔ S (e a) (e b)) (x y : Option X) :
    compatible R x y ↔ compatible S (x.map e) (y.map e) := by
  cases x <;> cases y <;> first | rfl | exact h _ _

def flagEquiv {X Y : Type} {p : ℕ → X → Prop} {q : ℕ → Y → Prop}
    {R : X → X → Prop} {S : Y → Y → Prop} (e : X ≃ Y)
    (h : ∀ r x, p r x ↔ q r (e x)) (ho : ∀ x y, R x y ↔ S (e x) (e y))
    (a b c : Option ℕ) : RankFlag p R a b c ≃ RankFlag q S a b c := by
  let H := (slotEquiv e h a).prodCongr ((slotEquiv e h b).prodCongr (slotEquiv e h c))
  apply H.subtypeEquiv
  rintro ⟨x,y,z⟩
  change _ ↔ compatible S (selected a (slotEquiv e h a x)) (selected b (slotEquiv e h b y)) ∧
    compatible S (selected a (slotEquiv e h a x)) (selected c (slotEquiv e h c z)) ∧
    compatible S (selected b (slotEquiv e h b y)) (selected c (slotEquiv e h c z))
  simp only [selected_map]
  exact and_congr (compatible_map e ho _ _) (and_congr (compatible_map e ho _ _) (compatible_map e ho _ _))

def indexLevel (r : ℕ) (i : Fin 30) : Prop := augmentedRank i = r
def indexOrder (g : GraphData 30 64) (i j : Fin 30) : Prop := arrow g.order i j = true

private instance (r : Option ℕ) : Fintype (Slot indexLevel r) := by
  cases r with
  | none => exact inferInstanceAs (Fintype Unit)
  | some r => exact inferInstanceAs (Fintype {i : Fin 30 // augmentedRank i = r})

private instance {X : Type} {rel : X → X → Prop} [DecidableRel rel] (a b : Option X) :
    Decidable (compatible rel a b) := by cases a <;> cases b <;> unfold compatible <;> infer_instance

private instance (g : GraphData 30 64) : DecidableRel (indexOrder g) :=
  fun i j ↦ inferInstanceAs (Decidable (arrow g.order i j = true))

private instance (g : GraphData 30 64) (a b c : Option ℕ) :
    Fintype (RankFlag indexLevel (indexOrder g) a b c) := by
  haveI : DecidablePred (tripleProperty indexLevel (indexOrder g) a b c) := fun _ ↦ by
    unfold tripleProperty; infer_instance
  exact inferInstanceAs (Fintype (Subtype (tripleProperty indexLevel (indexOrder g) a b c)))

def modelCount (g : GraphData 30 64) (a b c : Option ℕ) : ℕ :=
  Fintype.card (RankFlag indexLevel (indexOrder g) a b c)

/-- Counts all proper flags whose vertex, edge, and facet levels are selected.
The predicate uses the intrinsic cover relation of the actual augmented order. -/
noncomputable def actualCount (X : Type) [PartialOrder X] (a b c : Option ℕ) : ℕ :=
  Nat.card (RankFlag (AtLevel (X:=Pinned X)) (· ≤ ·) a b c)

theorem count_physical {V X : Type} [PartialOrder V] [PartialOrder X] {g : GraphData 30 64}
    (m : GraphRealization V g) (graded : raisesRank g) (hd : rankConditions g) (e : V ≃o X)
    (a b c : Option ℕ) : modelCount g a b c = actualCount X a b c := by
  let t : Pinned V ≃o Pinned X := e.withTopCongr.withBotCongr
  let iso := m.point.trans t.toEquiv
  have lev (r i) : indexLevel r i ↔ AtLevel r (iso i) :=
    ((rank_iff m graded hd r i).symm).trans (level_order_iso t r (m.point i)).symm
  have ord (i j) : indexOrder g i j ↔ iso i ≤ iso j := (m.order i j).trans t.le_iff_le.symm
  exact (Nat.card_eq_fintype_card.symm).trans (Nat.card_congr (flagEquiv iso lev ord a b c))

def eight (f : Option ℕ → Option ℕ → Option ℕ → ℕ) : Vector Nat 8 :=
  #v[f none none none, f (some 2) none none, f none (some 3) none, f none none (some 4),
    f (some 2) (some 3) none, f (some 2) none (some 4), f none (some 3) (some 4), f (some 2) (some 3) (some 4)]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem model_counts :
    eight (modelCount graph) = #v[1,7,12,7,24,24,24,48] ∧
    eight (modelCount hexGraph) = #v[1,7,12,7,24,24,24,48] := by decide +kernel

open PolytopalProducts.Geometry in
theorem actual_complete_flags :
    eight (actualCount (ExposedFace body)) = #v[1,7,12,7,24,24,24,48] ∧
    eight (actualCount (ExposedFace hexagonalPyramid)) = #v[1,7,12,7,24,24,24,48] := by
  have l := funext fun a ↦ funext fun b ↦ funext fun c ↦
    count_physical graphModel both_raise_rank.1 rank_data.1 faceIso a b c
  have r := funext fun a ↦ funext fun b ↦ funext fun c ↦
    count_physical hexGraphRealization both_raise_rank.2 rank_data.2 hexagonalPyramidFaceIso a b c
  rw [← l,← r]
  exact model_counts

#print axioms count_physical
#print axioms actual_complete_flags
end PolytopalProducts.Truncated

