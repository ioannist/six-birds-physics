import Mathlib

noncomputable section
namespace EmergenceCalc

variable {Z X : Type*}

def FiberConstant (f : Z → X) (p : Z → Bool) : Prop :=
  ∀ z₁ z₂, f z₁ = f z₂ → p z₁ = p z₂

def DefPred (f : Z → X) :=
  { p : Z → Bool // FiberConstant f p }

noncomputable instance instFintypeDefPred {Z X : Type*} [Fintype Z] (f : Z → X) :
    Fintype (DefPred f) := by
  classical
  have : Finite (DefPred f) := by
    simpa using (Subtype.finite : Finite { p : Z → Bool // FiberConstant f p })
  exact Fintype.ofFinite (DefPred f)

noncomputable instance instFintypeRange {Z X : Type*} [Fintype Z] (f : Z → X) :
    Fintype (Set.range f) := by
  classical
  have : Finite (Set.range f) := by
    simpa using (Set.finite_range f)
  exact Fintype.ofFinite (Set.range f)

def pullback (f : Z → X) (g : X → Bool) : Z → Bool := fun z => g (f z)

lemma fiberConstant_pullback (f : Z → X) (g : X → Bool) : FiberConstant f (pullback f g) := by
  intro z₁ z₂ h
  simp [pullback, h]

noncomputable def defPredEquivRange
  {Z X : Type*} [Fintype Z]
  (f : Z → X) :
  DefPred f ≃ (Set.range f → Bool) := by
  classical
  refine
    { toFun := fun p x => p.1 (Classical.choose x.property)
      invFun := fun g =>
        ⟨fun z => g ⟨f z, ⟨z, rfl⟩⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z₁ z₂ h
    have hx :
        (⟨f z₁, ⟨z₁, rfl⟩⟩ : Set.range f)
          = ⟨f z₂, ⟨z₂, rfl⟩⟩ := by
      apply Subtype.ext
      simp [h]
    simpa [hx]
  · intro p
    apply Subtype.ext
    funext z
    have hx : ∃ z', f z' = f z := ⟨z, rfl⟩
    have hz : f (Classical.choose hx) = f z := Classical.choose_spec hx
    have h := p.property _ _ hz
    simpa using h
  · intro g
    funext x
    have hx : f (Classical.choose x.property) = x := Classical.choose_spec x.property
    have hx' :
        (⟨f (Classical.choose x.property), ⟨Classical.choose x.property, rfl⟩⟩ :
          Set.range f) = x := by
      apply Subtype.ext
      simpa [hx]
    simpa [hx']

theorem card_DefPred_range
  {Z X : Type*} [Fintype Z]
  (f : Z → X) :
  Fintype.card (DefPred f) = 2 ^ (Fintype.card (Set.range f)) := by
  classical
  let e := defPredEquivRange (f := f)
  calc
    Fintype.card (DefPred f) = Fintype.card (Set.range f → Bool) := Fintype.card_congr e
    _ = 2 ^ (Fintype.card (Set.range f)) := by
          simpa [Fintype.card_fun]

noncomputable def defPredEquiv
  {Z X : Type*} [Fintype Z] [Fintype X]
  (f : Z → X) (hf : Function.Surjective f) :
  DefPred f ≃ (X → Bool) := by
  classical
  refine
    { toFun := fun p x => p.1 (Classical.choose (hf x))
      invFun := fun g => ⟨pullback f g, fiberConstant_pullback f g⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply Subtype.ext
    funext z
    have hz : f (Classical.choose (hf (f z))) = f z := Classical.choose_spec (hf (f z))
    have h := p.property _ _ hz
    simpa [pullback] using h
  · intro g
    funext x
    have hx : f (Classical.choose (hf x)) = x := Classical.choose_spec (hf x)
    simpa [pullback, hx]

theorem card_DefPred
  {Z X : Type*} [Fintype Z] [Fintype X]
  (f : Z → X) (hf : Function.Surjective f) :
  Fintype.card (DefPred f) = 2 ^ (Fintype.card X) := by
  classical
  let e := defPredEquiv (f := f) hf
  calc
    Fintype.card (DefPred f) = Fintype.card (X → Bool) := Fintype.card_congr e
    _ = 2 ^ (Fintype.card X) := by
          simpa [Fintype.card_fun]

theorem card_DefPred_fst
  {X : Type*} [Fintype X]
  (m : ℕ) [NeZero m] :
  Fintype.card (DefPred (Prod.fst : X × Fin m → X)) = 2 ^ (Fintype.card X) := by
  classical
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let i0 : Fin m := ⟨0, hm⟩
  have hs : Function.Surjective (Prod.fst : X × Fin m → X) := by
    intro x
    exact ⟨(x, i0), rfl⟩
  simpa using (card_DefPred (f := (Prod.fst : X × Fin m → X)) hs)

end EmergenceCalc
