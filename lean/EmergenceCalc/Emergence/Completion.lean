import EmergenceCalc.Emergence.Lens

namespace EmergenceCalc

noncomputable section

variable {Z X : Type*} [Fintype Z] [DecidableEq Z] [Fintype X] [DecidableEq X]

/-- Section axiom for a right inverse of `Q_f`. -/
def SectionAxiom (f : Z → X) (U : PMF X → PMF Z) : Prop :=
  ∀ ν : PMF X, Q_f f (U ν) = ν

/-- Completion operator `E(μ) = U (Q_f μ)`. -/
def E (f : Z → X) (U : PMF X → PMF Z) : PMF Z → PMF Z :=
  fun μ => U (Q_f f μ)

lemma E_idempotent (f : Z → X) (U : PMF X → PMF Z)
    (h : SectionAxiom f U) (μ : PMF Z) :
    E f U (E f U μ) = E f U μ := by
  unfold E
  have : Q_f f (U (Q_f f μ)) = Q_f f μ := h (Q_f f μ)
  simpa [this]

end

end EmergenceCalc
