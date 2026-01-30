import EmergenceCalc.Emergence.Completion

namespace EmergenceCalc

noncomputable section

variable {Z X : Type*} [Fintype Z] [DecidableEq Z] [Fintype X] [DecidableEq X]

/-- Coarse operator defined as completion. -/
def C (f : Z → X) (U : PMF X → PMF Z) : PMF Z → PMF Z :=
  E f U

/-- Pointwise route mismatch between coarse-then-evolve and evolve-then-coarse. -/
def routeMismatch (f : Z → X) (U : PMF X → PMF Z) (T : PMF Z → PMF Z) (μ : PMF Z) : Prop :=
  C f U (T μ) ≠ T (C f U μ)

/-- Global commutation property for coarse operator and dynamics. -/
def Commutes (f : Z → X) (U : PMF X → PMF Z) (T : PMF Z → PMF Z) : Prop :=
  ∀ μ : PMF Z, C f U (T μ) = T (C f U μ)

lemma commutes_of_intertwine (f : Z → X) (U : PMF X → PMF Z) (T : PMF Z → PMF Z)
    (S : PMF X → PMF X)
    (hQ : ∀ μ : PMF Z, Q_f f (T μ) = S (Q_f f μ))
    (hU : ∀ ν : PMF X, T (U ν) = U (S ν)) :
    Commutes f U T := by
  unfold Commutes
  intro μ
  unfold C E
  have hQ' : U (Q_f f (T μ)) = U (S (Q_f f μ)) := by
    simpa using congrArg U (hQ μ)
  have hU' : U (S (Q_f f μ)) = T (U (Q_f f μ)) := by
    simpa using (hU (Q_f f μ)).symm
  exact hQ'.trans hU'

end

end EmergenceCalc
