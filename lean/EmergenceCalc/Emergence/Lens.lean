import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace EmergenceCalc

noncomputable section
variable {Z X : Type*} [Fintype Z] [DecidableEq Z] [Fintype X] [DecidableEq X]

/-- Pushforward of a finite distribution along a lens `f : Z → X`. -/
def Q_f (f : Z → X) (μ : PMF Z) : PMF X :=
  μ.map f

lemma Q_f_pure (f : Z → X) (z : Z) : Q_f f (PMF.pure z) = PMF.pure (f z) := by
  simpa [Q_f] using (PMF.pure_map (f := f) z)

lemma Q_id (μ : PMF Z) : Q_f (fun z : Z => z) μ = μ := by
  simpa [Q_f] using (PMF.map_id (p := μ))

lemma Q_comp {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : Z → X) (g : X → Y) (μ : PMF Z) :
    Q_f g (Q_f f μ) = Q_f (g ∘ f) μ := by
  simpa [Q_f] using (PMF.map_comp (f := f) (p := μ) g)

end

end EmergenceCalc
