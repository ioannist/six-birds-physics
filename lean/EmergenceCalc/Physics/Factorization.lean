import Mathlib
import EmergenceCalc.Emergence.RouteMismatch
import EmergenceCalc.Emergence.Completion
import EmergenceCalc.Physics.UniformLift

namespace EmergenceCalc

noncomputable section
open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (m : ℕ) [NeZero m]

/-- Micro dynamics factors through a macro dynamics, and preserves uniform fibers. -/
def FactorsThrough
    (T : PMF (X × Fin m) → PMF (X × Fin m))
    (S : PMF X → PMF X) : Prop :=
  (∀ μ : PMF (X × Fin m), Q_f (f := Prod.fst) (T μ) = S (Q_f (f := Prod.fst) μ))
  ∧
  (∀ ν : PMF X, T (U_uniform (m := m) ν) = U_uniform (m := m) (S ν))

/-- If micro dynamics factors through a macro dynamics and preserves uniform fibers, then
    it commutes with the uniform-fiber completion. -/
theorem commutes_of_factorsThrough
    {T : PMF (X × Fin m) → PMF (X × Fin m)}
    {S : PMF X → PMF X}
    (h : FactorsThrough (m := m) T S)
    (μ : PMF (X × Fin m)) :
    E (f := Prod.fst) (U := U_uniform (m := m)) (T μ)
      =
    T (E (f := Prod.fst) (U := U_uniform (m := m)) μ) := by
  have hcomm : Commutes (f := Prod.fst) (U := U_uniform (m := m)) (T := T) :=
    commutes_of_intertwine (f := Prod.fst) (U := U_uniform (m := m)) (T := T) (S := S)
      (hQ := h.1) (hU := h.2)
  simpa [Commutes, C] using hcomm μ

end

end EmergenceCalc
