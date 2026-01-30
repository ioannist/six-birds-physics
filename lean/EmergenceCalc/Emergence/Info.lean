import Mathlib
import EmergenceCalc.Emergence.Lens

namespace EmergenceCalc

noncomputable section

/-- KL divergence on PMFs via the associated measures. -/
def KL {Z : Type*} [Fintype Z] [DecidableEq Z] [MeasurableSpace Z]
    (p q : PMF Z) : ENNReal :=
  InformationTheory.klDiv (p.toMeasure) (q.toMeasure)

/-- Data-processing inequality for deterministic pushforward along `Q_f` (TODO). -/
def DPI_KL_Qf {Z X : Type*} [Fintype Z] [DecidableEq Z] [Fintype X] [DecidableEq X]
    [MeasurableSpace Z] [MeasurableSpace X] (f : Z → X) : Prop :=
  ∀ p q : PMF Z, KL (Q_f f p) (Q_f f q) ≤ KL p q

-- TODO: prove DPI_KL_Qf using InformationTheory (data-processing inequality).

end

end EmergenceCalc
