import Mathlib

open ProbabilityTheory
open MeasureTheory
open scoped BigOperators

section
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

-- Finite probability type(s)
#check PMF
#check PMF.toMeasure
#check MeasureTheory.IsProbabilityMeasure

-- Markov kernels / stochastic matrices
#check ProbabilityTheory.Kernel
#check ProbabilityTheory.IsMarkovKernel
#check doublyStochastic

-- KL divergence / relative entropy
#check InformationTheory.klDiv
#check InformationTheory.klFun

variable {n : Type*} [Fintype n] [DecidableEq n]
#check (fun (M : Matrix n n ℝ) => (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = (1 : ℝ)))

end
