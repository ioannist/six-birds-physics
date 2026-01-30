# Lean feasibility survey (mathlib inventory)

## Finite probability types
Status: Available
Evidence:
- Modules: Mathlib.Probability.ProbabilityMassFunction.Basic
- Names: PMF, PMF.toMeasure, MeasureTheory.IsProbabilityMeasure
- Grep hits: Mathlib/Probability/ProbabilityMassFunction/Basic.lean

## Markov kernels / stochastic matrices
Status: Found but awkward
Evidence:
- Kernels available:
  - Module: Mathlib.Probability.Kernel.Defs
  - Names: ProbabilityTheory.Kernel, ProbabilityTheory.IsMarkovKernel
  - Grep hits: Mathlib/Probability/Kernel/Defs.lean
- Stochastic matrices:
  - No dedicated StochasticMatrix type found
  - Available: doublyStochastic predicate (Submonoid) in Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean
  - Suggested encoding: Matrix with nonneg entries + row-sum-to-1 property

## KL divergence / relative entropy
Status: Available
Evidence:
- Modules: Mathlib.InformationTheory.KullbackLeibler.Basic, Mathlib.InformationTheory.KullbackLeibler.KLFun
- Names: InformationTheory.klDiv, InformationTheory.klFun
- Grep hits: Mathlib/InformationTheory/KullbackLeibler/Basic.lean, Mathlib/InformationTheory/KullbackLeibler/KLFun.lean

## Data Processing Inequality (DPI)
Status: Not found
Evidence:
- Grep search terms: data processing, data_processing, DPI, kl_map, relEntropy_map
- No DPI lemma surfaced in Mathlib/InformationTheory/KullbackLeibler/* or Probability/Kernel/*
- Only unrelated "DPI" hits in DividedPowers (RingTheory/DividedPowers/SubDPIdeal.lean)

## Recommended modeling choice for our project
- Use PMF for finite distributions; bridge to measures via PMF.toMeasure where needed.
- Use ProbabilityTheory.Kernel for dynamics; encode stochastic matrices as Matrix with row-sum=1 predicate.
- Use InformationTheory.klDiv for KL divergence (measure-level).
- DPI appears missing; plan to prove in project or search further with focused keyword variants.
