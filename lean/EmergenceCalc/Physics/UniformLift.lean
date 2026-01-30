import Mathlib
import EmergenceCalc.Emergence.Lens
import EmergenceCalc.Emergence.Completion
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace EmergenceCalc

noncomputable section
open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (m : ℕ) [NeZero m]

abbrev Z := X × Fin m

/-- Uniform lift: spread mass uniformly across each fiber `x × Fin m`. -/
def U_uniform (ν : PMF X) : PMF (X × Fin m) :=
  PMF.ofFintype (fun z => ν z.1 / (m : ENNReal)) (by
    classical
    have htsum : (∑' x : X, ν x) = ∑ x : X, ν x := by
      simpa using
        (tsum_eq_sum (s := (Finset.univ)) (f := fun x : X => ν x)
          (by intro x hx; exact (hx (Finset.mem_univ x)).elim))
    calc
      (∑ z : X × Fin m, ν z.1 / (m : ENNReal))
          = ∑ x : X, ∑ _i : Fin m, ν x / (m : ENNReal) := by
              simpa [Fintype.sum_prod_type]
      _ = ∑ x : X, (m : ENNReal) * (ν x / (m : ENNReal)) := by
              simp
      _ = ∑ x : X, ν x := by
              classical
              have hm : (m : ENNReal) ≠ 0 := by exact_mod_cast (NeZero.ne m)
              have hm' : (m : ENNReal) ≠ (⊤ : ENNReal) := by simp
              have hmul : ∀ x : X, (m : ENNReal) * (ν x / (m : ENNReal)) = ν x := by
                intro x
                calc
                  (m : ENNReal) * (ν x / (m : ENNReal))
                      = (m : ENNReal) * (ν x * (m : ENNReal)⁻¹) := by
                          simp [div_eq_mul_inv]
                  _ = ((m : ENNReal) * (m : ENNReal)⁻¹) * ν x := by
                          ac_rfl
                  _ = 1 * ν x := by
                          simp [ENNReal.mul_inv_cancel hm hm']
                  _ = ν x := by simp
              refine Finset.sum_congr rfl ?_
              intro x hx
              simpa using hmul x
      _ = 1 := by
              simpa using (htsum.symm.trans (PMF.tsum_coe ν))
    )

@[simp] lemma U_uniform_apply (ν : PMF X) (x : X) (i : Fin m) :
    U_uniform (m := m) ν (x, i) = ν x / (m : ENNReal) := by
  simp [U_uniform]

lemma section_uniform :
    SectionAxiom (Z := X × Fin m) (X := X) (f := Prod.fst) (U := U_uniform (m := m)) := by
  intro ν
  ext x
  classical
  have htsum :
      (∑ z : X × Fin m, if x = z.1 then ν z.1 / (m : ENNReal) else 0) = ν x := by
    calc
      (∑ z : X × Fin m, if x = z.1 then ν z.1 / (m : ENNReal) else 0)
          = ∑ x1 : X, ∑ _i : Fin m, if x = x1 then ν x1 / (m : ENNReal) else 0 := by
              simpa [Fintype.sum_prod_type]
      _ = ∑ x1 : X, if x = x1 then (m : ENNReal) * (ν x1 / (m : ENNReal)) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro x1 _
              by_cases h : x = x1
              · simp [h]
              · simp [h]
      _ = (m : ENNReal) * (ν x / (m : ENNReal)) := by
              simp
      _ = ν x := by
              have hm : (m : ENNReal) ≠ 0 := by exact_mod_cast (NeZero.ne m)
              have hm' : (m : ENNReal) ≠ (⊤ : ENNReal) := by simp
              calc
                (m : ENNReal) * (ν x / (m : ENNReal))
                    = (m : ENNReal) * (ν x * (m : ENNReal)⁻¹) := by
                        simp [div_eq_mul_inv]
                _ = ((m : ENNReal) * (m : ENNReal)⁻¹) * ν x := by
                        ac_rfl
                _ = 1 * ν x := by
                        simp [ENNReal.mul_inv_cancel hm hm']
                _ = ν x := by simp
  -- compute pushforward along `Prod.fst` using `map_apply`
  -- and convert `tsum` to a finite sum
  have htsum' :
      (∑' z : X × Fin m, if x = z.1 then ν z.1 / (m : ENNReal) else 0)
        = ∑ z : X × Fin m, if x = z.1 then ν z.1 / (m : ENNReal) else 0 := by
    simpa using
      (tsum_eq_sum (s := (Finset.univ))
        (f := fun z : X × Fin m => if x = z.1 then ν z.1 / (m : ENNReal) else 0)
        (by intro z hz; exact (hz (Finset.mem_univ z)).elim))
  have hmap := (PMF.map_apply (f := Prod.fst) (p := U_uniform (m := m) ν) x)
  -- unfold and finish
  simpa [Q_f, U_uniform, htsum', htsum] using hmap

@[simp] lemma Q_f_fst_U_uniform (ν : PMF X) :
    Q_f (f := Prod.fst) (U_uniform (m := m) ν) = ν := by
  simpa using (section_uniform (m := m) (X := X) ν)

lemma E_uniform_apply (μ : PMF (X × Fin m)) (x : X) (i : Fin m) :
    E (Z := X × Fin m) (X := X) Prod.fst (U_uniform (m := m)) μ (x, i)
      = (Q_f (f := Prod.fst) μ x) / (m : ENNReal) := by
  simp [E, U_uniform_apply]

lemma E_idempotent_uniform (μ : PMF (X × Fin m)) :
    E (Z := X × Fin m) (X := X) Prod.fst (U_uniform (m := m))
        (E Prod.fst (U_uniform (m := m)) μ) =
      E Prod.fst (U_uniform (m := m)) μ := by
  exact E_idempotent (f := Prod.fst) (U := U_uniform (m := m)) (section_uniform (m := m)) μ

end

end EmergenceCalc
