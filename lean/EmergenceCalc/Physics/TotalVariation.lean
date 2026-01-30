import Mathlib
import EmergenceCalc.Emergence.Lens

namespace EmergenceCalc

noncomputable section
open scoped BigOperators

/-- Total variation distance for finite PMFs (as an `ℝ` value). -/
def TV {Z : Type*} [Fintype Z] [DecidableEq Z] (p q : PMF Z) : ℝ :=
  (1 / 2 : ℝ) * ∑ z : Z, abs ((p z).toReal - (q z).toReal)

lemma map_toReal_apply
  {Z X : Type*} [Fintype Z] [DecidableEq Z] [Fintype X] [DecidableEq X]
  (f : Z → X) (p : PMF Z) (x : X) :
  ((p.map f) x).toReal = ∑ z : Z, if x = f z then (p z).toReal else 0 := by
  classical
  have htsum : (∑' z : Z, if x = f z then p z else 0) =
      ∑ z : Z, if x = f z then p z else 0 := by
    simpa using
      (tsum_eq_sum (s := (Finset.univ))
        (f := fun z : Z => if x = f z then p z else 0)
        (by intro z hz; exact (hz (Finset.mem_univ z)).elim))
  have hne : ∀ z ∈ (Finset.univ : Finset Z), (if x = f z then p z else 0) ≠ (⊤ : ENNReal) := by
    intro z hz
    by_cases h : x = f z
    · simp [h, p.apply_ne_top z]
    · simp [h]
  have hmap' :
      (p.map f) x = ∑' z : Z, @ite ENNReal (x = f z)
        (Classical.propDecidable (x = f z)) (p z) 0 :=
    PMF.map_apply (f := f) (p := p) x
  have hmap : (p.map f) x = ∑' z : Z, if x = f z then p z else 0 := by
    refine hmap'.trans ?_
    refine tsum_congr ?_
    intro z
    by_cases h : x = f z
    · simp [h]
    · simp [h]
  have hmap_toReal :
      ((p.map f) x).toReal = ENNReal.toReal (∑' z : Z, if x = f z then p z else 0) := by
    simpa [hmap]
  have htsum' :
      ENNReal.toReal (∑' z : Z, if x = f z then p z else 0)
        = ENNReal.toReal (∑ z : Z, if x = f z then p z else 0) := by
    simpa using congrArg ENNReal.toReal htsum
  have hmap' : ((p.map f) x).toReal = ENNReal.toReal (∑ z : Z, if x = f z then p z else 0) :=
    hmap_toReal.trans htsum'
  calc
    ((p.map f) x).toReal
        = ENNReal.toReal (∑ z : Z, if x = f z then p z else 0) := by
            simpa using hmap'
    _ = ∑ z : Z, ENNReal.toReal (if x = f z then p z else 0) := by
            simpa using
              (ENNReal.toReal_sum (s := (Finset.univ))
                (f := fun z : Z => if x = f z then p z else 0) hne)
    _ = ∑ z : Z, if x = f z then (p z).toReal else 0 := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            by_cases h : x = f z
            · simp [h]
            · simp [h]

/-- Contraction of TV under deterministic pushforward. -/
theorem TV_Q_f_le
  {Z X : Type*} [Fintype Z] [DecidableEq Z] [Fintype X] [DecidableEq X]
  (f : Z → X) (p q : PMF Z) :
  TV (Q_f f p) (Q_f f q) ≤ TV p q := by
  classical
  let d : Z → ℝ := fun z => (p z).toReal - (q z).toReal
  have hdiff : ∀ x : X,
      (Q_f f p x).toReal - (Q_f f q x).toReal =
        ∑ z : Z, if x = f z then d z else 0 := by
    intro x
    have hp := map_toReal_apply (f := f) (p := p) x
    have hq := map_toReal_apply (f := f) (p := q) x
    calc
      (Q_f f p x).toReal - (Q_f f q x).toReal
          = ((p.map f) x).toReal - ((q.map f) x).toReal := by
                rfl
      _ = (∑ z : Z, if x = f z then (p z).toReal else 0)
              - (∑ z : Z, if x = f z then (q z).toReal else 0) := by
                rw [hp, hq]
      _ = (Finset.univ.sum (fun z : Z =>
            (if x = f z then (p z).toReal else 0) - (if x = f z then (q z).toReal else 0))) := by
                have hsub :=
                  (Finset.sum_sub_distrib (s := (Finset.univ : Finset Z))
                    (f := fun z : Z => if x = f z then (p z).toReal else 0)
                    (g := fun z : Z => if x = f z then (q z).toReal else 0))
                exact hsub.symm
      _ = (Finset.univ.sum (fun z : Z => if x = f z then d z else 0)) := by
                refine Finset.sum_congr rfl ?_
                intro z hz
                by_cases h : x = f z
                · simp [d, h]
                · simp [d, h]
      _ = ∑ z : Z, if x = f z then d z else 0 := by
                simp
  have habs : ∀ x : X,
      abs ((Q_f f p x).toReal - (Q_f f q x).toReal) ≤ ∑ z : Z, abs (if x = f z then d z else 0) := by
    intro x
    have := (Finset.abs_sum_le_sum_abs (f := fun z : Z => if x = f z then d z else 0)
      (s := (Finset.univ : Finset Z)))
    simpa [hdiff x] using this
  have hsum_le :
      (∑ x : X, abs ((Q_f f p x).toReal - (Q_f f q x).toReal))
        ≤ ∑ x : X, ∑ z : Z, abs (if x = f z then d z else 0) := by
    refine Finset.sum_le_sum ?_
    intro x hx
    exact habs x
  have hswap :
      (∑ x : X, ∑ z : Z, abs (if x = f z then d z else 0))
        = ∑ z : Z, ∑ x : X, abs (if x = f z then d z else 0) := by
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset X))
      (t := (Finset.univ : Finset Z)) (f := fun x z => abs (if x = f z then d z else 0)))
  have hcollapse :
      (∑ z : Z, ∑ x : X, abs (if x = f z then d z else 0)) = ∑ z : Z, abs (d z) := by
    refine Finset.sum_congr rfl ?_
    intro z hz
    let ad : ℝ := abs (d z)
    have h1 : (∑ x : X, abs (if x = f z then d z else 0)) =
        (∑ x : X, if x = f z then ad else (0 : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      by_cases h : x = f z
      · simp [h, ad]
      · simp [h, ad]
    have h2 : (∑ x : X, if x = f z then ad else (0 : ℝ)) = ad := by
      simpa using
        (Finset.sum_ite_eq (M := ℝ) (s := (Finset.univ : Finset X)) (a := f z)
          (b := fun _ => ad))
    simpa [h1, ad] using h2
  have hsum' :
      (∑ x : X, abs ((Q_f f p x).toReal - (Q_f f q x).toReal)) ≤ ∑ z : Z, abs (d z) := by
    exact hsum_le.trans (by simpa [hswap, hcollapse])
  have hnonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have := mul_le_mul_of_nonneg_left hsum' hnonneg
  simpa [TV, d, Q_f] using this

/-- TV contraction as a Prop, now proved by `TV_Q_f_le`. -/
def TV_contraction_Qf
    {Z X : Type*} [Fintype Z] [DecidableEq Z] [Fintype X] [DecidableEq X]
    (f : Z → X) : Prop :=
  ∀ p q : PMF Z, TV (Q_f f p) (Q_f f q) ≤ TV p q

theorem TV_contraction_Qf_true
  {Z X : Type*} [Fintype Z] [DecidableEq Z] [Fintype X] [DecidableEq X]
  (f : Z → X) : TV_contraction_Qf (Z := Z) (X := X) f := by
  intro p q
  simpa [TV_contraction_Qf] using (TV_Q_f_le (f := f) p q)

end

end EmergenceCalc
