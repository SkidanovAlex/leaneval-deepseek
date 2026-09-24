/-
# `APSwitchUpper.riPhi_le_env` — the explicit majorant `riPhiEnv` of `riPhi` on `s ≥ 11/5`

The switched-window excess is bounded by the numerical window sum of the Rosser–Iwaniec upper
profile `riPhi = F − 1`.  This module proves the analytic input of that sum: the explicit
elementary majorant `riPhiEnv` of `riPhiEnvDefs` dominates `riPhi` on `[11/5, ∞)`.

## The shape of the argument

Write `Cv n = ∫_2^{2n+4} oddSum n`, `Tv n = ∫_3^{2n+3} evenSum n` for the level constants of the
delay calculus (`riPhiLevelCore`), and

* `P i = ∫_2^{2i+4} profC (2i+1)`,  `Ctot = ∑'_i P i`  (the total mass `∫_2^∞ riPsi`),
* `Q j = ∫_3^{2j+3} profC (2j)`,   `Ttot = ∑'_j Q j`  (the total mass `∫_3^∞ riPhi`),

so that `Cv n = ∑_{i≤n} P i`, `Tv n = ∑_{j≤n} Q j` and `Cv → Ctot`, `Tv → Ttot`.  The finite
level inequalities

* `moment_ineq  : 2 Cv (n+1) ≤ (4 − 3 log 3) + Cv n (2 − log 3) − Tv (n+1)`,
* `mass_ineq2   : (3+Cv n) k₁ + Tv (n+1) k₃ + k₂ + c (Cv (n+1) − (3+Cv n) A₄ − (Tv (n+1) − 4) log 2 − 2) ≤ Tv (n+2)`,
* `Cv_lower    : (3+Cv n) κ + (Tv (n+1) − 4) log 2 + 2 ≤ Cv (n+1)`

pass to the limit and give

`Ctot ≤ mCmax ≤ 563/1000 < envC = 0.5692`  and  `mTmin ≥ 738/10000 = 0.0738 ≥ 0.0785 − ε`,

where `mCmax`, `mTmin` solve the two-by-two linear system determined by the moment and mass
inequalities (and `Cv_lower` supplies the lower bound on `Ctot` needed for `mTmin`).

## The comparison

For `s ≥ 3`, with `x = s − 1` and using the tail identity `∫_x^{2i+4} profC (2i+1) = P i − ∫_2^x profC (2i+1)`,

`s · evenSum (n+1) s = ∑_{i≤n} ∫_x^{2i+4} profC (2i+1) ≤ ∑'_i ∫_x^{2i+4} profC (2i+1) = Ctot − Ψ(x)`,

where `Ψ(x) = ∑'_i ∫_2^x profC (2i+1) = (3+Ctot) A'(x) + (Ttot − 4) log (x/2) + (x − 2)` is the
limit of the integrated odd recursion `oddSum_int_eq`.  Since `Ψ` is increasing in `x` the bound
only improves beyond `x = 4`, so it suffices to prove

`Ctot − Ψ(x) ≤ envNum (x+1)`  for `2 ≤ x ≤ 4`

and `Ctot − Ψ(4) ≤ envNum 5`.  Both reduce to

`(Ctot − envC)(1 − A'(x)) + (envT − Ttot) log (x/2) ≤ 0`,

which follows from `Ctot ≤ 563/1000`, `Ttot ≥ 738/10000`, `log(x/2) ≤ log 2 ≤ 0.6931471808` and
`A'(x) ≤ A'(4) ≤ 0.3576` (the last from `riPhiEnvBasic`), with margin `0.00072`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnvBasic
import Submission.Work.NumberTheory.Chen.APSwitchUpper.oddSum_formula
import Submission.Work.NumberTheory.Chen.APSwitchUpper.integral_oddSum_Icc
import Submission.Work.NumberTheory.Chen.APSwitchUpper.mass_identity
import Submission.Work.NumberTheory.Chen.APSwitchUpper.moment_ineq
import Submission.Work.NumberTheory.Chen.APSwitchUpper.Cv_lower
import Submission.Work.NumberTheory.Chen.APSwitchUpper.level_bounds
import Submission.Work.NumberTheory.Chen.APSwitchUpper.oddSum_int_eq
import Submission.Work.NumberTheory.Chen.APSwitchUpper.mass_ineq2

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory Finset Filter
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable



/-! ## §1  The level series of the two profiles -/

/-- `P i = ∫_2^{2i+4} profC (2i+1)`: the total mass of the `i`-th odd delay profile
(`profC (2i+1)` is supported on `[1, 2i+4)`). -/
noncomputable def P (i : ℕ) : ℝ := ∫ u in (2 : ℝ)..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u

/-- `Q j = ∫_3^{2j+3} profC (2j)`: the mass of the `j`-th even delay profile beyond `3`. -/
noncomputable def Q (j : ℕ) : ℝ := ∫ u in (3 : ℝ)..(((2 * j + 3 : ℕ)) : ℝ), profC (2 * j) u

theorem P_nonneg (i : ℕ) : 0 ≤ P i := by
  rw [P]
  refine intervalIntegral.integral_nonneg_of_forall ?_ (fun u => profC_nonneg _ _)
  exact_mod_cast (by omega : 2 ≤ 2 * i + 4)

theorem Q_nonneg (j : ℕ) : 0 ≤ Q j := by
  rw [Q]
  refine intervalIntegral.integral_nonneg_of_forall ?_ (fun u => profC_nonneg _ _)
  exact_mod_cast (by omega : 3 ≤ 2 * j + 3)

theorem oddSum_eq_sum (n : ℕ) :
    oddSum n = fun u => ∑ i ∈ Finset.range (n + 1), profC (2 * i + 1) u := rfl

theorem evenSum_eq_sum (n : ℕ) :
    evenSum n = fun u => ∑ j ∈ Finset.range (n + 1), profC (2 * j) u := rfl

theorem Cv_eq_sum_P (n : ℕ) : Cv n = ∑ i ∈ Finset.range (n + 1), P i := by
  rw [Cv, oddSum_eq_sum n,
    intervalIntegral.integral_finset_sum (fun i _ => profC_intervalIntegrable (2 * i + 1) _ _)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [P]
  have hle : (((2 * i + 4 : ℕ)) : ℝ) ≤ (((2 * n + 4 : ℕ)) : ℝ) := by
    push_cast; exact_mod_cast (by omega : 2 * i + 4 ≤ 2 * n + 4)
  have hz : (∫ u in (((2 * i + 4 : ℕ)) : ℝ)..(((2 * n + 4 : ℕ)) : ℝ), profC (2 * i + 1) u) = 0 := by
    rw [show (0 : ℝ) = ∫ u in (((2 * i + 4 : ℕ)) : ℝ)..(((2 * n + 4 : ℕ)) : ℝ), (0 : ℝ) by simp]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hu
    exact profC_support (2 * i + 1) u (by push_cast at hu ⊢; linarith [hu.1])
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (profC_intervalIntegrable (2 * i + 1) (2 : ℝ) (((2 * i + 4 : ℕ)) : ℝ))
    (profC_intervalIntegrable (2 * i + 1) (((2 * i + 4 : ℕ)) : ℝ) (((2 * n + 4 : ℕ)) : ℝ))
  linarith [hadd, hz]

theorem Tv_eq_sum_Q (n : ℕ) : Tv n = ∑ j ∈ Finset.range (n + 1), Q j := by
  rw [Tv, evenSum_eq_sum n,
    intervalIntegral.integral_finset_sum (fun j _ => profC_intervalIntegrable (2 * j) _ _)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  rw [Q]
  have hle : (((2 * j + 3 : ℕ)) : ℝ) ≤ (((2 * n + 3 : ℕ)) : ℝ) := by
    push_cast; exact_mod_cast (by omega : 2 * j + 3 ≤ 2 * n + 3)
  have hz : (∫ u in (((2 * j + 3 : ℕ)) : ℝ)..(((2 * n + 3 : ℕ)) : ℝ), profC (2 * j) u) = 0 := by
    rw [show (0 : ℝ) = ∫ u in (((2 * j + 3 : ℕ)) : ℝ)..(((2 * n + 3 : ℕ)) : ℝ), (0 : ℝ) by simp]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hu
    exact profC_support (2 * j) u (by push_cast at hu ⊢; linarith [hu.1])
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (profC_intervalIntegrable (2 * j) (3 : ℝ) (((2 * j + 3 : ℕ)) : ℝ))
    (profC_intervalIntegrable (2 * j) (((2 * j + 3 : ℕ)) : ℝ) (((2 * n + 3 : ℕ)) : ℝ))
  linarith [hadd, hz]

theorem summable_P : Summable P := by
  refine summable_of_sum_range_le (f := P) (c := 4) (fun i => P_nonneg i) (fun n => ?_)
  rcases n with _ | m
  · simp
  · rw [← Cv_eq_sum_P m]; exact level_bounds.1 m

theorem summable_Q : Summable Q := by
  refine summable_of_sum_range_le (f := Q) (c := 6) (fun j => Q_nonneg j) (fun n => ?_)
  rcases n with _ | m
  · simp
  · rw [← Tv_eq_sum_Q m]; exact level_bounds.2 m

/-- `Ctot = ∫_2^∞ riPsi`, the total mass of the lower profile. -/
noncomputable def Ctot : ℝ := ∑' i, P i

/-- `Ttot = ∫_3^∞ riPhi`, the total mass of the upper profile beyond `3`. -/
noncomputable def Ttot : ℝ := ∑' j, Q j

theorem hasSum_P : HasSum P Ctot := summable_P.hasSum

theorem hasSum_Q : HasSum Q Ttot := summable_Q.hasSum

theorem Cv_le_Ctot (n : ℕ) : Cv n ≤ Ctot := by
  rw [Cv_eq_sum_P n]
  exact summable_P.sum_le_tsum (Finset.range (n + 1)) (fun i _ => P_nonneg i)

theorem Tv_le_Ttot (n : ℕ) : Tv n ≤ Ttot := by
  rw [Tv_eq_sum_Q n]
  exact summable_Q.sum_le_tsum (Finset.range (n + 1)) (fun j _ => Q_nonneg j)

theorem tendsto_Cv : Tendsto Cv atTop (𝓝 Ctot) := by
  have h2 : (fun n : ℕ => Cv n)
      = (fun n : ℕ => ∑ i ∈ Finset.range n, P i) ∘ (fun n : ℕ => n + 1) := by
    funext n
    show Cv n = ∑ i ∈ Finset.range (n + 1), P i
    exact Cv_eq_sum_P n
  have h := hasSum_P.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have : Tendsto (fun n : ℕ => Cv n) atTop (𝓝 Ctot) := by rwa [h2]
  exact this

theorem tendsto_Tv : Tendsto Tv atTop (𝓝 Ttot) := by
  have h2 : (fun n : ℕ => Tv n)
      = (fun n : ℕ => ∑ j ∈ Finset.range n, Q j) ∘ (fun n : ℕ => n + 1) := by
    funext n
    show Tv n = ∑ j ∈ Finset.range (n + 1), Q j
    exact Tv_eq_sum_Q n
  have h := hasSum_Q.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have : Tendsto (fun n : ℕ => Tv n) atTop (𝓝 Ttot) := by rwa [h2]
  exact this

/-- General limit lemmas for the shifted sequences. -/
theorem tendsto_Cv_add (k : ℕ) : Tendsto (fun n : ℕ => Cv (n + k)) atTop (𝓝 Ctot) :=
  tendsto_Cv.comp (tendsto_add_atTop_nat k)

theorem tendsto_Tv_add (k : ℕ) : Tendsto (fun n : ℕ => Tv (n + k)) atTop (𝓝 Ttot) :=
  tendsto_Tv.comp (tendsto_add_atTop_nat k)

/-! ## §2  The limit relations of the delay calculus -/

theorem moment_lim : Real.log 3 * Ctot + Ttot ≤ 4 - 3 * Real.log 3 := by
  have h1 : Tendsto (fun n : ℕ => 2 * Cv (n + 1)) atTop (𝓝 (2 * Ctot)) :=
    (tendsto_Cv_add 1).const_mul 2
  have h2 : Tendsto (fun n : ℕ => 4 - 3 * Real.log 3 + Cv n * (2 - Real.log 3) - Tv (n + 1))
      atTop (𝓝 (4 - 3 * Real.log 3 + Ctot * (2 - Real.log 3) - Ttot)) := by
    have A : Tendsto (fun n : ℕ => (4 - 3 * Real.log 3) + Cv n * (2 - Real.log 3)) atTop
        (𝓝 ((4 - 3 * Real.log 3) + Ctot * (2 - Real.log 3))) :=
      tendsto_const_nhds.add ((tendsto_Cv).mul_const (2 - Real.log 3))
    exact A.sub (tendsto_Tv_add 1)
  have h3 := le_of_tendsto_of_tendsto' h1 h2 (fun n => moment_ineq n)
  linarith

/-! ## §3  The numerical constants and the bounds they force on `Ctot`, `Ttot` -/

noncomputable def mK1 : ℝ := -1763 / 12 - (35137 / 9 : ℝ) * Real.log 2 + 2597 * Real.log 3
noncomputable def mK2 : ℝ := 97 / 12 - (221 / 3 : ℝ) * Real.log 2 + 39 * Real.log 3
noncomputable def mK3 : ℝ := -5 / 32 + (77 / 12 : ℝ) * Real.log 2 - (15 / 4 : ℝ) * Real.log 3
noncomputable def mC : ℝ := 49 / 96
noncomputable def mA4 : ℝ := -17 / 30 + (184 / 15 : ℝ) * Real.log 2 - (69 / 10 : ℝ) * Real.log 3
noncomputable def mKap : ℝ := -5 / 4 + (64 / 3 : ℝ) * Real.log 2 - 12 * Real.log 3

noncomputable def mA : ℝ := mK1 + mC * (1 - mA4)
noncomputable def mB : ℝ := 3 * mK1 + mK2 - 3 * mC * mA4 + 4 * mC * Real.log 2 - 2 * mC
noncomputable def mD : ℝ := 1 - mK3 + mC * Real.log 2
noncomputable def mK0 : ℝ := 4 - 3 * Real.log 3
noncomputable def mAl : ℝ := (3 * mKap + 2 - 4 * Real.log 2) / (1 - mKap)
noncomputable def mBe : ℝ := Real.log 2 / (1 - mKap)
noncomputable def mCmax : ℝ := (mK0 * mD - mB) / (mA + mD * Real.log 3)
noncomputable def mTmin : ℝ := (mA * mAl + mB) / (mD - mA * mBe)

theorem mass_lim :
    (3 + Ctot) * mK1 + Ttot * mK3 + mK2
      + mC * (Ctot - (3 + Ctot) * mA4 - (Ttot - 4) * Real.log 2 - 2) ≤ Ttot := by
  have hmass : ∀ n : ℕ, (3 + Cv n) * mK1 + Tv (n + 1) * mK3 + mK2
      + mC * (Cv (n + 1) - (3 + Cv n) * mA4 - (Tv (n + 1) - 4) * Real.log 2 - 2)
      ≤ Tv (n + 2) := fun n => by
    simpa [mK1, mK2, mK3, mC, mA4] using mass_ineq2 n
  have hL : Tendsto (fun n : ℕ => (3 + Cv n) * mK1 + Tv (n + 1) * mK3 + mK2
      + mC * (Cv (n + 1) - (3 + Cv n) * mA4 - (Tv (n + 1) - 4) * Real.log 2 - 2)) atTop
      (𝓝 ((3 + Ctot) * mK1 + Ttot * mK3 + mK2
        + mC * (Ctot - (3 + Ctot) * mA4 - (Ttot - 4) * Real.log 2 - 2))) := by
    have hA : Tendsto (fun n : ℕ => (3 + Cv n) * mK1) atTop (𝓝 ((3 + Ctot) * mK1)) :=
      (tendsto_const_nhds.add tendsto_Cv).mul tendsto_const_nhds
    have hB : Tendsto (fun n : ℕ => Tv (n + 1) * mK3) atTop (𝓝 (Ttot * mK3)) :=
      (tendsto_Tv_add 1).mul tendsto_const_nhds
    have hK2 : Tendsto (fun _ : ℕ => mK2) atTop (𝓝 mK2) := tendsto_const_nhds
    have hinner : Tendsto (fun n : ℕ =>
        Cv (n + 1) - (3 + Cv n) * mA4 - (Tv (n + 1) - 4) * Real.log 2 - 2) atTop
        (𝓝 (Ctot - (3 + Ctot) * mA4 - (Ttot - 4) * Real.log 2 - 2)) := by
      have i1 : Tendsto (fun n : ℕ => (3 + Cv n) * mA4) atTop (𝓝 ((3 + Ctot) * mA4)) :=
        (tendsto_const_nhds.add tendsto_Cv).mul tendsto_const_nhds
      have i2 : Tendsto (fun n : ℕ => (Tv (n + 1) - 4) * Real.log 2) atTop
          (𝓝 ((Ttot - 4) * Real.log 2)) :=
        ((tendsto_Tv_add 1).sub tendsto_const_nhds).mul tendsto_const_nhds
      exact (((tendsto_Cv_add 1).sub i1).sub i2).sub tendsto_const_nhds
    have h4 : Tendsto (fun n : ℕ =>
        mC * (Cv (n + 1) - (3 + Cv n) * mA4 - (Tv (n + 1) - 4) * Real.log 2 - 2)) atTop
        (𝓝 (mC * (Ctot - (3 + Ctot) * mA4 - (Ttot - 4) * Real.log 2 - 2))) :=
      tendsto_const_nhds.mul hinner
    exact ((hA.add hB).add hK2).add h4
  exact le_of_tendsto_of_tendsto' hL (tendsto_Tv_add 2) hmass

theorem Cv_lower_lim : (3 + Ctot) * mKap + (Ttot - 4) * Real.log 2 + 2 ≤ Ctot := by
  have hcv : ∀ n : ℕ, (3 + Cv n) * mKap + (Tv (n + 1) - 4) * Real.log 2 + 2 ≤ Cv (n + 1) :=
    fun n => by simpa [mKap] using Cv_lower n
  have hL : Tendsto (fun n : ℕ => (3 + Cv n) * mKap + (Tv (n + 1) - 4) * Real.log 2 + 2) atTop
      (𝓝 ((3 + Ctot) * mKap + (Ttot - 4) * Real.log 2 + 2)) := by
    have hA : Tendsto (fun n : ℕ => (3 + Cv n) * mKap) atTop (𝓝 ((3 + Ctot) * mKap)) :=
      (tendsto_const_nhds.add tendsto_Cv).mul tendsto_const_nhds
    have hB : Tendsto (fun n : ℕ => (Tv (n + 1) - 4) * Real.log 2) atTop
        (𝓝 ((Ttot - 4) * Real.log 2)) :=
      ((tendsto_Tv_add 1).sub tendsto_const_nhds).mul tendsto_const_nhds
    exact (hA.add hB).add_const 2
  exact le_of_tendsto_of_tendsto' hL (tendsto_Cv_add 1) hcv

/-! ### Rational bounds for the constants -/

private lemma mK1_bounds :
    (55836 / 1000000 : ℝ) ≤ mK1 ∧ mK1 ≤ (55840 / 1000000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_gt_d9
  have h4 := Real.log_three_lt_d9
  constructor <;> · rw [mK1]; linarith

private lemma mK2_bounds :
    (-132630 / 1000000 : ℝ) ≤ mK2 ∧ mK2 ≤ (-132629 / 1000000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_gt_d9
  have h4 := Real.log_three_lt_d9
  constructor <;> · rw [mK2]; linarith

private lemma mK3_bounds :
    (171648 / 1000000 : ℝ) ≤ mK3 ∧ mK3 ≤ (171649 / 1000000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_gt_d9
  have h4 := Real.log_three_lt_d9
  constructor <;> · rw [mK3]; linarith

private lemma mA4_bounds :
    (355513 / 1000000 : ℝ) ≤ mA4 ∧ mA4 ≤ (355514 / 1000000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_gt_d9
  have h4 := Real.log_three_lt_d9
  constructor <;> · rw [mA4]; linarith

private lemma mKap_bounds :
    (353792 / 1000000 : ℝ) ≤ mKap ∧ mKap ≤ (353793 / 1000000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_gt_d9
  have h4 := Real.log_three_lt_d9
  constructor <;> · rw [mKap]; linarith

private lemma mA_bounds :
    (3847923 / 10000000 : ℝ) ≤ mA ∧ mA ≤ (384797 / 1000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := mK1_bounds
  obtain ⟨h3, h4⟩ := mA4_bounds
  constructor <;> · rw [mA, mC]; linarith

private lemma mB_bounds :
    (-115161 / 1000000 : ℝ) ≤ mB ∧ mB ≤ (-115146 / 1000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := mK1_bounds
  obtain ⟨h3, h4⟩ := mK2_bounds
  obtain ⟨h5, h6⟩ := mA4_bounds
  have h7 := Real.log_two_gt_d9
  have h8 := Real.log_two_lt_d9
  constructor <;> · rw [mB, mC]; linarith

private lemma mD_bounds :
    (1182144 / 1000000 : ℝ) ≤ mD ∧ mD ≤ (1182146 / 1000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := mK3_bounds
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  constructor <;> · rw [mD, mC]; linarith

private lemma mK0_bounds :
    (704163 / 1000000 : ℝ) ≤ mK0 ∧ mK0 ≤ (704164 / 1000000 : ℝ) := by
  have h3 := Real.log_three_gt_d9
  have h4 := Real.log_three_lt_d9
  constructor <;> · rw [mK0]; linarith

private lemma mAl_bounds :
    (446895 / 1000000 : ℝ) ≤ mAl ∧ mAl ≤ (446901 / 1000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := mKap_bounds
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  have h5 : (0 : ℝ) < 1 - mKap := by linarith
  constructor
  · rw [mAl, le_div_iff₀ h5]; linarith
  · rw [mAl, div_le_iff₀ h5]; linarith

private lemma mBe_bounds :
    (1072637 / 1000000 : ℝ) ≤ mBe ∧ mBe ≤ (1072640 / 1000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := mKap_bounds
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  have h5 : (0 : ℝ) < 1 - mKap := by linarith
  constructor
  · rw [mBe, le_div_iff₀ h5]; linarith
  · rw [mBe, div_le_iff₀ h5]; linarith

private lemma mCmax_le : mCmax ≤ (563 / 1000 : ℝ) := by
  obtain ⟨hA1, hA2⟩ := mA_bounds
  obtain ⟨hB1, hB2⟩ := mB_bounds
  obtain ⟨hD1, hD2⟩ := mD_bounds
  obtain ⟨hK1, hK2⟩ := mK0_bounds
  have hK0pos : (0 : ℝ) < mK0 := by linarith
  have hDpos : (0 : ℝ) < mD := by linarith
  have hprod : mK0 * mD ≤ (704164 / 1000000 : ℝ) * (1182146 / 1000000 : ℝ) := by
    nlinarith [hK2, hD2, hK0pos, hDpos]
  have hnum : mK0 * mD - mB ≤ (947586 / 1000000 : ℝ) := by linarith
  have hden : (1683483 / 1000000 : ℝ) ≤ mA + mD * Real.log 3 := by
    have hy := Real.log_three_gt_d9
    nlinarith [hA1, hD1, hy]
  have hdenpos : (0 : ℝ) < mA + mD * Real.log 3 := by linarith
  rw [mCmax, div_le_iff₀ hdenpos]
  have h2 : (947586 / 1000000 : ℝ) ≤ (563 / 1000) * (1683483 / 1000000) := by norm_num
  nlinarith [hnum, hden, h2]

private lemma mTmin_ge : (738 / 10000 : ℝ) ≤ mTmin := by
  obtain ⟨hA1, hA2⟩ := mA_bounds
  obtain ⟨hB1, hB2⟩ := mB_bounds
  obtain ⟨hD1, hD2⟩ := mD_bounds
  obtain ⟨hL1, hL2⟩ := mAl_bounds
  obtain ⟨hE1, hE2⟩ := mBe_bounds
  have hnum : (56800 / 1000000 : ℝ) ≤ mA * mAl + mB := by
    have hp : (3847923 / 10000000 : ℝ) * (446895 / 1000000) ≤ mA * mAl := by
      nlinarith [hA1, hL1]
    have h2 : (56800 / 1000000 : ℝ) ≤ (3847923 / 10000000 : ℝ) * (446895 / 1000000)
        + (-115161 / 1000000 : ℝ) := by norm_num
    linarith
  have hden : mD - mA * mBe ≤ (769404 / 1000000 : ℝ) := by
    have hp : (3847923 / 10000000 : ℝ) * (1072637 / 1000000) ≤ mA * mBe := by
      nlinarith [hA1, hE1]
    linarith
  have hpos : (0 : ℝ) < mD - mA * mBe := by
    have hp : mA * mBe ≤ (384797 / 1000000 : ℝ) * (1072640 / 1000000) := by
      nlinarith [hA2, hE2]
    linarith
  rw [mTmin, le_div_iff₀ hpos]
  have h2 : (738 / 10000 : ℝ) * (769404 / 1000000) ≤ (56800 / 1000000 : ℝ) := by norm_num
  linarith

theorem Ctot_le_Cmax : Ctot ≤ mCmax := by
  have h1 : Real.log 3 * Ctot + Ttot ≤ mK0 := by rw [mK0]; exact moment_lim
  have h2 : mA * Ctot + mB ≤ mD * Ttot := by
    have h := mass_lim
    simp only [mA, mB, mD, mK1, mK2, mK3, mC, mA4] at h ⊢
    linarith
  obtain ⟨hA1, hA2⟩ := mA_bounds
  obtain ⟨hD1, hD2⟩ := mD_bounds
  have hDpos : (0 : ℝ) < mD := by linarith
  have hy := Real.log_three_gt_d9
  have hdenpos : (0 : ℝ) < mA + mD * Real.log 3 := by nlinarith [hA1, hD1, hy]
  rw [mCmax, le_div_iff₀ hdenpos]
  nlinarith [h1, h2, hDpos]

theorem Tmin_le_Ttot : mTmin ≤ Ttot := by
  have h2 : mA * Ctot + mB ≤ mD * Ttot := by
    have h := mass_lim
    simp only [mA, mB, mD, mK1, mK2, mK3, mC, mA4] at h ⊢
    linarith
  have h3 : mAl + mBe * Ttot ≤ Ctot := by
    have h := Cv_lower_lim
    have h1m : (0 : ℝ) < 1 - mKap := by
      obtain ⟨h1, h2⟩ := mKap_bounds
      linarith
    have key : (3 * mKap + 2 - 4 * Real.log 2) + Real.log 2 * Ttot ≤ Ctot * (1 - mKap) := by
      linarith [h]
    rw [mAl, mBe, div_mul_eq_mul_div, ← add_div, div_le_iff₀ h1m]
    exact key
  obtain ⟨hA1, hA2⟩ := mA_bounds
  have hApos : (0 : ℝ) < mA := by linarith
  obtain ⟨hD1, hD2⟩ := mD_bounds
  obtain ⟨hE1, hE2⟩ := mBe_bounds
  have hden : (0 : ℝ) < mD - mA * mBe := by
    have hp : mA * mBe ≤ (384797 / 1000000 : ℝ) * (1072640 / 1000000) := by
      nlinarith [hA2, hE2]
    linarith
  rw [mTmin, div_le_iff₀ hden]
  nlinarith [h2, h3, hApos]

/-! ## §4  The tail identity and the final comparison -/

/-- The total mass of the odd delay profiles above the level `x`; the tail of `∫ riPsi`. -/
noncomputable def Tail (x : ℝ) : ℝ := ∑' i, ∫ u in x..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u

/-- The limit of the integrated odd recursion:
`Ψ(x) = (3+Ctot)·A'(x) + (Ttot − 4)·log (x/2) + (x − 2)`. -/
noncomputable def PsiInt (x : ℝ) : ℝ :=
  (3 + Ctot) * Aprime x + (Ttot - 4) * Real.log (x / 2) + (x - 2)

theorem integral_eq_zero_of_support {i : ℕ} {a b : ℝ} (h : ((2 * i + 4 : ℕ) : ℝ) ≤ a)
    (hab : a ≤ b) :
    (∫ u in a..b, profC (2 * i + 1) u) = 0 := by
  refine (intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) (fun u hu => ?_)).trans ?_
  · rw [Set.uIcc_of_le hab, Set.mem_Icc] at hu
    exact profC_support (2 * i + 1) u (by push_cast at h ⊢; linarith [hu.1])
  · simp

theorem tail_int_nonneg (i : ℕ) {a : ℝ} (ha : 2 ≤ a) :
    0 ≤ ∫ u in a..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u := by
  rcases le_total a (((2 * i + 4 : ℕ)) : ℝ) with h | h
  · exact intervalIntegral.integral_nonneg_of_forall h (fun u => profC_nonneg _ _)
  · have hz : (∫ u in a..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u) = 0 := by
      rw [intervalIntegral.integral_symm (((2 * i + 4 : ℕ)) : ℝ) a,
        integral_eq_zero_of_support (i := i) (a := (((2 * i + 4 : ℕ)) : ℝ)) (b := a) le_rfl h,
        neg_zero]
    rw [hz]

theorem tail_term_nonneg (i : ℕ) (x : ℝ) :
    0 ≤ ∫ u in x..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u := by
  rcases le_total x (((2 * i + 4 : ℕ)) : ℝ) with h | h
  · exact intervalIntegral.integral_nonneg_of_forall h (fun u => profC_nonneg _ _)
  · have hz : (∫ u in x..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u) = 0 := by
      rw [intervalIntegral.integral_symm (((2 * i + 4 : ℕ)) : ℝ) x,
        integral_eq_zero_of_support (i := i) (a := (((2 * i + 4 : ℕ)) : ℝ)) (b := x) le_rfl h,
        neg_zero]
    rw [hz]

theorem Tail_nonneg (x : ℝ) : 0 ≤ Tail x :=
  tsum_nonneg (fun i => tail_term_nonneg i x)

theorem tail_int_le_P (i : ℕ) {a : ℝ} (ha : 2 ≤ a) :
    (∫ u in a..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u) ≤ P i := by
  rcases le_total a (((2 * i + 4 : ℕ)) : ℝ) with h | h
  · rw [P]
    have h1 : IntervalIntegrable (profC (2 * i + 1)) volume (2 : ℝ) a :=
      profC_intervalIntegrable _ _ _
    have h2 : IntervalIntegrable (profC (2 * i + 1)) volume a (((2 * i + 4 : ℕ)) : ℝ) :=
      profC_intervalIntegrable _ _ _
    have hnn : 0 ≤ ∫ u in (2 : ℝ)..a, profC (2 * i + 1) u :=
      intervalIntegral.integral_nonneg_of_forall ha (fun u => profC_nonneg _ _)
    linarith [intervalIntegral.integral_add_adjacent_intervals h1 h2]
  · rw [intervalIntegral.integral_symm (((2 * i + 4 : ℕ)) : ℝ) a,
      integral_eq_zero_of_support (i := i) (a := (((2 * i + 4 : ℕ)) : ℝ)) (b := a) le_rfl h,
      neg_zero]
    exact P_nonneg i

theorem abs_tail_int_le_P (i : ℕ) {a : ℝ} (ha : 2 ≤ a) :
    |∫ u in a..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u| ≤ P i := by
  rcases le_total a (((2 * i + 4 : ℕ)) : ℝ) with h | h
  · rw [abs_of_nonneg (tail_int_nonneg i ha)]
    exact tail_int_le_P i ha
  · rw [intervalIntegral.integral_symm (((2 * i + 4 : ℕ)) : ℝ) a,
      integral_eq_zero_of_support (i := i) (a := (((2 * i + 4 : ℕ)) : ℝ)) (b := a) le_rfl h,
      neg_zero, abs_zero]
    exact P_nonneg i

/-- Summability of the tail series `i ↦ ∫_a^{2i+4} profC (2i+1)` for `a ≥ 2`. -/
theorem tail_summable {a : ℝ} (ha : 2 ≤ a) :
    Summable (fun i : ℕ => ∫ u in a..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u) :=
  Summable.of_norm_bounded summable_P (fun i => by
    rw [Real.norm_eq_abs]
    exact abs_tail_int_le_P i ha)

theorem tail_int_le_P' (i : ℕ) {x : ℝ} (h2 : 2 ≤ x) (h4 : x ≤ 4) :
    (∫ u in (2 : ℝ)..x, profC (2 * i + 1) u) ≤ P i := by
  rw [P]
  have h1 : IntervalIntegrable (profC (2 * i + 1)) volume (2 : ℝ) x :=
    profC_intervalIntegrable _ _ _
  have h2' : IntervalIntegrable (profC (2 * i + 1)) volume x (((2 * i + 4 : ℕ)) : ℝ) :=
    profC_intervalIntegrable _ _ _
  have hxi : x ≤ (((2 * i + 4 : ℕ)) : ℝ) :=
    le_trans h4 (by push_cast; exact_mod_cast (by omega : 4 ≤ 2 * i + 4))
  have hnn : 0 ≤ ∫ u in x..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u :=
    intervalIntegral.integral_nonneg_of_forall hxi (fun u => profC_nonneg _ _)
  linarith [intervalIntegral.integral_add_adjacent_intervals h1 h2']

/-- Summability of the truncated series `i ↦ ∫_2^x profC (2i+1)` for `2 ≤ x ≤ 4`. -/
theorem Psi_summable {x : ℝ} (h2 : 2 ≤ x) (h4 : x ≤ 4) :
    Summable (fun i : ℕ => ∫ u in (2 : ℝ)..x, profC (2 * i + 1) u) :=
  Summable.of_nonneg_of_le
    (fun i => intervalIntegral.integral_nonneg_of_forall h2 (fun u => profC_nonneg _ _))
    (fun i => tail_int_le_P' i h2 h4) summable_P

theorem Tail_int_eq (i : ℕ) {a : ℝ} (ha : 2 ≤ a) :
    (∫ u in a..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u)
      = P i - ∫ u in (2 : ℝ)..a, profC (2 * i + 1) u := by
  have h1 : IntervalIntegrable (profC (2 * i + 1)) volume (2 : ℝ) a :=
    profC_intervalIntegrable _ _ _
  have h2 : IntervalIntegrable (profC (2 * i + 1)) volume a (((2 * i + 4 : ℕ)) : ℝ) :=
    profC_intervalIntegrable _ _ _
  have h := intervalIntegral.integral_add_adjacent_intervals h1 h2
  rw [P]
  linarith

theorem PsiInt_eq_tsum {x : ℝ} (h2 : 2 ≤ x) (h4 : x ≤ 4) :
    PsiInt x = ∑' i, ∫ u in (2 : ℝ)..x, profC (2 * i + 1) u := by
  have hsum := Psi_summable h2 h4
  have h1 : Tendsto (fun m : ℕ => ∫ u in (2 : ℝ)..x, oddSum (m + 1) u) atTop
      (𝓝 ((3 + Ctot) * Aprime x + (Ttot - 4) * Real.log (x / 2) + (x - 2))) := by
    have hA : Tendsto (fun m : ℕ => (3 + Cv m) * Aprime x) atTop
        (𝓝 ((3 + Ctot) * Aprime x)) :=
      (tendsto_const_nhds.add tendsto_Cv).mul tendsto_const_nhds
    have hB : Tendsto (fun m : ℕ => (Tv (m + 1) - 4) * Real.log (x / 2)) atTop
        (𝓝 ((Ttot - 4) * Real.log (x / 2))) :=
      ((tendsto_Tv_add 1).sub tendsto_const_nhds).mul tendsto_const_nhds
    have hAB : Tendsto (fun m : ℕ =>
        ((3 + Cv m) * Aprime x + (Tv (m + 1) - 4) * Real.log (x / 2)) + (x - 2)) atTop
        (𝓝 (((3 + Ctot) * Aprime x + (Ttot - 4) * Real.log (x / 2)) + (x - 2))) :=
      (hA.add hB).add_const (x - 2)
    have hfun : (fun m : ℕ => ∫ u in (2 : ℝ)..x, oddSum (m + 1) u)
        = fun m : ℕ =>
            ((3 + Cv m) * Aprime x + (Tv (m + 1) - 4) * Real.log (x / 2)) + (x - 2) := by
      funext m
      rw [oddSum_int_eq m h2 h4]
    rw [hfun]
    exact hAB
  have h2' : Tendsto (fun m : ℕ => ∫ u in (2 : ℝ)..x, oddSum (m + 1) u) atTop
      (𝓝 (∑' i, ∫ u in (2 : ℝ)..x, profC (2 * i + 1) u)) := by
    have hnat : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range (m + 2),
        ∫ u in (2 : ℝ)..x, profC (2 * i + 1) u) atTop
        (𝓝 (∑' i, ∫ u in (2 : ℝ)..x, profC (2 * i + 1) u)) :=
      hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
    have hfun : (fun m : ℕ => ∑ i ∈ Finset.range (m + 2),
        ∫ u in (2 : ℝ)..x, profC (2 * i + 1) u)
        = fun m : ℕ => ∫ u in (2 : ℝ)..x, oddSum (m + 1) u := by
      funext m
      rw [oddSum_eq_sum (m + 1)]
      exact (intervalIntegral.integral_finset_sum
        (fun i _ => profC_intervalIntegrable (2 * i + 1) _ _)).symm
    rwa [hfun] at hnat
  rw [PsiInt]
  exact tendsto_nhds_unique h1 h2'

theorem Tail_eq {x : ℝ} (h2 : 2 ≤ x) (h4 : x ≤ 4) : Tail x = Ctot - PsiInt x := by
  have hsum := Psi_summable h2 h4
  have h1 : Tail x = ∑' i, (P i - ∫ u in (2 : ℝ)..x, profC (2 * i + 1) u) := by
    rw [Tail]
    exact tsum_congr (fun i => Tail_int_eq i h2)
  rw [h1, Summable.tsum_sub summable_P hsum, PsiInt_eq_tsum h2 h4]
  rfl

theorem integral_oddSum_shift (m : ℕ) (a : ℝ) :
    (∫ u in a..(((2 * m + 4 : ℕ)) : ℝ), oddSum m u)
      = ∑ i ∈ Finset.range (m + 1),
          ∫ u in a..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u := by
  rw [oddSum_eq_sum m,
    intervalIntegral.integral_finset_sum (fun i _ => profC_intervalIntegrable (2 * i + 1) _ _)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have hle : (((2 * i + 4 : ℕ)) : ℝ) ≤ (((2 * m + 4 : ℕ)) : ℝ) := by
    push_cast; exact_mod_cast (by omega : 2 * i + 4 ≤ 2 * m + 4)
  have hz : (∫ u in (((2 * i + 4 : ℕ)) : ℝ)..(((2 * m + 4 : ℕ)) : ℝ),
      profC (2 * i + 1) u) = 0 :=
    integral_eq_zero_of_support (i := i) (a := (((2 * i + 4 : ℕ)) : ℝ))
      (b := (((2 * m + 4 : ℕ)) : ℝ)) le_rfl hle
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (profC_intervalIntegrable (2 * i + 1) a (((2 * i + 4 : ℕ)) : ℝ))
    (profC_intervalIntegrable (2 * i + 1) (((2 * i + 4 : ℕ)) : ℝ) (((2 * m + 4 : ℕ)) : ℝ))
  linarith [hadd, hz]

/-- `(3−s)⁺ = 0` for `s ≥ 3`. -/
theorem cut_three_sub {s : ℝ} (hs : 3 ≤ s) : (if s ≤ 3 then (3 - s) else 0) = 0 := by
  by_cases h : s ≤ 3
  · rw [if_pos h]; linarith
  · rw [if_neg h]

/-- **The key comparison.**  For `s ≥ 3`, `s · evenSum n s` is dominated by the tail `Tail a`
for every `a ∈ [2, s-1]`. -/
theorem evenSum_mul_le_Tail (n : ℕ) {s a : ℝ} (hs : 3 ≤ s) (ha : 2 ≤ a) (has : a ≤ s - 1) :
    s * evenSum n s ≤ Tail a := by
  rcases n with _ | m
  · have h0 : evenSum 0 s = 0 := by
      rw [evenSum, Finset.range_one, Finset.sum_singleton, profC_zero]
      by_cases h : s ≤ 3
      · rw [if_pos ⟨by linarith, h⟩]
        have hs3 : s = 3 := le_antisymm h hs
        rw [hs3]; norm_num
      · rw [if_neg (fun hh => h hh.2)]
    rw [h0, mul_zero]
    exact Tail_nonneg a
  · rw [Tail,
      evenSum_succ_mul m (by linarith : (1 : ℝ) ≤ s),
      cut_three_sub hs, max_eq_left (by linarith : (2 : ℝ) ≤ s - 1)]
    have hstep1 : (∫ u in (s - 1)..(((2 * m + 4 : ℕ)) : ℝ), oddSum m u)
        ≤ ∫ u in a..(((2 * m + 4 : ℕ)) : ℝ), oddSum m u := by
      have h := intervalIntegral.integral_add_adjacent_intervals
        (oddSum_intervalIntegrable m a (s - 1))
        (oddSum_intervalIntegrable m (s - 1) (((2 * m + 4 : ℕ)) : ℝ))
      have hnn : 0 ≤ ∫ u in a..(s - 1), oddSum m u :=
        intervalIntegral.integral_nonneg_of_forall has (fun u => oddSum_nonneg m u)
      linarith [h]
    have hstep2 : (∫ u in a..(((2 * m + 4 : ℕ)) : ℝ), oddSum m u)
        ≤ ∑' i, ∫ u in a..(((2 * i + 4 : ℕ)) : ℝ), profC (2 * i + 1) u := by
      rw [integral_oddSum_shift m a]
      exact (tail_summable ha).sum_le_tsum (Finset.range (m + 1))
        (fun i _ => tail_int_nonneg i ha)
    linarith [hstep1, hstep2]

/-! ### Summability of the profile series and the limit of the partial sums -/

theorem evenSum_le_six {s : ℝ} (hs : 1 ≤ s) (n : ℕ) : evenSum n s ≤ 6 := by
  have hs0 : (0 : ℝ) < s := by linarith
  rcases n with _ | m
  · rw [evenSum, Finset.range_one, Finset.sum_singleton]
    by_cases h3 : s ≤ 3
    · rw [profC_zero, if_pos ⟨hs, h3⟩, div_le_iff₀ hs0]
      linarith
    · rw [profC_zero, if_neg (fun h => h3 h.2)]
      norm_num
  · by_cases h3 : s ≤ 3
    · rw [evenSum_formula m hs h3, div_le_iff₀ hs0]
      have hCv := level_bounds.1 m
      linarith
    · have heq : evenSum (m + 1) s
          = (∫ u in (s - 1)..(((2 * m + 4 : ℕ)) : ℝ), oddSum m u) / s := by
        rw [eq_div_iff (ne_of_gt hs0), mul_comm]
        rw [evenSum_succ_mul m hs, if_neg h3, max_eq_left (by linarith : (2 : ℝ) ≤ s - 1)]
        ring
      rw [heq, div_le_iff₀ hs0]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (oddSum_intervalIntegrable m (s - 1) (2 : ℝ))
        (oddSum_intervalIntegrable m (2 : ℝ) (((2 * m + 4 : ℕ)) : ℝ))
      have hsym : (∫ u in (s - 1)..(2 : ℝ), oddSum m u)
          = -(∫ u in (2 : ℝ)..(s - 1), oddSum m u) :=
        intervalIntegral.integral_symm (2 : ℝ) (s - 1)
      have hnn : 0 ≤ ∫ u in (2 : ℝ)..(s - 1), oddSum m u :=
        intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => oddSum_nonneg m u)
      have hCv : (∫ u in (2 : ℝ)..(((2 * m + 4 : ℕ)) : ℝ), oddSum m u) = Cv m := rfl
      have hCvb := level_bounds.1 m
      linarith [hsplit, hsym, hnn, hCv, hCvb]

theorem summable_profC_even (s : ℝ) (hs : 1 ≤ s) : Summable (fun j : ℕ => profC (2 * j) s) := by
  refine summable_of_sum_range_le (f := fun j : ℕ => profC (2 * j) s) (c := 6)
    (fun j => profC_nonneg _ _) (fun n => ?_)
  rcases n with _ | m
  · simp
  · have h : (∑ j ∈ Finset.range (m + 1), profC (2 * j) s) = evenSum m s := rfl
    rw [h]
    exact evenSum_le_six hs m

theorem tendsto_evenSum (s : ℝ) (hs : 1 ≤ s) :
    Tendsto (fun n : ℕ => evenSum n s) atTop (𝓝 (riPhi s)) := by
  have hsum := summable_profC_even s hs
  have h2 : (fun n : ℕ => evenSum n s)
      = (fun n : ℕ => ∑ j ∈ Finset.range n, profC (2 * j) s) ∘ (fun n : ℕ => n + 1) := by
    funext n
    show evenSum n s = ∑ j ∈ Finset.range (n + 1), profC (2 * j) s
    rfl
  have h := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h3 : Tendsto (fun n : ℕ => evenSum n s) atTop (𝓝 (∑' j, profC (2 * j) s)) := by rwa [h2]
  rw [show riPhi s = ∑' j, profC (2 * j) s from rfl]
  exact h3

/-! ### The comparison with `envNum` -/

theorem envNum_ge {s : ℝ} (h3 : 3 ≤ s) (h5 : s ≤ 5) : Ctot - PsiInt (s - 1) ≤ envNum s := by
  have hx2 : (2 : ℝ) ≤ s - 1 := by linarith
  have hx4 : s - 1 ≤ 4 := by linarith
  have hA4 : Aprime (s - 1) ≤ 3576 / 10000 := by
    have h := Aprime_monoOn (show (s - 1) ∈ Set.Icc (2 : ℝ) 4 from ⟨hx2, hx4⟩)
      (show (4 : ℝ) ∈ Set.Icc (2 : ℝ) 4 by norm_num) hx4
    linarith [h, Aprime_four_le]
  have hC : Ctot ≤ 563 / 1000 := le_trans Ctot_le_Cmax mCmax_le
  have hT : (738 / 10000 : ℝ) ≤ Ttot := le_trans mTmin_ge Tmin_le_Ttot
  have hLle : Real.log ((s - 1) / 2) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  have hmin : min (s - 1) 4 = s - 1 := min_eq_left hx4
  rw [envNum, hmin, PsiInt, envC, envT]
  have h1 : (Ctot - 5692 / 10000) * (1 - Aprime (s - 1))
      ≤ (563 / 1000 - 5692 / 10000) * (1 - 3576 / 10000) := by
    have hc : Ctot - 5692 / 10000 ≤ 563 / 1000 - 5692 / 10000 := by linarith
    have hv : (1 : ℝ) - 3576 / 10000 ≤ 1 - Aprime (s - 1) := by linarith
    nlinarith [hc, hv]
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hLnn : (0 : ℝ) ≤ Real.log ((s - 1) / 2) := Real.log_nonneg (by linarith)
  have h2 : (-47 / 10000 : ℝ) * Real.log 2
      ≤ (Ttot - 785 / 10000) * Real.log ((s - 1) / 2) := by
    rcases le_total 0 (Ttot - 785 / 10000) with hc | hc
    · nlinarith [hc, hLnn, hlog2nn]
    · have ha : (Ttot - 785 / 10000) * Real.log 2
          ≤ (Ttot - 785 / 10000) * Real.log ((s - 1) / 2) :=
        mul_le_mul_of_nonpos_left hLle hc
      have hb : (-47 / 10000 : ℝ) * Real.log 2 ≤ (Ttot - 785 / 10000) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hlog2nn
      linarith
  have hz : (563 / 1000 - 5692 / 10000) * (1 - 3576 / 10000)
      + 47 / 10000 * Real.log 2 ≤ 0 := by
    nlinarith [hlog2]
  have key : (Ctot - 5692 / 10000) * (1 - Aprime (s - 1))
      + (785 / 10000 - Ttot) * Real.log ((s - 1) / 2) ≤ 0 := by
    linarith [h1, h2, hz]
  nlinarith [key]

/-! ### The main theorem -/

theorem riPhi_le_env (s : ℝ) (hs : 11 / 5 ≤ s) :
    Work.NumberTheory.Chen.APSwitchUpper.riPhi s
      ≤ Work.NumberTheory.Chen.APSwitchUpper.riPhiEnv s := by
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hCmax : Ctot ≤ (563 / 1000 : ℝ) := le_trans Ctot_le_Cmax mCmax_le
  have hlim := tendsto_evenSum s hs1
  rcases le_total s 3 with h3 | h3
  · have hb : ∀ n : ℕ, evenSum n s ≤ ((3 - s) + envC) / s := by
      intro n
      rcases n with _ | m
      · rw [evenSum, Finset.range_one, Finset.sum_singleton, profC_zero, if_pos ⟨hs1, h3⟩]
        have hspos : (0 : ℝ) < s := by linarith
        refine div_le_div_of_nonneg_right ?_ hspos.le
        have henv : (0 : ℝ) ≤ envC := by rw [envC]; norm_num
        linarith
      · rw [evenSum_formula m hs1 h3]
        have hspos : (0 : ℝ) < s := by linarith
        refine div_le_div_of_nonneg_right ?_ hspos.le
        have hcv : Cv m ≤ envC := by rw [envC]; linarith [Cv_le_Ctot m, hCmax]
        linarith
    have hle : riPhi s ≤ ((3 - s) + envC) / s := le_of_tendsto hlim (Eventually.of_forall hb)
    rwa [riPhiEnv_of_le_three h3]
  · rcases le_total s 5 with h5 | h5
    · have hx2 : (2 : ℝ) ≤ s - 1 := by linarith
      have hx4 : s - 1 ≤ 4 := by linarith
      have hb : ∀ n : ℕ, evenSum n s ≤ envNum s / s := by
        intro n
        have htail := evenSum_mul_le_Tail n h3 hx2 (le_refl (s - 1))
        rw [Tail_eq hx2 hx4] at htail
        have hs0 : (0 : ℝ) < s := by linarith
        rw [le_div_iff₀ hs0]
        have h := envNum_ge h3 h5
        linarith [htail, h]
      have hle : riPhi s ≤ envNum s / s := le_of_tendsto hlim (Eventually.of_forall hb)
      rwa [riPhiEnv_of_three_le h3]
    · have hb : ∀ n : ℕ, evenSum n s ≤ envNum 5 / s := by
        intro n
        have htail := evenSum_mul_le_Tail n (by linarith : (3 : ℝ) ≤ s)
          (by norm_num : (2 : ℝ) ≤ 4) (by linarith : (4 : ℝ) ≤ s - 1)
        rw [Tail_eq (by norm_num : (2 : ℝ) ≤ 4) le_rfl] at htail
        have hs0 : (0 : ℝ) < s := by linarith
        rw [le_div_iff₀ hs0]
        have hcomp : Ctot - PsiInt 4 ≤ envNum 5 := by
          have h := envNum_ge (by norm_num : (3 : ℝ) ≤ 5) (le_refl 5)
          norm_num at h
          linarith
        linarith [htail, hcomp]
      have hle : riPhi s ≤ envNum 5 / s := le_of_tendsto hlim (Eventually.of_forall hb)
      rwa [riPhiEnv_of_five_le h5]
