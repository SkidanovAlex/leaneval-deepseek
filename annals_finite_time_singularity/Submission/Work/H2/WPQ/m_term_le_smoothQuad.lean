import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.HkIntegrand_zmul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

theorem HkIntegrand_zmul_le (α : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] a z| ≤ K) →
      Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => a z) →
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (fun z θ => a z * f z θ) z θ
          ≤ C * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ := by
  refine ⟨(((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1,
    by positivity, ?_⟩
  intro a K hK hKa ha f hf z hz θ hθ
  -- basic facts at the point `(z,θ)`
  have hzpos : 0 < z := hz
  have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    linarith
  have hQnn : 0 ≤ Work.Spaces.HkIntegrand α n f z θ :=
    Work.Spaces.HkIntegrand_nonneg α n f z θ
  -- the binomial coefficients are bounded by `2^n`
  have hchoose : ∀ (m b : ℕ), m ≤ n → |((m.choose b : ℕ) : ℝ)| ≤ (2 : ℝ) ^ n := by
    intro m b hmn
    calc |((m.choose b : ℕ) : ℝ)| = ((m.choose b : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      _ ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_two_pow m b
      _ = (2 : ℝ) ^ m := by push_cast; ring
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hmn
  -- a partial sum of the first (radial) block is bounded by the whole integrand
  have hzsum : ∀ i : ℕ, i ≤ n →
      (∑ m ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ Work.Spaces.HkIntegrand α n f z θ := by
    intro i hin
    rw [Work.Spaces.HkIntegrand]
    have hsub : (∑ m ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (∑ m ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro m hm
          have hm' : m < i + 1 := Finset.mem_range.mp hm
          exact Finset.mem_range.mpr (by omega))
        (fun m _ _ => sq_nonneg _)
    exact le_trans hsub (le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α n f z θ))
  -- a partial sum of the second (mixed) block is bounded by `(j+1)` integrands
  have hmsum : ∀ i j : ℕ, 1 ≤ i → i + j ≤ n →
      (∑ m ∈ Finset.range (j + 1),
        (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ((j : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ := by
    intro i j hi1 hij
    calc (∑ m ∈ Finset.range (j + 1),
          (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∑ _m ∈ Finset.range (j + 1), Work.Spaces.HkIntegrand α n f z θ :=
          Finset.sum_le_sum fun m hm => by
            have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            exact Work.Spaces.sq_le_HkIntegrand_mixed α n f z θ i m hi1 (by omega)
      _ = ((j : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- the two blocks of the left-hand side are handled separately
  have hZi : (∑ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => a z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
          * Work.Spaces.HkIntegrand α n f z θ := by
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => a z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
            * Work.Spaces.HkIntegrand α n f z θ := by
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      -- Leibniz for `D_z^i (a · f)`
      have hleib : Work.Spaces.DzIter i (fun z θ => a z * f z θ) z θ
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] a z * Work.Spaces.DzIter (i - b) f z θ) := by
        have h := Work.FTS.LocData.DzIter_mul_smoothQuad i (fun z θ : ℝ => a z) f
          (z := z) (θ := θ) hzIz (ha.curry_z hθ) (hf.curry_z hθ)
        rw [h]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [congrFun (Work.FTS.LocData.Zop_iterate_slice b (fun z θ : ℝ => a z) θ) z]
      -- multiply by the weight and distribute
      have hmul : Work.Spaces.DzIter i (fun z θ => a z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] a z * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
        rw [hleib, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [hmul]
      -- Cauchy–Schwarz on the binomial convolution
      have hbin := binom_sum_sq_le (i := i) (D := (2 : ℝ) ^ n) (K := K) hK
        (x := fun b => Work.Spaces.Zop^[b] a z)
        (y := fun m => Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (fun b hb => hKa b (le_trans hb hin) z hz)
        (fun b hb => hchoose i b hin)
      have hbin' : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.Zop^[b] a z * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          ≤ (((i : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
              * (∑ m ∈ Finset.range (i + 1),
                  (Work.Spaces.DzIter m f z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ))
                        ^ (Work.Spaces.eta / 2))) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hbin
      refine le_trans hbin' ?_
      have hconst : (((i : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
          ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2 := by
        have hbase : ((i : ℝ) + 1) * (2 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right
            (by
              have : (i : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hin
              linarith)
            (by positivity)
        have hle : ((i : ℝ) + 1) * (2 : ℝ) ^ n * K ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n * K :=
          mul_le_mul_of_nonneg_right hbase hK
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK) hle 2
      exact mul_le_mul hconst (hzsum i hin) (Finset.sum_nonneg fun m _ => sq_nonneg _)
        (by positivity)
    calc (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i (fun z θ => a z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (n + 1), ((((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
            * Work.Spaces.HkIntegrand α n f z θ) := Finset.sum_le_sum hterm
      _ = (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
            * Work.Spaces.HkIntegrand α n f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hMi : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (((n : ℝ) + 1) ^ 3 * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
          * Work.Spaces.HkIntegrand α n f z θ := by
    have hsummand : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
            * Work.Spaces.HkIntegrand α n f z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ n
      · rw [if_pos hc]
        obtain ⟨hi1, hij⟩ := hc
        have hin : i ≤ n := by omega
        have hjn : j ≤ n := by omega
        -- Leibniz for `D_z^j D_θ^i (a · f)`
        have hexp : Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] a z * Work.Spaces.mixed (j - b) i f z θ) :=
          mixed_zmul j i a f hzIoi hθ ha hf
        have hmul : Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
              * Work.Spaces.Wt α z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] a z
                    * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ)) := by
          rw [hexp, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [hmul]
        have hbin := binom_sum_sq_le (i := j) (D := (2 : ℝ) ^ n) (K := K) hK
          (x := fun b => Work.Spaces.Zop^[b] a z)
          (y := fun m => Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ)
          (fun b hb => hKa b (le_trans hb hjn) z hz)
          (fun b hb => hchoose j b hjn)
        have hbin' : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] a z * (Work.Spaces.mixed (j - b) i f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2
            ≤ (((j : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
                * (∑ m ∈ Finset.range (j + 1),
                    (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hbin
        refine le_trans hbin' ?_
        have hconst : (((j : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
            ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2 := by
          have hbase : ((j : ℝ) + 1) * (2 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right
              (by
                have : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hjn
                linarith)
              (by positivity)
          have hle : ((j : ℝ) + 1) * (2 : ℝ) ^ n * K ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n * K :=
            mul_le_mul_of_nonneg_right hbase hK
          exact pow_le_pow_left₀
            (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK) hle 2
        have hA : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          have : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hjn
          linarith
        have hAZ : 0 ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2 := by positivity
        calc (((j : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
              * (∑ m ∈ Finset.range (j + 1),
                  (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
                * (((j : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ) :=
              mul_le_mul hconst (hmsum i j hi1 hij)
                (Finset.sum_nonneg fun m _ => sq_nonneg _) hAZ
          _ ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
                * (((n : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hQnn) hAZ
          _ = (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
                * Work.Spaces.HkIntegrand α n f z θ := by ring
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hQnn
    calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n
            then (Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ _i ∈ Finset.range (n + 1), ∑ _j ∈ Finset.range (n + 1),
            ((((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
              * Work.Spaces.HkIntegrand α n f z θ) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hsummand i hi j hj
      _ = (((n : ℝ) + 1) ^ 3 * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
            * Work.Spaces.HkIntegrand α n f z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- add the two blocks
  conv_lhs => rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hZi hMi) ?_
  have hKsq : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith [hK]
  have hkey : (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
        * Work.Spaces.HkIntegrand α n f z θ
      + (((n : ℝ) + 1) ^ 3 * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
        * Work.Spaces.HkIntegrand α n f z θ
      = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * K ^ 2
        * Work.Spaces.HkIntegrand α n f z θ := by ring
  rw [hkey]
  have h0 : 0 ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) := by
    positivity
  have hstep1 : ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * K ^ 2
        * Work.Spaces.HkIntegrand α n f z θ
      ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α n f z θ := by
    calc ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * K ^ 2
          * Work.Spaces.HkIntegrand α n f z θ
        = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2)
            * (K ^ 2 * Work.Spaces.HkIntegrand α n f z θ) := by ring
      _ ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2)
            * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKsq hQnn) h0
      _ = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * (1 + K) ^ 2
            * Work.Spaces.HkIntegrand α n f z θ := by ring
  refine le_trans hstep1 ?_
  have h1 : 0 ≤ (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ :=
    mul_nonneg (by positivity) hQnn
  calc ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α n f z θ
      = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) := by ring
    _ ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) :=
        mul_le_mul_of_nonneg_right (by linarith) h1
    _ = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1) * (1 + K) ^ 2
          * Work.Spaces.HkIntegrand α n f z θ := by ring

end Work.FTS.CoercivityFix.E2Bound
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zmul_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/


/-- `|i.choose b| ≤ 2^n` in `ℝ` whenever `i ≤ n`. -/
private lemma choose_cast_abs_le (n i b : ℕ) (hbn : i ≤ n) :
    |((i.choose b : ℕ) : ℝ)| ≤ (2 : ℝ) ^ n := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 : i.choose b ≤ 2 ^ n :=
    le_trans (Nat.choose_le_two_pow i b) (Nat.pow_le_pow_right (by norm_num) hbn)
  have h2 : ((i.choose b : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := Nat.cast_le.mpr h1
  have h3 : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  linarith



/-! ## The pure `D_z` sum -/


/-! ## The mixed sum -/


/-! ## The requested lemma -/


end Work.FTS.CoercivityFix.E2Bound.SlotMul
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zrev_at_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Auxiliary lemmas -/




/-! ## The requested lemma -/


end Work.FTS.CoercivityFix.E2Bound.SlotMul
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeColl.limitBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeColl


end Work.FTS.EllipticEst.AeColl
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_A_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Upsi_A_integrable` — the `A`-slot domination lemma

The target of this file is

`Work.FTS.EllipticEst.AeI1Fts.Upsi_A_integrable`,

the `z`-integrability of `z ↦ w z ^ 2 · χ z · ∫_θ (U u z θ · ψ θ) ^ 2 · sin(2θ)^{-η}` from
`HkMem α 0 (grad u)` (`U u = grad u` definitionally) plus a bound on `ψ`.

## Where the difficulty is

The *value* part of the statement is elementary: on `Iθ` the level-`0` `H^k`-integrand of
`U u` is `w z ^ 2 · (U u z θ) ^ 2 · sin(2θ)^{-η}` (`HkIntegrand_zero_U` below), so

`w z ^ 2 · χ z · ∫_θ (U u · ψ) ^ 2 σ ≤ Cχ · Cψ · ∫_θ HkIntegrand α 0 (U u) z θ`

for every `z ∈ Iz`, and the right-hand side is `z`-integrable by `HkMem.2`.

The obstacle is the *measurability* half of `MeasureTheory.Integrable`: Mathlib defines
`Integrable f μ := AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ`, so the conclusion of
`Upsi_A_integrable` requires `AEStronglyMeasurable` of the slice-integral.  The hypotheses of
`Upsi_A_integrable` do not give it:

* `HkMem α 0 (grad u)` is a purely *slicewise* statement (for each `z` the `θ`-slice of
  `(U u) ^ 2 · w ^ 2 · σ` is integrable, and the `z`-marginal of that slice integral is
  integrable).  It gives no joint measurability of `(z,θ) ↦ (U u z θ) ^ 2 · w z ^ 2 · σ z θ`
  (nothing at all is assumed about the measurability of `u` itself), and
* `hψ` is only a pointwise bound on `Iθ`, so `ψ` need not be measurable.

`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` — the tool every sibling domination
lemma of this development uses — requires the *joint* a.e. strong measurability of the integrand,
which the sibling `Upsi_P_integrable` obtains precisely from its extra hypothesis
`Work.FTS.EllipticEst.SmoothOpen u`; the `A`-version has no such hypothesis.

## What is proved here

`Upsi_A_integrable_of_smooth` is the same statement with the two measurability hypotheses that
make it true: joint measurability of the datum (`SmoothOpen u`) and measurability of `ψ`
(`Measurable ψ`).  With those, the proof is the value bound above plus the standard
`aesm_of_continuousOn_Qd` ∘ `integral_prod_right'` measurability chain.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 800000




end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.pointwise_ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise identity `(†)` of the `I₁` bound, in the weak class

With `u` of class `C³` on the **open** quadrant `qd = (0,∞) × (0,π/2)` and the vocabulary of
`AeI1Fts/Defs` (`U u = z ∂_z u`, `AA u = z²∂_zz u`, `BB u = ∂_θθ u`, `Hh u = z ∂_z ∂_θθ u`,
`w z = (1+z)²/z²`, `cw z = 2(z-1)/(1+z)`), the elementary product rule

`∂_z(z · U·B·w²) = w²·(A·B + cw·U·B + U·H)`

holds at every `(z,θ)` with `z > 0`, `θ ∈ (0,π/2)`.  Indeed the left-hand side is

`((2U + A)·B + U·H)·w² + (U·B)·2 z w w'`,

and the identity `2 + 2 z (w'/w) = cw` (equivalently `(w²)'·z/w² = -4/(1+z)`) collects the
`U·B`-terms into the drift `cw·U·B` of the right-hand side.  This file contains the pointwise
calculus only: the slice derivatives of `u` are supplied by the joint `C³` hypothesis through the
`Fréchet`-derivative description of the curried partials.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false



/-- `Work.Spaces.pth` lowers the order of smoothness by one on an open set, because the curried
`θ`-partial is the composition of the Fréchet derivative with the evaluation at `(0,1)`. -/
private theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (n := (n + 1 : ℕ)) (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain



end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.AeI1MixedDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-! ## The slots -/

/-- `U u = z ∂_z u` (definitionally `H2W.Ae.grad u`). -/
def i1U (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ




/-- `B u = ∂_θθ u` (definitionally `H2W.Ae.ang2 u`). -/
def i1B (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u


/-! ## The angular weights (the tree's own `sig` / `sig2`) -/




/-! ## The 1-D slice flux -/


/-! ## The `z`-slice integrals of the `θ`-outer bookkeeping -/







end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngClean.I1_ibp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# The radial integration by parts of `I₁` (`Work.FTS.EllipticEst.AngSecond.I1_ibp_identity`)

Removing the cut-off `χ_n` from the cut-off identity `I1_cutoff_identity` gives the honest
identity

  `IP (z²∂_zzΨ) (∂_θθΨ) = - IP (z∂_zΨ) (z ∂_z∂_θθΨ) - IP (z∂_zΨ) (cw · ∂_θθΨ)`,

`cw z = 2(z-1)/(1+z)`, which is the point where the `z`-derivative of the paper's `I₁` is moved
onto the other factor.  Every step is a dominated-convergence limit in `n` of the corresponding
object of the cut-off identity, the dominating functions being the `z`-integrands of the
`IPMem`-honest pairings.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Real ContDiff

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-! ## The `z`-integrands of the pairings -/

/-- The integrand of the `θ`-inner integral of `IP (z²∂_zzΨ) (∂_θθΨ)`. -/
def Akern (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ

/-- The `z`-integrand of `IP (G Ψ) (Φ Ψ)`. -/
def Phi1 (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z

/-- The `z`-integrand of `IP (G Ψ) (H Ψ)`. -/
def BHfun (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, sig θ * (G Ψ z θ * H Ψ z θ) * w2 z

/-- The `z`-integrand of `IP (G Ψ) (cw · Φ Ψ)`. -/
def Cwfun (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, sig θ * (G Ψ z θ * (cw z * Phi Ψ z θ)) * w2 z

/-- The `θ`-integrand of the `z`-integrand `Bfun` of the limit of the right-hand side of the
cut-off identity (`χ_n → 1`). -/
def Ainner (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  sig θ * w2 z * (2 * G Ψ z θ * Phi Ψ z θ + G Ψ z θ * H Ψ z θ
    - 4 * G Ψ z θ * Phi Ψ z θ / (1 + z))

/-- The limit of the `z`-integrand of the right-hand side of the cut-off identity. -/
def Bfun (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Ainner Ψ z θ

/-- The `z`-outer function of the right-hand side of the cut-off identity. -/
def nfun (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, sig θ * nice n Ψ z θ

/-- The `z`-integrand of `IP (z²∂_zzΨ) (∂_θθΨ)`. -/
def Afun (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, Akern Ψ z θ

/-! ## Membership of the cut-off transition regions -/


/-- Almost every `z ∈ Iz` is positive. -/
theorem ae_pos_of_Iz : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
  have hdiff : ∀ᵐ z ∂(volume : MeasureTheory.Measure ℝ), z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hdiff,
    ae_restrict_mem measurableSet_Ici] with z hz hzI
  exact lt_of_le_of_ne hzI (Ne.symm hz)

/-! ## Integrability of the cut-off factors -/

theorem integrableOn_cut_mul {X : ℝ → ℝ} (hX : IntegrableOn X Work.Spaces.Iz) (n : ℕ) :
    IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z * X z) Work.Spaces.Iz := by
  refine (hX.norm).mono' ?_ ?_
  · exact ((cut_contDiff n).continuous.aestronglyMeasurable.mul hX.aestronglyMeasurable)
  · filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr
      ⟨by linarith [Work.FTS.EllipticEst.cut_nonneg n z],
       Work.FTS.EllipticEst.cut_le_one n z⟩)

theorem integrableOn_cutDeriv_mul {X : ℝ → ℝ} (hX : IntegrableOn X Work.Spaces.Iz) (n : ℕ) :
    IntegrableOn (fun z => X z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) Work.Spaces.Iz := by
  obtain ⟨K, hKpos, hKbound, -, -⟩ := cut_deriv_uniform
  refine (hX.norm.const_mul K).mono' ?_ ?_
  · exact (hX.aestronglyMeasurable.mul
      ((continuous_id.mul (continuous_deriv_cut n)).aestronglyMeasurable))
  · filter_upwards with z
    simp only [Real.norm_eq_abs, abs_mul]
    calc |X z| * (|z| * |deriv (Work.FTS.EllipticEst.cut n) z|)
        = |X z| * |z * deriv (Work.FTS.EllipticEst.cut n) z| := by rw [abs_mul]
      _ ≤ |X z| * K := mul_le_mul_of_nonneg_left (hKbound n z) (abs_nonneg _)
      _ = K * |X z| := by ring

/-! ## The two dominated-convergence limits -/

theorem tendsto_setIntegral_cut_mul {X : ℝ → ℝ} (hX : IntegrableOn X Work.Spaces.Iz) :
    Filter.Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.cut n z * X z) Filter.atTop
      (nhds (∫ z in Work.Spaces.Iz, X z)) := by
  obtain ⟨K, hKpos, hKbound, hKtend, -⟩ := cut_deriv_uniform
  have hbound : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ‖Work.FTS.EllipticEst.cut n z * X z‖ ≤ ‖X z‖ := by
    intro n
    filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr
      ⟨by linarith [Work.FTS.EllipticEst.cut_nonneg n z],
       Work.FTS.EllipticEst.cut_le_one n z⟩)
  have hlim : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z * X z) Filter.atTop
        (nhds (X z)) := by
    filter_upwards [ae_pos_of_Iz] with z hz
    have h := (hKtend z hz).mul_const (X z)
    simpa using h
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iz) (F := fun n z =>
      Work.FTS.EllipticEst.cut n z * X z) (f := X) (fun z => ‖X z‖)
    (fun n => (cut_contDiff n).continuous.aestronglyMeasurable.mul hX.aestronglyMeasurable)
    hX.norm hbound hlim
  simpa using hmain

theorem tendsto_setIntegral_cutDeriv_mul {X : ℝ → ℝ} (hX : IntegrableOn X Work.Spaces.Iz) :
    Filter.Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        X z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) Filter.atTop (nhds 0) := by
  obtain ⟨K, hKpos, hKbound, -, hKderiv⟩ := cut_deriv_uniform
  have hbound : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ‖X z * (z * deriv (Work.FTS.EllipticEst.cut n) z)‖ ≤ K * ‖X z‖ := by
    intro n
    filter_upwards with z
    simp only [Real.norm_eq_abs, abs_mul]
    calc |X z| * (|z| * |deriv (Work.FTS.EllipticEst.cut n) z|)
        = |X z| * |z * deriv (Work.FTS.EllipticEst.cut n) z| := by rw [abs_mul]
      _ ≤ |X z| * K := mul_le_mul_of_nonneg_left (hKbound n z) (abs_nonneg _)
      _ = K * |X z| := by ring
  have hlim : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun n : ℕ => X z * (z * deriv (Work.FTS.EllipticEst.cut n) z))
        Filter.atTop (nhds 0) := by
    filter_upwards with z
    have h := (hKderiv z).const_mul (X z)
    simpa using h
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iz) (F := fun n z =>
      X z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) (f := fun _ => (0 : ℝ))
    (fun z => K * ‖X z‖)
    (fun n => hX.aestronglyMeasurable.mul
      ((continuous_id.mul (continuous_deriv_cut n)).aestronglyMeasurable))
    (hX.norm.const_mul K) hbound hlim
  simpa using hmain

/-! ## Pointwise identities for the `z`-integrands -/

theorem measurable_cw : Measurable cw := by
  unfold cw; measurability

theorem cw_eq {z : ℝ} (hz : 0 ≤ z) : cw z = 2 - 4 / (1 + z) := by
  have h1 : (1 : ℝ) + z ≠ 0 := by positivity
  rw [cw]
  field_simp
  ring

theorem abs_cw_le_two {z : ℝ} (hz : 0 ≤ z) : |cw z| ≤ 2 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : |z - 1| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [cw, abs_div, abs_mul, abs_of_pos h1]
  rw [div_le_iff₀ h1]
  have h3 : |(2 : ℝ)| = 2 := by norm_num
  rw [h3]
  linarith

theorem integrableOn_aInner (Ψ : ℝ → ℝ → ℝ) (hUφ : IPMem (G Ψ) (Phi Ψ))
    (hUH : IPMem (G Ψ) (H Ψ)) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (Ainner Ψ z) Work.Spaces.Iθ := by
  have hmGφ : IntegrableOn (fun θ => sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hUφ.1 z hz) ?_ measurableSet_Icc
    intro θ _; ring
  have hmGH : IntegrableOn (fun θ => sig θ * (G Ψ z θ * H Ψ z θ) * w2 z)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hUH.1 z hz) ?_ measurableSet_Icc
    intro θ _; ring
  have h1 : IntegrableOn (fun θ => (2 : ℝ) * (sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z))
      Work.Spaces.Iθ := hmGφ.const_mul 2
  have h3 : IntegrableOn (fun θ => (4 / (1 + z)) * (sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z))
      Work.Spaces.Iθ := hmGφ.const_mul _
  refine MeasureTheory.IntegrableOn.congr_fun ((h1.add hmGH).sub h3) ?_ measurableSet_Icc
  intro θ _
  simp only [Ainner, G, Phi, H, Pi.add_apply, Pi.sub_apply]
  ring

/-- The `θ`-inner integral of the cut-off identity, written through the two `z`-integrands. -/
theorem nfun_eq (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hUφ : IPMem (G Ψ) (Phi Ψ))
    (hUH : IPMem (G Ψ) (H Ψ)) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    nfun n Ψ z = Work.FTS.EllipticEst.cut n z * Bfun Ψ z
      + Phi1 Ψ z * (z * deriv (Work.FTS.EllipticEst.cut n) z) := by
  have hmGφ : IntegrableOn (fun θ => sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hUφ.1 z hz) ?_ measurableSet_Icc
    intro θ _; ring
  have hAint := integrableOn_aInner Ψ hUφ hUH hz
  rw [nfun, Bfun, Phi1]
  rw [show (∫ θ in Work.Spaces.Iθ, sig θ * nice n Ψ z θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.cut n z * Ainner Ψ z θ
          + (z * deriv (Work.FTS.EllipticEst.cut n) z)
            * (sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z)) from
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
        simp only [nice, Ainner, G, Phi, H]; ring)]
  rw [MeasureTheory.integral_add (hAint.const_mul _) (hmGφ.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  ring

/-- The limit `Bfun` of the `z`-integrand of the right-hand side of the cut-off identity. -/
theorem Bfun_eq (Ψ : ℝ → ℝ → ℝ) (hUφ : IPMem (G Ψ) (Phi Ψ)) (hUH : IPMem (G Ψ) (H Ψ))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    Bfun Ψ z = cw z * Phi1 Ψ z + BHfun Ψ z := by
  have hmGφ : IntegrableOn (fun θ => sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hUφ.1 z hz) ?_ measurableSet_Icc
    intro θ _; ring
  have hmGH : IntegrableOn (fun θ => sig θ * (G Ψ z θ * H Ψ z θ) * w2 z)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hUH.1 z hz) ?_ measurableSet_Icc
    intro θ _; ring
  rw [Bfun, Phi1, BHfun]
  rw [show (∫ θ in Work.Spaces.Iθ, Ainner Ψ z θ)
      = ∫ θ in Work.Spaces.Iθ, (cw z * (sig θ * (G Ψ z θ * Phi Ψ z θ) * w2 z)
          + sig θ * (G Ψ z θ * H Ψ z θ) * w2 z) from
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
        simp only [Ainner, G, Phi, H]; rw [cw_eq hz]; ring)]
  rw [MeasureTheory.integral_add (hmGφ.const_mul _) hmGH,
    MeasureTheory.integral_const_mul]

/-! ## Integrability of the `z`-integrands, from the `IPMem` hypotheses -/

theorem integrableOn_Afun (Ψ : ℝ → ℝ → ℝ)
    (hQ : IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ)) :
    IntegrableOn (Afun Ψ) Work.Spaces.Iz := by
  refine MeasureTheory.IntegrableOn.congr_fun hQ.2 ?_ measurableSet_Ici
  intro z _
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => by simp only [Akern])

theorem integrableOn_Phi1 (Ψ : ℝ → ℝ → ℝ) (hUφ : IPMem (G Ψ) (Phi Ψ)) :
    IntegrableOn (Phi1 Ψ) Work.Spaces.Iz := by
  refine MeasureTheory.IntegrableOn.congr_fun hUφ.2 ?_ measurableSet_Ici
  intro z _
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

theorem integrableOn_BHfun (Ψ : ℝ → ℝ → ℝ) (hUH : IPMem (G Ψ) (H Ψ)) :
    IntegrableOn (BHfun Ψ) Work.Spaces.Iz := by
  refine MeasureTheory.IntegrableOn.congr_fun hUH.2 ?_ measurableSet_Ici
  intro z _
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

theorem integrableOn_cwPhi1 (Ψ : ℝ → ℝ → ℝ) (hPhi1 : IntegrableOn (Phi1 Ψ) Work.Spaces.Iz) :
    IntegrableOn (fun z => cw z * Phi1 Ψ z) Work.Spaces.Iz := by
  refine (hPhi1.norm.const_mul 2).mono' ?_ ?_
  · exact measurable_cw.aestronglyMeasurable.mul hPhi1.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    simp only [Real.norm_eq_abs, abs_mul]
    calc |cw z| * |Phi1 Ψ z| ≤ 2 * |Phi1 Ψ z| :=
          mul_le_mul_of_nonneg_right (abs_cw_le_two hz) (abs_nonneg _)
      _ = 2 * ‖Phi1 Ψ z‖ := by rw [Real.norm_eq_abs]

theorem integrableOn_Bfun (Ψ : ℝ → ℝ → ℝ) (hUφ : IPMem (G Ψ) (Phi Ψ))
    (hUH : IPMem (G Ψ) (H Ψ)) : IntegrableOn (Bfun Ψ) Work.Spaces.Iz := by
  have h1 := integrableOn_cwPhi1 Ψ (integrableOn_Phi1 Ψ hUφ)
  have h2 := integrableOn_BHfun Ψ hUH
  refine MeasureTheory.IntegrableOn.congr_fun (h1.add h2) ?_ measurableSet_Ici
  intro z hz
  exact (Bfun_eq Ψ hUφ hUH hz).symm

/-! ## The cut-off identity in the language of the `z`-integrands -/

theorem IP_cut_eq (n : ℕ) (Ψ : ℝ → ℝ → ℝ) :
    IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
        (Work.Spaces.pthIter 2 Ψ)
      = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Afun Ψ z := by
  rw [IP]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [show (∫ θ in Work.Spaces.Iθ, (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        * Work.FTS.EllipticEst.cut n z) z θ * (Work.Spaces.pthIter 2 Ψ) z θ * w2 z * sig θ)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.cut n z
          * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * Work.Spaces.pthIter 2 Ψ z θ
              * w2 z * sig θ) from
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]
  rfl

/-! ## The limit `n → ∞` -/


end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg

set_option autoImplicit false

/-- `κ = (1-η)/(1+η)`, the constant of the target. -/
def kap : ℝ := (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)

/-- **The a.e. mixed honesty** `(H1)+(H2)` of the target, as a single `Prop`: for a.e. `z` the
angular slice of `V = z∂_z∂_θu` is `σ`-honest, and the (unweighted) `z`-integral of the slice
energy is finite. -/
def MixedHon (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz

/-- **The a.e. endpoint rate of the slices of `U = z∂_zu`** (the analytic input of the collar
bound): for a.e. `z`, `(z∂_zu(z,·))²` is controlled by `θ^{1+η}` (resp. `(π/2-θ)^{1+η}`) times
the partial `σ`-energy of `V`. -/
def SliceRate (K : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (z * Work.Spaces.pz u z θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t))
    ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (z * Work.Spaces.pz u z θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo θ (Real.pi / 2), (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t))


/-- **The 1-D collar bound for the angular cut-off `psiD δ`** (schema in the rate constant `K`):
for `0 < δ ≤ π/8` and every `f : ℝ → ℝ` of class `C¹` on `(0,π/2)` with `σ(f')²` integrable and
the two endpoint rates, the `ψ_δ''`-moment of `f²` is bounded by `Cw·K` times the two *collar*
`σ`-energies of `f'`. -/
def CollarBound (Cw : ℝ) : Prop :=
  ∀ (K : ℝ), 0 < K → ∀ (δ : ℝ), 0 < δ → 4 * δ ≤ Real.pi / 2 → ∀ (f : ℝ → ℝ),
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig t)) →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig t)) →
    |∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AngSecond.sig θ
        * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2|
      ≤ Cw * K * ((∫ θ in Set.Ioo 0 δ,
            Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2)
          + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
              Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2))

/-- **The per-`(χ_n, ψ_δ)` inequality** (the `δ > 0` form of the chain, before the two limits):
with the radial cut-off `χ_n = cut n` and the angular bump `ψ_δ = psiD δ`,

`κ·P_χψ ≤ D_χψ + Tr_χψ − 2η·A_χψ + Cw·K·Col_χδ`,

where `P, D, Tr, A, Col` are the truncated quantities of `AeColl.Defs`
(`Ptr`, `Dtr`, `Trtr`, `Atr`, `Col`) and `Cw·K` is the bound on the collar term `½|W_χψ|`. -/
def TruncPairLe (Cw : ℝ) : Prop :=
  ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    MixedHon u →
    ∀ (K : ℝ), 0 < K → SliceRate K u →
    ∀ (n : ℕ) (δ : ℝ), 0 < δ → 4 * δ ≤ Real.pi / 2 →
      kap * Work.FTS.EllipticEst.AeColl.Ptr u n δ
        ≤ Work.FTS.EllipticEst.AeColl.Dtr u n δ + Work.FTS.EllipticEst.AeColl.Trtr u n δ
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Atr u n δ
          + Cw * K * Work.FTS.EllipticEst.AeColl.Col u n δ

/-- **The `ψ_δ ↓ 0` limit** for fixed `n`: the per-`δ` inequality (`TruncPairLe`) passes to the
limit `δ → 0⁺`, giving the inequality with the `δ`-free truncated quantities
`Pcut, Dcut, Trcut, Acut` of `AeColl.Defs`. -/
def PairLimit (Cw : ℝ) : Prop :=
  ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    MixedHon u →
    ∀ (K : ℝ), 0 < K → SliceRate K u →
    (hpair : ∀ (n : ℕ) (δ : ℝ), 0 < δ → 4 * δ ≤ Real.pi / 2 →
      kap * Work.FTS.EllipticEst.AeColl.Ptr u n δ
        ≤ Work.FTS.EllipticEst.AeColl.Dtr u n δ + Work.FTS.EllipticEst.AeColl.Trtr u n δ
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Atr u n δ
          + Cw * K * Work.FTS.EllipticEst.AeColl.Col u n δ) →
    ∀ n : ℕ,
      kap * Work.FTS.EllipticEst.AeColl.Pcut u n
        ≤ Work.FTS.EllipticEst.AeColl.Dcut u n + Work.FTS.EllipticEst.AeColl.Trcut u n
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n

end Work.FTS.EllipticEst.Deleg
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.psiDIntegralLimitAlt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

theorem psiDIntegralLimitAlt {c : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Set.Ioi (0 : ℝ))))
    (hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))))
    (hGz : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Integrable (fun θ => G z θ) (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
    (hdom : Integrable (fun z => |c z| *
        ∫ θ, |G z θ| ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    Tendsto (fun δ : ℝ => ∫ z, c z *
        (∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ
          ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z, c z * (∫ θ, G z θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
        ∂(volume.restrict (Set.Ioi (0 : ℝ))))) := by
  set ν : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) with hν
  have hψc : ∀ δ : ℝ, Continuous (Work.FTS.EllipticEst.AeColl.psiD δ) := fun δ =>
    (Work.FTS.EllipticEst.AeColl.psiD_contDiff δ).continuous
  -- (1) a.e. strong measurability of the integrands
  have hmeas : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun z => c z *
        (∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine Filter.Eventually.of_forall (fun δ => ?_)
    have h1 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.psiD δ p.2 * G p.1 p.2)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod ν) :=
      ((hψc δ).measurable.comp measurable_snd).aestronglyMeasurable.mul hjoint
    exact hc.mul h1.integral_prod_right'
  -- (2) domination by the absolute marginal
  have hpt : ∀ (z : ℝ) (δ θ : ℝ), ‖Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ‖ ≤ |G z θ| := by
    intro z δ θ
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (Work.FTS.EllipticEst.AeColl.psiD_nonneg δ θ)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Work.FTS.EllipticEst.AeColl.psiD_le_one δ θ)
  have hbound : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖c z * (∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν)‖
          ≤ |c z| * ∫ θ, |G z θ| ∂ν := by
    refine Filter.Eventually.of_forall (fun δ => ?_)
    filter_upwards [hGz] with z hzint
    have h3 : ‖∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν‖
        ≤ ∫ θ, |G z θ| ∂ν :=
      le_trans (norm_integral_le_integral_norm _)
        (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => norm_nonneg _) hzint.norm
          (Filter.Eventually.of_forall fun θ => hpt z δ θ))
    calc ‖c z * (∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν)‖
        = |c z| * ‖∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν‖ := by
          rw [norm_mul, Real.norm_eq_abs]
      _ ≤ |c z| * ∫ θ, |G z θ| ∂ν := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  -- (3) pointwise convergence for a.e. `z`
  have hlim : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Tendsto (fun δ : ℝ => c z * (∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν))
        (𝓝[>] (0 : ℝ)) (𝓝 (c z * (∫ θ, G z θ ∂ν))) := by
    filter_upwards [hGz, hjoint.prodMk_left] with z hzint hzslice
    have hinner : Tendsto (fun δ : ℝ =>
        ∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ θ, G z θ ∂ν)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun θ => |G z θ|)
        ?_ ?_ hzint.norm ?_
      · exact Filter.Eventually.of_forall (fun δ =>
          (hψc δ).measurable.aestronglyMeasurable.mul hzslice)
      · exact Filter.Eventually.of_forall (fun δ =>
          ae_restrict_of_forall_mem measurableSet_Ioo (fun θ _ => hpt z δ θ))
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
        have h := Work.FTS.EllipticEst.AeColl.psiD_tendsto_one θ hθ
        simpa using h.mul_const (G z θ)
    exact hinner.const_mul (c z)
  -- (4) the outer dominated convergence
  exact tendsto_integral_filter_of_dominated_convergence (fun z => |c z| * ∫ θ, |G z θ| ∂ν)
    hmeas hbound hdom hlim

end

end Work.FTS.EllipticEst.Deleg
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.psiDSecondDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg

set_option autoImplicit false

/-! ### The second derivative of the angular bump `psiD δ`

`psiD δ θ = ψ((θ - δ/4)/(δ/4)) · ψ(((π/2 - δ/4) - θ)/(δ/4))` with `ψ = Real.smoothTransition`
is a product of two bumps of width `δ/4`, so its second derivative is `O(δ⁻²)`. -/

section PsiDSecondDeriv

private lemma differentiable_smoothTransition : Differentiable ℝ Real.smoothTransition :=
  (Real.smoothTransition.contDiff (n := 2)).differentiable (by norm_num)

/-- Chain rule for `y ↦ F ((y - a)/k)`. -/
private lemma hasDerivAt_div_sub_comp (F : ℝ → ℝ) (k a x : ℝ)
    (hF : DifferentiableAt ℝ F ((x - a) / k)) :
    HasDerivAt (fun y : ℝ => F ((y - a) / k)) (deriv F ((x - a) / k) * (1 / k)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y - a) / k) (1 / k) x := by
    simpa using ((hasDerivAt_id' (x := x)).sub_const a).div_const k
  have h := (hF.hasDerivAt).comp x h1
  convert h using 1
  funext y
  rfl

/-- Chain rule for `y ↦ F ((c - y)/k)`. -/
private lemma hasDerivAt_sub_div_comp (F : ℝ → ℝ) (k c x : ℝ)
    (hF : DifferentiableAt ℝ F ((c - x) / k)) :
    HasDerivAt (fun y : ℝ => F ((c - y) / k)) (deriv F ((c - x) / k) * (-(1 / k))) x := by
  have h1 : HasDerivAt (fun y : ℝ => (c - y) / k) (-(1 / k)) x := by
    have h := ((hasDerivAt_const (x := x) c).sub (hasDerivAt_id' (x := x))).div_const k
    have hval : (0 - 1) / k = -(1 / k) := by ring
    rwa [hval] at h
  have h := (hF.hasDerivAt).comp x h1
  convert h using 1
  funext y
  rfl

/-- **The second derivative of the angular bump is `O(δ⁻²)`.** -/
theorem psiD_deriv2_bound_alt : ∃ Cψ : ℝ, 0 < Cψ ∧ ∀ (δ : ℝ), 0 < δ → ∀ θ : ℝ,
    |deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ| ≤ Cψ / δ ^ 2 := by
  have hcont1 : Continuous (deriv Real.smoothTransition) := by
    have h : deriv Real.smoothTransition = iteratedDeriv 1 Real.smoothTransition := by
      rw [iteratedDeriv_one]
    rw [h]
    exact (Real.smoothTransition.contDiff (n := 2)).continuous_iteratedDeriv 1 (by norm_num)
  have hcont2 : Continuous (deriv (deriv Real.smoothTransition)) := by
    have h := (Real.smoothTransition.contDiff (n := 3)).continuous_iteratedDeriv 2 (by norm_num)
    have e : deriv (deriv Real.smoothTransition) = iteratedDeriv 2 Real.smoothTransition := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
    rw [e]
    exact h
  obtain ⟨S1, hS1nn, hS1⟩ :=
    Work.FTS.EllipticEst.PropL2CutKids.exists_bound_of_continuous_zero_off
      (deriv Real.smoothTransition) hcont1 (a := 0) (b := 1) (fun x hx => by
        rcases hx with h | h
        · exact Work.FTS.EllipticEst.PropL2CutKids.deriv_smoothTransition_eq_zero_of_lt h
        · exact Work.FTS.EllipticEst.PropL2CutKids.deriv_smoothTransition_eq_zero_of_gt h)
  obtain ⟨S2, hS2nn, hS2⟩ :=
    Work.FTS.EllipticEst.PropL2CutKids.exists_bound_of_continuous_zero_off
      (deriv (deriv Real.smoothTransition)) hcont2 (a := 0) (b := 1) (fun x hx => by
        rcases hx with h | h
        · exact Work.FTS.EllipticEst.PropL2CutKids.deriv2_smoothTransition_eq_zero_of_lt h
        · exact Work.FTS.EllipticEst.PropL2CutKids.deriv2_smoothTransition_eq_zero_of_gt h)
  have hd2diff : Differentiable ℝ (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two
  refine ⟨16 * (2 * S2 + 2 * S1 ^ 2) + 1, by nlinarith [hS1nn, hS2nn], ?_⟩
  intro δ hδ θ
  have hk : (0 : ℝ) < δ / 4 := by linarith
  have hpsi_fun : Work.FTS.EllipticEst.AeColl.psiD δ
      = fun y : ℝ => Real.smoothTransition ((y - δ / 4) / (δ / 4))
          * Real.smoothTransition (((Real.pi / 2 - δ / 4) - y) / (δ / 4)) := by
    funext y
    exact Work.FTS.EllipticEst.AeColl.psiD_apply δ y
  -- the first derivative, as a function
  have hderiv_eq : deriv (Work.FTS.EllipticEst.AeColl.psiD δ)
      = fun y : ℝ => deriv Real.smoothTransition ((y - δ / 4) / (δ / 4)) * (1 / (δ / 4))
            * Real.smoothTransition (((Real.pi / 2 - δ / 4) - y) / (δ / 4))
          + Real.smoothTransition ((y - δ / 4) / (δ / 4))
              * (deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - y) / (δ / 4))
                  * (-(1 / (δ / 4)))) := by
    rw [hpsi_fun]
    funext y
    exact ((hasDerivAt_div_sub_comp Real.smoothTransition (δ / 4) (δ / 4) y
        (differentiable_smoothTransition.differentiableAt)).mul
      (hasDerivAt_sub_div_comp Real.smoothTransition (δ / 4) (Real.pi / 2 - δ / 4) y
        (differentiable_smoothTransition.differentiableAt))).deriv
  -- the derivatives of the four pieces of the first derivative
  have hP : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => deriv Real.smoothTransition ((z - δ / 4) / (δ / 4)) * (1 / (δ / 4)))
      ((deriv (deriv Real.smoothTransition) ((y - δ / 4) / (δ / 4)) * (1 / (δ / 4)))
        * (1 / (δ / 4))) y := by
    intro y
    exact (hasDerivAt_div_sub_comp (deriv Real.smoothTransition) (δ / 4) (δ / 4) y
      (hd2diff.differentiableAt)).mul_const (1 / (δ / 4))
  have hQ : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => Real.smoothTransition (((Real.pi / 2 - δ / 4) - z) / (δ / 4)))
      (deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - y) / (δ / 4))
        * (-(1 / (δ / 4)))) y := fun y =>
    hasDerivAt_sub_div_comp Real.smoothTransition (δ / 4) (Real.pi / 2 - δ / 4) y
      (differentiable_smoothTransition.differentiableAt)
  have hR : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => Real.smoothTransition ((z - δ / 4) / (δ / 4)))
      (deriv Real.smoothTransition ((y - δ / 4) / (δ / 4)) * (1 / (δ / 4))) y := fun y =>
    hasDerivAt_div_sub_comp Real.smoothTransition (δ / 4) (δ / 4) y
      (differentiable_smoothTransition.differentiableAt)
  have hS : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - z) / (δ / 4))
        * (-(1 / (δ / 4))))
      ((deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - y) / (δ / 4))
          * (-(1 / (δ / 4))))
        * (-(1 / (δ / 4)))) y := by
    intro y
    exact (hasDerivAt_sub_div_comp (deriv Real.smoothTransition) (δ / 4) (Real.pi / 2 - δ / 4) y
      (hd2diff.differentiableAt)).mul_const (-(1 / (δ / 4)))
  -- the second derivative
  have hsec : deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ
      = ((deriv (deriv Real.smoothTransition) ((θ - δ / 4) / (δ / 4)) * (1 / (δ / 4)))
            * (1 / (δ / 4)))
          * Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
        + (deriv Real.smoothTransition ((θ - δ / 4) / (δ / 4)) * (1 / (δ / 4)))
          * (deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
              * (-(1 / (δ / 4))))
        + ((deriv Real.smoothTransition ((θ - δ / 4) / (δ / 4)) * (1 / (δ / 4)))
          * (deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
              * (-(1 / (δ / 4))))
        + Real.smoothTransition ((θ - δ / 4) / (δ / 4))
          * ((deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
              * (-(1 / (δ / 4))))
            * (-(1 / (δ / 4))))) := by
    rw [hderiv_eq]
    exact (((hP θ).mul (hQ θ)).add ((hR θ).mul (hS θ))).deriv
  rw [hsec]
  -- the four summands of the second derivative
  set K : ℝ := 1 / (δ / 4) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hKnn : 0 ≤ K := le_of_lt hKpos
  have hKsq : K ^ 2 = 16 / δ ^ 2 := by
    rw [hKdef, one_div, inv_div]
    ring
  set t1 : ℝ := ((deriv (deriv Real.smoothTransition) ((θ - δ / 4) / (δ / 4)) * K) * K)
      * Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4)) with ht1def
  set t2 : ℝ := (deriv Real.smoothTransition ((θ - δ / 4) / (δ / 4)) * K)
      * (deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4)) * (-K)) with ht2def
  set t4 : ℝ := Real.smoothTransition ((θ - δ / 4) / (δ / 4))
      * ((deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - θ) / (δ / 4)) * (-K))
        * (-K)) with ht4def
  have hb1 : |deriv Real.smoothTransition ((θ - δ / 4) / (δ / 4))| ≤ S1 := hS1 _
  have hb2 : |deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| ≤ S1 := hS1 _
  have hb3 : |deriv (deriv Real.smoothTransition) ((θ - δ / 4) / (δ / 4))| ≤ S2 := hS2 _
  have hb4 : |deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| ≤ S2 :=
    hS2 _
  have hP1 : |Real.smoothTransition ((θ - δ / 4) / (δ / 4))| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hP2 : |Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have ht1b : |t1| ≤ S2 * K ^ 2 := by
    rw [ht1def]
    simp only [abs_mul, abs_of_nonneg hKnn]
    calc |deriv (deriv Real.smoothTransition) ((θ - δ / 4) / (δ / 4))| * K * K
          * |Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))|
        ≤ S2 * K * K * 1 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hb3 le_rfl hKnn hS2nn) le_rfl hKnn
            (mul_nonneg hS2nn hKnn)) hP2 (abs_nonneg _) (by positivity)
      _ = S2 * K ^ 2 := by ring
  have ht2b : |t2| ≤ S1 ^ 2 * K ^ 2 := by
    rw [ht2def]
    simp only [abs_mul, abs_neg, abs_of_nonneg hKnn]
    calc |deriv Real.smoothTransition ((θ - δ / 4) / (δ / 4))| * K
          * (|deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| * K)
        ≤ S1 * K * (S1 * K) := by
          refine mul_le_mul (mul_le_mul hb1 le_rfl hKnn hS1nn)
            (mul_le_mul hb2 le_rfl hKnn hS1nn) (by positivity) (by positivity)
      _ = S1 ^ 2 * K ^ 2 := by ring
  have ht4b : |t4| ≤ S2 * K ^ 2 := by
    rw [ht4def]
    simp only [abs_mul, abs_neg, abs_of_nonneg hKnn]
    calc |Real.smoothTransition ((θ - δ / 4) / (δ / 4))|
          * ((|deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| * K)
            * K)
        ≤ 1 * (S2 * (K * K)) := by
          refine mul_le_mul hP1 ?_ (by positivity) (by norm_num)
          calc ((|deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| * K)
                * K) ≤ (S2 * K) * K :=
                mul_le_mul_of_nonneg_right (mul_le_mul hb4 le_rfl hKnn hS2nn) hKnn
            _ = S2 * (K * K) := by ring
      _ = S2 * K ^ 2 := by ring
  have htri : |(t1 + t2) + (t2 + t4)| ≤ (|t1| + |t2|) + (|t2| + |t4|) :=
    (abs_add_le (t1 + t2) (t2 + t4)).trans
      (add_le_add (abs_add_le t1 t2) (abs_add_le t2 t4))
  calc |(t1 + t2) + (t2 + t4)| ≤ (|t1| + |t2|) + (|t2| + |t4|) := htri
    _ ≤ (S2 * K ^ 2 + S1 ^ 2 * K ^ 2) + (S1 ^ 2 * K ^ 2 + S2 * K ^ 2) :=
        add_le_add (add_le_add ht1b ht2b) (add_le_add ht2b ht4b)
    _ = (2 * S2 + 2 * S1 ^ 2) * K ^ 2 := by ring
    _ = (2 * S2 + 2 * S1 ^ 2) * (16 / δ ^ 2) := by rw [hKsq]
    _ = 16 * (2 * S2 + 2 * S1 ^ 2) / δ ^ 2 := by ring
    _ ≤ (16 * (2 * S2 + 2 * S1 ^ 2) + 1) / δ ^ 2 := by
        have hδ2 : 0 < δ ^ 2 := by positivity
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hδ2)

end PsiDSecondDeriv

end Work.FTS.EllipticEst.Deleg
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.psiD_deriv2_zero_mid =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.EllipticEst.Deleg

/-- `psiD δ` agrees with the constant `1` on the *open* interval `(δ/2, π/2 - δ/2)`
(where it is already known to equal `1`), hence — that interval being open — its germ at any
interior point `θ` is the germ of the constant `1`.  Consequently both `deriv` and
`deriv ∘ deriv` of `psiD δ` vanish at `θ`. -/
theorem psiD_deriv2_zero_mid : ∀ (δ : ℝ), 0 < δ → ∀ θ : ℝ, δ / 2 < θ → θ < Real.pi / 2 - δ / 2 →
    deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ = 0 := by
  intro δ hδ θ h1 h2
  -- `psiD δ` is the germ of the constant `1` at `θ`.
  have hmem : Set.Ioo (δ / 2) (Real.pi / 2 - δ / 2) ∈ 𝓝 θ :=
    isOpen_Ioo.mem_nhds ⟨h1, h2⟩
  have heq : Work.FTS.EllipticEst.AeColl.psiD δ =ᶠ[𝓝 θ] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem hmem fun θ' hθ' =>
      Work.FTS.EllipticEst.AeColl.psiD_eq_one_of_mem hδ (le_of_lt hθ'.1) (le_of_lt hθ'.2)
  -- Differentiating preserves the germ relation.
  have h1eq : deriv (Work.FTS.EllipticEst.AeColl.psiD δ) =ᶠ[𝓝 θ] deriv (fun _ => (1 : ℝ)) :=
    heq.deriv
  calc deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ
      = deriv (deriv (fun _ => (1 : ℝ))) θ := h1eq.deriv_eq
    _ = 0 := by simp

end Work.FTS.EllipticEst.Deleg
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.aeI1Base =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The open half-strip `(0,∞) × (0,π/2)`. -/
abbrev ftsQd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)


theorem isOpen_ftsQd : IsOpen ftsQd := isOpen_Ioi.prod isOpen_Ioo

theorem natCast_succ_ne_zero (n : ℕ) : ((n + 1 : ℕ) : ℕ∞ω) ≠ 0 := by
  simp

/-! ## Finite-order smoothness of the slice derivatives -/

/-- `Work.Spaces.pz` lowers the order of smoothness by one. -/
theorem contDiffOn_uncurry_pz_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn
      (natCast_succ_ne_zero n)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `Work.Spaces.pth` lowers the order of smoothness by one. -/
theorem contDiffOn_uncurry_pth_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn
      (natCast_succ_ne_zero n)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-! ## The smoothness of the derivative factors of `Φ` on the open quadrant -/

theorem contDiffOn_uncurry_pz {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Φ)) ftsQd :=
  contDiffOn_uncurry_pz_fin isOpen_ftsQd hsm

theorem contDiffOn_uncurry_pth {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Φ)) ftsQd :=
  contDiffOn_uncurry_pth_fin isOpen_ftsQd hsm

theorem contDiffOn_uncurry_pzIter_two {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 2 Φ)) ftsQd := by
  have h1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Φ)) ftsQd :=
    contDiffOn_uncurry_pz hsm
  have h2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz Φ))) ftsQd :=
    contDiffOn_uncurry_pz_fin isOpen_ftsQd (n := 1) h1
  simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h2

theorem contDiffOn_uncurry_pthIter_two {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pthIter 2 Φ)) ftsQd := by
  have h1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Φ)) ftsQd :=
    contDiffOn_uncurry_pth hsm
  have h2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth Φ))) ftsQd :=
    contDiffOn_uncurry_pth_fin isOpen_ftsQd (n := 1) h1
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h2



theorem continuousOn_uncurry_pz {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz Φ)) ftsQd :=
  (contDiffOn_uncurry_pz hsm).continuousOn

theorem continuousOn_uncurry_pth {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pth Φ)) ftsQd :=
  (contDiffOn_uncurry_pth hsm).continuousOn

theorem continuousOn_uncurry_pthIter_two {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pthIter 2 Φ)) ftsQd :=
  (contDiffOn_uncurry_pthIter_two hsm).continuousOn

theorem continuousOn_uncurry_pzIter_two {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 Φ)) ftsQd :=
  (contDiffOn_uncurry_pzIter_two hsm).continuousOn


/-! ## Vanishing on strips -/







/-! ## Instantiating the vanishing for `Φ` supported in the rectangle -/





section Support

variable {Φ : ℝ → ℝ → ℝ} {a b c d : ℝ}





end Support

/-! ## Clairaut on the open quadrant -/


end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeWAux.niceSliceIBPOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeWAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Two elementary bookkeeping facts -/

/-- The half-line set integrals over `Iz = [0,∞)` and over `Ioi 0 = (0,∞)` agree: the two
measures differ only at the null point `0`. -/
private theorem setIntegral_Iz_eq_setIntegral_Ioi (f : ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, f z) = ∫ z in Set.Ioi (0 : ℝ), f z := by
  rw [Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]

/-- A function continuous on `[a,b]` (`0 < a ≤ b`) and vanishing outside `[a,b]` is integrable
on `(0,∞)`; its support is the compact subset `[a,b] ⊆ (0,∞)`. -/
private theorem integrableOn_Ioi_of_Icc_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hcont : ContinuousOn f (Set.Icc a b))
    (hzero : ∀ z, z ∉ Set.Icc a b → f z = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
  have hInd : MeasureTheory.Integrable ((Set.Icc a b).indicator f) volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (hcont.integrableOn_compact isCompact_Icc)
  have hfun : f = (Set.Icc a b).indicator f := by
    funext z
    by_cases hz : z ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hzero z hz]
  rw [hfun]
  refine ⟨hInd.aestronglyMeasurable.mono_measure Measure.restrict_le_self, ?_⟩
  calc ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume.restrict (Set.Ioi 0))
      ≤ ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume : MeasureTheory.Measure ℝ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := hInd.hasFiniteIntegral

/-! ## The pointwise identity `nice = ∂_z u · Dv`, in the open class -/

/-- The `z`-derivative of `z ↦ z² · ∂_θ²u(z,θ) · cut n z · w²(z)`, in raw expanded form.
The open-quadrant analogue of `Work.FTS.EllipticEst.AngSecond.hasDerivAt_z2_phi_chi_w2`. -/
theorem hasDerivAt_z2_phi_chi_w2_open (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 u z' θ
        * Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AngSecond.w2 z')
      (2 * z * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.w2 z
        + z ^ 2 * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ
          * Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.w2 z
        + z ^ 2 * Work.Spaces.pthIter 2 u z θ * deriv (Work.FTS.EllipticEst.cut n) z
          * Work.FTS.EllipticEst.AngSecond.w2 z
        + z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * deriv Work.FTS.EllipticEst.AngSecond.w2 z) z := by
  have h1 : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
    have h := (hasDerivAt_id z).pow 2
    have h2 : ((2 : ℕ) : ℝ) * z ^ (2 - 1) * (1 : ℝ) = 2 * z := by norm_num
    exact h.congr_deriv h2
  have hP : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 u) := by
    have h := hu.pth.pth
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h
  have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pthIter 2 u z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z := hP.hasDerivAt_slice hθ hz
  have h3 : HasDerivAt (fun z' : ℝ => Work.FTS.EllipticEst.cut n z')
      (deriv (Work.FTS.EllipticEst.cut n) z) z :=
    ((Work.FTS.EllipticEst.cut_contDiff n).differentiable (by simp)).differentiableAt.hasDerivAt
  have h4 : HasDerivAt Work.FTS.EllipticEst.AngSecond.w2
      (deriv Work.FTS.EllipticEst.AngSecond.w2 z) z :=
    (Work.FTS.EllipticEst.AngSecond.hasDerivAt_w2 hz).differentiableAt.hasDerivAt
  have htot := ((h1.mul h2).mul h3).mul h4
  refine htot.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

/-- The same derivative, in the bundled form `Dv n u z θ`. -/
theorem hasDerivAt_v_eq_Dv_open (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 u z' θ
        * Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AngSecond.w2 z')
      (Work.FTS.EllipticEst.AngSecond.Dv n u z θ) z :=
  hasDerivAt_z2_phi_chi_w2_open n u hu hz hθ

/-- The pointwise expansion of the `z`-derivative, i.e. the right-hand side of the definition
of `nice`. -/
theorem pz_mul_deriv_expansion_open (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz u z θ
        * deriv (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 u z' θ
            * Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AngSecond.w2 z') z
      = Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.w2 z
          * (2 * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ)
              + (z * Work.Spaces.pz u z θ)
                  * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
              - 4 * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ) / (1 + z))
        + Work.FTS.EllipticEst.AngSecond.w2 z
            * ((z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ))
            * (z * deriv (Work.FTS.EllipticEst.cut n) z) := by
  rw [(hasDerivAt_z2_phi_chi_w2_open n u hu hz hθ).deriv]
  rw [Work.FTS.EllipticEst.AngSecond.deriv_w2_eq' hz]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp
  ring

/-- **The pointwise form of the cut-off identity, in the open class.**
`∂_z u(z,θ) · Dv n u z θ = nice n u z θ` for every `z > 0` and every interior angle. -/
theorem pz_mul_Dv_eq_nice_open (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz u z θ * Work.FTS.EllipticEst.AngSecond.Dv n u z θ
      = Work.FTS.EllipticEst.AngSecond.nice n u z θ := by
  have h := pz_mul_deriv_expansion_open n u hu hz hθ
  have hd : deriv (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 u z' θ
      * Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AngSecond.w2 z') z
      = Work.FTS.EllipticEst.AngSecond.Dv n u z θ := (hasDerivAt_v_eq_Dv_open n u hu hz hθ).deriv
  rw [hd] at h
  rw [h]
  simp only [Work.FTS.EllipticEst.AngSecond.nice, Work.FTS.EllipticEst.AngSecond.G,
    Work.FTS.EllipticEst.AngSecond.Phi, Work.FTS.EllipticEst.AngSecond.H]

/-! ## The per-angle integration by parts on the half-line -/

/-- **The slice form of the `z`-integration by parts**, for data which are `C^∞` only on the
open quadrant.  Same statement as `Work.FTS.EllipticEst.AngSecond.slice_ibp_halfline`, with
`Work.Spaces.SmoothNbhd u` replaced by `Work.FTS.EllipticEst.SmoothOpen u` and a closed angle
by an interior one. -/
theorem slice_ibp_halfline_open (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pz u z θ
        * Work.FTS.EllipticEst.AngSecond.Dv n u z θ)
      = -∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pzIter 2 u z θ
          * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.w2 z) := by
  have ha : (0 : ℝ) < 1 / (2 * (n + 1 : ℝ)) := by positivity
  have hab : 1 / (2 * (n + 1 : ℝ)) ≤ 4 * (n + 1 : ℝ) := by
    have h1 : 1 / (2 * (n + 1 : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h2 : (1 : ℝ) ≤ 4 * (n + 1 : ℝ) := by
      have : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      linarith
    linarith
  have hsub : Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ⊆ Set.Ioi (0 : ℝ) :=
    fun z hz => lt_of_lt_of_le ha hz.1
  have hP : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 u) := by
    have h := hu.pth.pth
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h
  have hQ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pz (Work.Spaces.pthIter 2 u)) := hP.pz
  have hR : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pzIter 2 u) := hu.pzIter 2
  have hcont_pth : ContinuousOn (fun z : ℝ => Work.Spaces.pthIter 2 u z θ)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
    (hP.curry_z hθ).continuousOn.mono hsub
  have hcont_pzpth : ContinuousOn (fun z : ℝ => Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
    (hQ.curry_z hθ).continuousOn.mono hsub
  have hcont_pz : ContinuousOn (fun z : ℝ => Work.Spaces.pz u z θ)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
    ((hu.pz).curry_z hθ).continuousOn.mono hsub
  have hcont_pzIter : ContinuousOn (fun z : ℝ => Work.Spaces.pzIter 2 u z θ)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
    (hR.curry_z hθ).continuousOn.mono hsub
  have hcont_cut : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.cut n z)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
    (Work.FTS.EllipticEst.cut_contDiff n).continuous.continuousOn
  have hDv : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.Dv n u z θ)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) := by
    have hφ := hcont_pth
    have hφ' := hcont_pzpth
    have hχ := hcont_cut
    have hχ' : ContinuousOn (fun z : ℝ => deriv (Work.FTS.EllipticEst.cut n) z)
        (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      (Work.FTS.EllipticEst.AngSecond.continuous_deriv_cut n).continuousOn
    have hw : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.w2 z)
        (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      Work.FTS.EllipticEst.AngSecond.continuousOn_w2' ha
    have hw' : ContinuousOn (fun z : ℝ => deriv Work.FTS.EllipticEst.AngSecond.w2 z)
        (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      Work.FTS.EllipticEst.AngSecond.continuousOn_deriv_w2' ha
    simp only [Work.FTS.EllipticEst.AngSecond.Dv]
    fun_prop
  have hu' : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => Work.Spaces.pz u z θ)
      (Work.Spaces.pzIter 2 u x θ) x := by
    intro x hx
    have h := (hu.pz).hasDerivAt_slice hθ hx
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h
  have hv' : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AngSecond.w2 z) (Work.FTS.EllipticEst.AngSecond.Dv n u x θ) x :=
    fun x hx => hasDerivAt_v_eq_Dv_open n u hu hx hθ
  have hI1 : MeasureTheory.IntegrableOn (fun z => Work.Spaces.pz u z θ
      * Work.FTS.EllipticEst.AngSecond.Dv n u z θ) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_Icc_support (f := fun z => Work.Spaces.pz u z θ
      * Work.FTS.EllipticEst.AngSecond.Dv n u z θ) ha hab ?_ ?_
    · exact hcont_pz.mul hDv
    · intro z hz
      rw [Work.FTS.EllipticEst.AngSecond.Dv_eq_zero_of_notMem n u hz, mul_zero]
  have hI2 : MeasureTheory.IntegrableOn (fun z => Work.Spaces.pzIter 2 u z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.w2 z)) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_Icc_support (f := fun z => Work.Spaces.pzIter 2 u z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.w2 z)) ha hab ?_ ?_
    · have hz2χφ : ContinuousOn (fun z : ℝ => z ^ 2 * Work.Spaces.pthIter 2 u z θ
          * Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.w2 z)
          (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
        (((continuousOn_id.pow 2).mul hcont_pth).mul hcont_cut).mul
          (Work.FTS.EllipticEst.AngSecond.continuousOn_w2' ha)
      exact hcont_pzIter.mul hz2χφ
    · intro z hz
      have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      have ha' : 1 / (2 * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) :=
        one_div_le_one_div_of_le hn (by linarith)
      simp only [Set.mem_Icc, not_and_or, not_le] at hz
      rcases hz with hzlt | hzgt
      · have h1 : z ≤ 1 / (n + 1 : ℝ) := by linarith
        simp [Work.FTS.EllipticEst.cut_apply_zero_of_le n h1]
      · have h1 : 3 * (n + 1 : ℝ) ≤ z := by linarith
        simp [Work.FTS.EllipticEst.cut_apply_zero_of_ge n h1]
  have hmem0 : ∀ᶠ z in 𝓝[>] (0 : ℝ), z < 1 / (n + 1 : ℝ) := by
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hmem : Set.Iio (1 / (n + 1 : ℝ)) ∈ 𝓝 (0 : ℝ) :=
      isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Set.Iio (1 / (n + 1 : ℝ)) from hpos)
    exact nhdsWithin_le_nhds hmem
  have hbnd0 : Filter.Tendsto (fun z => Work.Spaces.pz u z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.w2 z)) (𝓝[>] (0 : ℝ)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hmem0] with z hz
    simp [Work.FTS.EllipticEst.cut_apply_zero_of_le n hz.le]
  have hbndT : Filter.Tendsto (fun z => Work.Spaces.pz u z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.w2 z)) Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (3 * (n + 1 : ℝ))] with z hz
    simp [Work.FTS.EllipticEst.cut_apply_zero_of_ge n hz]
  have hIBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := (0 : ℝ))
    (b' := (0 : ℝ))
    (u := fun z => Work.Spaces.pz u z θ) (u' := fun z => Work.Spaces.pzIter 2 u z θ)
    (v := fun z => z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AngSecond.w2 z)
    (v' := fun z => Work.FTS.EllipticEst.AngSecond.Dv n u z θ)
    hu' hv' hI1 hI2 hbnd0 hbndT
  simpa using hIBP

/-! ## The target -/

theorem niceSliceIBPOpen (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.nice n u z θ)
      = -∫ z in Work.Spaces.Iz, Work.Spaces.pzIter 2 u z θ
          * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.w2 z) := by
  have hu : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hmul : (fun z => Work.FTS.EllipticEst.AngSecond.nice n u z θ)
      =ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => Work.Spaces.pz u z θ * Work.FTS.EllipticEst.AngSecond.Dv n u z θ) := by
    rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact (pz_mul_Dv_eq_nice_open n u hu hz hθ).symm
  calc (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.nice n u z θ)
      = ∫ z in Work.Spaces.Iz, Work.Spaces.pz u z θ
          * Work.FTS.EllipticEst.AngSecond.Dv n u z θ :=
        MeasureTheory.integral_congr_ae hmul
    _ = ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pz u z θ
          * Work.FTS.EllipticEst.AngSecond.Dv n u z θ :=
        setIntegral_Iz_eq_setIntegral_Ioi _
    _ = -∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pzIter 2 u z θ
          * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.w2 z) :=
        slice_ibp_halfline_open n u hu hθ
    _ = -∫ z in Work.Spaces.Iz, Work.Spaces.pzIter 2 u z θ
          * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.w2 z) := by
        rw [setIntegral_Iz_eq_setIntegral_Ioi]

end Work.FTS.EllipticEst.H2W.AeWAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.mixed_pth_expand_V =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

/-! ## Linearity of `∂_z` (and of `D_z^j`) over a finite sum with `θ`-dependent coefficients -/

/-- `∂_z` is linear over a finite sum whose coefficients depend only on `θ`, in the smooth
class `SmV` on the open box `V`. -/
theorem pz_sum_eqOn_V (N : ℕ) (c : ℕ → ℝ → ℝ) (F : ℕ → ℝ → ℝ → ℝ)
    (hF : ∀ m, SmV (F m)) :
    Set.EqOn
      (Function.uncurry
        (Work.Spaces.pz (fun z θ => ∑ m ∈ Finset.range N, c m θ * F m z θ)))
      (Function.uncurry
        (fun z θ => ∑ m ∈ Finset.range N, c m θ * Work.Spaces.pz (F m) z θ)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hdiff : ∀ m, DifferentiableAt ℝ (fun z' => F m z' θ) z := by
    intro m
    have h1 : DifferentiableAt ℝ (Function.uncurry (F m)) (z, θ) :=
      ((hF m).contDiffAt hp.1 hp.2).differentiableAt Work.FTS.LocData.smoothOrder_ne_zero
    have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
      (hasFDerivAt_prodMk_left z θ).differentiableAt
    have h3 := h1.comp z h2
    simpa [Function.comp_def, Function.uncurry] using h3
  show deriv (fun z' => ∑ m ∈ Finset.range N, c m θ * F m z' θ) z
      = ∑ m ∈ Finset.range N, c m θ * deriv (fun z' => F m z' θ) z
  have hfun : (fun z' => ∑ m ∈ Finset.range N, c m θ * F m z' θ)
      = ∑ m ∈ Finset.range N, (fun z' => c m θ * F m z' θ) := by
    funext z'
    rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun m _ => (hdiff m).const_mul (c m θ))]
  exact Finset.sum_congr rfl fun m _ => deriv_const_mul_field (c m θ)

/-- `D_z^j` is linear over a finite sum whose coefficients depend only on `θ`. -/
theorem DzIter_sum_eqOn_V (j N : ℕ) (c : ℕ → ℝ → ℝ) (F : ℕ → ℝ → ℝ → ℝ)
    (hF : ∀ m, SmV (F m)) :
    Set.EqOn
      (Function.uncurry
        (Work.Spaces.DzIter j (fun z θ => ∑ m ∈ Finset.range N, c m θ * F m z θ)))
      (Function.uncurry
        (fun z θ => ∑ m ∈ Finset.range N, c m θ * Work.Spaces.DzIter j (F m) z θ)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      intro p hp
      obtain ⟨z, θ⟩ := p
      have hFs : ∀ m, SmV (Work.Spaces.DzIter j (F m)) := fun m => (hF m).DzIter j
      have hcongr := Work.Spaces.pz_congr_of_isOpen isOpen_V ih hp
      have hstep := pz_sum_eqOn_V N c (fun m => Work.Spaces.DzIter j (F m)) hFs hp
      simp only [Function.uncurry] at hstep
      show Work.Spaces.Dz
          (Work.Spaces.DzIter j (fun z θ => ∑ m ∈ Finset.range N, c m θ * F m z θ)) z θ
        = ∑ m ∈ Finset.range N, c m θ * Work.Spaces.Dz (Work.Spaces.DzIter j (F m)) z θ
      show z * Work.Spaces.pz
            (Work.Spaces.DzIter j (fun z θ => ∑ m ∈ Finset.range N, c m θ * F m z θ)) z θ
        = ∑ m ∈ Finset.range N, c m θ * (z * Work.Spaces.pz (Work.Spaces.DzIter j (F m)) z θ)
      rw [hcongr, hstep, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring

/-! ## The `D_θ`-expansion of `D_θ^i (∂_θG)` in the genuine smooth order -/


/-! ## The target -/


end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.PsiCutDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Small trigonometric bounds -/

theorem abs_sin_le_one (x : ℝ) : |Real.sin x| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

theorem abs_cos_le_one (x : ℝ) : |Real.cos x| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

/-! ## The one-variable Leibniz rules

The product rules for the one-variable operators `Dz1 f = z f'` and `Dth1 b = sin(2θ) b'` of
`psiCut_mixed_factor`.  They hold pointwise, with no restriction on the point, unlike the
two-variable `Work.Spaces.DzIter_mul`/`DthIter_mul` (whose `ContDiffOn ℝ ⊤` hypothesis is the
analytic order and hence unusable for the smooth steps). -/







end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.PsiCutLayer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false




end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.LN_indicator_wrongWeight_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc.Subcut

/-! ## Elementary angular estimates

On the layer `LN N` (`N ≥ 1`) the angle `θ` stays a definite distance from `0` and from `π/2`, so
`sin(2θ)` is bounded below by a positive constant depending only on `N`.  The exact lower bound used
below is `4/(π (N+1))`, obtained from Jordan's inequality `(2/π) x ≤ sin x` on `[0, π/2]` applied to
`min (2θ) (π - 2θ)`. -/




/-! ## The weight comparison -/




end Work.FTS.GalBasis.cc.Subcut
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.MajDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The sharp majorant of the pointwise product bound for `χ_N f = f - ψ N · f`. -/
def Maj (α : ℝ) (C κN : ℝ) (N : ℕ) (f : Fn) : ℝ → ℝ → ℝ := fun z θ =>
  C * ((UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
    + (LN N).indicator (fun _ => (1 : ℝ)) θ *
        ∑ b ∈ Finset.range 4, (zslotW α b f z θ) ^ 2)

/-- The reduced majorant: the wrong-weight slots on the layer are replaced by the pure `D_z`-slots. -/
def MajRed (α : ℝ) (C κN : ℝ) (N : ℕ) (f : Fn) : ℝ → ℝ → ℝ := fun z θ =>
  C * ((UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
    + κN * ((LN N).indicator (fun _ => (1 : ℝ)) θ * Work.Spaces.HkIntegrand α 4 f z θ))

@[simp] theorem Maj_apply (α : ℝ) (C κN : ℝ) (N : ℕ) (f : Fn) (z θ : ℝ) :
    Maj α C κN N f z θ =
      C * ((UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
        + (LN N).indicator (fun _ => (1 : ℝ)) θ *
            ∑ b ∈ Finset.range 4, (zslotW α b f z θ) ^ 2) := rfl

@[simp] theorem MajRed_apply (α : ℝ) (C κN : ℝ) (N : ℕ) (f : Fn) (z θ : ℝ) :
    MajRed α C κN N f z θ =
      C * ((UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
        + κN * ((LN N).indicator (fun _ => (1 : ℝ)) θ * Work.Spaces.HkIntegrand α 4 f z θ)) := rfl

/-- The layer indicator distributes over the finite sum of wrong-weight slots. -/
theorem Maj_eq_sum_form (α : ℝ) (C κN : ℝ) (N : ℕ) (f : Fn) (z θ : ℝ) :
    Maj α C κN N f z θ =
      C * ((UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
        + ∑ b ∈ Finset.range 4, (LN N).indicator (fun _ => (1 : ℝ)) θ *
            (zslotW α b f z θ) ^ 2) := by
  rw [Maj_apply]
  congr 1
  rw [Finset.mul_sum]

end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.psiCut_cutA_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "𝕋" => Real.smoothTransition

/-! ## 1. Elementary facts about the smooth step -/

/-- The smooth step takes its values in `[0,1]`. -/
theorem abs_smoothTransition_le_one (u : ℝ) : |𝕋 u| ≤ 1 := by
  rcases le_or_gt u 0 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos h, abs_zero]; norm_num
  rcases le_or_gt 1 u with h1 | h1
  · rw [Real.smoothTransition.one_of_one_le h1, abs_one]
  · have h0 : 0 ≤ 𝕋 u := by
      rw [← Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))]
      exact Real.smoothTransition.monotone (le_of_lt h)
    rw [abs_of_nonneg h0]
    calc 𝕋 u ≤ 𝕋 1 := Real.smoothTransition.monotone (le_of_lt h1)
      _ = 1 := Real.smoothTransition.one_of_one_le le_rfl

/-- `∂^a` of a constant function vanishes in positive order. -/
theorem iteratedDeriv_const_eq_zero {c : ℝ} {a : ℕ} (ha : a ≠ 0) (x : ℝ) :
    iteratedDeriv a (fun _ : ℝ => c) x = 0 := by
  rw [iteratedDeriv_const, if_neg ha]

/-- `𝕋` is (locally) constantly `0` to the left of `0`, so all its derivatives vanish there. -/
theorem iteratedDeriv_smoothTransition_eq_zero_of_lt_zero {u : ℝ} (hu : u < 0) (a : ℕ) :
    iteratedDeriv a 𝕋 u = 0 := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [iteratedDeriv_zero, Real.smoothTransition.zero_of_nonpos (le_of_lt hu)]
  · have hev : 𝕋 =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hu] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [hev.iteratedDeriv_eq a,
      iteratedDeriv_const_eq_zero (Nat.pos_iff_ne_zero.mp hpos)]

/-- `𝕋` is (locally) constantly `1` to the right of `1`, so all its derivatives of positive order
vanish there. -/
theorem iteratedDeriv_smoothTransition_eq_zero_of_one_lt {u : ℝ} (hu : 1 < u) {a : ℕ}
    (ha : a ≠ 0) : iteratedDeriv a 𝕋 u = 0 := by
  have hev : 𝕋 =ᶠ[𝓝 u] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [hev.iteratedDeriv_eq a, iteratedDeriv_const_eq_zero ha]

/-! ## 2. Weighted derivative bounds for the smooth step -/

/-- **The weighted derivatives of the smooth step are bounded**, uniformly in the shift `c`.
There is `A : ℕ → ℝ` with `1 ≤ A a` and `|(u − c)^a · ∂^a 𝕋 u| ≤ A a` for all `a` and all `u`.

On `u ∈ [0,1]` this is the compactness of the (continuous) function
`u ↦ (u − c)^a ∂^a 𝕋 u`; off `[0,1]` the step is locally constant, so all the derivatives with
`a ≥ 1` vanish (`iteratedDeriv_smoothTransition_eq_zero_of_*`), while for `a = 0` the bound is
`|𝕋 u| ≤ 1` (`abs_smoothTransition_le_one`). -/
theorem exists_weighted_smoothTransition_bound (c : ℝ) :
    ∃ A : ℕ → ℝ, (∀ a : ℕ, 1 ≤ A a) ∧ ∀ (a : ℕ) (u : ℝ),
      |(u - c) ^ a * iteratedDeriv a 𝕋 u| ≤ A a := by
  have h : ∀ a : ℕ, ∃ C : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |(u - c) ^ a * iteratedDeriv a 𝕋 u| ≤ C := by
    intro a
    have hcont : Continuous (fun u : ℝ => (u - c) ^ a * iteratedDeriv a 𝕋 u) :=
      ((continuous_id.sub continuous_const).pow a).mul
        ((contDiff_smoothTransition a).continuous_iteratedDeriv a (by simp))
    have hc : ContinuousOn (fun u : ℝ => (u - c) ^ a * iteratedDeriv a 𝕋 u)
        (Set.Icc (0 : ℝ) 1) := hcont.continuousOn
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    exact ⟨C, fun u hu => by simpa only [Real.norm_eq_abs] using hC u hu⟩
  choose A hA using h
  have hApos : ∀ a : ℕ, 0 ≤ max (A a) 1 := fun a => le_trans zero_le_one (le_max_right (A a) 1)
  refine ⟨fun a => max (A a) 1, ?_, fun a u => ?_⟩
  · intro a; exact le_max_right (A a) 1
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [pow_zero, one_mul, iteratedDeriv_zero]
    exact le_trans (abs_smoothTransition_le_one u) (le_max_right (A 0) 1)
  · by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
    · exact le_trans (hA a u hu) (le_max_left (A a) 1)
    · have hane : a ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have hu' : ¬(0 ≤ u ∧ u ≤ 1) := by simpa only [Set.mem_Icc] using hu
      rcases lt_or_ge u 0 with hlt | hge
      · rw [iteratedDeriv_smoothTransition_eq_zero_of_lt_zero hlt a, mul_zero, abs_zero]
        exact hApos a
      · have hgt : 1 < u := lt_of_not_ge fun h => hu' ⟨hge, h⟩
        rw [iteratedDeriv_smoothTransition_eq_zero_of_one_lt hgt hane, mul_zero, abs_zero]
        exact hApos a

/-! ## 3. The affine chain rule for `iteratedDeriv` -/

/-- **Iterated derivative of an affine substitution.**  For a smooth `F`,
`∂^a (F (λ · + a₀)) z = λ^a · ∂^a F (λ z + a₀)`: differentiating `F (λ ·)` `a` times pulls out `a`
factors of `λ` (Mathlib's `iteratedDeriv_comp_const_mul`), and the translation does not change the
iterated derivative (`iteratedDeriv_comp_add_const`). -/
theorem iteratedDeriv_comp_mul_add (F : ℝ → ℝ) (hF : ∀ m : ℕ, ContDiff ℝ m F)
    (lam a₀ : ℝ) (a : ℕ) (z : ℝ) :
    iteratedDeriv a (fun z : ℝ => F (lam * z + a₀)) z
      = lam ^ a * iteratedDeriv a F (lam * z + a₀) := by
  have hG : ContDiff ℝ (a : WithTop ℕ∞) (fun y : ℝ => F (y + a₀)) :=
    (hF a).comp (contDiff_id.add contDiff_const)
  have h1 : iteratedDeriv a (fun z : ℝ => (fun y : ℝ => F (y + a₀)) (lam * z)) z
      = lam ^ a * iteratedDeriv a (fun y : ℝ => F (y + a₀)) (lam * z) :=
    congrFun (iteratedDeriv_comp_const_mul (f := fun y : ℝ => F (y + a₀)) hG lam) z
  have h2 : iteratedDeriv a (fun y : ℝ => F (y + a₀)) (lam * z)
      = iteratedDeriv a F (lam * z + a₀) :=
    congrFun (iteratedDeriv_comp_add_const a F a₀) (lam * z)
  have hfun : (fun z : ℝ => F (lam * z + a₀))
      = (fun z : ℝ => (fun y : ℝ => F (y + a₀)) (lam * z)) := rfl
  rw [hfun, h1, h2]

/-! ## 4. The bound for a product of two rescaled steps -/


/-! ## 5. `cutA` -/



/-! ## 6. The requested statement -/


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.psiCut_cutB_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The iterated angular operator on functions of `θ` alone

`Work.Spaces.Lop φ = sin(2·) · φ'` is the action of `D_θ` on the `θ`-slice, and
`DthIter n f z = Lop^[n] (fun θ => f z θ)`.  We need that the iterates of `Lop` preserve `C^∞`,
and the binomial expansion of `Lop^[j] (u · v)`. -/

/-- The iterates of `Lop` preserve smoothness. -/
theorem contDiff_Lop_iter {u : ℝ → ℝ} (hu : ∀ n : ℕ, ContDiff ℝ n u) :
    ∀ k n : ℕ, ContDiff ℝ n (Work.Spaces.Lop^[k] u) := by
  intro k
  induction k with
  | zero => intro n; simpa using hu n
  | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply']
      have hsin : ContDiff ℝ n (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
      have h1 : ContDiff ℝ n (deriv (Work.Spaces.Lop^[k] u)) := (ih (n + 1)).deriv'
      exact hsin.mul h1

/-- **Leibniz rule for `Lop`.**  For globally smooth `u`, `v` the `j`-th iterate of
`Lop = sin(2·) ∂` applied to the pointwise product satisfies the binomial expansion. -/
theorem Lop_iter_mul {u v : ℝ → ℝ} (hu : ∀ n : ℕ, ContDiff ℝ n u)
    (hv : ∀ n : ℕ, ContDiff ℝ n v) :
    ∀ j : ℕ, ∀ θ : ℝ, Work.Spaces.Lop^[j] (u * v) θ =
      ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
        ((Work.Spaces.Lop^[a] u) θ * (Work.Spaces.Lop^[j - a] v) θ) := by
  intro j
  induction j with
  | zero => intro θ; simp
  | succ j ih =>
      intro θ
      rw [Function.iterate_succ_apply']
      have hfun : Work.Spaces.Lop^[j] (u * v) = fun θ' => ∑ a ∈ Finset.range (j + 1),
          (j.choose a : ℝ) * ((Work.Spaces.Lop^[a] u) θ' * (Work.Spaces.Lop^[j - a] v) θ') := by
        funext θ'; exact ih θ'
      rw [hfun]
      have hdu : ∀ a, DifferentiableAt ℝ (Work.Spaces.Lop^[a] u) θ :=
        fun a => ((contDiff_Lop_iter hu a 1).differentiable (by norm_num)).differentiableAt
      have hdv : ∀ a, DifferentiableAt ℝ (Work.Spaces.Lop^[a] v) θ :=
        fun a => ((contDiff_Lop_iter hv a 1).differentiable (by norm_num)).differentiableAt
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => (j.choose a : ℝ) *
            ((Work.Spaces.Lop^[a] u) θ' * (Work.Spaces.Lop^[j - a] v) θ')) θ :=
        fun a _ => ((hdu a).mul (hdv (j - a))).const_mul _
      have hfun2 : (fun θ' => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ) * ((Work.Spaces.Lop^[a] u) θ' * (Work.Spaces.Lop^[j - a] v) θ'))
          = ∑ a ∈ Finset.range (j + 1),
            (fun θ' => (j.choose a : ℝ) *
              ((Work.Spaces.Lop^[a] u) θ' * (Work.Spaces.Lop^[j - a] v) θ')) := by
        funext θ'; rw [Finset.sum_apply]
      show Real.sin (2 * θ) * deriv (fun θ' => ∑ a ∈ Finset.range (j + 1),
          (j.choose a : ℝ) * ((Work.Spaces.Lop^[a] u) θ' * (Work.Spaces.Lop^[j - a] v) θ')) θ = _
      rw [hfun2, deriv_sum hmem, Finset.mul_sum]
      rw [Finset.sum_congr rfl
        (fun a _ => Work.Spaces.sin_deriv_term u v θ j a (hdu a) (hdv (j - a)))]
      exact Work.Spaces.leibniz_step j (fun b => (Work.Spaces.Lop^[b] u) θ)
        (fun b => (Work.Spaces.Lop^[b] v) θ)

/-! ## 2. A bound on the iterates of `E_ρ` applied to the profile

`Eiter k ρ f = (ρ ∂)^k f` is the iterate of the operator `Eop ρ f = ρ · f'` (defined in
`PsiCutAux`).  If `f = Real.smoothTransition` is the step profile, if `M` bounds the first three
derivatives of `ρ` and `B` those of `f` on the transition layer `[0,1]`, then

`1 + ∑_{k ≤ 4} Cbnd M B k 0`

bounds `|Eiter k ρ f v|` for *all* `k ≤ 4` and *all* `v : ℝ`: on the layer this is the abstract
induction `Eiter_deriv_bound`, off the layer the profile is locally constant and all positive
iterates vanish.  Note that the constant only depends on `M` and `B`, not on `ρ` itself — this is
what makes it uniform in the mesh. -/

/-! ## 3. The rescaled angular coefficient `ρ (u) = a sin (2 (u+1)/a)`

`rhoM a` is the coefficient with which the operator `D_θ = sin(2θ) ∂_θ` acts in the rescaled
variable `u = a θ - 1` (`DthIter_affine` of `PsiCutAux`).  We compute its first three derivatives
and bound them by `8` on the transition layer `[0,1]`, uniformly in `a ≥ 1`. -/






/-! ## 4. The two affine substitutions in the rescaled variable -/

/-- The rescaled coefficient of the angular substitution `u = a θ + c` for the *lower* layer
`c = -1` is `rhoM a`. -/
theorem coef_affine_eq_rhoM (a : ℝ) :
    (fun u : ℝ => a * Real.sin (2 * ((u - (-1)) / a))) = rhoM a := by
  funext u
  simp only [rhoM]
  rw [show 2 * ((u - (-1)) / a) = 2 * (u + 1) / a from by ring]

/-- The rescaled coefficient of the angular substitution `u = -a θ + (a π/2 - 1)` for the *upper*
layer `θ ↦ st (a (π/2 - θ) - 1)` is `-rhoM a`. -/
theorem coef_affine_eq_neg_rhoM (a : ℝ) (ha : a ≠ 0) :
    (fun u : ℝ => (-a) * Real.sin (2 * ((u - (a * (Real.pi / 2) - 1)) / (-a)))) =
      fun u : ℝ => -(rhoM a u) := by
  funext u
  simp only [rhoM]
  rw [show 2 * ((u - (a * (Real.pi / 2) - 1)) / (-a)) = Real.pi - 2 * (u + 1) / a from by
    field_simp
    ring]
  rw [Real.sin_pi_sub]
  ring

/-! ## 5. Recombining the two factors -/

/-- `DthIter i f z` for a function `f` that does not depend on `z` is the `i`-th iterate of `Lop`
applied to the `θ`-profile. -/
theorem DthIter_zindep (g : ℝ → ℝ) (z : ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun (_ : ℝ) θ => g θ) z = Work.Spaces.Lop^[i] g := by
  rw [Work.Spaces.DthIter_eq_iterate_Lop]

/-- The affine substitution `u = a θ + c` applied to `Lop`: the iterates of `Lop` on the rescaled
profile `θ ↦ st (a θ + c)` are the iterates of `E_ρ`, `ρ (u) = a sin (2 (u - c)/a)`, evaluated at
`u = a θ + c`. -/
theorem Lop_iter_affine_st (a c : ℝ) (ha : a ≠ 0) (i : ℕ) :
    ∀ θ : ℝ, Work.Spaces.Lop^[i] (fun θ' : ℝ => Real.smoothTransition (a * θ' + c)) θ =
      Eiter i (fun u => a * Real.sin (2 * ((u - c) / a))) Real.smoothTransition (a * θ + c) := by
  intro θ
  rw [← DthIter_zindep (fun θ' : ℝ => Real.smoothTransition (a * θ' + c)) 0 i]
  exact DthIter_affine Real.smoothTransition a c ha i contDiff_smoothTransition 0 θ


/-! ## 6. The uniform bound -/


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.H2.STQ.FBnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.STQ

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)
set_option maxHeartbeats 1000000

/-! ## Auxiliary: the `𝒲^{l,∞}`-norm is nonnegative -/

theorem WlInf_nonneg {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ} (hW : Spaces.WlInfMem α l f) :
    0 ≤ Spaces.WlInf α l f := by
  rw [Spaces.WlInf]
  exact add_nonneg (Spaces.wlZSum_nonneg α l f hW) (Spaces.wlThSum_nonneg α l f hW)

/-! ## Joint smoothness of the iterated `z`-partials -/





/-- A function vanishing at a fixed `θ` has all its `z`-derivatives vanishing there. -/
theorem pzIter_eq_zero_of_slice_zero {f : ℝ → ℝ → ℝ} {θ₀ : ℝ} (h : ∀ z, f z θ₀ = 0)
    (m : ℕ) (z : ℝ) : Spaces.pzIter m f z θ₀ = 0 := by
  induction m generalizing z with
  | zero => exact h z
  | succ n ih =>
      rw [Spaces.pzIter_succ, Spaces.pz]
      have : (fun z' => Spaces.pzIter n f z' θ₀) = fun _ => (0 : ℝ) := funext ih
      rw [this, deriv_const]

/-! ## The mean value bound on the `z`-difference quotient -/




/-! ## Continuity and `θ`-differentiability of the slices at interior points -/








/-- Triangle inequality in the form `|x - y| ≤ |x| + |y|`. -/
theorem abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using abs_add_le x (-y)


end Work.FTS.H2.STQ
end
end
-- ===== merged: Submission.Work.FTS.H2.WPQ.Final =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- For every `z ∈ Iz`, the sum of the angular `L²`-norms of the mixed slots of `g` is dominated
by four times the angular integral of the `ℋ⁴`-integrand of `g`. -/
theorem sum_Aang_le (α : ℝ) {g : ℝ → ℝ → ℝ} (hgm : Work.Spaces.HkMem α 4 g) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    ∑ d ∈ Finset.range 4, Aang α g d z
      ≤ 4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  have hd : ∀ d ∈ Finset.range 4, Aang α g d z
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
    intro d hd4
    have hd3 : d ≤ 3 := Nat.le_of_lt_succ (Finset.mem_range.mp hd4)
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hgm.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ =>
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 d le_rfl (by omega))
  calc ∑ d ∈ Finset.range 4, Aang α g d z
      ≤ ∑ _d ∈ Finset.range 4, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ :=
        Finset.sum_le_sum hd
    _ = 4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num


/-! ## The final layer -/


end Work.FTS.H2.WPQ
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The two-operator Leibniz rule in the open-quadrant class `SmoothOpen`

`Work.FTS.EllipticEst.SmoothOpen` is genuine `C^∞` on the *open* quadrant
`Q0 = (0,∞) × (0,π/2)` (the order `Work.Stability.smoothOrder`, *not* the analytic order
`⊤`), so neither the derivation-like structures `Work.Spaces.Zb_DerivLike`,
`Work.Spaces.Tb_DerivLike` (analytic order on `quadU = (-1,∞) × (0,π/2)`) nor their
genuine-order siblings `Work.FTS.H2.WPQ.Zb_DerivLike_sm`, `Tb_DerivLike_sm` (genuine order,
but still on the *bigger* quadrant `quadU`, which `SmoothOpen` does not reach at `z ≤ 0`)
apply directly.  Here the two instances are rebuilt on `Q0`, exactly as in
`Submission/Work/FTS/H2/WPQ/Leibniz.lean`, and the abstract two-operator rule
`Work.Spaces.DerivLike.twoOp_iterate_mul` then produces the binomial expansion, translated
back with `Work.Spaces.Zb_iterate_uncurry`, `Work.Spaces.Tb_iterate_uncurry` and
`Work.Spaces.uncurry_mul`. -/

/-- Uncurried functions which are `C^∞` in the genuine order on the open quadrant
`Q0 = (0,∞) × (0,π/2)`.  This is definitionally the class of
`Work.FTS.EllipticEst.SmoothOpen`. -/
def SmoothOpenU (F : ℝ × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder F Work.FTS.EllipticEst.Q0

lemma SmoothOpenU.differentiableAt {F : ℝ × ℝ → ℝ} (h : SmoothOpenU F) {p : ℝ × ℝ}
    (hp : p ∈ Work.FTS.EllipticEst.Q0) : DifferentiableAt ℝ F p :=
  (h.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt (by simp)

theorem SmoothOpenU_FunClass : Work.Spaces.FunClass (X := ℝ × ℝ) SmoothOpenU where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun p => c * A p) Work.FTS.EllipticEst.Q0
    exact ContDiffOn.const_smul c hA

/-- `Zb = z ∂_z` is a derivation-like operator on the `C^∞`-functions of the open quadrant
`Q0`.  (`Work.FTS.H2.WPQ.Zb_DerivLike_sm` is the same statement on the larger quadrant
`quadU`.) -/
theorem Zb_DerivLike_open :
    Work.Spaces.DerivLike Work.FTS.EllipticEst.Q0 SmoothOpenU Work.Spaces.Zb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hB.differentiableAt hp)
    show Work.Spaces.Zb (A + B) (z, θ) = Work.Spaces.Zb A (z, θ) + Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [show (fun z' => (A + B) (z', θ)) =
          (fun z' => A (z', θ)) + (fun z' => B (z', θ)) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hB.differentiableAt hp)
    show Work.Spaces.Zb (A * B) (z, θ)
        = Work.Spaces.Zb A (z, θ) * B (z, θ) + A (z, θ) * Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [show (fun z' => (A * B) (z', θ)) =
          (fun z' => A (z', θ)) * (fun z' => B (z', θ)) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun z' => A (z', θ)) (fun z' => B (z', θ)) (Set.Ioi (0 : ℝ)) :=
      fun z' hz' => h ⟨hz', hp.2⟩
    show Work.Spaces.Zb A (z, θ) = Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [hs.deriv isOpen_Ioi hp.1]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) Work.FTS.EllipticEst.Q0 :=
      hA.fderiv_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
        (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (fderiv ℝ A p) (1, 0)) Work.FTS.EllipticEst.Q0 :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 * (fderiv ℝ A p) (1, 0)) Work.FTS.EllipticEst.Q0 :=
      (contDiff_fst.contDiffOn).mul hev
    refine hfun.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    dsimp only
    show Work.Spaces.Zb A (z, θ) = z * (fderiv ℝ A (z, θ)) (1, 0)
    simp only [Work.Spaces.Zb]
    rw [Work.Spaces.deriv_slice_fst A z θ (hA.differentiableAt hp)]
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hA.differentiableAt hp)
    show Work.Spaces.Zb (fun p => c * A p) (z, θ) = c * Work.Spaces.Zb A (z, θ)
    simp only [Work.Spaces.Zb]
    rw [deriv_const_mul c hA']
    ring

/-- `Tb = sin(2θ) ∂_θ` is a derivation-like operator on the `C^∞`-functions of the open
quadrant `Q0`.  (`Work.FTS.H2.WPQ.Tb_DerivLike_sm` is the same statement on `quadU`.) -/
theorem Tb_DerivLike_open :
    Work.Spaces.DerivLike Work.FTS.EllipticEst.Q0 SmoothOpenU Work.Spaces.Tb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hB.differentiableAt hp)
    show Work.Spaces.Tb (A + B) (z, θ) = Work.Spaces.Tb A (z, θ) + Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [show (fun θ' => (A + B) (z, θ')) =
          (fun θ' => A (z, θ')) + (fun θ' => B (z, θ')) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hB.differentiableAt hp)
    show Work.Spaces.Tb (A * B) (z, θ)
        = Work.Spaces.Tb A (z, θ) * B (z, θ) + A (z, θ) * Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [show (fun θ' => (A * B) (z, θ')) =
          (fun θ' => A (z, θ')) * (fun θ' => B (z, θ')) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun θ' => A (z, θ')) (fun θ' => B (z, θ')) (Set.Ioo 0 (π / 2)) :=
      fun θ' hθ' => h ⟨hp.1, hθ'⟩
    show Work.Spaces.Tb A (z, θ) = Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [hs.deriv isOpen_Ioo hp.2]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) Work.FTS.EllipticEst.Q0 :=
      hA.fderiv_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
        (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (fderiv ℝ A p) (0, 1)) Work.FTS.EllipticEst.Q0 :=
      hfd.clm_apply contDiffOn_const
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2) * (fderiv ℝ A p) (0, 1))
        Work.FTS.EllipticEst.Q0 :=
      hsin.mul hev
    refine hfun.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    dsimp only
    show Work.Spaces.Tb A (z, θ) = Real.sin (2 * θ) * (fderiv ℝ A (z, θ)) (0, 1)
    simp only [Work.Spaces.Tb]
    rw [Work.Spaces.deriv_slice_snd A z θ (hA.differentiableAt hp)]
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hA.differentiableAt hp)
    show Work.Spaces.Tb (fun p => c * A p) (z, θ) = c * Work.Spaces.Tb A (z, θ)
    simp only [Work.Spaces.Tb]
    rw [deriv_const_mul c hA']
    ring

theorem leibniz_open_mixed :
    ∀ (j i : ℕ) (f g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      Work.FTS.EllipticEst.SmoothOpen g → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ =
        ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) := by
  intro j i f g hf hg z θ hz hθ0 hθ1
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have h2 := (Work.Spaces.DerivLike.twoOp_iterate_mul (X := ℝ × ℝ)
      (s := Work.FTS.EllipticEst.Q0) (P := SmoothOpenU) (Z := Work.Spaces.Zb)
      (Θb := Work.Spaces.Tb) SmoothOpenU_FunClass Zb_DerivLike_open
      Tb_DerivLike_open j i (show SmoothOpenU (Function.uncurry f) from hf)
      (show SmoothOpenU (Function.uncurry g) from hg)) hp
  have h2' : Work.Spaces.Zb^[j] (Work.Spaces.Tb^[i]
        (Function.uncurry f * Function.uncurry g)) (z, θ)
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * ((Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry f))) (z, θ)
               * (Work.Spaces.Zb^[j - b] (Work.Spaces.Tb^[i - a] (Function.uncurry g)))
                   (z, θ)) := by
    simpa using h2
  have hL : Work.Spaces.Zb^[j] (Work.Spaces.Tb^[i]
        (Function.uncurry f * Function.uncurry g)) (z, θ)
      = Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ := by
    rw [Work.Spaces.uncurry_mul f g,
      Work.Spaces.Tb_iterate_uncurry i (fun z θ => f z θ * g z θ),
      Work.Spaces.Zb_iterate_uncurry j (Work.Spaces.DthIter i (fun z θ => f z θ * g z θ))]
    rfl
  have e_f : ∀ a b, Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry f)) (z, θ)
      = Work.Spaces.mixed b a f z θ := fun a b => by
    rw [Work.Spaces.Tb_iterate_uncurry a f,
      Work.Spaces.Zb_iterate_uncurry b (Work.Spaces.DthIter a f)]
    rfl
  have e_g : ∀ a b, Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry g)) (z, θ)
      = Work.Spaces.mixed b a g z θ := fun a b => by
    rw [Work.Spaces.Tb_iterate_uncurry a g,
      Work.Spaces.Zb_iterate_uncurry b (Work.Spaces.DthIter a g)]
    rfl
  rw [← hL, h2']
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  rw [e_f a b, e_g (i - a) (j - b)]

end Work.FTS.OpenPkg.ProdOpen
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EiterEngine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option linter.unusedVariables false

open Work.FTS.GalBasis.cc (Eiter Eop Cbnd contDiff_Eiter Eiter_zero Eiter_succ
  Eiter_eq_zero_of_open_const)

/-- **The abstract bound at all orders.**  If `M` bounds every derivative of `ρ` and `B` every
derivative of `f` on `[0,1]`, then the recursive constant `Cbnd M B k j` bounds the `j`-th
derivative of the `k`-th iterate of `E_ρ f = ρ f'` on `[0,1]`. -/
theorem Eiter_deriv_bound_all {ρ f : ℝ → ℝ} {M B : ℕ → ℝ}
    (hMnn : ∀ m, 0 ≤ M m) (hBnn : ∀ m, 0 ≤ B m)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hf : ∀ n : ℕ, ContDiff ℝ n f)
    (hM : ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m ρ u| ≤ M m)
    (hB : ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m f u| ≤ B m) :
    ∀ k j : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv j (Eiter k ρ f) u| ≤ Cbnd M B k j := by
  intro k
  induction k with
  | zero =>
    intro j u hu
    have e : iteratedDeriv j (Eiter 0 ρ f) u = iteratedDeriv j f u := by rw [Eiter_zero]
    rw [e]
    exact hB j u hu
  | succ k ih =>
    intro j u hu
    rw [Eiter_succ, Eop]
    have hρj : ContDiffAt ℝ (↑j) ρ u := (hρ j).contDiffAt
    have hgard : ContDiffAt ℝ (↑j) (deriv (Eiter k ρ f)) u :=
      ((contDiff_Eiter hρ hf k (j + 1)).deriv').contDiffAt
    rw [iteratedDeriv_mul hρj hgard]
    simp only [Cbnd]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro i hi
    simp only [Finset.mem_range] at hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp hi
    rw [abs_mul, abs_mul]
    have hci : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
    rw [abs_of_nonneg hci]
    have h1 : |iteratedDeriv i ρ u| ≤ M i := hM i u hu
    have he : iteratedDeriv (j - i + 1) (Eiter k ρ f) u
        = iteratedDeriv (j - i) (deriv (Eiter k ρ f)) u := by
      rw [iteratedDeriv_succ']
    rw [← he]
    have h2 : |iteratedDeriv (j - i + 1) (Eiter k ρ f) u| ≤ Cbnd M B k (j - i + 1) :=
      ih (j - i + 1) u hu
    exact mul_le_mul (mul_le_mul le_rfl h1 (abs_nonneg _) (by positivity)) h2 (abs_nonneg _)
      (mul_nonneg (by positivity) (hMnn i))

/-- All the iterated derivatives of the smooth step are bounded on `[0,1]`, by a constant
depending on the order. -/
theorem exists_iteratedDeriv_smoothTransition_bound :
    ∃ B : ℕ → ℝ, (∀ m : ℕ, 0 ≤ B m) ∧ ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv m Real.smoothTransition u| ≤ B m := by
  have hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv m Real.smoothTransition u| ≤ C := by
    intro m
    have hcont : Continuous (iteratedDeriv m Real.smoothTransition) := by
      apply ContDiff.continuous_iteratedDeriv' m
      exact Real.smoothTransition.contDiff
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun u hu => by
      have h := hC u hu
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)⟩
  choose B hB0 hB using hb
  exact ⟨B, hB0, hB⟩


end Work.FTS.PhiStar.Honesty.CptApp
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxReg_of_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Auxiliary: uniform convergence transferred across an equality on the set -/


/-! ## The main theorem -/


end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.L2Mem_of_HkMem_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# From `H^0`-membership (weighted) to plain `L²`-membership

The `H^0`-weighted integrand of `g` is

`HkIntegrand α 0 g z θ = (g z θ · w(z) / sin(2θ)^{η/2})²`

and on the *interior* of the quadrant (`z > 0`, `0 < θ < π/2`) the weight
`w(z)/sin(2θ)^{η/2}` is `≥ 1` (both `w z ≥ 1` and `sin(2θ)^{η/2} ≤ 1` there), so the
weighted integrand dominates `g²` pointwise a.e.  Together with the vanishing hypothesis
`g 0 θ = 0` at the degenerate line `z = 0` (where `w = 0` by Lean's totalised division and
the weighted integrand carries no information) this gives the honesty of `∫_θ g²` for
every `z ≥ 0`, and — with the a.e. measurability hypotheses ensuring that the sliced
integrals are measurable — also the honesty of `∫_z ∫_θ g²`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- The radial weight is at least `1` on the open half-line: `w(z) = ((1+z)/z)² ≥ 1`. -/
lemma one_le_w (z : ℝ) (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have h : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by
    rw [Work.Spaces.w, div_pow]
  rw [h]
  have h1 : 1 ≤ (1 + z) / z := by
    rw [le_div_iff₀ hz]
    linarith
  exact one_le_pow₀ h1

/-- `sin(2θ)^{η/2} ≤ 1` on the open angular interval. -/
lemma sin_two_rpow_le_one {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  exact Real.rpow_le_one hs0 hs1 (by norm_num [Work.Spaces.eta])

/-- The `H^0`-weight `w(z)/sin(2θ)^{η/2}` is at least `1` in the interior of the quadrant. -/
lemma one_le_weight {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs0 : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hpos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  refine (one_le_div hpos).mpr ?_
  exact le_trans (sin_two_rpow_le_one h0 h1) (one_le_w z hz)




end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.slotSliceData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Elementary endpoint estimates

The angular weight `sin(2θ)^{-η}` is integrable on `[0,π/2]` (`η < 1`), so the only real
content of the slice integrability of the level-`0` `ℋ`-integrand of `Ψ / cos θ` is the
*boundedness* of `θ ↦ Ψ z θ / cos θ` on the closed interval.  Two facts are used:

* `cos θ` has the same size as `π/2 - θ` (Jordan's inequality, `Real.mul_le_sin`);
* `BoxReg Ψ` together with `Ψ z (π/2) = 0` forces `|Ψ z θ| ≲ (π/2 - θ)` (mean value
  inequality on the closed box, `Convex.norm_image_sub_le_of_norm_derivWithin_le`). -/





end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.H2.WPQ.m_term_le_smoothQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.WPQ

open scoped Real

set_option maxHeartbeats 0

/-- `0 ≤ sin(2θ)` on the open quadrant. -/
private theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) := (Work.FTS.H2.WPQ.sin_two_pos_of_Ioo hθ).le

/-- The square of the `f`-side angular factor `(α + sin 2θ) sin(2θ)^{α/5}` is
`(α + sin 2θ)² sin(2θ)^{2α/5}`. -/
private theorem phi_sq {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  rw [mul_pow]
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hss : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [show ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          = ((Real.sin (2 * θ)) ^ (α / 5)) ^ ((2 : ℝ)) from (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hs, show (α / 5) * (2 : ℝ) = 2 * α / 5 by ring]
  rw [hss]

/-- `(α + sin 2θ)² sin(2θ)^{2α/5} ≤ 4` for `0 < α ≤ 1` and `0 < θ < π/2`. -/
private theorem psi2_le_four {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 4 := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have h1 : (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 1 :=
    Real.rpow_le_one hs (Real.sin_le_one _) (by linarith)
  have h2 : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
    nlinarith [hs, Real.sin_le_one (2 * θ), hα, hα1]
  nlinarith [h1, h2, Real.rpow_nonneg hs (2 * α / 5)]



end Work.H2.WPQ
end
