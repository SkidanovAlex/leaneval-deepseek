import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.SupOpenH2Z
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.EllipticEst.Core.mixedFamily_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# The mixed-derivative family of the interpolation estimate

For `1 ≤ i` and `i + j ≤ k` the `(i,j)`-summand of the left-hand side of
`HkSqLHS_le_summands` is

`∫_z w(z)² ∫_θ (D_z^{j+1} D_θ^i ∂_θ V)² sin(2θ)^{-γ}`,

a mixed derivative of order `i + j` of `∂_θ V`.  The present file shows that the whole
family is dominated by the `ℋ^k`-norm of `∂_θ²V`: the point is that

`D_θ^i ∂_θ V = D_θ^{i-1}(sin(2θ) · ∂_θ²V)`

and the Leibniz expansion of `D_θ^{i-1}` of that product produces only the derivatives
`D_θ^b ∂_θ²V`, `b ≤ i - 1`, with coefficients `D_θ^a(sin 2θ)` that are `O(sin 2θ)`.
The `θ`-pointwise inequality for this expansion is `mixedSliceLe_pointwise` (already
proved in `mixedSliceLe`); here we

* identify the weighted square `(D_z^{j+1}D_θ^b∂_θ²V · W)²` of the right-hand side of
  that pointwise inequality with one of the *summands* of `HkIntegrand α k (∂_θ²V)`
  (`Work.Spaces.sq_le_HkIntegrand_mixed`/`_z`), so that each of them is bounded by the
  whole integrand;
* integrate the resulting slicewise inequality in `θ` (`integral_mono_of_nonneg`, which
  needs no measurability of the smaller integrand) and in `z` (same, using the
  marginal integrability supplied by `HkMem`);
* sum over the finitely many slots `(i,j)`, `1 ≤ i`, `i+j ≤ k`, and use `α ≤ 1/4` so
  that `α² ≤ 1`.

Nothing here needs the two angular-vanishing hypotheses of the statement, nor the
`ℋ^k`-membership of `D_zV` or `D_z²V`; they are simply carried along.
-/

/-! ## Weight identities on `Iθ` -/

/-- `wTheta α θ ^ 2 = thGam α θ` on `Iθ`, for `0 < α`: the angular weight of the mixed
slots of `HkIntegrand` is the square of the weight `w_θ` of the paper. -/
lemma wTheta_sq_eq_thGam {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.wTheta α θ ^ 2 = Work.FTS.EllipticEst.thGam α θ := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ2 : -(Work.Spaces.gam α / 2) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (by linarith : 0 < Work.Spaces.gam α / 2))
  have hγ : -(Work.Spaces.gam α) ≠ 0 := neg_ne_zero.mpr (ne_of_gt hγpos)
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs with h0 | hpos
  · simp only [Work.Spaces.wTheta, Work.FTS.EllipticEst.thGam, ← h0]
    rw [Real.zero_rpow hγ2, Real.zero_rpow hγ]
    norm_num
  · simp only [Work.Spaces.wTheta, Work.FTS.EllipticEst.thGam]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hpos)]
    congr 1
    ring

/-- `Wt α z θ ^ 2 = w z ^ 2 * thGam α θ` on `Iθ`: the square of the full weight of the
mixed slots is the radial weight squared times the angular weight. -/
lemma Wt_sq_eq {α : ℝ} (hα : 0 < α) (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Wt α z θ ^ 2 = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
  simp only [Work.Spaces.Wt]
  rw [mul_pow, wTheta_sq_eq_thGam hα hθ]

/-- `(w z / sin(2θ)^{η/2})^2 = w z ^ 2 * thEta θ` on `Iθ`: the square of the radial weight
of the `D_z`-family is the radial weight squared times `thEta`. -/
lemma w_div_sin_sq_eq (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  have hη : (Work.Spaces.eta) ≠ 0 := by norm_num [Work.Spaces.eta]
  have hη2 : (Work.Spaces.eta / 2) ≠ 0 := by norm_num [Work.Spaces.eta]
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs with h0 | hpos
  · simp only [Work.FTS.EllipticEst.thEta, ← h0]
    rw [Real.zero_rpow (neg_ne_zero.mpr hη), Real.zero_rpow hη2]
    simp
  · have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hpos)]
      congr 1
      ring
    simp only [Work.FTS.EllipticEst.thEta]
    rw [div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hpos) Work.Spaces.eta]

/-- The `θ`-integral of the `ℋ^k`-integrand is nonnegative. -/
lemma integral_HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
  MeasureTheory.integral_nonneg_of_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))

/-! ## The pointwise (in `(z,θ)`) bound -/

/-- **The pointwise bound of the mixed family.**  For `1 ≤ i`, `i + j ≤ k`, `z > 0` and
every `θ ∈ Iθ`, the weighted square of `D_z^{j+1}D_θ^i∂_θV` (with the *unweighted*
weight `w(z)² thGam α θ`) is bounded by a constant times the `ℋ^k`-integrand of
`∂_θ²V`.  It is the Leibniz expansion `mixedSliceLe_pointwise` followed by the
identification of each of its terms with a summand of `HkIntegrand α k (∂_θ²V)`. -/
lemma mixedIntS_pointwise_le {k : ℕ} {K : ℝ} (hKpos : 0 ≤ K)
    (hK : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter i s1 θ| ≤ K * s1 θ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {V : ℝ → ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ)
        ≤ ((i : ℝ) * 4 ^ (i - 1) * K ^ 2) * ((i : ℝ) + 1)
            * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by
  intro θ hθ
  have hik : i ≤ k := by omega
  have hCptnn : 0 ≤ (i : ℝ) * 4 ^ (i - 1) * K ^ 2 := by positivity
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ :=
    Work.Spaces.HkIntegrand_nonneg _ _ _ _ _
  have hpw := mixedSliceLe_pointwise hKpos hK hα hα1 hV hi hik j hz θ hθ
  have h2 := mul_le_mul_of_nonneg_left hpw (sq_nonneg (Work.Spaces.w z))
  have hb : ∀ b ∈ Finset.Icc 1 (i - 1),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ)
      ≤ Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by
    intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hbjk : b + (j + 1) ≤ k := by
      have := (Finset.mem_Icc.mp hb).2
      omega
    have hmix := Work.Spaces.sq_le_HkIntegrand_mixed α k (Work.Spaces.pthIter 2 V) z θ b
      (j + 1) hb1 hbjk
    have hgoal : (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ
          * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) := by
      rw [mul_pow, Wt_sq_eq hα z hθ]; ring
    rwa [hgoal] at hmix
  have hzsl : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      ≤ Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by
    have hz0 := Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 V) z θ (j + 1)
      (by omega)
    have hgoal : (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
      rw [mul_pow, w_div_sin_sq_eq z hθ]; ring
    rwa [hgoal] at hz0
  have hsum : (Work.Spaces.w z) ^ 2 * ((∑ b ∈ Finset.Icc 1 (i - 1),
        (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ)
      + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      ≤ ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by
    rw [mul_add, Finset.mul_sum]
    have hcard : ((Finset.Icc 1 (i - 1)).card : ℝ) ≤ (i : ℝ) := by
      have h1 : (Finset.Icc 1 (i - 1)).card ≤ i := by
        have hsub : Finset.Icc 1 (i - 1) ⊆ Finset.range i := fun b hb =>
          Finset.mem_range.mpr (by have h := (Finset.mem_Icc.mp hb).2; omega)
        calc (Finset.Icc 1 (i - 1)).card ≤ (Finset.range i).card := Finset.card_le_card hsub
          _ = i := Finset.card_range i
      exact_mod_cast h1
    calc (∑ b ∈ Finset.Icc 1 (i - 1), (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) b
            (Work.Spaces.pthIter 2 V) z θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ))
          + (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
        ≤ (∑ b ∈ Finset.Icc 1 (i - 1),
            Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ)
          + Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ :=
          add_le_add (Finset.sum_le_sum hb) hzsl
      _ = ((Finset.Icc 1 (i - 1)).card : ℝ)
            * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ
          + Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (i : ℝ) * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ
          + Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ :=
          add_le_add (mul_le_mul_of_nonneg_right hcard hHnn) le_rfl
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by ring
  calc (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ)
      ≤ (Work.Spaces.w z) ^ 2 * (((i : ℝ) * 4 ^ (i - 1) * K ^ 2)
          * ((∑ b ∈ Finset.Icc 1 (i - 1),
                (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thGam α θ)
            + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)) := h2
    _ = ((i : ℝ) * 4 ^ (i - 1) * K ^ 2)
          * ((Work.Spaces.w z) ^ 2 * ((∑ b ∈ Finset.Icc 1 (i - 1),
                (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thGam α θ)
            + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)) := by ring
    _ ≤ ((i : ℝ) * 4 ^ (i - 1) * K ^ 2)
          * (((i : ℝ) + 1) * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ) :=
        mul_le_mul_of_nonneg_left hsum hCptnn
    _ = ((i : ℝ) * 4 ^ (i - 1) * K ^ 2) * ((i : ℝ) + 1)
          * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by ring

/-! ## Integration of the pointwise bound -/

/-- The slicewise consequence of `mixedIntS_pointwise_le`: for every `z ∈ Iz` the
`θ`-slice integrand `mixedIntS α i j V z` is bounded by a constant times the
`θ`-integral of the `ℋ^k`-integrand of `∂_θ²V`. -/
lemma mixedIntS_le_slice {k : ℕ} {K : ℝ} (hKpos : 0 ≤ K)
    (hK : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter i s1 θ| ≤ K * s1 θ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {V : ℝ → ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    ∀ z ∈ Work.Spaces.Iz,
      mixedIntS α i j V z
        ≤ ((i : ℝ) * 4 ^ (i - 1) * K ^ 2) * ((i : ℝ) + 1)
            * (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ) := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [show mixedIntS α i j V z = 0 from by
        rw [← hz0]; simp [mixedIntS, Work.Spaces.w]]
    exact mul_nonneg (by positivity) (integral_HkIntegrand_nonneg α k _ z)
  · have hrew : mixedIntS α i j V z
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ) := by
      rw [mixedIntS]
      exact (MeasureTheory.integral_const_mul _ _).symm
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))))
      ((hmem.1 z hz).const_mul _)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mixedIntS_pointwise_le hKpos hK hα hα1 hV hi hij hzpos θ hθ))
    rw [hrew, MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
    exact hmono

/-- **The slot estimate.**  For `1 ≤ i`, `i + j ≤ k`, the `z`-integral of
`mixedIntS α i j V z` is bounded by a constant times `HkSq α k (∂_θ²V)`.  This is
`mixedIntS_le_slice` integrated in `z` with `integral_mono_of_nonneg`. -/
lemma mixedIntS_integral_le {k : ℕ} {K : ℝ} (hKpos : 0 ≤ K)
    (hK : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter i s1 θ| ≤ K * s1 θ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {V : ℝ → ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    ∫ z in Work.Spaces.Iz, mixedIntS α i j V z
      ≤ ((i : ℝ) * 4 ^ (i - 1) * K ^ 2) * ((i : ℝ) + 1)
          * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) := by
  have hpt := mixedIntS_le_slice hKpos hK hα hα1 hV hmem hi hij
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => by
      rw [mixedIntS]
      exact mul_nonneg (sq_nonneg _)
        (MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => mul_nonneg (sq_nonneg _)
              (Work.FTS.EllipticEst.thGam_nonneg hθ))))))
    (hmem.2.const_mul _)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hpt z hz)
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono

/-! ## The family -/

/-- **The mixed-derivative family of the interpolation estimate.**  For every `k` there
is a constant `C > 0` such that for `0 < α ≤ 1/4` and every `V` smooth on the open
quadrant with `V ∈ ℋ^k` in the three relevant norms,

`α² ∑_{1 ≤ i, i+j ≤ k} ∫_z w² ∫_θ (D_z^{j+1}D_θ^i∂_θV)² sin(2θ)^{-γ}
   ≤ C (α⁴ HkSq(D_z²V) + HkSq(∂_θ²V) + α² HkSq(D_zV))`.

Each summand is estimated by a summand of `HkSq α k (∂_θ²V)`, so the right-hand side is
dominated by its second term; the factor `α² ≤ 1` and the finitely many slots produce
the stated constant. -/
theorem mixedFamily_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
          else 0)
        ≤ C * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.sd_lop_iter_sin_bound k
  have hKnn : 0 ≤ K := hKpos.le
  refine ⟨1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k, ?_, ?_⟩
  · positivity
  · intro α V hα hα14 hV _ _ _ hPth2 _
    have hα1 : α ≤ 1 := by linarith
    have hV' : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU := hV
    set B : ℝ := Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) with hB
    have hBnn : 0 ≤ B := by rw [hB]; exact Work.Spaces.HkSq_nonneg _ _ _
    -- the per-slot estimate
    have hslot : ∀ i j, i ∈ Finset.range (k + 1) → j ∈ Finset.range (k + 1) →
        (if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, mixedIntS α i j V z else 0)
          ≤ K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B := by
      intro i j hi hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc]
        refine le_trans (mixedIntS_integral_le hKnn hK hα hα1 hV' hPth2 hc.1 hc.2) ?_
        have hi1 : (i : ℝ) ≤ (k : ℝ) + 1 := by
          exact_mod_cast (by omega : i ≤ k + 1)
        have hi2 : (i : ℝ) + 1 ≤ (k : ℝ) + 1 := by
          exact_mod_cast (by omega : i + 1 ≤ k + 1)
        have hp : (4 : ℝ) ^ (i - 1) ≤ (4 : ℝ) ^ k :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hfirst : (i : ℝ) * 4 ^ (i - 1) * K ^ 2 ≤ ((k : ℝ) + 1) * (4 : ℝ) ^ k * K ^ 2 :=
          mul_le_mul (mul_le_mul hi1 hp (by positivity) (by positivity)) le_rfl
            (sq_nonneg K) (by positivity)
        have hle : (i : ℝ) * 4 ^ (i - 1) * K ^ 2 * ((i : ℝ) + 1)
            ≤ K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 := by
          calc (i : ℝ) * 4 ^ (i - 1) * K ^ 2 * ((i : ℝ) + 1)
              ≤ (((k : ℝ) + 1) * (4 : ℝ) ^ k * K ^ 2) * ((k : ℝ) + 1) :=
                mul_le_mul hfirst hi2 (by positivity) (by positivity)
            _ = K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 := by ring
        exact mul_le_mul_of_nonneg_right hle hBnn
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hBnn
    -- the full sum
    have hsum : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, mixedIntS α i j V z else 0))
        ≤ (((k : ℝ) + 1) * ((k : ℝ) + 1))
            * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              ∫ z in Work.Spaces.Iz, mixedIntS α i j V z else 0))
          ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
              (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B) :=
            Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hslot i j hi hj
        _ = (((k : ℝ) + 1) * ((k : ℝ) + 1))
              * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hα2le : α ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α - 1)]
    have hcnn : 0 ≤ 1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k := by positivity
    calc α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, mixedIntS α i j V z else 0))
        ≤ α ^ 2 * ((((k : ℝ) + 1) * ((k : ℝ) + 1))
            * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B)) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg α)
      _ ≤ 1 * ((((k : ℝ) + 1) * ((k : ℝ) + 1))
            * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B)) :=
          mul_le_mul_of_nonneg_right hα2le (by positivity)
      _ = ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k * B := by ring
      _ ≤ (1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k) * B := by
          have h1 : ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k
              ≤ 1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k := by linarith
          calc ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k * B
              = (((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k) * B := by ring
            _ ≤ (1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k) * B :=
                mul_le_mul_of_nonneg_right h1 hBnn
      _ ≤ (1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k)
            * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
              + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
              + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcnn
          rw [hB]
          have hA : 0 ≤ α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) :=
            mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
          have hD : 0 ≤ α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
            mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
          linarith

end

end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.cmode_memLp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal BigOperators symmDiff
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

/-! ## The product set `Ioi 0 ×ˢ Iθ` is `Q0` up to a null set -/

/-- The boundary `Ioi 0 ×ˢ {0, π/2}` of the closed quadrant `Ioi 0 ×ˢ Iθ` is null. -/
theorem volume_Ioi_prod_pair : (volume : Measure (ℝ × ℝ))
    (Set.Ioi 0 ×ˢ ({0, π / 2} : Set ℝ)) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Work.Spaces.null_pair, mul_zero]

/-- Restricted to `Ioi 0 ×ˢ Iθ`, the Lebesgue measure agrees with its restriction to the open
quadrant `Q0` (the two sets differ by the null set `Ioi 0 ×ˢ {0, π/2}`). -/
theorem restrict_Ioi_prod_Iθ_eq_Q0 :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0 := by
  have hnull := volume_Ioi_prod_pair
  have hsub : (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) \ Work.FTS.EllipticEst.Q0
      ⊆ Set.Ioi 0 ×ˢ ({0, π / 2} : Set ℝ) := by
    intro p hp
    rw [Set.mem_sdiff] at hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp1
    refine Set.mem_prod.mpr ⟨hz, ?_⟩
    have hθ' : (0 : ℝ) ≤ p.2 ∧ p.2 ≤ π / 2 := hθ
    by_cases h : p.2 = 0
    · rw [h]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · have hpos : 0 < p.2 := lt_of_le_of_ne hθ'.1 (Ne.symm h)
      have hlt : p.2 = π / 2 := by
        by_contra hne
        exact hp2 (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hpos, lt_of_le_of_ne hθ'.2 hne⟩)
      rw [hlt]; exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
  refine Measure.restrict_congr_set ?_
  rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
  refine measure_mono_null ?_ hnull
  rintro p (hp | hp)
  · exact hsub hp
  · exfalso
    rw [Set.mem_sdiff] at hp
    exact hp.2 (Set.mem_prod.mpr ⟨(Work.FTS.EllipticEst.mem_Q0.mp hp.1).1,
      ⟨le_of_lt (Work.FTS.EllipticEst.mem_Q0.mp hp.1).2.1,
       le_of_lt (Work.FTS.EllipticEst.mem_Q0.mp hp.1).2.2⟩⟩)

/-! ## Measurability of the mode coefficients -/

/-- The numerator `bInt m F` of the mode coefficient is a.e. strongly measurable in `z`:
it is the `z`-slice integral of a function which is continuous on the open quadrant. -/
theorem aesm_bInt {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) (m : ℕ) :
    AEStronglyMeasurable (fun z => bInt m F z) (volume.restrict (Set.Ioi 0)) := by
  set φ : ℝ × ℝ → ℝ := fun p =>
    (Real.sqrt (Real.cos p.2) * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
      * (Real.sqrt (Real.cos p.2) * F p.1 p.2) with hφ
  have hcont : ContinuousOn φ Work.FTS.EllipticEst.Q0 := by
    have h1 : Continuous (fun p : ℝ × ℝ => Real.sqrt (Real.cos p.2)) :=
      Real.continuous_sqrt.comp (Real.continuous_cos.comp continuous_snd)
    have h2 : Continuous (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2) :=
      (continuous_eFam m).comp continuous_snd
    exact (h1.continuousOn.mul h2.continuousOn).mul (h1.continuousOn.mul hsm.continuousOn)
  have haesmφ : AEStronglyMeasurable φ (volume.restrict Work.FTS.EllipticEst.Q0) :=
    hcont.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have hν : (volume : Measure ℝ).restrict Work.Spaces.Iθ
      = (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) :=
    Measure.restrict_congr_set Work.Spaces.Iθ_ae_eq_Ioo
  have hprod : (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ))
      = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0 := by
    rw [hν, Measure.prod_restrict, Measure.volume_eq_prod]
    rfl
  have haesmφ' : AEStronglyMeasurable φ (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
    rw [hprod]; exact haesmφ
  have h := haesmφ'.integral_prod_right'
  have hfun : (fun z => ∫ (y : ℝ), φ (z, y)
        ∂((volume : Measure ℝ).restrict Work.Spaces.Iθ)) = fun z => bInt m F z := by
    funext z
    simp only [hφ, bInt]
  rwa [hfun] at h

/-- The mode coefficients `cmode m F` are a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_cmode {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) (m : ℕ) :
    AEStronglyMeasurable (fun z => Work.FTS.PhiStar.Series.cmode m F z)
      (volume.restrict (Set.Ioi 0)) := by
  have hb := aesm_bInt hsm m
  have hdiv : AEStronglyMeasurable (fun z => bInt m F z / eNorm m)
      (volume.restrict (Set.Ioi 0)) := by
    simpa only [div_eq_mul_inv] using hb.mul_const (eNorm m)⁻¹
  exact hdiv.congr (Eventually.of_forall fun z => (cmode_eq m F z).symm)

/-! ## Integrability of the squared mode coefficients -/

/-- **Bessel's inequality, integrated in `z`.**  For every `z` the Bessel bound of
`cmode_bessel` holds; Tonelli then identifies the `z`-integral of its right-hand side with the
double integral over `Ioi 0 ×ˢ Iθ`, which is finite. -/
theorem lintegral_ofReal_eNorm_mul_cmode_sq_lt_top {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Work.FTS.EllipticEst.Q0)
    (m : ℕ) :
    (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (eNorm m *
      (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)) < ∞ := by
  let G : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2)
  have hbd : ∀ z, ENNReal.ofReal (eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) ≤
      ∫⁻ θ in Work.Spaces.Iθ, G (z, θ) := by
    intro z
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (cmode_bessel F z m)
    have hterm : (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
        * Work.FTS.PhiStar.Series.cmode m F z ^ 2
        = eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := rfl
    rw [← hterm]
    refine Finset.single_le_sum (f := fun k => (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam k θ ^ 2 * Real.cos θ)
        * Work.FTS.PhiStar.Series.cmode k F z ^ 2) (fun k _ => ?_)
      (Finset.mem_range.mpr (Nat.lt_succ_self m))
    have hk : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam k θ ^ 2 * Real.cos θ) = eNorm k := rfl
    rw [hk]
    exact mul_nonneg (le_of_lt (eNorm_pos k)) (sq_nonneg _)
  have hGcont : ContinuousOn G Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
        Work.FTS.EllipticEst.Q0 :=
      (hsm.continuousOn.pow 2).mul (Real.continuous_cos.comp continuous_snd).continuousOn
    exact ENNReal.continuous_ofReal.comp_continuousOn h1
  have hGmeas : AEMeasurable G
      ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
    rw [restrict_Ioi_prod_Iθ_eq_Q0]
    exact hGcont.aemeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have h1 : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (eNorm m *
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, G (z, θ) := lintegral_mono hbd
  have h2 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, G (z, θ))
      = ∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, G p :=
    (setLIntegral_prod G hGmeas).symm
  have h3 : (∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, G p)
      ≤ ∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (F p.1 p.2 ^ 2) := by
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure (ℝ × ℝ)))
      (s := Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
      (MeasurableSet.prod measurableSet_Ioi measurableSet_Iθ)] with p hp
    exact ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right (sq_nonneg _) (Real.cos_le_one p.2))
  have h4 : (∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (F p.1 p.2 ^ 2))
      = ∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2) := by
    rw [restrict_Ioi_prod_Iθ_eq_Q0]
  have h5 : (∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2)) < ∞ := by
    have hf := hasFiniteIntegral_iff_enorm.mp hL2.2
    rwa [lintegral_congr (fun p => ?_)] at hf
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  calc (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (eNorm m *
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, G (z, θ) := h1
    _ = ∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, G p := h2
    _ ≤ ∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (F p.1 p.2 ^ 2) := h3
    _ = ∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2) := h4
    _ < ∞ := h5

/-- The squared mode coefficients are a.e. finite in the `lintegral` sense. -/
theorem lintegral_ofReal_cmode_sq_lt_top {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Work.FTS.EllipticEst.Q0)
    (m : ℕ) :
    (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2)) < ∞ := by
  have hNpos : (0 : ℝ) < eNorm m := eNorm_pos m
  have hNne : ENNReal.ofReal (eNorm m) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hNpos)
  have hle : (fun z => ENNReal.ofReal ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ fun z => (ENNReal.ofReal (eNorm m))⁻¹ *
          ENNReal.ofReal (eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by
    intro z
    have hz : (ENNReal.ofReal (eNorm m))⁻¹ *
        ENNReal.ofReal (eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
        = ENNReal.ofReal ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by
      rw [ENNReal.ofReal_mul (le_of_lt hNpos), ← mul_assoc,
        ENNReal.inv_mul_cancel hNne ENNReal.ofReal_ne_top, one_mul]
    exact le_of_eq hz.symm
  calc (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, (ENNReal.ofReal (eNorm m))⁻¹ *
          ENNReal.ofReal (eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) :=
        lintegral_mono hle
    _ = (ENNReal.ofReal (eNorm m))⁻¹ *
          ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (eNorm m *
            (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hNne)
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hNpos))
        (lintegral_ofReal_eNorm_mul_cmode_sq_lt_top hsm hL2 m)

/-- **The mode coefficients of an `L²` source are square integrable in the radial variable.** -/
theorem cmode_memLp {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Work.FTS.EllipticEst.Q0)
    (m : ℕ) : MeasureTheory.IntegrableOn (fun z => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) (Set.Ioi 0) := by
  refine ⟨?_, ?_⟩
  · exact aesm_cmode hsm m |>.pow 2
  · rw [hasFiniteIntegral_iff_enorm]
    have henorm : (fun z => ‖(Work.FTS.PhiStar.Series.cmode m F z) ^ 2‖ₑ)
        = fun z => ENNReal.ofReal ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by
      funext z
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
    rw [henorm]
    exact lintegral_ofReal_cmode_sq_lt_top hsm hL2 m

end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.FTS.ClassC.VopGen.HkMem_zero_slice_mu =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopGen

set_option autoImplicit false

theorem HkMem_zero_slice_mu {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (h : Work.Spaces.HkMem α 0 g) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ := by
  intro z hz
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (by positivity) (by positivity)
  -- Step 1: the `sEta`-weighted slice, from the level-`0` membership.
  have hEta : IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have hWt := Work.FTS.EllipticEst.remov.HkMem_zero_slice_Wt h hzIz
    have hfac : (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.remov.Wt z θ)
        = fun θ => (Work.Spaces.w z) ^ 2
            * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      funext θ
      simp only [Work.FTS.EllipticEst.remov.Wt]
      ring
    rw [hfac] at hWt
    have h2 := hWt.const_mul ((Work.Spaces.w z) ^ 2)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h2 (fun θ _ => ?_)
      Work.FTS.EllipticEst.remov.measurableSet_Iθ
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hw), one_mul]
  -- Step 2: restrict to the open angular interval (the endpoints are null).
  have hEta' : IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (π / 2)) :=
    hEta.mono_set (by intro θ hθ; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- Step 3: the `sin(2θ)`-factor is positive on the open interval.
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  -- Step 4: the target slice is continuous on the open interval.
  have hcont : ContinuousOn
      (fun θ : ℝ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo 0 (π / 2)) := by
    have hg : ContinuousOn (fun θ : ℝ => g z θ) (Set.Ioo 0 (π / 2)) :=
      Work.FTS.LocData.continuousOn_slice_theta hsm.continuousOn hz
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    exact (hg.pow 2).mul (hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ))))
  -- Step 5: domination by the `sEta`-weighted slice on the open interval.
  have hmono : IntegrableOn
      (fun θ : ℝ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo 0 (π / 2)) := by
    refine MeasureTheory.Integrable.mono' hEta'
      (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    rw [MeasureTheory.ae_restrict_iff' (s := Set.Ioo 0 (π / 2)) measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    have hnn : 0 ≤ (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [Work.FTS.EllipticEst.sEta]
    refine Real.rpow_le_rpow_of_exponent_ge (hsinpos θ hθ) (Real.sin_le_one _) ?_
    simp only [Work.Spaces.gam, Work.Spaces.eta]
    nlinarith [hα, hα4]
  -- Step 6: transport back to the closed interval.
  refine MeasureTheory.IntegrableOn.congr_set_ae hmono ?_
  show Set.Icc 0 (π / 2) =ᵐ[volume] Set.Ioo 0 (π / 2)
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

end Work.FTS.ClassC.VopGen
end
end
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.dzIterSumConstMul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux


end Work.FTS.EllSol.VopAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeU2.sliceSigmaTraceZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeU2

/-!
# Second-order `σ`-Poincaré on one angular slice, with vanishing endpoint traces

Target of this file: `Work.FTS.EllipticEst.H2W.AeU2.sliceSigmaTraceZero`, the `∫⁻`-form of the
second-order weighted Poincaré inequality on a single angular slice.  For a function `f` of class
`C²` on the open interval `(0, π/2)` whose one-sided endpoint limits both vanish and whose second
derivative is square integrable against the angular weight `σ θ = sin(2θ)^{-η}` (`η = 99/100`),

  `∫⁻_{Iθ} ofReal (f² σ) ≤ ofReal C · ∫⁻_{Iθ} ofReal ((f'')² σ)`,

with a universal constant `C` (`Iθ = [0, π/2]`).

The real-integral form is proved here as `sliceEtaPoincareC2` (with the additional output that
`f²σ` and `(f')²σ` are integrable on `Iθ`); it is the `C²`-version of the `C^∞` statement
`Work.FTS.EllipticEst.H2W.sliceEtaPoincare` and is proved by the same argument, copied and adapted
to the weak class: write `f' = c₀ + V` with `V = ∫_0^θ f''` the primitive of `f''`; the constant
`c₀` is pinned down by `∫_{Iθ} f' = 0` (a consequence of the two vanishing endpoint limits, via the
fundamental theorem of calculus with limits) and is bounded by `c₀² ≤ (2/π) ∫_{Iθ} V²`; the weighted
Hardy inequality `HardyPrimEta` (primitive form) is then applied to `g = f''` and to `g = f'`.
Only the first and the second derivative of `f` are ever used, so `ContDiffOn ℝ 2` is enough.

The `∫⁻`/`ofReal` bridge between the two forms is
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal` (`f²σ ≥ 0` on `Iθ` and integrable there).
-/

noncomputable section

open scoped Real Topology Interval ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- The first derivative of a `C²` function is `C¹` on the open interval. -/
private theorem contDiffOn_deriv_one {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  hu.deriv_of_isOpen isOpen_Ioo (by norm_num)

/-- The second derivative of a `C²` function is continuous on the open interval. -/
private theorem continuousOn_deriv_deriv {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (deriv (deriv u)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (contDiffOn_deriv_one hu).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

/-- A closed unordered interval contained in `[0, π/2]` is contained in `Iθ`. -/
private theorem uIcc_subset_Iθ {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ Real.pi / 2)
    (hb' : b ≤ Real.pi / 2) : Set.uIcc a b ⊆ Work.Spaces.Iθ := by
  intro x hx
  exact ⟨le_trans (le_min ha hb) hx.1, le_trans hx.2 (max_le ha' hb')⟩

/-- An integrable function on `Iθ` is interval integrable on `[0, π/2]`. -/
private theorem intervalIntegrable_of_integrableOn_Iθ {f : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn f Work.Spaces.Iθ) :
    IntervalIntegrable f volume 0 (Real.pi / 2) := by
  have h' : MeasureTheory.IntegrableOn f (Set.uIcc (0 : ℝ) (Real.pi / 2)) volume := by
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2), ← Work.Spaces.Iθ]
    exact h
  exact h'.intervalIntegrable

/-- **The `C²` weighted slice Poincaré inequality** with the angular weight `sin(2θ)^{-η}`.

For a `C²` function `u` on the open interval `(0, π/2)` whose one-sided endpoint limits both
vanish and whose second derivative satisfies `∫_{Iθ} (u'')² sin(2θ)^{-η} < ∞`, both `u` and `u'`
are square integrable against `sin(2θ)^{-η}`, and their weighted norms are controlled by the
weighted norm of the second derivative — this is `sliceEtaPoincare` with `C^∞` weakened to `C²`. -/
theorem sliceEtaPoincareC2 :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ,
      ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  obtain ⟨K, hKpos, hKmain⟩ := HardyPrimEta
  obtain ⟨hwint, hwle, hone, hwnn, hwcont⟩ := SliceEtaFacts
  refine ⟨(2 * 10 ^ 4 + 2) * (K + K ^ 2), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 2 * 10 ^ 4 + 2 := by norm_num
    have h2 : (0 : ℝ) < K + K ^ 2 := by nlinarith
    exact mul_pos h1 h2
  · intro u hu hlim0 hlim1 hint
    have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
    have hpi4 : (0 : ℝ) < Real.pi / 4 := by positivity
    -- the open interval and `Iθ` carry the same restricted measure
    have hIoo_ae : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
        = volume.restrict Work.Spaces.Iθ :=
      Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
    have hcontW : ContinuousOn (fun θ => Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      fun θ hθ => (hwcont θ hθ).continuousWithinAt
    have hone_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        1 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [← hIoo_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact hone θ hθ
    -- weak regularity of `u'` and `u''` on the open interval
    have hderiv1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u θ) θ :=
      fun θ hθ =>
        ((hu.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have hderiv2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (deriv u) (deriv (deriv u) θ) θ := fun θ hθ =>
      (((contDiffOn_deriv_one hu).differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have hcontD1 : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_deriv_one hu).continuousOn
    have hcontD2 : ContinuousOn (deriv (deriv u)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      continuousOn_deriv_deriv hu
    -- the weighted norm of `u''`
    set R : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hR
    have hRnn : 0 ≤ R := by
      rw [hR]
      exact setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (hwnn θ hθ))
    -- `(u'')²` and `u''` are integrable on `Iθ`
    have hu2sq_int : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2) Work.Spaces.Iθ := by
      refine Integrable.mono'
        (g := fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) hint ?_ ?_
      · rw [← hIoo_ae]
        exact (hcontD2.pow 2).aestronglyMeasurable measurableSet_Ioo
      · filter_upwards [hone_ae] with θ hθ
        have h2 : (0 : ℝ) ≤ (deriv (deriv u) θ) ^ 2 := sq_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg h2]
        nlinarith [h2, hθ]
    have hu2_int : IntegrableOn (fun θ => deriv (deriv u) θ) Work.Spaces.Iθ := by
      refine Integrable.mono'
        (g := fun θ => (1 / 2) * ((deriv (deriv u) θ) ^ 2 + 1)) ?_ ?_ ?_
      · exact (hu2sq_int.add (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))).const_mul
          (1 / 2)
      · rw [← hIoo_ae]
        exact hcontD2.aestronglyMeasurable measurableSet_Ioo
      · filter_upwards with θ
        rw [Real.norm_eq_abs]
        refine abs_le.2 ⟨?_, ?_⟩
        · nlinarith [sq_nonneg (deriv (deriv u) θ + 1)]
        · nlinarith [sq_nonneg (deriv (deriv u) θ - 1)]
    -- the primitive `V` of `u''`
    set V : ℝ → ℝ := fun θ => ∫ t in (0 : ℝ)..θ, deriv (deriv u) t with hV
    have hVval : ∀ θ : ℝ, V θ = ∫ t in (0 : ℝ)..θ, deriv (deriv u) t := fun θ => by simp [hV]
    have hVcont : ContinuousOn V Work.Spaces.Iθ := by
      have h : ContinuousOn (fun θ : ℝ => ∫ t in (0 : ℝ)..θ, deriv (deriv u) t)
          (Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
        intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := Real.pi / 2)
          (f := fun t => deriv (deriv u) t) (by
            rw [Set.uIcc_of_le hpi.le, ← Work.Spaces.Iθ]; exact hu2_int)
      rwa [Set.uIcc_of_le hpi.le, ← Work.Spaces.Iθ] at h
    have hIθ_compact : IsCompact Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact isCompact_Icc
    obtain ⟨CV, hCV⟩ := hIθ_compact.exists_bound_of_continuousOn hVcont
    have hV2_int : IntegrableOn (fun θ => (V θ) ^ 2) Work.Spaces.Iθ := by
      refine Integrable.mono' (g := fun _ : ℝ => (max CV 0) ^ 2) ?_ ?_ ?_
      · exact integrableOn_const (s := Work.Spaces.Iθ) (C := (max CV 0) ^ 2)
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      · exact (hVcont.pow 2).aestronglyMeasurable measurableSet_Icc
      · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with θ hθ
        have hb : ‖V θ‖ ≤ max CV 0 := (hCV θ hθ).trans (le_max_left _ _)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        calc (V θ) ^ 2 = ‖V θ‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
          _ ≤ (max CV 0) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hV_memLp : MemLp V 2 (volume.restrict Work.Spaces.Iθ) := by
      rw [memLp_two_iff_integrable_sq (hVcont.aestronglyMeasurable measurableSet_Icc)]
      exact hV2_int
    have h1_memLp : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) := by
      rw [memLp_two_iff_integrable_sq aestronglyMeasurable_const]
      simpa using (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    have hvol : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Measure.real_def,
        Work.Spaces.Iθ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    have hVsq_le : (∫ θ in Work.Spaces.Iθ, V θ) ^ 2 ≤ (Real.pi / 2)
        * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := by
      have hcs := Work.Spaces.cs_integral (u := V) (v := fun _ : ℝ => (1 : ℝ))
        (s := Work.Spaces.Iθ) hV_memLp h1_memLp
      simpa [mul_one, one_pow, hvol, mul_comm] using hcs
    -- the constant `c₀` and the identity `u' = c₀ + V`
    set c₀ : ℝ := deriv u (Real.pi / 4) - V (Real.pi / 4) with hc0
    have hFTCmid : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        ∫ t in (Real.pi / 4)..θ, deriv (deriv u) t = deriv u θ - deriv u (Real.pi / 4) := by
      intro θ hθ
      have hsub1 : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩
      have hsub2 : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
        ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, Real.pi_pos]⟩
      have hI1 : Set.uIcc (Real.pi / 4) θ ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ (by positivity) hθ.1.le (by linarith [Real.pi_pos]) hθ.2.le
      have hI2 : Set.uIcc θ (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ hθ.1.le (by positivity) hθ.2.le (by linarith [Real.pi_pos])
      rcases le_total (Real.pi / 4) θ with hle | hle
      · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle (hcontD1.mono hsub1)
          (fun x hx => hderiv2 x (hsub1 ⟨hx.1.le, hx.2.le⟩))
          (hu2_int.mono_set hI1).intervalIntegrable
      · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle (hcontD1.mono hsub2)
          (fun x hx => hderiv2 x (hsub2 ⟨hx.1.le, hx.2.le⟩))
          (hu2_int.mono_set hI2).intervalIntegrable
        have hsym := intervalIntegral.integral_symm (μ := volume) (a := θ) (b := Real.pi / 4)
          (f := fun t => deriv (deriv u) t)
        linarith [h, hsym]
    have hdecomp : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv u θ = c₀ + V θ := by
      intro θ hθ
      have hI1 : Set.uIcc (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ le_rfl (by positivity) (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos])
      have hI2 : Set.uIcc (Real.pi / 4) θ ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ (by positivity) hθ.1.le (by linarith [Real.pi_pos]) hθ.2.le
      have hint1 : IntervalIntegrable (fun t => deriv (deriv u) t) volume (0 : ℝ)
          (Real.pi / 4) := (hu2_int.mono_set hI1).intervalIntegrable
      have hint2 : IntervalIntegrable (fun t => deriv (deriv u) t) volume (Real.pi / 4) θ :=
        (hu2_int.mono_set hI2).intervalIntegrable
      have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      rw [hVval θ, hc0, hVval (Real.pi / 4), ← hadd, hFTCmid θ hθ]
      ring
    -- `u'` is bounded, hence integrable
    have hderiv_bound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        ‖deriv u θ‖ ≤ |c₀| + CV := by
      intro θ hθ
      have hVb : |V θ| ≤ CV := by
        have h := hCV θ (⟨hθ.1.le, hθ.2.le⟩ : θ ∈ Work.Spaces.Iθ)
        rwa [Real.norm_eq_abs] at h
      rw [hdecomp θ hθ, Real.norm_eq_abs]
      calc |c₀ + V θ| ≤ |c₀| + |V θ| := abs_add_le _ _
        _ ≤ |c₀| + CV := by linarith
    have hderiv_int : IntegrableOn (fun θ => deriv u θ) Work.Spaces.Iθ := by
      refine Integrable.mono' (g := fun _ : ℝ => |c₀| + CV) ?_ ?_ ?_
      · exact integrableOn_const (s := Work.Spaces.Iθ) (C := |c₀| + CV)
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      · rw [← hIoo_ae]
        exact hcontD1.aestronglyMeasurable measurableSet_Ioo
      · rw [← hIoo_ae]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact hderiv_bound θ hθ
    -- `∫_{Iθ} u' = 0`, from the two vanishing endpoint limits
    have hzero : ∫ θ in (0 : ℝ)..(Real.pi / 2), deriv u θ = 0 := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
        (b := Real.pi / 2) (f := u) (f' := fun θ => deriv u θ) hpi hderiv1
        (intervalIntegrable_of_integrableOn_Iθ hderiv_int) hlim0 hlim1
      simpa using h
    have hkey : ∀ f : ℝ → ℝ,
        (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
      intro f
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hpi.le]
    -- the identity `c₀ = -(2/π) ∫_{Iθ} V`
    have hc0_eq : c₀ = -(2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, V θ := by
      have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
        rw [MeasureTheory.ae_iff]
        have hset : {x : ℝ | ¬(x ≠ Real.pi / 2)} = {Real.pi / 2} := by
          ext x; simp
        rw [hset]
        exact MeasureTheory.measure_singleton (Real.pi / 2)
      have hcongr_int : ∫ θ in (0 : ℝ)..(Real.pi / 2), deriv u θ
          = ∫ θ in (0 : ℝ)..(Real.pi / 2), (c₀ + V θ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hne] with x hx hmem
        rw [Set.uIoc_of_le hpi.le] at hmem
        exact hdecomp x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
      have hsplit : ∫ θ in (0 : ℝ)..(Real.pi / 2), (c₀ + V θ)
          = c₀ * (Real.pi / 2) + ∫ θ in (0 : ℝ)..(Real.pi / 2), V θ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const
          (hVcont.intervalIntegrable_of_Icc hpi.le), intervalIntegral.integral_const]
        ring
      have hval : c₀ * (Real.pi / 2) + ∫ θ in (0 : ℝ)..(Real.pi / 2), V θ = 0 := by
        rw [← hsplit, ← hcongr_int, hzero]
      rw [hkey V] at ⊢
      rw [← hkey V] at hval
      field_simp at hval ⊢
      linarith
    -- `c₀²` is controlled by the weighted norm of `V`
    have hc0sq : c₀ ^ 2 ≤ (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := by
      have hsq : c₀ ^ 2 = (2 / Real.pi) ^ 2 * (∫ θ in Work.Spaces.Iθ, V θ) ^ 2 := by
        rw [hc0_eq]; ring
      rw [hsq]
      calc (2 / Real.pi) ^ 2 * (∫ θ in Work.Spaces.Iθ, V θ) ^ 2
          ≤ (2 / Real.pi) ^ 2 * ((Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hVsq_le (by positivity)
        _ = (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := by
            have hc : (2 / Real.pi) ^ 2 * (Real.pi / 2) = 2 / Real.pi := by field_simp
            rw [← mul_assoc, hc]
    -- the weighted Hardy inequality for the datum `u''`
    have hHard2 := hKmain (fun θ => deriv (deriv u) θ) hu2_int hint
      (fun θ hθ => hcontD2.continuousAt (isOpen_Ioo.mem_nhds hθ))
    have hfun_prim : (fun θ => (∫ t in (0 : ℝ)..θ, deriv (deriv u) t) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        = fun θ => (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      funext θ; rw [hVval θ]
    have hV2w_int : IntegrableOn
        (fun θ => (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      hHard2.1.congr (Filter.Eventually.of_forall (congrFun hfun_prim))
    have hV2w_le : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ≤ K * R := by
      have h1 : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          = ∫ θ in Work.Spaces.Iθ,
              (∫ t in (0 : ℝ)..θ, deriv (deriv u) t) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        rw [hfun_prim]
      rw [h1, hR]
      exact hHard2.2
    have hV2_le_w : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      refine integral_mono_ae hV2_int hV2w_int ?_
      filter_upwards [hone_ae] with θ hθ
      nlinarith [sq_nonneg (V θ)]
    have hc0sq_le : c₀ ^ 2 ≤ K * R := by
      have h2π : (2 / Real.pi : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Real.pi_gt_three]
      have hKR : 0 ≤ K * R := mul_nonneg (le_of_lt hKpos) hRnn
      calc c₀ ^ 2 ≤ (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := hc0sq
        _ ≤ (2 / Real.pi) * (K * R) := by
            refine mul_le_mul_of_nonneg_left (le_trans hV2_le_w hV2w_le) (by positivity)
        _ ≤ K * R := by
            calc (2 / Real.pi) * (K * R) ≤ 1 * (K * R) :=
                  mul_le_mul_of_nonneg_right h2π hKR
              _ = K * R := one_mul _
    -- `u` is the primitive of `u'`
    have hu_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ = ∫ t in (0 : ℝ)..θ, deriv u t := by
      intro θ hθ
      have hcont : ContinuousAt u θ :=
        hu.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hθ)
      have hsub : Set.uIcc (0 : ℝ) θ ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ le_rfl hθ.1.le (by linarith [Real.pi_pos]) hθ.2.le
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
        (b := θ) hθ.1 (fun x hx => hderiv1 x ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2.le⟩)
        (hderiv_int.mono_set hsub).intervalIntegrable hlim0
        (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      simpa using h.symm
    -- the weighted Hardy inequality for the datum `u'`
    have hdom_int : IntegrableOn
        (fun θ => (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := by
      refine ((hwint.const_mul (2 * c₀ ^ 2)).add (hV2w_int.const_mul 2)).congr
        (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Pi.add_apply]
      ring
    have hae_dom : (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ => (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ) := by
      rw [← hIoo_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := hwnn θ ⟨hθ.1.le, hθ.2.le⟩
      have hpt : (deriv u θ) ^ 2 ≤ 2 * c₀ ^ 2 + 2 * (V θ) ^ 2 := by
        rw [hdecomp θ hθ]
        nlinarith [sq_nonneg (c₀ - V θ)]
      exact mul_le_mul_of_nonneg_right hpt hs
    have hderivsq_int : IntegrableOn
        (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
      refine Integrable.mono' (g := fun θ => (2 * c₀ ^ 2 + 2 * (V θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ) hdom_int ?_ ?_
      · rw [← hIoo_ae]
        exact ((hcontD1.pow 2).mul hcontW).aestronglyMeasurable measurableSet_Ioo
      · rw [← hIoo_ae]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
        have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := hwnn θ ⟨hθ.1.le, hθ.2.le⟩
        have hpt : (deriv u θ) ^ 2 ≤ 2 * c₀ ^ 2 + 2 * (V θ) ^ 2 := by
          rw [hdecomp θ hθ]
          nlinarith [sq_nonneg (c₀ - V θ)]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hs)]
        exact mul_le_mul_of_nonneg_right hpt hs
    have hHard1 := hKmain (fun θ => deriv u θ) hderiv_int hderivsq_int
      (fun θ hθ => hcontD1.continuousAt (isOpen_Ioo.mem_nhds hθ))
    have hae_eq : (fun θ => (∫ t in (0 : ℝ)..θ, deriv u t) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      rw [← hIoo_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      show (∫ t in (0 : ℝ)..θ, deriv u t) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [hu_eq θ hθ]
    have hu2w_int : IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := hHard1.1.congr hae_eq
    have hu2w_le : ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      rw [← integral_congr_ae hae_eq]
      exact hHard1.2
    -- `∫ (u')² w ≤ (2·10⁴ + 2) K R`
    have hderivsq_le : ∫ θ in Work.Spaces.Iθ,
        (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ≤ (2 * 10 ^ 4 + 2) * K * R := by
      have hmono : ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ ∫ θ in Work.Spaces.Iθ,
              (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ :=
        integral_mono_ae hderivsq_int hdom_int hae_dom
      have hsplit2 : ∫ θ in Work.Spaces.Iθ,
          (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ
          = (2 * c₀ ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
            + 2 * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        have hcongr : ∫ θ in Work.Spaces.Iθ,
            (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ
            = ∫ θ in Work.Spaces.Iθ,
                ((2 * c₀ ^ 2) * Work.FTS.EllipticEst.sEta θ
                  + 2 * ((V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          show (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ
            = (2 * c₀ ^ 2) * Work.FTS.EllipticEst.sEta θ
              + 2 * ((V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ring
        rw [hcongr, integral_add (hwint.const_mul (2 * c₀ ^ 2)) (hV2w_int.const_mul 2),
          integral_const_mul, integral_const_mul]
      rw [hsplit2] at hmono
      have hterm1 : (2 * c₀ ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
          ≤ (2 * c₀ ^ 2) * 10 ^ 4 :=
        mul_le_mul_of_nonneg_left hwle (by positivity)
      have hterm2 : 2 * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ 2 * (K * R) := mul_le_mul_of_nonneg_left hV2w_le (by norm_num)
      have hcombine : (2 * c₀ ^ 2) * 10 ^ 4 + 2 * (K * R) ≤ (2 * 10 ^ 4 + 2) * K * R := by
        nlinarith [hc0sq_le, hRnn, hKpos]
      linarith [hmono, hterm1, hterm2, hcombine]
    refine ⟨hu2w_int, hderivsq_int, ?_, ?_⟩
    · have h1 : ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ K * ((2 * 10 ^ 4 + 2) * K * R) :=
        le_trans hu2w_le (mul_le_mul_of_nonneg_left hderivsq_le (le_of_lt hKpos))
      have h2 : K * ((2 * 10 ^ 4 + 2) * K * R) = (2 * 10 ^ 4 + 2) * K ^ 2 * R := by ring
      have h3 : (2 * 10 ^ 4 + 2) * K ^ 2 * R
          ≤ ((2 * 10 ^ 4 + 2) * (K + K ^ 2)) * R := by
        refine mul_le_mul_of_nonneg_right ?_ hRnn
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (le_of_lt hKpos)) (by norm_num)
      linarith [h1, h3, le_of_eq h2]
    · have hC : (2 * 10 ^ 4 + 2) * K ≤ (2 * 10 ^ 4 + 2) * (K + K ^ 2) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg K)) (by norm_num)
      exact le_trans hderivsq_le (mul_le_mul_of_nonneg_right hC hRnn)

/-! ## The `∫⁻`-form of the slice estimate -/

/-- **Second-order σ-Poincaré on one angular slice, with vanishing endpoint traces.** -/
theorem sliceSigmaTraceZero : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (f θ ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ENNReal.ofReal C
        * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨C, hCpos, hC⟩ := sliceEtaPoincareC2
  refine ⟨C, hCpos, fun f hf hint hlim0 hlim1 => ?_⟩
  -- the real-integral estimate, together with the integrability of `f²σ`
  obtain ⟨hLint, -, hle, -⟩ := hC f hf hlim0 hlim1 hint
  -- both integrands are nonnegative on `Iθ`, where `σ = sEta ≥ 0`
  have hnn1 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      fun θ => f θ ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ)
  have hnn2 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      fun θ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ)
  -- the `∫⁻`/`∫` bridges
  have h1 := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hLint hnn1
  have h2 := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn2
  rw [← h1, ← h2, ← ENNReal.ofReal_mul hCpos.le]
  exact ENNReal.ofReal_le_ofReal hle

end

end Work.FTS.EllipticEst.H2W.AeU2
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.thetaIbpTwoD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-! ## Measurability/absolute-continuity helpers for the angular interval `Iθ` -/

/-- Two functions which agree on the *open* interval `(0, π/2)` agree almost everywhere for the
restriction of Lebesgue measure to `Iθ = [0, π/2]` (they may differ at the two endpoints). -/
theorem ae_eq_top_Iθ {f g : ℝ → ℝ} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f θ = g θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), θ ∈ Work.Spaces.Iθ → f θ = g θ := by
  rw [MeasureTheory.ae_iff]
  have hle : {θ : ℝ | ¬(θ ∈ Work.Spaces.Iθ → f θ = g θ)} ⊆ ({0} ∪ {Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp, Work.Spaces.Iθ, Set.mem_Icc] at hθ
    obtain ⟨⟨h1, h2⟩, hne⟩ := hθ
    by_contra hc
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hc
    exact hne (h θ ⟨lt_of_le_of_ne h1 (Ne.symm hc.1), lt_of_le_of_ne h2 hc.2⟩)
  refine measure_mono_null hle ?_
  exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))

/-- Version of `ae_eq_top_Iθ` for the restricted measure on `Iθ`. -/
theorem ae_restrict_Iθ {f g : ℝ → ℝ} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f θ = g θ) :
    f =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] g := by
  show ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))), f θ = g θ
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  exact ae_eq_top_Iθ h

/-- Two functions which agree on the open interval `(0, π/2)` have the same integral over `Iθ`. -/
theorem setIntegral_Iθ_congr {f g : ℝ → ℝ} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f θ = g θ) :
    ∫ θ in Work.Spaces.Iθ, f θ = ∫ θ in Work.Spaces.Iθ, g θ :=
  MeasureTheory.setIntegral_congr_ae measurableSet_Icc (ae_eq_top_Iθ h)




/-- Almost every point of `Iz = [0,∞)` is positive. -/
theorem ae_pos_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
  rw [MeasureTheory.ae_iff]
  have hset : {a : ℝ | ¬(0 < a)} = Set.Iic (0 : ℝ) := by ext a; exact not_lt
  rw [hset, show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
    MeasureTheory.Measure.restrict_apply measurableSet_Iic]
  have h0 : Set.Iic (0 : ℝ) ∩ Set.Ici (0 : ℝ) = ({0} : Set ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici, Set.mem_singleton_iff]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h ▸ le_rfl, h ▸ le_rfl⟩⟩
  rw [h0]
  exact measure_singleton 0

/-! ## Slice smoothness and the Clairaut identities on the open quadrant -/


/-- **Clairaut for `∂_θ` and `D_z`**: `∂_θ (D_z G) = D_z (∂_θ G)` on the open quadrant. -/
theorem pth_Dz_eq_of_smooth {G : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pth (Work.Spaces.Dz G) z θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall G).mp hS 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds h)
  have h1 : Work.Spaces.pth (Work.Spaces.Dz G) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz G) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz G z θ') θ = z * Work.Spaces.pth (Work.Spaces.pz G) z θ
    rw [deriv_const_mul_field]
    rfl
  rw [h1, ← Work.Spaces.pz_pth_comm hcd]
  rfl

/-- **Clairaut for `∂_θ²` and `D_z`**: `∂_θ² (D_z G) = D_z (∂_θ² G)` on the open quadrant. -/
theorem pthIter2_Dz_eq_of_smooth {G : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ := by
  have hev1 : ∀ᶠ y in 𝓝 (z, θ), y ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.eventually_mem h
  have hslice : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
    (Continuous.prodMk_right z).continuousAt.eventually hev1
  have hev : (fun θ' => Work.Spaces.pth (Work.Spaces.Dz G) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.Dz (Work.Spaces.pth G) z θ') := by
    filter_upwards [hslice] with θ' hθ'
    exact pth_Dz_eq_of_smooth hS (Work.FTS.EllipticEst.mem_Q0.mp hθ')
  have h2 : Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ
      = Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth G)) z θ :=
    EventuallyEq.deriv_eq hev
  rw [h2, pth_Dz_eq_of_smooth hS.pth h]
  rfl

/-! ## The slicewise identity -/


/-! ## The two-dimensional identity -/


end Work.FTS.EllipticEst.Prop
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.DivSinOpen.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false



/-- The pure `D_z` summand of the `ℋ^k`-integrand of `∂_θΦ`. -/
def RZ (Φ : ℝ → ℝ → ℝ) (z : ℝ) (i : ℕ) (θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed summand of the `ℋ^k`-integrand of `∂_θΦ`. -/
def RM (k : ℕ) (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z : ℝ) (i j : ℕ) (θ : ℝ) : ℝ :=
  if 1 ≤ i ∧ i + j ≤ k then
    (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2
  else 0







/-- `sin(2θ) > 0` on the open angular interval. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- `Φ / sin(2θ)` is `C^∞` on the open quadrant when `Φ` is. -/
theorem smoothOpen_div_sin {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φ z θ / Real.sin (2 * θ)) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hnum : ContDiffOn ℝ n (Function.uncurry Φ) Work.FTS.EllipticEst.Q0 := hΦ.forall n
  have hden : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by fun_prop
  refine hnum.div hden (fun p hp => ?_)
  obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (sin_two_pos_Ioo ⟨h1, h2⟩)

/-- The slice of the uncurried `F` at a positive radius is `C^∞` on the open angular interval. -/
theorem contDiffOn_slice_uncurry {F : ℝ → ℝ → ℝ} (hF : ∀ m : ℕ,
    ContDiffOn ℝ m (Function.uncurry F) Work.FTS.EllipticEst.Q0) {z : ℝ} (hz : 0 < z)
    (n : ℕ) : ContDiffOn ℝ n (fun θ => F z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hg : ContDiffOn ℝ n (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (contDiffOn_const (c := z)).prodMk (contDiffOn_id : ContDiffOn ℝ n (fun θ : ℝ => θ) _)
  have hmap : Set.MapsTo (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Ioo 0 (Real.pi / 2))
      Work.FTS.EllipticEst.Q0 :=
    fun θ hθ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcomp := (hF n).comp hg hmap
  simpa [Function.comp_def, Function.uncurry] using hcomp

/-- The slice of `D_z^j Φ` at a positive radius is `C^∞` on the open angular interval. -/
theorem contDiffOn_slice_DzIter {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j : ℕ) {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffOn ℝ n (fun θ => Work.Spaces.DzIter j Φ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  contDiffOn_slice_uncurry (hΦ.DzIter j).forall hz n





end Work.FTS.EllipticEst.RPFresh
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_PthFstarMixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

/-!
# `row15_PthFstarMixed`: the mixed-derivative bound for `∂_θ F_*`

Row 15 of the nonlinear estimates needs a pointwise bound on the mixed derivatives
`D_z^l D_θ^m (∂_θF_*)` of the angular derivative of the profile
`F_*(z,θ) = α (Γ(θ)/c(α)) · F̲(z)` (`Work.Construction.Fstar`, `F̲ = Work.FM.Fstar`),
because `N₂^{ss} = -2·U(Φ̃_*)·∂_θF_*`.

The whole estimate rests on the **separation of variables**: `∂_θF_*` is the product of an
angular factor and a radial one,

  `∂_θF_*(z,θ) = (α/c(α)) · Γ'(θ) · F̲(z)`   (`Work.Construction.pth_Fstar_eq`),

and the two operators `D_θ = sin(2θ)∂_θ` and `D_z = z∂_z` act on their own factor
(`mixedSepDecomp`):

  `D_z^l D_θ^m (∂_θF_*)(z,θ)
     = (α/c(α)) · (D_θ^m Γ')(θ) · ((OpZ)^l F̲)(z)`.

So it remains to bound the angular factor, which is exactly the first half of
`Gam_deriv_bounds` (`|D_θ^m Γ'| ≤ C α Γ (cot θ + tan θ + 1)`, `m ≤ 4`), together with the
elementary `cot θ + tan θ + 1 ≤ 3/sin(2θ)` (`sinTwoInvBound`) and `1/c(α) ≤ 10`
(`c_bounds`).
-/


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.zslot_window_perz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the `η`-weight `sin(2θ)^{-η}` -/

/-- On the open angular interval `sin(2θ) > 0`. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The pointwise slot dominations -/

/-- The exact rewriting of the weighted square of a `D_z`-slot:
`(D_z^jf z θ · w z / sin(2θ)^{η/2})² = sin(2θ)^{-η} · (D_z^jf z θ · w z)²`. -/
theorem dz_wt_ident (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (j : ℕ) :
    (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) := (sin_two_pos_of_mem_Ioo hθ).le
  rw [mul_pow,
    Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta hs
      (ne_of_gt Work.Spaces.eta_pos),
    mul_pow]
  ring

/-- A `D_z`-slot of the `ℋ^k`-integrand, with the weight `w` on the slot and the weight
`sin(2θ)^{-η}` in front, is dominated by `HkIntegrand`. -/
theorem dz_wt_slot_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {j : ℕ} (hj : j ≤ k) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [← dz_wt_ident f hθ j]
  exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hj

/-- The bare `D_z`-slot, with only the weight `sin(2θ)^{-η}` in front, is dominated by
`HkIntegrand`; the missing radial weight `w z` is paid for by `w z ≥ 1`. -/
theorem dz_slot_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {j : ℕ} (hj : j ≤ k) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.DzIter j f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hw : 1 ≤ Work.Spaces.w z := Work.FTS.TransportS.one_le_w hz
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg (sin_two_pos_of_mem_Ioo hθ).le _
  have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.DzIter j f z θ) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ hsnn
    calc (Work.Spaces.DzIter j f z θ) ^ 2
        = (Work.Spaces.DzIter j f z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hw) (sq_nonneg _)
      _ = (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2 := by rw [mul_pow]
  exact le_trans h1 (dz_wt_slot_le α k f hθ hj)

/-! ## The window step at a fixed angle -/

/-- **The window step for a `z`-slot.**  For `z > 0`, an interior angle `σ`, a slot `i` with
`i + 1 ≤ k` (so that both the slot and its radial derivative occur in `ℋ^k`) and a window
radius `R₀ ≥ z`,

  `sin(2σ)^{-η}·(D_z^if z σ)² ≤ (2 + 2/R₀)·∫_s HkIntegrand α k f s σ ds`.

The two window integrands of `half_line_window_bound` are dominated by `HkIntegrand` (at the
slots `i + 1` and `i`), so that multiplying the window inequality by `sin(2σ)^{-η}` cancels
the weight. -/
theorem zslot_window_step (α : ℝ) {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    {k i : ℕ} (hi : i + 1 ≤ k) {z R₀ σ : ℝ} (hz : 0 < z) (hR : z ≤ R₀)
    (hσ : σ ∈ Set.Ioo 0 (Real.pi / 2))
    (hσint : MeasureTheory.IntegrableOn (fun s : ℝ => Work.Spaces.HkIntegrand α k f s σ)
      Work.Spaces.Iz) :
    (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.DzIter i f z σ) ^ 2
      ≤ (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  -- the hypotheses of the radial Hardy inequality in window form
  have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
      HasDerivAt (fun x : ℝ => Work.Spaces.DzIter i f x σ)
        (Work.Spaces.pz (Work.Spaces.DzIter i f) x σ) x :=
    fun x hx => (hF.DzIter i).hasDerivAt_slice hσ (lt_of_lt_of_le hz hx.1)
  have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.DzIter i f x σ) (Set.Icc R₀ (2 * R₀)) :=
    ((hF.DzIter i).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
  have hcont' : ContinuousOn (fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter i f) x σ)
      (Set.Icc z (2 * R₀)) :=
    (((hF.DzIter i).pz).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz hx.1)
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => (Work.Spaces.DzIter i f x σ) ^ 2)
      (Set.Icc R₀ (2 * R₀)) := (hcont.pow 2).integrableOn_Icc
  have hwin := Work.FTS.TransportS.half_line_window_bound hz hR hderiv hcont hcont' hint
  -- continuity of the two weighted window integrands and of the `HkIntegrand`
  have hcontW : ContinuousOn (fun x : ℝ =>
      x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x)
      (Set.Icc z (2 * R₀)) := by
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
  have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.Icc z (2 * R₀)) := by
    have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀))
        Work.FTS.EllipticEst.Q0 :=
      fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
    have hc := (hF.continuousOn_HkIntegrand α k).comp
      (continuousOn_id.prodMk continuousOn_const) hmap
    simpa only [Function.comp_def, id_eq] using hc
  -- the two window integrals
  set u : ℝ := (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) with hu_def
  have hu : 0 ≤ u := by
    rw [hu_def]
    exact Real.rpow_nonneg (sin_two_pos_of_mem_Ioo hσ).le _
  set IA : ℝ := ∫ x in z..(2 * R₀),
    (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2 with hIA_def
  set IB : ℝ := ∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter i f x σ) ^ 2 with hIB_def
  have hwin' : (Work.Spaces.DzIter i f z σ) ^ 2 ≤ 2 * IA + (2 / R₀) * IB := by
    rw [hIA_def, hIB_def]
    exact hwin
  have huAint : IntervalIntegrable (fun x : ℝ => u
      * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => u
        * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact continuousOn_const.mul (hcontW.pow 2)
  have hHkAint : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact hHkcont
  have huBint : IntervalIntegrable (fun x : ℝ => u * (Work.Spaces.DzIter i f x σ) ^ 2)
      volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => u * (Work.Spaces.DzIter i f x σ) ^ 2)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact continuousOn_const.mul (hcont.pow 2)
  have hHkBint : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
  -- the pointwise domination of the two window integrands
  have hptA : ∀ x ∈ Set.Icc z (2 * R₀), u
      * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
    have hcomm : x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ
        = Work.Spaces.DzIter (i + 1) f x σ := rfl
    rw [hcomm]
    exact dz_wt_slot_le α k f hσ hi
  have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀), u * (Work.Spaces.DzIter i f x σ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hRpos hx.1
    exact dz_slot_le α k f hxpos hσ (by omega)
  have hIA_le : u * IA ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
    rw [hIA_def, ← intervalIntegral.integral_const_mul]
    refine le_trans (intervalIntegral.integral_mono_on hz2R huAint hHkAint hptA) ?_
    rw [intervalIntegral.integral_of_le hz2R]
    refine MeasureTheory.setIntegral_mono_set hσint
      (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
    exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
  have hIB_le : u * IB ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
    rw [hIB_def, ← intervalIntegral.integral_const_mul]
    refine le_trans (intervalIntegral.integral_mono_on hR2R huBint hHkBint hptB) ?_
    rw [intervalIntegral.integral_of_le hR2R]
    refine MeasureTheory.setIntegral_mono_set hσint
      (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
    exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
  -- assembly
  have hmain : u * (Work.Spaces.DzIter i f z σ) ^ 2
      ≤ 2 * (u * IA) + (2 / R₀) * (u * IB) := by
    have h1 : u * (Work.Spaces.DzIter i f z σ) ^ 2 ≤ u * (2 * IA + (2 / R₀) * IB) :=
      mul_le_mul_of_nonneg_left hwin' hu
    calc u * (Work.Spaces.DzIter i f z σ) ^ 2 ≤ u * (2 * IA + (2 / R₀) * IB) := h1
      _ = 2 * (u * IA) + (2 / R₀) * (u * IB) := by ring
  have hfinal : u * (Work.Spaces.DzIter i f z σ) ^ 2
      ≤ (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
    have h2 : 2 * (u * IA) + (2 / R₀) * (u * IB)
        ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
          + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) :=
      add_le_add (mul_le_mul_of_nonneg_left hIA_le (by norm_num))
        (mul_le_mul_of_nonneg_left hIB_le (div_nonneg (by norm_num) hRpos.le))
    calc u * (Work.Spaces.DzIter i f z σ) ^ 2
        ≤ 2 * (u * IA) + (2 / R₀) * (u * IB) := hmain
      _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
            + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := h2
      _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by ring
  rw [hu_def] at hfinal
  exact hfinal

/-! ## The assigned lemma -/

theorem zslot_window_perz (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) (i : ℕ) (hi : i + 1 ≤ k)
    {z R₀ σ : ℝ} (hz : 0 < z) (hR : z ≤ R₀) (hσ : σ ∈ Set.Ioo 0 (Real.pi / 2))
    (hσint : MeasureTheory.IntegrableOn (fun s : ℝ => Work.Spaces.HkIntegrand α k f s σ)
      Work.Spaces.Iz) :
    (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / R₀)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
  have hstep := zslot_window_step α hF hi hz hR hσ hσint
  have hLHS : (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter i f z σ) ^ 2) := by
    have hs : 0 ≤ Real.sin (2 * σ) := (sin_two_pos_of_mem_Ioo hσ).le
    rw [mul_pow,
      Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * σ)) Work.Spaces.eta hs
        (ne_of_gt Work.Spaces.eta_pos)]
    ring
  rw [hLHS, mul_assoc]
  exact mul_le_mul_of_nonneg_left hstep (sq_nonneg _)

end Work.FTS.StrongEps.E5Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.mixed_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps

-- The hypotheses `hf`, `hz`, `hθ` of the requested statement are not used by its proof: the
-- identity holds on all of `ℝ²` (see the module docstring).  Silence the corresponding linter.
set_option linter.unusedVariables false

/-!
# Scalar homogeneity of the mixed derivative `D_z^j D_θ^i`

`Work.Spaces.mixed j i f = D_z^j D_θ^i f`, where `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ`.
Here we record that every one of these operators — `∂_z`, `∂_θ`, `D_z`, `D_θ` and all their
iterates, hence `mixed j i` — is scalar homogeneous:

  `D_z^j D_θ^i (c·f) = c · D_z^j D_θ^i f`.

The point of the argument is that `deriv` is *unconditionally* homogeneous,
`deriv (fun y => c * g y) x = c * deriv g x` (`deriv_const_mul_field`): when `g` is not
differentiable at `x` both sides are `0` (and if `c ≠ 0`, `c·g` is not differentiable either).
Hence no smoothness or range hypothesis is needed: `mixed_const_mul` holds on all of `ℝ²`,
which is why the hypotheses of the requested statement (`hf`, `hz`, `hθ`) can simply be
discarded by the proof.

(The file opens the `Real` notation scope because the statement writes the angle bound as
`θ ∈ Set.Ioo 0 (π / 2)`: with `autoImplicit = false` in this workspace a bare `π` is not an
identifier, so `open scoped Real` is what makes it denote `Real.pi` as intended.  The statement
itself is byte-for-byte the one requested.)
-/

/-- `∂_z` is scalar homogeneous (unconditionally). -/
theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  exact deriv_const_mul_field c

/-- `∂_θ` is scalar homogeneous (unconditionally). -/
theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field c

/-- `D_z = z ∂_z` is scalar homogeneous. -/
theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_const_mul]
  ring

/-- `D_θ = sin(2θ) ∂_θ` is scalar homogeneous. -/
theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_const_mul]
  ring

/-- Every iterate of `D_z` is scalar homogeneous. -/
theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih => simp only [Work.Spaces.DzIter_succ, ih, Dz_const_mul]

/-- Every iterate of `D_θ` is scalar homogeneous. -/
theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => simp only [Work.Spaces.DthIter_succ, ih, Dth_const_mul]

/-- Scalar homogeneity of the mixed derivative `D_z^j D_θ^i` (unconditional; the hypotheses of
the statement are not needed and are discarded by the proof). -/
theorem mixed_const_mul {j i : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed j i (fun z' θ' => c * f z' θ') z θ
      = c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul c f i,
    DzIter_const_mul c (Work.Spaces.DthIter i f) j]

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular jets of `c2m` up to order eight

`Work.Construction.c2m θ = cos(2θ) - sin²θ = (3cos(2θ) - 1)/2` is the angular coefficient
of the transport term.  Since `c2m` is a trigonometric polynomial of degree two and
`D_θ = sin(2θ)·∂_θ` (`Work.Spaces.dthU` in one variable), every iterate `D_θ^i c2m` with
`i ≥ 1` is `sin(2θ)²` times a polynomial in `sin(2θ)`, `cos(2θ)`; hence it is `O(sin(2θ)²)`
and a fortiori `O(sin(2θ))` on `Iθ`, where `0 ≤ sin(2θ) ≤ 1`.

This file supplies the requested `∃ C` bundle for `1 ≤ i ≤ 8`: the smoothness of `c2m` on
the open quadrant, the bound `|c2m| ≤ C` on `Iθ`, and the eight jet bounds
`|D_θ^i c2m| ≤ C·sin(2θ)` on `Iθ`.

Writing `u = sin(2θ)`, `v = cos(2θ)`, the closed forms are

* `D_θ^1 c2m = -3u²`,
* `D_θ^2 c2m = -12u²v`,
* `D_θ^3 c2m = 24u⁴ - 48u²v²`,
* `D_θ^4 c2m = 384u⁴v - 192u²v³`,
* `D_θ^5 c2m = 4224u⁴v² - 768u⁶ - 768u²v⁴`,
* `D_θ^6 c2m = 39936u⁴v³ - 26112u⁶v - 3072u²v⁵`,
* `D_θ^7 c2m = 350208u⁴v⁴ - 552960u⁶v² + 52224u⁸ - 12288u²v⁶`,
* `D_θ^8 c2m = 2949120u⁴v⁵ - 9437184u⁶v³ + 3047424u⁸v - 49152u²v⁷`,

the first four of which are `Work.FTS.Nonlinear.FstarPkg.dthU_c2m_iter_*`, the fifth and
sixth are the closed forms of `Work.FTS.StrongPersist.dthU_c2m_bound6`, and the last two are
computed here.  Every monomial in the last four has `u`-power `≥ 2`, so each is bounded by
`K·u²` with `K` the sum of the absolute values of its coefficients:

`|D_θ^5| ≤ 5760u²`, `|D_θ^6| ≤ 69120u²`, `|D_θ^7| ≤ 967680u²`, `|D_θ^8| ≤ 15482880u²`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

/-! ## Smoothness of `c2m` -/

private theorem contDiff_c2m (n : WithTop ℕ∞) : ContDiff ℝ n Work.Construction.c2m := by
  show ContDiff ℝ n (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
  exact (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub (Real.contDiff_sin.pow 2)

private theorem smoothOpen_c2m_ang :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0
  exact (contDiff_c2m Work.Stability.smoothOrder).contDiffOn.comp contDiffOn_snd
    (fun p _ => Set.mem_univ p.2)

private theorem abs_c2m_le_two_prv (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq, abs_le]
  have h2 : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  constructor
  · nlinarith [Real.neg_one_le_cos (2 * θ), sq_nonneg (Real.sin θ), h2]
  · nlinarith [Real.cos_le_one (2 * θ), sq_nonneg (Real.sin θ)]

/-! ## The derivative of the fourth closed form -/

/-- `(θ ↦ 384 sin(2θ)⁴cos(2θ) - 192 sin(2θ)²cos(2θ)³)' = 4224 sin(2θ)³cos(2θ)²
- 768 sin(2θ)⁵ - 768 sin(2θ)cos(2θ)⁴`. -/
private lemma deriv_c2m_L4 (θ : ℝ) :
    deriv (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t)
        - 192 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3) θ
      = 4224 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 5
        - 768 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 4 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hc3 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 3)
      (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 3
  have hA : HasDerivAt (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t))
      ((384 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) * Real.cos (2 * θ)
        + (384 * (Real.sin (2 * θ)) ^ 4) * (-Real.sin (2 * θ) * 2)) θ :=
    (hs4.const_mul 384).mul hc
  have hB : HasDerivAt (fun t : ℝ => (192 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)
      ((192 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 3
        + (192 * (Real.sin (2 * θ)) ^ 2)
          * (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 192).mul hc3
  have hfin := hA.sub hB
  rw [show (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t)
        - 192 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)
      = ((fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t))
        - (fun t : ℝ => (192 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)) from by
    funext t; simp only [Pi.sub_apply],
    hfin.deriv]
  ring_nf

/-- `D_θ` of the fourth closed form: `D_θ^5 c2m = 4224u⁴v² - 768u⁶ - 768u²v⁴`. -/
private lemma dthU_L4_eq :
    Work.Spaces.dthU (fun θ : ℝ => (384 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
        - 192 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3)
      = fun θ : ℝ => 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
          - 768 * (Real.sin (2 * θ)) ^ 6
          - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4 := by
  funext θ
  rw [Work.Spaces.dthU_apply, deriv_c2m_L4 θ]
  ring_nf

/-! ## The derivative of the fifth closed form -/

/-- `(θ ↦ 4224 sin(2θ)⁴cos(2θ)² - 768 sin(2θ)⁶ - 768 sin(2θ)²cos(2θ)⁴)' =
39936 sin(2θ)³cos(2θ)³ - 26112 sin(2θ)⁵cos(2θ) - 3072 sin(2θ)cos(2θ)⁵`. -/
private lemma deriv_c2m_L5 (θ : ℝ) :
    deriv (fun t : ℝ => 4224 * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2
        - 768 * (Real.sin (2 * t)) ^ 6
        - 768 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4) θ
      = 39936 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 5 * Real.cos (2 * θ)
        - 3072 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 5 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hv2 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 2)
      (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 2
  have hs6 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 6)
      (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 6
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hv4 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 4)
      (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 4
  have hA : HasDerivAt (fun t : ℝ => (4224 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2)
      ((4224 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 2
        + (4224 * (Real.sin (2 * θ)) ^ 4)
          * (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs4.const_mul 4224).mul hv2
  have hB : HasDerivAt (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 6)
      (768 * (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2))) θ :=
    hs6.const_mul 768
  have hC : HasDerivAt (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)
      ((768 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 4
        + (768 * (Real.sin (2 * θ)) ^ 2)
          * (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 768).mul hv4
  have hfin := (hA.sub hB).sub hC
  rw [show (fun t : ℝ => 4224 * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2
        - 768 * (Real.sin (2 * t)) ^ 6
        - 768 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)
      = (((fun t : ℝ => (4224 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2)
          - (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 6))
        - (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)) from by
    funext t; simp only [Pi.sub_apply],
    hfin.deriv]
  ring_nf

/-- `D_θ` of the fifth closed form: `D_θ^6 c2m = 39936u⁴v³ - 26112u⁶v - 3072u²v⁵`. -/
private lemma dthU_L5_eq :
    Work.Spaces.dthU (fun θ : ℝ => 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 6
        - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4)
      = fun θ : ℝ => 39936 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
          - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
          - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5 := by
  funext θ
  rw [Work.Spaces.dthU_apply, deriv_c2m_L5 θ]
  ring_nf

/-! ## The derivative of the sixth closed form -/

/-- `(θ ↦ 39936 sin(2θ)⁴cos(2θ)³ - 26112 sin(2θ)⁶cos(2θ) - 3072 sin(2θ)²cos(2θ)⁵)' =
350208 sin(2θ)³cos(2θ)⁴ - 552960 sin(2θ)⁵cos(2θ)² + 52224 sin(2θ)⁷
- 12288 sin(2θ)cos(2θ)⁶`. -/
private lemma deriv_c2m_L6 (θ : ℝ) :
    deriv (fun t : ℝ => (39936 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 3
        - 26112 * (Real.sin (2 * t)) ^ 6 * Real.cos (2 * t)
        - 3072 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 5) θ
      = 350208 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 4
        - 552960 * (Real.sin (2 * θ)) ^ 5 * (Real.cos (2 * θ)) ^ 2
        + 52224 * (Real.sin (2 * θ)) ^ 7
        - 12288 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 6 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hc3 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 3)
      (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 3
  have hs6 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 6)
      (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 6
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hc5 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 5)
      (5 * (Real.cos (2 * θ)) ^ (5 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 5
  have hA : HasDerivAt (fun t : ℝ => (39936 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 3)
      ((39936 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 3
        + (39936 * (Real.sin (2 * θ)) ^ 4)
          * (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs4.const_mul 39936).mul hc3
  have hB : HasDerivAt (fun t : ℝ => (26112 : ℝ) * (Real.sin (2 * t)) ^ 6 * Real.cos (2 * t))
      ((26112 * (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2))) * Real.cos (2 * θ)
        + (26112 * (Real.sin (2 * θ)) ^ 6) * (-Real.sin (2 * θ) * 2)) θ :=
    (hs6.const_mul 26112).mul hc
  have hC : HasDerivAt (fun t : ℝ => (3072 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 5)
      ((3072 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 5
        + (3072 * (Real.sin (2 * θ)) ^ 2)
          * (5 * (Real.cos (2 * θ)) ^ (5 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 3072).mul hc5
  have hfin := (hA.sub hB).sub hC
  have hfun : (fun t : ℝ => (39936 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 3
        - 26112 * (Real.sin (2 * t)) ^ 6 * Real.cos (2 * t)
        - 3072 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 5)
      = (((fun t : ℝ => (39936 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 3)
          - (fun t : ℝ => (26112 : ℝ) * (Real.sin (2 * t)) ^ 6 * Real.cos (2 * t)))
        - (fun t : ℝ => (3072 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 5)) := by
    funext t; simp only [Pi.sub_apply]
  rw [hfun, hfin.deriv]
  ring_nf

/-- `D_θ` of the sixth closed form:
`D_θ^7 c2m = 350208u⁴v⁴ - 552960u⁶v² + 52224u⁸ - 12288u²v⁶`. -/
private lemma dthU_L6_eq :
    Work.Spaces.dthU (fun θ : ℝ => (39936 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
        - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5)
      = fun θ : ℝ => 350208 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 4
          - 552960 * (Real.sin (2 * θ)) ^ 6 * (Real.cos (2 * θ)) ^ 2
          + 52224 * (Real.sin (2 * θ)) ^ 8
          - 12288 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 6 := by
  funext θ
  rw [Work.Spaces.dthU_apply, deriv_c2m_L6 θ]
  ring_nf

/-! ## The derivative of the seventh closed form -/

/-- `(θ ↦ 350208 sin(2θ)⁴cos(2θ)⁴ - 552960 sin(2θ)⁶cos(2θ)² + 52224 sin(2θ)⁸
- 12288 sin(2θ)²cos(2θ)⁶)' = 2949120 sin(2θ)³cos(2θ)⁵ - 9437184 sin(2θ)⁵cos(2θ)³
+ 3047424 sin(2θ)⁷cos(2θ) - 49152 sin(2θ)cos(2θ)⁷`. -/
private lemma deriv_c2m_L7 (θ : ℝ) :
    deriv (fun t : ℝ => (350208 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 4
        - 552960 * (Real.sin (2 * t)) ^ 6 * (Real.cos (2 * t)) ^ 2
        + 52224 * (Real.sin (2 * t)) ^ 8
        - 12288 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 6) θ
      = 2949120 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 5
        - 9437184 * (Real.sin (2 * θ)) ^ 5 * (Real.cos (2 * θ)) ^ 3
        + 3047424 * (Real.sin (2 * θ)) ^ 7 * Real.cos (2 * θ)
        - 49152 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 7 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hc4 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 4)
      (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 4
  have hs6 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 6)
      (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 6
  have hc2 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 2)
      (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 2
  have hs8 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 8)
      (8 * (Real.sin (2 * θ)) ^ (8 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 8
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hc6 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 6)
      (6 * (Real.cos (2 * θ)) ^ (6 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 6
  have hA : HasDerivAt
      (fun t : ℝ => (350208 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 4)
      ((350208 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)))
          * (Real.cos (2 * θ)) ^ 4
        + (350208 * (Real.sin (2 * θ)) ^ 4)
          * (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs4.const_mul 350208).mul hc4
  have hB : HasDerivAt
      (fun t : ℝ => (552960 : ℝ) * (Real.sin (2 * t)) ^ 6 * (Real.cos (2 * t)) ^ 2)
      ((552960 * (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2)))
          * (Real.cos (2 * θ)) ^ 2
        + (552960 * (Real.sin (2 * θ)) ^ 6)
          * (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs6.const_mul 552960).mul hc2
  have hC : HasDerivAt (fun t : ℝ => (52224 : ℝ) * (Real.sin (2 * t)) ^ 8)
      (52224 * (8 * (Real.sin (2 * θ)) ^ (8 - 1) * (Real.cos (2 * θ) * 2))) θ :=
    hs8.const_mul 52224
  have hD : HasDerivAt
      (fun t : ℝ => (12288 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 6)
      ((12288 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)))
          * (Real.cos (2 * θ)) ^ 6
        + (12288 * (Real.sin (2 * θ)) ^ 2)
          * (6 * (Real.cos (2 * θ)) ^ (6 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 12288).mul hc6
  have hfin := ((hA.sub hB).add hC).sub hD
  have hfun : (fun t : ℝ => (350208 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 4
        - 552960 * (Real.sin (2 * t)) ^ 6 * (Real.cos (2 * t)) ^ 2
        + 52224 * (Real.sin (2 * t)) ^ 8
        - 12288 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 6)
      = ((((fun t : ℝ => (350208 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 4)
          - (fun t : ℝ => (552960 : ℝ) * (Real.sin (2 * t)) ^ 6 * (Real.cos (2 * t)) ^ 2))
        + (fun t : ℝ => (52224 : ℝ) * (Real.sin (2 * t)) ^ 8))
        - (fun t : ℝ => (12288 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 6)) := by
    funext t; simp only [Pi.sub_apply, Pi.add_apply]
  rw [hfun, hfin.deriv]
  ring_nf

/-- `D_θ` of the seventh closed form:
`D_θ^8 c2m = 2949120u⁴v⁵ - 9437184u⁶v³ + 3047424u⁸v - 49152u²v⁷`. -/
private lemma dthU_L7_eq :
    Work.Spaces.dthU (fun θ : ℝ =>
          (350208 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 4
        - 552960 * (Real.sin (2 * θ)) ^ 6 * (Real.cos (2 * θ)) ^ 2
        + 52224 * (Real.sin (2 * θ)) ^ 8
        - 12288 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 6)
      = fun θ : ℝ => 2949120 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 5
          - 9437184 * (Real.sin (2 * θ)) ^ 6 * (Real.cos (2 * θ)) ^ 3
          + 3047424 * (Real.sin (2 * θ)) ^ 8 * Real.cos (2 * θ)
          - 49152 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 7 := by
  funext θ
  rw [Work.Spaces.dthU_apply, deriv_c2m_L7 θ]
  ring_nf

/-! ## The iterates, as values -/



/-- `D_θ^7 c2m = 350208u⁴v⁴ - 552960u⁶v² + 52224u⁸ - 12288u²v⁶`. -/
private lemma iter_seven_pt (θ : ℝ) :
    (Work.Spaces.dthU^[7]) Work.Construction.c2m θ
      = 350208 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 4
        - 552960 * (Real.sin (2 * θ)) ^ 6 * (Real.cos (2 * θ)) ^ 2
        + 52224 * (Real.sin (2 * θ)) ^ 8
        - 12288 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 6 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_succ_apply',
    show (6 : ℕ) = 5 + 1 from rfl, Function.iterate_succ_apply',
    show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply',
    show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f1_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f2_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f3_eq,
    dthU_L4_eq, dthU_L5_eq, dthU_L6_eq]

/-- `D_θ^8 c2m = 2949120u⁴v⁵ - 9437184u⁶v³ + 3047424u⁸v - 49152u²v⁷`. -/
private lemma iter_eight_pt (θ : ℝ) :
    (Work.Spaces.dthU^[8]) Work.Construction.c2m θ
      = 2949120 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 5
        - 9437184 * (Real.sin (2 * θ)) ^ 6 * (Real.cos (2 * θ)) ^ 3
        + 3047424 * (Real.sin (2 * θ)) ^ 8 * Real.cos (2 * θ)
        - 49152 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 7 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, Function.iterate_succ_apply',
    show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_succ_apply',
    show (6 : ℕ) = 5 + 1 from rfl, Function.iterate_succ_apply',
    show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply',
    show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f1_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f2_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f3_eq,
    dthU_L4_eq, dthU_L5_eq, dthU_L6_eq, dthU_L7_eq]

/-! ## The monomial bound and the four jet bounds -/

/-- A monomial `K·s^a·c^b` with `a ≥ 2` and `|s|, |c| ≤ 1` is bounded by `K·s²`. -/
private lemma monomial_sq_le {K s c : ℝ} (hK : 0 ≤ K) (hs : |s| ≤ 1) (hc : |c| ≤ 1)
    {a b : ℕ} (ha : 2 ≤ a) : |K * s ^ a * c ^ b| ≤ K * s ^ 2 := by
  have hsa : |s| ^ a ≤ |s| ^ 2 := pow_le_pow_of_le_one (abs_nonneg s) hs ha
  have hcb : |c| ^ b ≤ 1 := pow_le_one₀ (abs_nonneg c) hc
  have hmul : |s| ^ a * |c| ^ b ≤ |s| ^ 2 * 1 :=
    mul_le_mul hsa hcb (pow_nonneg (abs_nonneg c) b) (pow_nonneg (abs_nonneg s) 2)
  calc |K * s ^ a * c ^ b| = K * (|s| ^ a * |c| ^ b) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hK, abs_pow, abs_pow]; ring
    _ ≤ K * (|s| ^ 2 * 1) := mul_le_mul_of_nonneg_left hmul hK
    _ = K * s ^ 2 := by rw [sq_abs]; ring

/-- The `c = 1` case of `monomial_sq_le`: `|K·s^a| ≤ K·s²` for `a ≥ 2`. -/
private lemma monomial_sq_le' {K s : ℝ} (hK : 0 ≤ K) (hs : |s| ≤ 1)
    {a : ℕ} (ha : 2 ≤ a) : |K * s ^ a| ≤ K * s ^ 2 := by
  simpa using monomial_sq_le (K := K) (c := (1 : ℝ)) hK hs (by norm_num) (a := a) (b := 0) ha



/-- `|D_θ^7 c2m| ≤ 967680·sin(2θ)²`. -/
private lemma iter_seven_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[7]) Work.Construction.c2m θ|
      ≤ 967680 * (Real.sin (2 * θ)) ^ 2 := by
  rw [iter_seven_pt θ]
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h1 := monomial_sq_le (K := (350208 : ℝ)) (by norm_num) hs hc (a := 4) (b := 4) (by norm_num)
  have h2 := monomial_sq_le (K := (552960 : ℝ)) (by norm_num) hs hc (a := 6) (b := 2) (by norm_num)
  have h3 := monomial_sq_le' (K := (52224 : ℝ)) (by norm_num) hs (a := 8) (by norm_num)
  have h4 := monomial_sq_le (K := (12288 : ℝ)) (by norm_num) hs hc (a := 2) (b := 6) (by norm_num)
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

/-- `|D_θ^8 c2m| ≤ 15482880·sin(2θ)²`. -/
private lemma iter_eight_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[8]) Work.Construction.c2m θ|
      ≤ 15482880 * (Real.sin (2 * θ)) ^ 2 := by
  rw [iter_eight_pt θ]
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h1 := monomial_sq_le (K := (2949120 : ℝ)) (by norm_num) hs hc (a := 4) (b := 5) (by norm_num)
  have h2 := monomial_sq_le (K := (9437184 : ℝ)) (by norm_num) hs hc (a := 6) (b := 3) (by norm_num)
  have h3 := monomial_sq_le (K := (3047424 : ℝ)) (by norm_num) hs hc (a := 8) (b := 1) (by norm_num)
  have h4 := monomial_sq_le (K := (49152 : ℝ)) (by norm_num) hs hc (a := 2) (b := 7) (by norm_num)
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

/-! ## The assembly -/

/-- From `|X| ≤ K·s²` with `0 ≤ s ≤ 1`, `0 ≤ K` and `K ≤ C` conclude `|X| ≤ C·s`. -/
private lemma le_bound_of_sq_le_bound {X s K C : ℝ} (h : |X| ≤ K * s ^ 2)
    (hK : 0 ≤ K) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hKC : K ≤ C) : |X| ≤ C * s := by
  have hsq : s ^ 2 ≤ s := by
    have h1 := mul_nonneg hs0 (sub_nonneg.mpr hs1)
    nlinarith [h1]
  calc |X| ≤ K * s ^ 2 := h
    _ ≤ K * s := mul_le_mul_of_nonneg_left hsq hK
    _ ≤ C * s := mul_le_mul_of_nonneg_right hKC hs0

theorem c2mJets : ∃ C : ℝ, 0 < C ∧
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Work.Construction.c2m θ) ∧
    (∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ C) ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ 8 → ∀ (z θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        ≤ C * Real.sin (2 * θ) := by
  obtain ⟨C6, hC6pos, hC6⟩ := Work.FTS.StrongPersist.dthU_c2m_bound6
  refine ⟨max C6 15482880, lt_max_of_lt_right (by norm_num), smoothOpen_c2m_ang, ?_, ?_⟩
  · intro θ _
    exact le_trans (le_trans (abs_c2m_le_two_prv θ) (by norm_num : (2 : ℝ) ≤ 15482880))
      (le_max_right C6 15482880)
  · intro i hi1 hi8 z θ hθ
    rw [Work.FTS.LocData.DthIter_rad_eq i Work.Construction.c2m z θ]
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    by_cases h6 : i ≤ 6
    · exact le_bound_of_sq_le_bound (hC6 i hi1 h6 θ) hC6pos.le hs0 hs1 (le_max_left C6 15482880)
    · have hi78 : i = 7 ∨ i = 8 := by omega
      rcases hi78 with rfl | rfl
      · refine le_bound_of_sq_le_bound (iter_seven_bound θ) (by norm_num) hs0 hs1 ?_
        exact le_trans (by norm_num : (967680 : ℝ) ≤ 15482880) (le_max_right C6 15482880)
      · exact le_bound_of_sq_le_bound (iter_eight_bound θ) (by norm_num) hs0 hs1
          (le_max_right C6 15482880)

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkLowAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The weight-free level-`m` slice sum -/

/-- The level-`m` `ℋ`-integrand with the radial weight `(w z)²` removed: the radial slots keep
their `η`-weight, the mixed slots their `γ`-weight.  On the open angular interval
`HkIntegrand α m f z θ = (w z)² * lowSum α m f z θ` (`HkIntegrand_eq_w_sq_mul_lowSum`). -/
noncomputable def lowSum (α : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (m + 1),
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed i 0 f z θ) ^ 2)
    + ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        if 1 ≤ i ∧ i + j ≤ m then
          (Work.Spaces.mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        else 0

/-! ## The two slot identities -/

/-- A single radial slot: `(D_z^i f · w/sin(2θ)^{η/2})² = (w z)²·(D_z^i f)²·sin(2θ)^{-η}`. -/
theorem zslot_eq_low {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hs : 0 < Real.sin (2 * θ)) (i : ℕ) :
    (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed i 0 f z θ) ^ 2) := by
  rw [Work.Spaces.mixed_zero_right, mul_pow,
    Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta hs.le
      (ne_of_gt Work.Spaces.eta_pos)]
  ring

/-- A single mixed slot: `(D_z^jD_θ^if · Wt α)² = (w z)²·(D_z^jD_θ^if)²·sin(2θ)^{-γ(α)}`. -/
theorem mslot_eq_low {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hs : 0 < Real.sin (2 * θ)) (i j : ℕ) :
    (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  have hgam : Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]
    intro h
    linarith
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow,
    Work.Spaces.bt_rpow_sq (Work.Spaces.gam α) (Real.sin (2 * θ)) hs.le hgam]
  ring

/-! ## The factorisation of `HkIntegrand` -/

/-- **The level-`m` slice factorisation** on the open angular interval:
`HkIntegrand α m f z θ = (w z)² · lowSum α m f z θ`. -/
theorem HkIntegrand_eq_w_sq_mul_lowSum {α : ℝ} (hα : 0 < α) (m : ℕ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.HkIntegrand α m f z θ = (Work.Spaces.w z) ^ 2 * lowSum α m f z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  simp only [Work.Spaces.HkIntegrand, lowSum]
  rw [mul_add]
  simp only [Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => zslot_eq_low hs i
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ m
    · rw [if_pos hc, if_pos hc]
      exact mslot_eq_low hα hs i j
    · rw [if_neg hc, if_neg hc]
      ring

/-- Almost every point of `Iθ` is an interior point of the interval. -/
theorem ae_mem_Ioo_Iθ_low :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  rw [Work.Spaces.Iθ]
  rw [← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc]
  exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo

/-- The factorisation, almost everywhere on `Iθ`. -/
theorem ae_HkIntegrand_eq_w_sq_mul_lowSum {α : ℝ} (hα : 0 < α) (m : ℕ) (f : ℝ → ℝ → ℝ)
    (z : ℝ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α m f z θ = (Work.Spaces.w z) ^ 2 * lowSum α m f z θ :=
  ae_mem_Ioo_Iθ_low.mono fun _ hθ => HkIntegrand_eq_w_sq_mul_lowSum hα m f hθ

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.supDzAvgLevel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The level-`k` uniform-in-`z` angular-average bound

This file proves `supDzAvgLevel`: for a datum `f` of class `C^∞` on the open quadrant which
lies in the weighted space `ℋ^k` (`Work.Spaces.HkMem α k f`), the angular average at a fixed
radius `z > 0` of any radial derivative `D_z^b f` with `b + 1 ≤ k` is bounded by a universal
multiple of `HkSq α k f`:

  `∫_{Iθ} (D_z^b f z θ)^2 dθ ≤ 3 · HkSq α k f`   for every `z > 0`.

The proof is the level-`k` version of `Work.FTS.TransportS.SupDzAux.sup_dz_avg_le` (level `4`,
`b ≤ 2`) and of `Work.FTS.StrongPersist.N6.sliceAvg_le6` (level `6`, `a + b ≤ 5`): the same
window form of the radial Hardy inequality (`Work.FTS.TransportS.half_line_window_bound`) +
Tonelli.  The level-`k` ingredients used here are

* the pointwise domination `(D_z^j f z θ)^2 (w z)^2 ≤ HkIntegrand α k f z θ` for `j ≤ k`
  (`dzIter_sq_w_sq_le_HkIntegrand_k` below, which is `Work.Spaces.sq_le_HkIntegrand_z`
  combined with `sin(2θ)^(-η) ≥ 1`);
* the level-`k` Tonelli swap (`swapK` below, `Work.FTS.H2.swap_iterated_integral_of_nonneg`
  with `SmoothOpen.continuousOn_HkIntegrand`).

The hypothesis `b + 1 ≤ k` is exactly what the window argument needs: the derivative slot
`D_z^{b+1} f` must be a slot of `ℋ^k`, while the window term only needs `D_z^b f`, i.e. `b ≤ k`.
-/

/-! ## Pointwise domination of a single `D_z`-slot -/

/-- On the open quadrant, `(D_z^j f z θ)² * (w z)² ≤ HkIntegrand α k f z θ` for `j ≤ k`:
the plain `D_z`-slot bound `sq_le_HkIntegrand_z`, multiplied by the factor
`sin(2θ)^(-η) ≥ 1`.  (Level-`k` version of `Work.FTS.H2.dzIter_sq_w_le_HkIntegrand`.) -/
theorem dzIter_sq_w_sq_le_HkIntegrand_k (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hsin : 0 < Real.sin (2 * θ)) (j : ℕ) (hj : j ≤ k) :
    (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.FTS.H2.one_le_rpow_neg hsin hs1 Work.Spaces.eta_nonneg
  have hrew : (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta
      (le_of_lt hsin) (ne_of_gt Work.Spaces.eta_pos)]
    ring
  have hzle := Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hj
  rw [hrew] at hzle
  calc (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h1
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := hzle

/-- On the open quadrant, `(D_z^j f z θ)² ≤ HkIntegrand α k f z θ` for `j ≤ k`: the previous
bound divided by `w² ≥ 1` at `z > 0`.  (Level-`k` version of `avgDzIter_sq_le`.) -/
theorem avgDzIter_sq_le_k (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hz : 0 < z)
    (hsin : 0 < Real.sin (2 * θ)) (j : ℕ) (hj : j ≤ k) :
    (Work.Spaces.DzIter j f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have h := dzIter_sq_w_sq_le_HkIntegrand_k α k f z θ hsin j hj
  have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  calc (Work.Spaces.DzIter j f z θ) ^ 2
      = (Work.Spaces.DzIter j f z θ) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg _)
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := h

/-! ## Tonelli for the level-`k` integrand -/

/-- **Tonelli for the `ℋ^k`-integrand of an open-class datum.**  For `f` of class `C^∞` on the
open quadrant with `HkMem α k f`, the iterated integral of `HkIntegrand α k f` in the order
`∫_θ ∫_z` equals `HkSq α k f`, its partially integrated function is integrable on the angles,
and for almost every angle the radial slice is integrable.  (The `SmoothOpen`-version of
`Work.FTS.H2.HkSqSwap` and of `Work.FTS.TransportS.SupDzAux.avgHkSqSwap`, with the numeral `4`
replaced by `k`.) -/
theorem swapK (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α k f) :
    (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ
        = Work.Spaces.HkSq α k f) ∧
      MeasureTheory.Integrable
        (fun σ : ℝ => ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α k f s σ)
          Work.Spaces.Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_HkIntegrand α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  have houter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice houter
  refine ⟨?_, h2, h3⟩
  rw [Work.Spaces.HkSq]
  exact h1

/-- Almost every angle of `Iθ` lies in the open interval `(0, π/2)`. -/
theorem ae_mem_Ioo_Iθ_k :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
  filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
    (b := Real.pi / 2)] with σ h
  exact fun hmem' => h.mpr hmem'

/-! ## The main estimate -/

/-- Level-`k` generalisation of the uniform-in-`z` angular-average bound.
Templates in the tree: `Work.FTS.TransportS.SupDzAux.sup_dz_avg_le` (level 4, `b ≤ 2`, constant 3)
and `Work.FTS.StrongPersist.N6.sliceAvg_le6` (level 6, mixed slots with `a + b ≤ 5`, constant 4);
both are the same window-bound + Tonelli argument with `4`/`6` replaced by `k`.  The needed
level-`k` ingredients are: the pointwise domination
`(DzIter j f z θ)^2 * (w z)^2 ≤ HkIntegrand α k f z θ` for `j ≤ k` (from
`Work.Spaces.sq_le_HkIntegrand_z` plus `1 ≤ sin(2θ)^(-η)`), the level-`k` Tonelli swap
(`Work.FTS.H2.swap_iterated_integral_of_nonneg` with `SmoothOpen.continuousOn_HkIntegrand`),
and `Work.FTS.TransportS.half_line_window_bound`. -/
theorem supDzAvgLevel : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (k b : ℕ), 0 < α →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α k f → b + 1 ≤ k →
    ∀ z : ℝ, 0 < z →
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α f k b hα hF hmem hbk z hz
  obtain ⟨hswap, hGint, hGslice⟩ := swapK α k f hF hmem
  have hbk' : b ≤ k := by omega
  have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ae_mem_Ioo_Iθ_k
  -- the window bound, for every radius `R₀ ≥ z`
  have hbound : ∀ R₀ : ℝ, z ≤ R₀ →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
        ≤ (2 + 2 / R₀) * Work.Spaces.HkSq α k f := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
    have hz2R : z ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hσbound : ∀ σ : ℝ, σ ∈ Set.Ioo 0 (π/2) →
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α k f s σ)
          Work.Spaces.Iz →
        (Work.Spaces.DzIter b f z σ) ^ 2
          ≤ (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
      intro σ hσ hσint
      have hsinσ : 0 < Real.sin (2 * σ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
      -- the hypotheses of the one-dimensional window inequality
      have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
          HasDerivAt (fun x : ℝ => Work.Spaces.DzIter b f x σ)
            (Work.Spaces.pz (Work.Spaces.DzIter b f) x σ) x :=
        fun x hx => hF.hasDerivAt_slice_DzIter b hσ (lt_of_lt_of_le hz hx.1)
      have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.DzIter b f x σ)
          (Set.Icc R₀ (2 * R₀)) :=
        ((hF.DzIter b).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
      have hcont' : ContinuousOn (fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ)
          (Set.Icc z (2 * R₀)) :=
        (((hF.DzIter b).pz).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have hint : MeasureTheory.IntegrableOn
          (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
        (hcont.pow 2).integrableOn_Icc
      have hwin := Work.FTS.TransportS.half_line_window_bound
        (h := fun x : ℝ => Work.Spaces.DzIter b f x σ)
        (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ)
        hz hR hderiv hcont hcont' hint
      -- continuity of the two relevant slices on the window intervals
      have hcontW : ContinuousOn
          (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x)
          (Set.Icc z (2 * R₀)) := by
        refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) ?_
        intro x hx
        exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
      have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
          (Set.Icc z (2 * R₀)) := by
        have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀))
            Work.FTS.EllipticEst.Q0 :=
          fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
        have hc := (hF.continuousOn_HkIntegrand α k).comp
          (continuousOn_id.prodMk continuousOn_const) hmap
        simpa only [Function.comp_def, id_eq] using hc
      have hIntL1 : IntervalIntegrable
          (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            * Work.Spaces.w x) ^ 2) volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            * Work.Spaces.w x) ^ 2) (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hcontW.pow 2
      have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
          (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hHkcont
      have hIntL2 : IntervalIntegrable
          (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2) volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2)
            (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hcont.pow 2
      have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
          volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
          (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
      -- pointwise domination of the two window integrands
      have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
          (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x) ^ 2
            ≤ Work.Spaces.HkIntegrand α k f x σ := by
        intro x hx
        have hcomm : x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            = Work.Spaces.DzIter (b + 1) f x σ := rfl
        rw [hcomm, mul_pow]
        exact dzIter_sq_w_sq_le_HkIntegrand_k α k f x σ hsinσ (b + 1) (by omega)
      have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
          (Work.Spaces.DzIter b f x σ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f x σ :=
        fun x hx => avgDzIter_sq_le_k α k f x σ (lt_of_lt_of_le hRpos hx.1) hsinσ b hbk'
      -- the two window integrals are dominated by the full radial integral
      have hbigA : ∫ x in z..(2 * R₀), Work.Spaces.HkIntegrand α k f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
        rw [intervalIntegral.integral_of_le hz2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
      have hbigB : ∫ x in R₀..(2 * R₀), Work.Spaces.HkIntegrand α k f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
        rw [intervalIntegral.integral_of_le hR2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hmonoA := intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hptA
      have hmonoB := intervalIntegral.integral_mono_on hR2R hIntL2 hIntR2 hptB
      calc (Work.Spaces.DzIter b f z σ) ^ 2
          ≤ 2 * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
              * Work.Spaces.w x) ^ 2)
            + (2 / R₀) * ∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter b f x σ) ^ 2 := hwin
        _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
            + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num))
              (mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity))
        _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz,
              Work.Spaces.HkIntegrand α k f s σ) := by ring
    -- integrate the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α k f s σ) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact hσbound σ hσθ hσint
    have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine MeasureTheory.Integrable.mono'
        (hmem.1 z (show z ∈ Work.Spaces.Iz from le_of_lt hz)) ?_ ?_
      · exact (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => Work.Spaces.DzIter b f p.1 p.2)
          ((hF.DzIter b).continuousOn) hz).pow 2
      · filter_upwards [Work.FTS.H2.ae_sin_two_pos] with σ hsin
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact avgDzIter_sq_le_k α k f z σ hz hsin b hbk'
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α k f s σ :=
          MeasureTheory.integral_mono_ae hLI (hGint.const_mul _) hle
      _ = (2 + 2 / R₀) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α k f s σ) := MeasureTheory.integral_const_mul _ _
      _ = (2 + 2 / R₀) * Work.Spaces.HkSq α k f := by rw [hswap]
  -- take `R₀ = max z 2`, so that the coefficient is at most `3`
  have hzmax : z ≤ max z 2 := le_max_left z 2
  have hbnd := hbound (max z 2) hzmax
  have hpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
  have h2max : 2 ≤ max z 2 := le_max_right z 2
  have hcoef : 2 + 2 / max z 2 ≤ 3 := by
    have h : 2 / max z 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact h2max
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ (2 + 2 / max z 2) * Work.Spaces.HkSq α k f := hbnd
    _ ≤ 3 * Work.Spaces.HkSq α k f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α k f)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.Spaces (Dz Dth DthIter DzIter mixed pz pth pzIter pthIter)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Multiplication of the open-quadrant smooth class -/

/-- `Work.FTS.EllipticEst.SmoothOpen` is closed under pointwise multiplication. -/
theorem smoothOpen_mul {F G : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ * G z θ)) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun z θ => F z θ * G z θ)
      = Function.uncurry F * Function.uncurry G := rfl
  rw [h1]
  exact hF.mul hG

/-! ## `D_z` commutes with the iterates of `D_θ` on the open quadrant, in the honest order -/

/-- **`D_z (D_θ^i g) = D_θ^i (D_z g)` on the open quadrant**, for `g` of class `SmoothOpen`.
This is the genuine-order (`Work.Stability.smoothOrder`) instance of
`Work.Spaces.DzDthIterCommOn` (which asks for analyticity) on `Q0 = (0,∞) × (0,π/2)`. -/
theorem Dz_DthIter_comm_Q0 {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      Work.FTS.EllipticEst.Q0) (a : ℕ) :
    Set.EqOn (Function.uncurry (Dz (DthIter a g)))
      (Function.uncurry (DthIter a (Dz g))) Work.FTS.EllipticEst.Q0 := by
  have hV : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have h2le : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [Work.Stability.smoothOrder]; exact WithTop.coe_le_coe.mpr le_top
  induction a with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hsmD : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (DthIter i g)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (DthIter i g)) y :=
        (ContDiffOn.of_le hsmD h2le).contDiffAt (hV.mem_nhds hy)
      have hcomm : Dz (Dth (DthIter i g)) y.1 y.2
          = Dth (Dz (DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := DthIter i g) hcd
      show Dz (Dth (DthIter i g)) y.1 y.2 = Dth (DthIter i (Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2) * pth (Dz (DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2) * pth (DthIter i (Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- `D_θ^i (D_z f) = D_z (D_θ^i f)` on the open quadrant, for `f` of class `SmoothOpen`
(the two sides of `Dz_DthIter_comm_Q0`, in the form used below). -/
theorem DthIter_Dz_eq_Q0 {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) :
    Set.EqOn (Function.uncurry (DthIter i (Dz f))) (Function.uncurry (Dz (DthIter i f)))
      Work.FTS.EllipticEst.Q0 :=
  (Dz_DthIter_comm_Q0 hf i).symm

/-! ## The resulting slot identity -/

/-- The pure radial instance: `D_z^b (D_z f) = D_z^{b+1} f` (a function identity). -/
theorem dzIter_Dz_eq (b : ℕ) (f : ℝ → ℝ → ℝ) : DzIter b (Dz f) = DzIter (b + 1) f := by
  induction b with
  | zero => rfl
  | succ n ih =>
      show Dz (DzIter n (Dz f)) = DzIter (n + 1 + 1) f
      rw [ih]
      exact (Work.Spaces.DzIter_succ (n + 1) f).symm

/-- **`mixed m i (D_z f) = mixed (m+1) i f` on the open quadrant.**  A `D_θ`-derivative that
lands on the factor `D_z f` of a Leibniz expansion is (the next slot of) a derivative of `f`:
`D_z^m D_θ^i (D_z f) = D_z^{m+1} D_θ^i f`. -/
theorem mixed_Dz_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (m i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    mixed m i (Dz f) z θ = mixed (m + 1) i f z θ := by
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  have hEq := (Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
    (DthIter_Dz_eq_Q0 hf i) m) hy
  have hEq' : DzIter m (DthIter i (Dz f)) z θ = DzIter m (Dz (DthIter i f)) z θ := hEq
  simp only [mixed]
  rw [hEq', dzIter_Dz_eq m (DthIter i f)]

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.supDz_zslice6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise `z`-slice bound for the level-6 strong-persistence ladder

For a datum `f` of class `C^∞` on the open quadrant which lies in the weighted space
`ℋ⁶` (`Work.Spaces.HkMem α 6 f`), and for a fixed *interior* angle `θ`, the value at
`z > 0` of the `b`-th radial derivative `D_z^b f` (`b ≤ 5`) is controlled by the weighted
`L²`-norm, over the *whole* half line, of the next radial derivative `D_z^{b+1} f`:

  `(D_z^b f z θ)² ≤ C · ∫_{z' ∈ Iz} (D_z^{b+1} f z' θ)² · w(z')²`,  `w(z) = (1+z)²/z²`.

Two integrability hypotheses on the single slice `z' ↦ D_z^b f z' θ` (for the `b`-th and
the `(b+1)`-st derivative) are part of the statement; they are what replaces the *decay*
hypothesis that the classical radial Hardy inequality `Work.Spaces.HardyZ` needs.  The
proof is the window form of the radial Hardy inequality
(`Work.FTS.TransportS.half_line_window_bound`): for every `R₀ ≥ z`,

  `(h z)² ≤ 2 ∫_{z}^{2R₀} (x h'(x) w(x))² + (2/R₀) ∫_{R₀}^{2R₀} h(x)²`,

the second (window) term is dominated by `(2/R₀) ∫_{Iz} h² w²` because `w ≥ 1` on `(0,∞)`,
and the first term is monotone in `R₀`; letting `R₀ → ∞` and using that the two integrals
are finite gives the bound with the constant `2`.

-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the weight -/


/-- `1 ≤ w z²` for `z > 0`. -/
theorem zslice6_one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 :=
  one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)

/-! ## The one-dimensional radial Hardy bound on a single slice -/

/-- **Radial Hardy inequality without a decay hypothesis.**  Let `h` be of class `C¹` on
`(0,∞)`, with radial derivative `x ↦ x h'(x)`; assume `h` is square integrable against the
weight `w²` and that `x ↦ x h'(x) w(x)` is square integrable on `Iz = [0,∞)`.  Then

  `h(z₀)² ≤ 2 ∫_{Iz} (x h'(x) w(x))² dx`

for every `z₀ > 0`.  (The hypothesis `∫ h² w² < ∞` plays the role of the decay hypothesis
of `Work.Spaces.HardyZ`: it is what forces the window term of the window form of the
inequality to be small.) -/
theorem zslice6_hardy {h h' : ℝ → ℝ} {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hderiv : ∀ x, 0 < x → HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h (Set.Ioi 0)) (hcont' : ContinuousOn h' (Set.Ioi 0))
    (hint : IntegrableOn (fun x => (h x) ^ 2 * (Work.Spaces.w x) ^ 2) Work.Spaces.Iz)
    (hint2 : IntegrableOn (fun x => (x * h' x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz) :
    (h z₀) ^ 2 ≤ 2 * ∫ x in Work.Spaces.Iz, (x * h' x * Work.Spaces.w x) ^ 2 := by
  set P := ∫ x in Work.Spaces.Iz, (x * h' x * Work.Spaces.w x) ^ 2 with hP
  set K := ∫ x in Work.Spaces.Iz, (h x) ^ 2 * (Work.Spaces.w x) ^ 2 with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici
      (fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- the window inequality, for every `R₀ ≥ z₀`
  have key : ∀ R₀ : ℝ, z₀ ≤ R₀ → (h z₀) ^ 2 ≤ 2 * P + (2 / R₀) * K := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz₀ hR
    have hz2R : z₀ ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hcontR : ContinuousOn h (Set.Icc R₀ (2 * R₀)) :=
      hcont.mono fun x hx => lt_of_lt_of_le hRpos hx.1
    have hwin := Work.FTS.TransportS.half_line_window_bound (h := h) (h' := h') hz₀ hR
      (fun x hx => hderiv x (lt_of_lt_of_le hz₀ hx.1)) hcontR
      (hcont'.mono fun x hx => lt_of_lt_of_le hz₀ hx.1)
      (hcontR.pow 2).integrableOn_Icc
    -- the first window integral is at most the full radial integral
    have hAle : ∫ x in z₀..(2 * R₀), (x * h' x * Work.Spaces.w x) ^ 2 ≤ P := by
      rw [intervalIntegral.integral_of_le hz2R, hP]
      refine MeasureTheory.setIntegral_mono_set hint2
        (Eventually.of_forall fun x => sq_nonneg _) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz₀ hx.1)
    -- the window average of `h²` is dominated by `∫ h² w²`, because `w ≥ 1` on `(0,∞)`
    have hBle : ∫ x in R₀..(2 * R₀), (h x) ^ 2 ≤ K := by
      rw [intervalIntegral.integral_of_le hR2R, hK]
      have hsub : Set.Ioc R₀ (2 * R₀) ⊆ Work.Spaces.Iz :=
        fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hInt1 : IntegrableOn (fun x => (h x) ^ 2) (Set.Ioc R₀ (2 * R₀)) :=
        (hcontR.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      have hInt2 : IntegrableOn (fun x => (h x) ^ 2 * (Work.Spaces.w x) ^ 2)
          (Set.Ioc R₀ (2 * R₀)) := hint.mono_set hsub
      have step1 := MeasureTheory.setIntegral_mono_on hInt1 hInt2 measurableSet_Ioc
        (fun x hx => by
          have hw : 1 ≤ (Work.Spaces.w x) ^ 2 :=
            zslice6_one_le_w_sq (lt_trans hRpos hx.1)
          simpa using mul_le_mul_of_nonneg_left hw (sq_nonneg (h x)))
      have step2 := MeasureTheory.setIntegral_mono_set hint
        (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Eventually.of_forall hsub)
      exact le_trans step1 step2
    have hcoef1 : (0 : ℝ) ≤ 2 := by norm_num
    have hcoef2 : (0 : ℝ) ≤ 2 / R₀ := by positivity
    exact le_trans hwin (add_le_add (mul_le_mul_of_nonneg_left hAle hcoef1)
      (mul_le_mul_of_nonneg_left hBle hcoef2))
  -- let `R₀ → ∞`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set R₀ := max z₀ (2 * K / ε) + 1 with hR₀
  have hmax : max z₀ (2 * K / ε) ≤ R₀ := by
    rw [hR₀]; exact le_add_of_nonneg_right zero_le_one
  have hR₀pos : 0 < R₀ :=
    lt_of_lt_of_le (lt_of_lt_of_le hz₀ (le_max_left _ _)) hmax
  have hR₀z : z₀ ≤ R₀ := le_trans (le_max_left _ _) hmax
  have hKle : (2 / R₀) * K ≤ ε := by
    have hlt : 2 * K / ε < R₀ :=
      lt_of_le_of_lt (le_max_right z₀ (2 * K / ε)) (by
        rw [hR₀]; exact lt_add_of_pos_right _ zero_lt_one)
    have h2 : 2 * K / R₀ < ε := by
      rw [div_lt_iff₀ hR₀pos]
      have hlt' : 2 * K < R₀ * ε := (div_lt_iff₀ hε).mp hlt
      rwa [mul_comm R₀ ε] at hlt'
    calc (2 / R₀) * K = 2 * K / R₀ := by ring
      _ ≤ ε := le_of_lt h2
  exact le_trans (key R₀ hR₀z) (add_le_add le_rfl hKle)

/-! ## The target -/


end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.SolFire.LGammaT_congr_of_agreeOnQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves.SolFire

/-- `z ∂_z` is a *local* operator: `pz f` at a point of the open quadrant `z > 0`,
`0 < θ < π/2` depends only on the values of `f` on that open quadrant. -/
private lemma pz_congr_of_agreeOnQ {f f' : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ := by
  rw [Work.Spaces.pz]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact h z' θ hz' hθ hθ2

/-- `∂_θ` is a *local* operator: `pth f` at a point of the open quadrant `z > 0`,
`0 < θ < π/2` depends only on the values of `f` on that open quadrant. -/
private lemma pth_congr_of_agreeOnQ {f f' : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ := by
  rw [Work.Spaces.pth]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ, hθ2⟩] with θ' hθ'
  exact h z θ' hz hθ'.1 hθ'.2

theorem LGammaT_congr_of_agreeOnQ {α : ℝ} {f f' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Coercivity.LGammaT α f z θ = Work.Coercivity.LGammaT α f' z θ := by
  have hf : f z θ = f' z θ := h z θ hz hθ hθ2
  have hpz : Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ := pz_congr_of_agreeOnQ hz hθ hθ2 h
  have hpt : Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ := pth_congr_of_agreeOnQ hz hθ hθ2 h
  have hLz : Work.Coercivity.L12f f z = Work.Coercivity.L12f f' z :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_of_lt hz) h
  have hTr : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Coercivity.Transport f z' θ' = Work.Coercivity.Transport f' z' θ' := by
    intro z' θ' hz' hθ' hθ2'
    simp only [Work.Coercivity.Transport, Work.Spaces.Dth, pth_congr_of_agreeOnQ hz' hθ' hθ2' h]
  have hL0 : Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport f') 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl 0) hTr
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.L,
    Work.Coercivity.Proj]
  rw [hL0, hLz, hf]
  simp only [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Spaces.Dz, hpz, hpt]

end Work.FTS_FinalLeaves.SolFire
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.StarVopWlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-! ## Part 4 — the uniform `𝒲^{4,∞}`-bound on `D_z^kD_θ^i W`, `k ≤ 2`, `i ≤ 2` -/

/-- The Stirling expansion of `D_z²` in powers of `z`:
`D_z² X = z·∂_zX + z²·∂_z²X`, for a function smooth on the open quadrant. -/
theorem DzIter_two_eq {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 2 X z θ
        = z * Work.Spaces.pzIter 1 X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 1 X z' θ)
      (Work.Spaces.pzIter 2 X z θ) z := hX.hasDerivAt_slice_pzIter 1 hθ hz
  have hmul := (hasDerivAt_id z).mul h2
  have hder : deriv (fun z' : ℝ => z' * Work.Spaces.pzIter 1 X z' θ) z
      = 1 * Work.Spaces.pzIter 1 X z θ + z * Work.Spaces.pzIter 2 X z θ := hmul.deriv
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pzIter 1 X z' θ) z
      = z * Work.Spaces.pzIter 1 X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ
  rw [hder]; ring

/-- **The uniform bound on the low-order mixed derivatives of `W`**: from
`WlInfMem α 4 W` and `α ≤ 1`,
`|D_z^kD_θ^i W| ≤ 4·WlInf α 4 W` for `k ≤ 2`, `i ≤ 2`, `z > 0`, `θ ∈ (0,π/2)`.

(For `i = 0` the `𝒲^{4,∞}`-bound is `WlInf/(z+1)^k`; for `i ≥ 1` it carries the extra angular
factor `(α + sin 2θ)·sin(2θ)^{α/5} ≤ 2`; the Stirling expansion of `D_z²` contributes a factor
`2`, whence the constant `4`.) -/
theorem mixed_two_le_WlInf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W : ℝ → ℝ → ℝ}
    (hW : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.WlInfMem α 4 W) :
    ∀ k i : ℕ, k ≤ 2 → i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed k i W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W := by
  intro k i hk hi z θ hz hθ0 hθ1
  have hzI : z ∈ Work.Spaces.Iz := hz.le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, by linarith [Real.pi_pos]⟩
  have hW₀nn : 0 ≤ Work.Spaces.WlInf α 4 W := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 W hmem)
      (Work.Spaces.wlThSum_nonneg α 4 W hmem)
  have hzp : (0 : ℝ) < z + 1 := by linarith
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hfac : (α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5) ≤ 2 := by
    have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
    have h2 : Real.sin (2 * θ) ^ (α / 5) ≤ 1 :=
      Real.rpow_le_one hs0.le hs1 (by linarith : (0 : ℝ) ≤ α / 5)
    have h3 : (0 : ℝ) ≤ α + Real.sin (2 * θ) := by linarith
    have h4 : (0 : ℝ) ≤ Real.sin (2 * θ) ^ (α / 5) := Real.rpow_nonneg hs0.le _
    nlinarith
  have hzbd : ∀ k' : ℕ, k' ≤ 2 →
      |Work.Spaces.pzIter k' W z θ| ≤ Work.Spaces.WlInf α 4 W / (z + 1) ^ k' :=
    fun k' hk' => Work.Spaces.pz_sup_bound α 4 W hmem k' (by omega) z θ hzI hθI
  have hjbd : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ k' : ℕ, k' ≤ 2 →
      |Work.Spaces.pzIter k' (Work.Spaces.DthIter j W) z θ|
        ≤ 2 * Work.Spaces.WlInf α 4 W / (z + 1) ^ k' := by
    intro j hj hj2 k' hk'
    have h := Work.Spaces.pz_Dth_sup_bound α hα 4 W hmem j k' hj (by omega) z θ hzI hθI
    have hpos : (0 : ℝ) < (z + 1) ^ k' := by positivity
    calc |Work.Spaces.pzIter k' (Work.Spaces.DthIter j W) z θ|
        ≤ Work.Spaces.WlInf α 4 W / (z + 1) ^ k'
            * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5)) := h
      _ = Work.Spaces.WlInf α 4 W
            * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5)) / (z + 1) ^ k' := by ring
      _ ≤ Work.Spaces.WlInf α 4 W * 2 / (z + 1) ^ k' := by
          refine div_le_div_of_nonneg_right ?_ hpos.le
          exact mul_le_mul_of_nonneg_left hfac hW₀nn
      _ = 2 * Work.Spaces.WlInf α 4 W / (z + 1) ^ k' := by ring
  have key1 : ∀ (X : ℝ → ℝ → ℝ) (M : ℝ),
      |Work.Spaces.pzIter 1 X z θ| ≤ M / (z + 1) → |Work.Spaces.DzIter 1 X z θ| ≤ M := by
    intro X M hX
    have h1 : |Work.Spaces.DzIter 1 X z θ| ≤ (z + 1) * |Work.Spaces.pzIter 1 X z θ| := by
      rw [show Work.Spaces.DzIter 1 X z θ = z * Work.Spaces.pzIter 1 X z θ from rfl,
        abs_mul, abs_of_nonneg hz.le]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    calc |Work.Spaces.DzIter 1 X z θ| ≤ (z + 1) * |Work.Spaces.pzIter 1 X z θ| := h1
      _ ≤ (z + 1) * (M / (z + 1)) := mul_le_mul_of_nonneg_left hX hzp.le
      _ = M := by field_simp
  have key2 : ∀ (X : ℝ → ℝ → ℝ) (M : ℝ), Work.FTS.EllipticEst.SmoothOpen X →
      |Work.Spaces.pzIter 1 X z θ| ≤ M / (z + 1) →
      |Work.Spaces.pzIter 2 X z θ| ≤ M / (z + 1) ^ 2 →
      |Work.Spaces.DzIter 2 X z θ| ≤ 2 * M := by
    intro X M hXs hX1 hX2
    have h1 : |z * Work.Spaces.pzIter 1 X z θ| ≤ M := by
      have ha : |z * Work.Spaces.pzIter 1 X z θ|
          ≤ (z + 1) * |Work.Spaces.pzIter 1 X z θ| := by
        rw [abs_mul, abs_of_nonneg hz.le]
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      calc |z * Work.Spaces.pzIter 1 X z θ| ≤ (z + 1) * |Work.Spaces.pzIter 1 X z θ| := ha
        _ ≤ (z + 1) * (M / (z + 1)) := mul_le_mul_of_nonneg_left hX1 hzp.le
        _ = M := by field_simp
    have h2 : |z ^ 2 * Work.Spaces.pzIter 2 X z θ| ≤ M := by
      have ha : |z ^ 2 * Work.Spaces.pzIter 2 X z θ|
          ≤ (z + 1) ^ 2 * |Work.Spaces.pzIter 2 X z θ| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 2)]
        exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
      calc |z ^ 2 * Work.Spaces.pzIter 2 X z θ|
          ≤ (z + 1) ^ 2 * |Work.Spaces.pzIter 2 X z θ| := ha
        _ ≤ (z + 1) ^ 2 * (M / (z + 1) ^ 2) :=
            mul_le_mul_of_nonneg_left hX2 (by positivity)
        _ = M := by field_simp
    rw [DzIter_two_eq hXs z θ hz hθ0 hθ1]
    calc |z * Work.Spaces.pzIter 1 X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ|
        ≤ |z * Work.Spaces.pzIter 1 X z θ| + |z ^ 2 * Work.Spaces.pzIter 2 X z θ| :=
          abs_add_le _ _
      _ ≤ M + M := add_le_add h1 h2
      _ = 2 * M := by ring
  interval_cases k
  · interval_cases i
    · show |W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W
      have h := hzbd 0 (by norm_num)
      simp only [pow_zero, div_one, Work.Spaces.pzIter_zero] at h
      linarith [h, hW₀nn]
    · show |Work.Spaces.DthIter 1 W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W
      have h := hjbd 1 (by norm_num) (by norm_num) 0 (by norm_num)
      simp only [pow_zero, div_one, Work.Spaces.pzIter_zero] at h
      linarith [h, hW₀nn]
    · show |Work.Spaces.DthIter 2 W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W
      have h := hjbd 2 (by norm_num) (by norm_num) 0 (by norm_num)
      simp only [pow_zero, div_one, Work.Spaces.pzIter_zero] at h
      linarith [h, hW₀nn]
  · by_cases hi0 : i = 0
    · subst hi0
      show |Work.Spaces.DzIter 1 W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W
      have h := hzbd 1 (by norm_num)
      have h2 := key1 W (Work.Spaces.WlInf α 4 W) (by simpa using h)
      linarith [h2, hW₀nn]
    · have hi1 : 1 ≤ i := by omega
      show |Work.Spaces.DzIter 1 (Work.Spaces.DthIter i W) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 W
      have h := hjbd i hi1 hi 1 (by norm_num)
      have h2 := key1 (Work.Spaces.DthIter i W) (2 * Work.Spaces.WlInf α 4 W) (by simpa using h)
      linarith [h2, hW₀nn]
  · by_cases hi0 : i = 0
    · subst hi0
      show |Work.Spaces.DzIter 2 W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W
      have h1 := hzbd 1 (by norm_num)
      have h2 := hzbd 2 (by norm_num)
      have h3 := key2 W (Work.Spaces.WlInf α 4 W) hW (by simpa using h1) (by simpa using h2)
      linarith [h3, hW₀nn]
    · have hi1 : 1 ≤ i := by omega
      show |Work.Spaces.DzIter 2 (Work.Spaces.DthIter i W) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 W
      have h1 := hjbd i hi1 hi 1 (by norm_num)
      have h2 := hjbd i hi1 hi 2 (by norm_num)
      have h3 := key2 (Work.Spaces.DthIter i W) (2 * Work.Spaces.WlInf α 4 W)
        (hW.DthIter i) (by simpa using h1) (by simpa using h2)
      linarith [h3, hW₀nn]


end Work.FTS_RegExport.RXT
end
end
