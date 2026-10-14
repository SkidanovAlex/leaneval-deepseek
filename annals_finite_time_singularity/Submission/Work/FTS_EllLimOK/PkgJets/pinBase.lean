import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_meas_engine
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.gRHS_tendsto
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.sliceF_deriv_le_sliceV =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VopAux

/-- `thGam α` is continuous on the open angular interval `(0, π/2)`. -/
private lemma continuousOn_thGam_open (α : ℝ) :
    ContinuousOn (Work.FTS.EllipticEst.thGam α) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-
# The one-dimensional `∂_θ`-Poincaré estimate with boundary *traces*

Same setting as `Work.FTS.EllSol.VopAux.sliceF_le_sliceV` (see that file): `sliceF K α u` is the
angular datum `∫_{Iθ}[(u)²thEta + ∑_{1≤i≤K}(L^i u)²thGam α]`, `L = D_θ = sin(2θ)∂_θ`,
`thEta = sin(2θ)^{-η}`, `thGam α = sin(2θ)^{-γ}`, `γ = 1+α/10`, `η = 99/100`.
`u` is `C^∞` on the OPEN interval `(0,π/2)` with vanishing endpoint LIMITS and the datum
`v = u''` has `∫v²·thEta < ∞` and `∫(L^m v)²·thGam < ∞` for `1 ≤ m ≤ K`.
Claim: `sliceF K α (deriv u) ≤ C_K · sliceF K α v` (uniformly in `α ∈ (0,1]` and `u`), and the
terms of `sliceF K α (deriv u)` are integrable on `Iθ`.

This is the `∂_θ`-case (as opposed to the `∂_θ²`-case of `sliceF_le_sliceV`) and it is NOT
obtained by applying that result to `w = deriv u` (which would produce the datum `w'' = u'''`);
it uses the first-order identity `L(deriv u) = sin(2θ)·v`.

ROUTE. `∫(u')²·thEta ≤ C·∫v²·thEta` (and the integrability of `(u')²·thEta`) is the second
conclusion of `Work.FTS.EllipticEst.H2W.sliceEtaPoincare` (sorry-free) — note `sliceV u = deriv
(deriv u)`, `sEta = thEta` definitionally. For `i ≥ 1`, `L^i(deriv u) = L^{i-1}(s·v)` because
`L(deriv u) = s·deriv(deriv u) = s·v`; expanding this by the iterated Leibniz rule
`Work.FTS.LocData.Lop_iter_mul_eqOn_smooth` (on `U = Set.Ioo 0 (π/2)`, with
`ContDiffOn ℝ Work.Stability.smoothOrder` obtained from the `∀ n` hypothesis via
`contDiffOn_infty.mpr`; the two factors are `fun θ => Real.sin (2*θ)` and `v`) gives
`L^i(deriv u) θ = ∑_{a ≤ i-1} C(i-1,a)·L^a(sin 2·)(θ)·L^{i-1-a}(v)(θ)`, and
`|L^a(sin 2·)(θ)| ≤ C_a·sin 2θ` (`Work.FTS.EllipticEst.sd_lop_iter_sin_bound`). Since
`sin(2θ) ≤ 1` on `Iθ`, the extra factor is harmless. The `a = i-1` term is
`L^{i-1}(sin 2·)(θ)·v θ` with `(L^{i-1}(sin 2·)(θ))² ≤ C·sin²(2θ)`, and
`sin²(2θ)·v²·thGam = v²·sin(2θ)^{2-γ} ≤ v²·thEta` because `2-γ ≥ -η` (uniform for `α ≤ 1`);
so the `m = 0` term is covered by `v²thEta` (integrable by hypothesis) — do NOT use `v²thGam`,
which need not be integrable. For `m ≥ 1` the terms are `(L^m v)²thGam`, integrable by
hypothesis. The resulting pointwise bound is
`(L^i(deriv u) θ)²·thGam α θ ≤ C_i·((v θ)²thEta θ + ∑_{1 ≤ m ≤ i-1}(L^m v θ)²·thGam α θ)`
(obtained via `(L^a(sin 2·)(θ))² ≤ C_a` plus the weight comparisons), and it integrates
directly against `sliceF K α (sliceV u)`. Integrate with
`MeasureTheory.integral_mono_of_nonneg` (a.e. measurability from continuity on `(0,π/2)`),
transporting `Ioo 0 (π/2)` to `Iθ` by `MeasureTheory.Ioo_ae_eq_Icc`, and bound the `i ≤ K` cases
by one constant using `sliceW_mono`/a finite max.
-/
theorem sliceF_deriv_le_sliceV (K : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ),
    0 < α → α ≤ 1 →
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ ∧
      (∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
        Work.Spaces.Iθ) ∧
      Work.FTS.EllSol.VopAux.sliceF K α (deriv u)
        ≤ C * Work.FTS.EllSol.VopAux.sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
  obtain ⟨Cs, hCspos, hCsb⟩ := Work.FTS.EllipticEst.sd_lop_iter_sin_bound K
  have hCs0 : 0 ≤ Cs := le_of_lt hCspos
  obtain ⟨C1, hC1pos, hC1main⟩ := Work.FTS.EllipticEst.H2W.sliceEtaPoincare
  have hM1 : (1 : ℝ) ≤ max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) := le_max_left _ _
  have hMpos : (0 : ℝ) < max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) :=
    lt_of_lt_of_le zero_lt_one hM1
  refine ⟨C1 + (K : ℝ) * max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) + 1, ?_, ?_⟩
  · have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hmm : 0 < max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) := hMpos
    have hKM : 0 ≤ (K : ℝ) * max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) :=
      mul_nonneg hK0 (le_of_lt hmm)
    linarith
  · intro α u hα0 hα1 hu hlim0 hlim1 hint hintK
    set M : ℝ := max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) with hM
    have hM0 : 0 ≤ M := by rw [hM]; exact le_of_lt hMpos
    have hrestrict : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
        = volume.restrict Work.Spaces.Iθ :=
      Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
    -- (A) the pointwise bound, a.e. on `Iθ`
    have hpt : ∀ i ∈ Finset.Icc 1 K, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          ≤ M * sliceW K α (Work.FTS.EllipticEst.sliceV u) θ := by
      intro i hi
      rw [hM, ← hrestrict]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact sliceDerivPointLe hu hCs0 hCsb hα1 hi hθ
    -- (B) integrability of the dominating function
    have hSW : MeasureTheory.IntegrableOn
        (fun θ => sliceW K α (Work.FTS.EllipticEst.sliceV u) θ) Work.Spaces.Iθ := by
      have hsum : MeasureTheory.IntegrableOn (fun θ => ∑ m ∈ Finset.Icc 1 K,
          (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ :=
        MeasureTheory.integrable_finsetSum (Finset.Icc 1 K) hintK
      show MeasureTheory.IntegrableOn (fun θ =>
          (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          + ∑ m ∈ Finset.Icc 1 K,
              (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ
      exact hint.add hsum
    have hMSW : MeasureTheory.IntegrableOn
        (fun θ => M * sliceW K α (Work.FTS.EllipticEst.sliceV u) θ) Work.Spaces.Iθ :=
      hSW.const_mul M
    -- (C) smoothness (hence measurability) of the iterates of `L` applied to `deriv u`
    have hsmooth : ∀ i m : ℕ, ContDiffOn ℝ m (Work.FTS.EllipticEst.LopIter i (deriv u))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      intro i
      induction i with
      | zero =>
          intro m
          have h : ContDiffOn ℝ m (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
            ContDiffOn.deriv_of_isOpen (m := ((m : ℕ) : WithTop ℕ∞))
              (n := ((m + 1 : ℕ) : WithTop ℕ∞)) (hu (m + 1)) isOpen_Ioo
              (by exact_mod_cast le_refl (m + 1))
          simpa only [Work.FTS.EllipticEst.LopIter_zero] using h
      | succ n ih =>
          intro m
          have h1 : ContDiffOn ℝ (m + 1) (Work.FTS.EllipticEst.LopIter n (deriv u))
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ih (m + 1)
          have h2 : ContDiffOn ℝ m (deriv (Work.FTS.EllipticEst.LopIter n (deriv u)))
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
            ContDiffOn.deriv_of_isOpen (m := ((m : ℕ) : WithTop ℕ∞))
              (n := ((m + 1 : ℕ) : WithTop ℕ∞)) h1 isOpen_Ioo
              (by exact_mod_cast le_refl (m + 1))
          have hsin : ContDiffOn ℝ m (fun θ : ℝ => Real.sin (2 * θ))
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
          have hL : Work.FTS.EllipticEst.LopIter (n + 1) (deriv u)
              = fun θ : ℝ => Real.sin (2 * θ)
                  * deriv (Work.FTS.EllipticEst.LopIter n (deriv u)) θ := by
            rw [Work.FTS.EllipticEst.LopIter_succ]; rfl
          rw [hL]
          simpa only [Pi.mul_apply] using hsin.mul h2
    have hmeas : ∀ i : ℕ, AEStronglyMeasurable
        (fun θ => (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) (volume.restrict Work.Spaces.Iθ) := by
      intro i
      rw [← hrestrict]
      exact (((hsmooth i 1).continuousOn.pow 2).mul (continuousOn_thGam_open α))
        |>.aestronglyMeasurable measurableSet_Ioo
    -- (D) integrability of the single terms
    have hLint : ∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
      intro i hi
      refine Integrable.mono' hMSW (hmeas i) ?_
      filter_upwards [hpt i hi, ae_restrict_mem measurableSet_Icc] with θ hb hmem
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hmem))]
      exact hb
    -- (E) the integral bounds of the single terms
    have hIle : ∀ i ∈ Finset.Icc 1 K,
        (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ)
          ≤ M * sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
      intro i hi
      calc (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
              * Work.FTS.EllipticEst.thGam α θ)
          ≤ ∫ θ in Work.Spaces.Iθ, M * sliceW K α (Work.FTS.EllipticEst.sliceV u) θ :=
            integral_mono_ae (hLint i hi) hMSW (hpt i hi)
        _ = M * sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
            rw [sliceF, MeasureTheory.integral_const_mul]
    -- (F) the `sliceEtaPoincare` consequences
    obtain ⟨hu2int, hderivInt, _hu2le, hderivLe⟩ := hC1main u hu hlim0 hlim1 hint
    have hdInt : MeasureTheory.IntegrableOn
        (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hderivInt
    have hVle : (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.sliceV u θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        ≤ sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
      rw [sliceF]
      refine integral_mono_of_nonneg ?_ hSW ?_
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        show (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          ≤ sliceW K α (Work.FTS.EllipticEst.sliceV u) θ
        rw [sliceW]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun m _ =>
          mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))
    have hderivBound : (∫ θ in Work.Spaces.Iθ,
          (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ C1 * sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
      calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          ≤ C1 * ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.sliceV u θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ := hderivLe
        _ ≤ C1 * sliceF K α (Work.FTS.EllipticEst.sliceV u) :=
            mul_le_mul_of_nonneg_left hVle (le_of_lt hC1pos)
    -- (G) the sum over `i`
    have hsumInt : MeasureTheory.IntegrableOn (fun θ => ∑ i ∈ Finset.Icc 1 K,
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ :=
      MeasureTheory.integrable_finsetSum (Finset.Icc 1 K) hLint
    have hsumBound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.Icc 1 K,
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ)
        ≤ (K : ℝ) * M * sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
      rw [MeasureTheory.integral_finsetSum (Finset.Icc 1 K) hLint]
      have h1 : ∑ i ∈ Finset.Icc 1 K, (∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
              * Work.FTS.EllipticEst.thGam α θ)
          ≤ ∑ _i ∈ Finset.Icc 1 K,
              M * sliceF K α (Work.FTS.EllipticEst.sliceV u) :=
        Finset.sum_le_sum fun i hi => hIle i hi
      have h2 : (∑ _i ∈ Finset.Icc 1 K,
            M * sliceF K α (Work.FTS.EllipticEst.sliceV u))
          = ((Finset.Icc 1 K).card : ℝ)
              * (M * sliceF K α (Work.FTS.EllipticEst.sliceV u)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h3 : ((Finset.Icc 1 K).card : ℝ) ≤ (K : ℝ) := by
        simp
      have h4 : ((Finset.Icc 1 K).card : ℝ)
            * (M * sliceF K α (Work.FTS.EllipticEst.sliceV u))
          ≤ (K : ℝ) * (M * sliceF K α (Work.FTS.EllipticEst.sliceV u)) :=
        mul_le_mul_of_nonneg_right h3
          (mul_nonneg hM0 (sliceF_nonneg K α (Work.FTS.EllipticEst.sliceV u)))
      linarith [h1, h4, le_of_eq h2]
    -- (H) assembly
    have hsplit : sliceF K α (deriv u)
        = (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.Icc 1 K,
              (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ) := by
      rw [sliceF]
      have hfun : (fun θ => sliceW K α (deriv u) θ)
          = fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
              + ∑ i ∈ Finset.Icc 1 K,
                  (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
                    * Work.FTS.EllipticEst.thGam α θ := by
        funext θ
        rw [sliceW]
      rw [hfun, MeasureTheory.integral_add hdInt hsumInt]
    have hfinal : sliceF K α (deriv u)
        ≤ (C1 + (K : ℝ) * M + 1) * sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
      rw [hsplit]
      have hS0 : 0 ≤ sliceF K α (Work.FTS.EllipticEst.sliceV u) :=
        sliceF_nonneg K α (Work.FTS.EllipticEst.sliceV u)
      nlinarith [hderivBound, hsumBound, hS0]
    exact ⟨hdInt, hLint, hfinal⟩

end Work.FTS.EllSol.VopAux
end
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.sliceF_le_sliceV =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The integration step

The pointwise bound of `Submission/Work/FTS/EllSol/VopAux/SliceDPointwise.lean`
(`(L^i u θ)²·thGam α θ ≤ Cd·sliceD K α u θ` at interior angles, for `1 ≤ i ≤ K`) is integrated
against the measure `volume.restrict Iθ` below.  The ingredients are
`Work.FTS.EllipticEst.H2W.sliceEtaPoincare` (integrability of `u²thEta` and `(u')²thEta`, and
their bounds by `∫(u'')²thEta`), the linearity of the integral over `Iθ` (to split `sliceF` and
`∫ sliceD`), and `integral_mono_ae` / `Integrable.mono'` for the transfer of the pointwise
bounds. -/

/-- The open interval `(0, π/2)` and `Iθ = [0, π/2]` carry the same restricted measure. -/
theorem sfIθ_ae :
    volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)


theorem sfIθ_continuousOn_thGam (α : ℝ) :
    ContinuousOn (thGam α) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- **The integration step.**  Given the pointwise bound of `SliceDPointwise` as a hypothesis,
the integrated single-slice estimate of `sliceF_le_sliceV` follows. -/
theorem sliceF_le_sliceV_of_pointwise (K : ℕ)
    (hPt : ∃ Cd : ℝ, 0 < Cd ∧ ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      ∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (LopIter i u θ) ^ 2 * thGam α θ ≤ Cd * sliceD K α u θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ),
    0 < α → α ≤ 1 →
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ ∧
      (∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
        Work.Spaces.Iθ) ∧
      Work.FTS.EllSol.VopAux.sliceF K α u
        ≤ C * Work.FTS.EllSol.VopAux.sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := hPt
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.EllipticEst.H2W.sliceEtaPoincare
  refine ⟨max 1 (C0 + (K : ℝ) * (Cd * (2 * C0 + 1))), lt_max_of_lt_left one_pos, ?_⟩
  intro α u hα0 hα1 hu hlim0 hlim1 hintV hintVm
  -- Poincaré input for the slice `u` and its first derivative
  have hpo := hC0 u hu hlim0 hlim1 hintV
  have hpoU : IntegrableOn (fun θ => (u θ) ^ 2 * thEta θ) Work.Spaces.Iθ := hpo.1
  have hpoD : IntegrableOn (fun θ => (deriv u θ) ^ 2 * thEta θ) Work.Spaces.Iθ := hpo.2.1
  have hpoUle : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
      ≤ C0 * ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ := hpo.2.2.1
  have hpoDle : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * thEta θ)
      ≤ C0 * ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ := hpo.2.2.2
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIVnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ :=
    MeasureTheory.setIntegral_nonneg hIθm
      (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))
  -- the integrability of the `m`-sum of the datum
  have hsumV_int : IntegrableOn (fun θ => ∑ m ∈ Finset.Icc 1 K,
      (LopIter m (sliceV u) θ) ^ 2 * thGam α θ) Work.Spaces.Iθ :=
    MeasureTheory.integrable_finsetSum (Finset.Icc 1 K) (fun m hm => hintVm m hm)
  -- integrality of the dominating function
  have hDint : IntegrableOn (fun θ => sliceD K α u θ) Work.Spaces.Iθ := by
    have hmain : IntegrableOn (fun θ => (u θ) ^ 2 * thEta θ
        + ((deriv u θ) ^ 2 * thEta θ
          + ((sliceV u θ) ^ 2 * thEta θ
            + ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)))
        Work.Spaces.Iθ := hpoU.add (hpoD.add (hintV.add hsumV_int))
    refine hmain.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [sliceD]
    ring
  -- the pointwise bound, upgraded to integrability of the left-hand integrands
  have hcontu : ∀ i : ℕ, ContinuousOn (LopIter i u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun i => (sd_LopIter_contDiffOn (sd_contDiffOn_smoothOrder hu) i).continuousOn
  have hLi_int : ∀ i ∈ Finset.Icc 1 K,
      IntegrableOn (fun θ => (LopIter i u θ) ^ 2 * thGam α θ) Work.Spaces.Iθ := by
    intro i hi
    refine Integrable.mono' (g := fun θ => Cd * sliceD K α u θ) (hDint.const_mul Cd) ?_ ?_
    · rw [← sfIθ_ae]
      exact (((hcontu i).pow 2).mul (sfIθ_continuousOn_thGam α)).aestronglyMeasurable
        measurableSet_Ioo
    · rw [← sfIθ_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (thGam_nonneg hθI))]
      exact hCd α u hα0 hα1 hu i hi θ hθ
  -- the integral bounds for the individual `L^i u`
  have hLi_le : ∀ i ∈ Finset.Icc 1 K,
      (∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
        ≤ Cd * ∫ θ in Work.Spaces.Iθ, sliceD K α u θ := by
    intro i hi
    have hae : (fun θ => (LopIter i u θ) ^ 2 * thGam α θ)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Cd * sliceD K α u θ) := by
      rw [← sfIθ_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact hCd α u hα0 hα1 hu i hi θ hθ
    have h := MeasureTheory.integral_mono_ae (hLi_int i hi) (hDint.const_mul Cd) hae
    rwa [MeasureTheory.integral_const_mul] at h
  -- the two decompositions of `sliceF`
  have hsumU_int : IntegrableOn (fun θ => ∑ i ∈ Finset.Icc 1 K,
      (LopIter i u θ) ^ 2 * thGam α θ) Work.Spaces.Iθ :=
    MeasureTheory.integrable_finsetSum (Finset.Icc 1 K) (fun i hi => hLi_int i hi)
  have hsliceF_u : sliceF K α u = (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
      + ∑ i ∈ Finset.Icc 1 K,
          ∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ := by
    have hw : sliceW K α u = fun θ => (u θ) ^ 2 * thEta θ
        + ∑ i ∈ Finset.Icc 1 K, (LopIter i u θ) ^ 2 * thGam α θ := by
      funext θ
      simp only [sliceW]
    have h1 : sliceF K α u = ∫ θ in Work.Spaces.Iθ, ((u θ) ^ 2 * thEta θ
        + ∑ i ∈ Finset.Icc 1 K, (LopIter i u θ) ^ 2 * thGam α θ) := by
      rw [sliceF, hw]
    rw [h1, MeasureTheory.integral_add hpoU hsumU_int,
      MeasureTheory.integral_finsetSum (Finset.Icc 1 K) (fun i hi => hLi_int i hi)]
  have hsliceF_v : sliceF K α (sliceV u)
      = (∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
      + ∑ m ∈ Finset.Icc 1 K,
          ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
    have hw : sliceW K α (sliceV u) = fun θ => (sliceV u θ) ^ 2 * thEta θ
        + ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
      funext θ
      simp only [sliceW]
    have h1 : sliceF K α (sliceV u) = ∫ θ in Work.Spaces.Iθ, ((sliceV u θ) ^ 2 * thEta θ
        + ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ) := by
      rw [sliceF, hw]
    rw [h1, MeasureTheory.integral_add hintV hsumV_int,
      MeasureTheory.integral_finsetSum (Finset.Icc 1 K) (fun m hm => hintVm m hm)]
  -- the value of `∫ sliceD`
  have hDval : (∫ θ in Work.Spaces.Iθ, sliceD K α u θ)
      = (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
        + ∑ m ∈ Finset.Icc 1 K,
            ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
    have hAB : IntegrableOn (fun θ => (u θ) ^ 2 * thEta θ + (deriv u θ) ^ 2 * thEta θ)
        Work.Spaces.Iθ := hpoU.add hpoD
    have hABC : IntegrableOn (fun θ => (u θ) ^ 2 * thEta θ + (deriv u θ) ^ 2 * thEta θ
        + (sliceV u θ) ^ 2 * thEta θ) Work.Spaces.Iθ := hAB.add hintV
    have hcongr : sliceD K α u = fun θ => ((u θ) ^ 2 * thEta θ
        + (deriv u θ) ^ 2 * thEta θ + (sliceV u θ) ^ 2 * thEta θ)
        + ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
      funext θ
      simp only [sliceD]
    rw [hcongr, MeasureTheory.integral_add hABC hsumV_int,
      MeasureTheory.integral_add hAB hintV, MeasureTheory.integral_add hpoU hpoD,
      MeasureTheory.integral_finsetSum (Finset.Icc 1 K) (fun m hm => hintVm m hm)]
  -- the nonnegativity of the summed data of `sliceF K α (sliceV u)`
  have hsumV_nn : 0 ≤ ∑ m ∈ Finset.Icc 1 K,
      ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.sum_nonneg fun m _ => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ hθ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ))
  have hIV_le : (∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
      ≤ sliceF K α (sliceV u) := by
    rw [hsliceF_v]
    linarith
  -- `∫ sliceD ≤ (2 C0 + 1)·sliceF K α (sliceV u)`
  have hIntD_le : (∫ θ in Work.Spaces.Iθ, sliceD K α u θ)
      ≤ (2 * C0 + 1) * sliceF K α (sliceV u) := by
    rw [hDval, hsliceF_v]
    have hc : (1 : ℝ) ≤ 2 * C0 + 1 := by linarith
    have hA : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
        ≤ (2 * C0 + 1) * ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ := by
      nlinarith [hpoUle, hpoDle, hIVnn]
    have hB : (∑ m ∈ Finset.Icc 1 K,
          ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
        ≤ (2 * C0 + 1) * ∑ m ∈ Finset.Icc 1 K,
          ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
      nlinarith [hsumV_nn, hc]
    have hdist : (2 * C0 + 1) * ((∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
        + ∑ m ∈ Finset.Icc 1 K,
            ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
        = (2 * C0 + 1) * (∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
          + (2 * C0 + 1) * ∑ m ∈ Finset.Icc 1 K,
              ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
      ring
    linarith [hA, hB, hdist]
  -- the bound for each `∫ (L^i u)² thGam`
  have hLi_bound : ∀ i ∈ Finset.Icc 1 K,
      (∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
        ≤ Cd * (2 * C0 + 1) * sliceF K α (sliceV u) := by
    intro i hi
    calc (∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
        ≤ Cd * ∫ θ in Work.Spaces.Iθ, sliceD K α u θ := hLi_le i hi
      _ ≤ Cd * ((2 * C0 + 1) * sliceF K α (sliceV u)) :=
          mul_le_mul_of_nonneg_left hIntD_le (le_of_lt hCdpos)
      _ = Cd * (2 * C0 + 1) * sliceF K α (sliceV u) := by ring
  -- the sum of the bounds
  have hsum_bound : (∑ i ∈ Finset.Icc 1 K,
        ∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
      ≤ ((K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) := by
    calc (∑ i ∈ Finset.Icc 1 K,
          ∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
        ≤ ∑ _i ∈ Finset.Icc 1 K, (Cd * (2 * C0 + 1) * sliceF K α (sliceV u)) :=
          Finset.sum_le_sum (fun i hi => hLi_bound i hi)
      _ = (K : ℝ) * (Cd * (2 * C0 + 1) * sliceF K α (sliceV u)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          norm_num
      _ = ((K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) := by ring
  -- the first-order term of `u`
  have hIU_le : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
      ≤ C0 * sliceF K α (sliceV u) := by
    calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
        ≤ C0 * ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ := hpoUle
      _ ≤ C0 * sliceF K α (sliceV u) :=
          mul_le_mul_of_nonneg_left hIV_le (le_of_lt hC0pos)
  refine ⟨hpoU, hLi_int, ?_⟩
  rw [hsliceF_u]
  have hSV : 0 ≤ sliceF K α (sliceV u) := sliceF_nonneg _ _ _
  have hmain : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
      + ∑ i ∈ Finset.Icc 1 K, (∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
      ≤ (C0 + (K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) := by
    have hdist : (C0 + (K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u)
        = C0 * sliceF K α (sliceV u)
          + ((K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) := by ring
    linarith [hIU_le, hsum_bound, hdist]
  calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
      + ∑ i ∈ Finset.Icc 1 K, (∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
      ≤ (C0 + (K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) := hmain
    _ ≤ max 1 (C0 + (K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hSV

/-
# The one-dimensional `∂_θ²`-Poincaré estimate with boundary *traces*

`sliceF K α u = ∫_{Iθ} [(u)²sin(2θ)^{-η} + ∑_{1≤i≤K}(L^i u)²sin(2θ)^{-γ}]`, `L = D_θ = sin(2θ)∂_θ`
(defined in `Submission/Work/FTS/EllSol/VopAux/SliceTraceDefs.lean`; `Work.FTS.EllipticEst.sliceV u = u'' = deriv(deriv u)`).
For a slice `u` which is `C^∞` on the OPEN interval `(0,π/2)` (NOT on a neighbourhood of
`[0,π/2]`), tends to `0` as `θ→0⁺` and as `θ→π/2⁻`, and has `(u'')²sin(2θ)^{-η}` and all
`(L^m u'')²sin(2θ)^{-γ}` (`1 ≤ m ≤ K`) integrable on `Iθ`:

  `sliceF K α u ≤ C_K · sliceF K α u''`,   with `C_K` uniform in `α ∈ (0,1]` and in `u`,

and all the terms of the left-hand `sliceF` are themselves integrable on `Iθ`.

The pointwise input is `Submission/Work/FTS/EllSol/VopAux/SliceDPointwise.lean`, and the
integration step is `sliceF_le_sliceV_of_pointwise` above.
-/
theorem sliceF_le_sliceV (K : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ),
    0 < α → α ≤ 1 →
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ ∧
      (∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
        Work.Spaces.Iθ) ∧
      Work.FTS.EllSol.VopAux.sliceF K α u
        ≤ C * Work.FTS.EllSol.VopAux.sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
  exact sliceF_le_sliceV_of_pointwise K (SliceDPointwise K)

end Work.FTS.EllSol.VopAux
end
-- ===== merged: Submission.Work.FTS.H2.ModalSol.TailBound.psiTrunc_tail =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real BigOperators Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSol.TailBound

set_option autoImplicit false

theorem psiTrunc_tail (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < π / 2) :
    ∃ (C : ℝ) (b : ℕ → ℝ), 0 < C ∧ (∀ N : ℕ, 0 ≤ b N) ∧
      Filter.Tendsto b Filter.atTop (nhds 0) ∧
      ∀ (N M : ℕ) (z : ℝ), 0 < z → ∀ θ ∈ Set.Icc δ (π / 2 - δ),
        |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
          - Work.FTS.PhiStar.Series.psiTrunc α F M z θ| ≤ C * z ^ (-(1 / 2) : ℝ) * (b N + b M) := by
  sorry

end Work.FTS.H2.ModalSol.TailBound
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.SourceSide.residualEnergyTendstoZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR.SourceSide

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

local notation "Iθ" => Work.Spaces.Iθ

/-- The weighted angular energy of the slice `F z ·`. -/
local notation "angE(" F ", " z ")" => (∫ θ in Iθ, F z θ ^ 2 * Real.cos θ)

/-- The energy of the first `N + 1` angular modes of the slice `F z ·`. -/
local notation "modE(" F ", " N ", " z ")" =>
  (∑ m ∈ Finset.range (N + 1),
    (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
      * (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))

/-- The `m`-th modal energy `∫_{Iθ} eFam m θ ^ 2 cos θ` is nonnegative. -/
lemma eFam_sq_cos_nonneg (m : ℕ) :
    0 ≤ ∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  show ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
    0 ≤ Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ
  rw [MeasureTheory.ae_restrict_iff' Work.EllipticEst.ModalSolution.measurableSet_Iθ]
  filter_upwards with θ hθ
  exact mul_nonneg (sq_nonneg _)
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)

/-- The truncated modal energy of a slice is nonnegative. -/
lemma modalEnergy_nonneg (F : ℝ → ℝ → ℝ) (N : ℕ) (z : ℝ) : 0 ≤ modE(F, N, z) :=
  Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (eFam_sq_cos_nonneg m))

theorem residualEnergyTendstoZero {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Filter.Tendsto (fun N : ℕ => ∫ z in Set.Ioi 0,
        ((∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
          - ∑ m ∈ Finset.range (N + 1),
              (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
                * (∫ θ in Work.Spaces.Iθ,
                    Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)))
      Filter.atTop (nhds 0) := by
  classical
  -- The product of the two restricted Lebesgue measures is the plane measure restricted to `Q0`.
  have hprod : ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0 := by
    rw [← Work.FTS.EllipticEst.LevelOneAsm.volume_restrict_prod_Ioi_Iθ]
    exact Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0
  -- Integrability of the unweighted square on the product measure.
  have hF2int : Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict Iθ)) := by
    rw [hprod]
    exact hL2
  -- A.e. strong measurability of the weighted square on the product measure.
  have hΦaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict Iθ)) := by
    rw [hprod]
    have hF : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
        ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) :=
      hsm.continuousOn.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    have hcos : AEStronglyMeasurable (fun p : ℝ × ℝ => Real.cos p.2)
        ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) :=
      (Real.continuous_cos.comp continuous_snd).aestronglyMeasurable
    have hsq : (((fun p : ℝ × ℝ => F p.1 p.2) * (fun p : ℝ × ℝ => F p.1 p.2))
          * (fun p : ℝ × ℝ => Real.cos p.2))
        = fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2 := by
      funext p
      simp only [Pi.mul_apply]
      ring
    rw [← hsq]
    exact (hF.mul hF).mul hcos
  -- Integrability of the weighted square on the product measure, by domination.
  have hΦint : Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict Iθ)) := by
    refine Integrable.mono' hF2int hΦaesm ?_
    rw [hprod]
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
      (s := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
      with p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hc0 : 0 ≤ Real.cos p.2 :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0], hθ1⟩)
    have hc1 : Real.cos p.2 ≤ 1 := Real.cos_le_one p.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (F p.1 p.2))]
    exact mul_le_of_le_one_right (sq_nonneg _) (by rwa [abs_of_nonneg hc0])
  -- The angular energy is integrable in `z` (Fubini).
  have hEnInt : Integrable (fun z => angE(F, z))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    hΦint.integral_prod_left
  have hEnAesm : AEStronglyMeasurable (fun z => angE(F, z))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    hΦaesm.integral_prod_right'
  -- A.e. strong measurability of the angular slices.
  have hSliceSM : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      AEStronglyMeasurable (fun θ => F z θ) ((volume : Measure ℝ).restrict Iθ) := by
    have hΦ : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
        (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((volume : Measure ℝ).restrict Iθ)) := by
      rw [hprod]
      exact hsm.continuousOn.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    exact hΦ.prodMk_left
  -- A.e. integrability of the weighted angular slices.
  have hSliceSq : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Iθ :=
    hΦint.prod_right_ae
  have hae : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      AEStronglyMeasurable (fun θ => F z θ) ((volume : Measure ℝ).restrict Iθ)
        ∧ IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Iθ := hSliceSM.and hSliceSq
  -- Pointwise Parseval for a.e. slice.
  have hparseval : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      Tendsto (fun N : ℕ => modE(F, N, z)) atTop (nhds (angE(F, z))) := by
    filter_upwards [hae] with z hz
    exact Work.EllipticEst.ModalSolution.eFam_parseval F z hz.1 hz.2
  -- The residual energy is nonnegative, through the pointwise Pythagoras identity.
  have hnonneg : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)), ∀ N : ℕ,
      0 ≤ angE(F, z) - modE(F, N, z) := by
    filter_upwards [hae] with z hz
    intro N
    have hpyth := Work.EllipticEst.ModalSolution.eFam_pythagoras_alt F z N hz.1 hz.2
    rw [← hpyth]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    show ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      0 ≤ (F z θ - ∑ m ∈ Finset.range (N + 1),
        Work.FTS.PhiStar.Series.cmode m F z
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ
    rw [MeasureTheory.ae_restrict_iff' Work.EllipticEst.ModalSolution.measurableSet_Iθ]
    filter_upwards with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- The truncated modal energies are nonnegative.
  have hmod_nonneg : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)), ∀ N : ℕ,
      0 ≤ modE(F, N, z) :=
    Filter.Eventually.of_forall (fun z N => modalEnergy_nonneg F N z)
  -- Domination of the residual by the angular energy.
  have hbound : ∀ N : ℕ, ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      ‖angE(F, z) - modE(F, N, z)‖ ≤ angE(F, z) := by
    intro N
    filter_upwards [hnonneg, hmod_nonneg] with z hn hm
    rw [Real.norm_eq_abs, abs_of_nonneg (hn N)]
    linarith [hm N]
  -- A.e. convergence of the residual energy to zero.
  have hlim : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      Tendsto (fun N : ℕ => angE(F, z) - modE(F, N, z)) atTop (nhds 0) := by
    filter_upwards [hparseval] with z hz
    have h := hz.const_sub (angE(F, z))
    simpa using h
  -- A.e. strong measurability of the modal coefficients.
  have haesm_cmode : ∀ m : ℕ,
      AEStronglyMeasurable (fun z => Work.FTS.PhiStar.Series.cmode m F z)
        ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    fun m => Work.EllipticEst.ModalSolution.aesm_cmode hsm m
  have hTNaesm : ∀ N : ℕ, AEStronglyMeasurable (fun z => modE(F, N, z))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    intro N
    have h := Finset.aestronglyMeasurable_fun_sum (Finset.range (N + 1))
      (f := fun m z => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        * (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
      (fun m _ => by
        have hm := ((haesm_cmode m).pow 2).mul_const
          (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
        simpa only [Pi.pow_apply] using hm)
    simpa using h
  -- The dominated convergence theorem.
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℝ).restrict (Set.Ioi 0))
    (bound := fun z => angE(F, z))
    (F := fun N z => angE(F, z) - modE(F, N, z))
    (f := fun _ => (0 : ℝ))
    (F_measurable := fun N => hEnAesm.sub (hTNaesm N))
    (bound_integrable := hEnInt) (h_bound := hbound) (h_lim := hlim)
  simpa using hmain

end Work.FTS.H2.ModalSolR.SourceSide
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ZSliceDomination =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Domination of a `z`-slice family by an integrable function of `θ`

Given `W` smooth on the open quadrant and `W ∈ ℋ¹`, and a compact interval `[a,b] ⊂ (0,∞)`
of radii, there is a *single* function `G` of the angle, integrable on `(0,π/2)`, which
dominates all the slices `θ ↦ W z θ`, `z ∈ [a,b]`.

The proof is the one-dimensional Agmon/Morrey argument in the radial variable, at fixed
angle: for `z ∈ [a,b]` and `θ ∈ (0,π/2)` the fundamental theorem of calculus gives

  `|W z θ| ≤ √(∫_J W(·,θ)²) / √L + √L · √(∫_J ∂_zW(·,θ)²)`,   `J = [a,b+1]`, `L = |J|`,

and the two `L²`-norms over `J` are bounded by the angular marginal `∫_J HkIntegrand`
(using `w z ≥ 1`, `sin(2θ)^{η/2} ≤ 1` and `z ≥ a`).  Since

  `√(A·Φ) ≤ (A + Φ)/2`   (`A ≥ 0`, `Φ ≥ 0`),

the dominating function may be taken to be a *sum*, `C · (1 + Φ(θ))`, whose integral over
`(0,π/2)` is finite because `Φ` is integrable there (Tonelli applied to the two conjuncts of
`HkMem α 1 W`).
-/

/-- An interval integral is the integral over the corresponding closed set. -/
private theorem intervalIntegral_eq_setIntegral_Icc {c d : ℝ} (h : c ≤ d) (f : ℝ → ℝ) :
    (∫ x in c..d, f x) = ∫ x in Set.Icc c d, f x := by
  rw [intervalIntegral.integral_of_le h, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The `ℋ^k`-integrand is nonnegative. -/
private theorem HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  exact add_nonneg (Work.Spaces.hkZSum_nonneg α k f z θ)
    (Work.Spaces.hkMixedSum_nonneg α k f z θ)

/-- The constant of the domination estimate. -/
private noncomputable def zSliceConst (a b : ℝ) : ℝ :=
  (1 / Real.sqrt (b + 1 - a) + Real.sqrt (b + 1 - a)) * Real.sqrt (1 / min 1 (a ^ 2))

private theorem zSliceConst_nonneg {a b : ℝ} (_ha : 0 < a) (hab : a ≤ b) :
    0 ≤ zSliceConst a b := by
  have hL : 0 < b + 1 - a := by linarith
  have hLnn : 0 ≤ Real.sqrt (b + 1 - a) := Real.sqrt_nonneg _
  rw [zSliceConst]
  exact mul_nonneg (add_nonneg (div_nonneg zero_le_one hLnn) hLnn)
    (Real.sqrt_nonneg _)

theorem ZSliceDomination {α : ℝ} {W : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ G : ℝ → ℝ, MeasureTheory.IntegrableOn G (Set.Ioo 0 (Real.pi / 2)) ∧
      ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |W z θ| ≤ G θ := by
  have hLpos : 0 < b + 1 - a := by linarith
  have hmpos : 0 < min 1 (a ^ 2) := lt_min one_pos (pow_pos ha 2)
  have hminv : 0 ≤ 1 / min 1 (a ^ 2) := le_of_lt (one_div_pos.mpr hmpos)
  have hφint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ∫ z in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_theta_marginal_HkIntegrand hsm hmem ha (by linarith)
  refine ⟨fun θ => (zSliceConst a b + 1) *
      (1 + ∫ z in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W z θ), ?_, ?_⟩
  · -- integrability of the majorant
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 (Real.pi / 2)) :=
      integrableOn_const (C := 1) measure_Ioo_lt_top.ne
    have h2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (1 : ℝ) + ∫ z in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W z θ)
        (Set.Ioo 0 (Real.pi / 2)) := h1.add hφint
    exact h2.integrable.const_mul (zSliceConst a b + 1)
  · intro z hz θ hθ
    have hzJ : z ∈ Set.Icc a (b + 1) := ⟨hz.1, by linarith [hz.2]⟩
    have hder : ∀ x ∈ Set.Icc a (b + 1),
        HasDerivAt (fun x' : ℝ => W x' θ) (Work.Spaces.pz W x θ) x :=
      fun x hx => hsm.hasDerivAt_slice hθ (by linarith [hx.1])
    have hg'cont : ContinuousOn (fun x : ℝ => Work.Spaces.pz W x θ) (Set.Icc a (b + 1)) :=
      ((hsm.pz).curry_z hθ).continuousOn.mono (fun x hx => lt_of_lt_of_le ha hx.1)
    have hAb := abs_le_sqrt_interval_integral (c := a) (d := b + 1)
      (by linarith : a < b + 1) hder hg'cont z hzJ
    rw [intervalIntegral_eq_setIntegral_Icc (c := a) (d := b + 1) (by linarith : a ≤ b + 1)
        (fun x => (W x θ) ^ 2),
      intervalIntegral_eq_setIntegral_Icc (c := a) (d := b + 1) (by linarith : a ≤ b + 1)
        (fun x => (Work.Spaces.pz W x θ) ^ 2)] at hAb
    let A : ℝ := ∫ x in Set.Icc a (b + 1), (W x θ) ^ 2
    let B : ℝ := ∫ x in Set.Icc a (b + 1), (Work.Spaces.pz W x θ) ^ 2
    let Φ : ℝ := ∫ x in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W x θ
    have hA0 : 0 ≤ A := by
      show 0 ≤ ∫ x in Set.Icc a (b + 1), (W x θ) ^ 2
      exact setIntegral_nonneg measurableSet_Icc (fun x _ => sq_nonneg _)
    have hB0 : 0 ≤ B := by
      show 0 ≤ ∫ x in Set.Icc a (b + 1), (Work.Spaces.pz W x θ) ^ 2
      exact setIntegral_nonneg measurableSet_Icc (fun x _ => sq_nonneg _)
    have hΦ0 : 0 ≤ Φ := by
      show 0 ≤ ∫ x in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W x θ
      exact setIntegral_nonneg measurableSet_Icc (fun x _ => HkIntegrand_nonneg α 1 W x θ)
    have hAB : A + B ≤ (1 / min 1 (a ^ 2)) * Φ := by
      show (∫ x in Set.Icc a (b + 1), (W x θ) ^ 2)
          + (∫ x in Set.Icc a (b + 1), (Work.Spaces.pz W x θ) ^ 2)
          ≤ (1 / min 1 (a ^ 2)) * ∫ x in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W x θ
      exact zSlice_sq_le_marginal hsm hmem ha (by linarith) hθ
    have hAle : A ≤ (1 / min 1 (a ^ 2)) * Φ := le_trans (le_add_of_nonneg_right hB0) hAB
    have hBle : B ≤ (1 / min 1 (a ^ 2)) * Φ := le_trans (le_add_of_nonneg_left hA0) hAB
    have hsqrtA : Real.sqrt A ≤ Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := by
      calc Real.sqrt A ≤ Real.sqrt ((1 / min 1 (a ^ 2)) * Φ) := Real.sqrt_le_sqrt hAle
        _ = Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := Real.sqrt_mul hminv Φ
    have hsqrtB : Real.sqrt B ≤ Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := by
      calc Real.sqrt B ≤ Real.sqrt ((1 / min 1 (a ^ 2)) * Φ) := Real.sqrt_le_sqrt hBle
        _ = Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := Real.sqrt_mul hminv Φ
    have hbnd : |W z θ| ≤ zSliceConst a b * Real.sqrt Φ := by
      have hLnn : 0 ≤ Real.sqrt (b + 1 - a) := Real.sqrt_nonneg _
      have hstep : Real.sqrt A / Real.sqrt (b + 1 - a) + Real.sqrt (b + 1 - a) * Real.sqrt B
          ≤ (1 / Real.sqrt (b + 1 - a) + Real.sqrt (b + 1 - a))
              * Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := by
        have e1 : Real.sqrt A / Real.sqrt (b + 1 - a)
            ≤ (Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ) / Real.sqrt (b + 1 - a) :=
          div_le_div_of_nonneg_right hsqrtA hLnn
        have e2 : Real.sqrt (b + 1 - a) * Real.sqrt B
            ≤ Real.sqrt (b + 1 - a) * (Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ) :=
          mul_le_mul_of_nonneg_left hsqrtB hLnn
        have hid : (Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ) / Real.sqrt (b + 1 - a)
            + Real.sqrt (b + 1 - a) * (Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ)
            = (1 / Real.sqrt (b + 1 - a) + Real.sqrt (b + 1 - a))
              * Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := by
          ring
        linarith [e1, e2, hid]
      rw [zSliceConst]
      exact le_trans hAb hstep
    have hsqrtle : Real.sqrt Φ ≤ 1 + Φ := by
      nlinarith [Real.sq_sqrt hΦ0, Real.sqrt_nonneg Φ, sq_nonneg (Real.sqrt Φ - 1 / 2)]
    have hCnn : 0 ≤ zSliceConst a b := zSliceConst_nonneg ha hab
    have hs1 : zSliceConst a b * Real.sqrt Φ ≤ zSliceConst a b * (1 + Φ) :=
      mul_le_mul_of_nonneg_left hsqrtle hCnn
    have hs2 : zSliceConst a b * (1 + Φ) ≤ (zSliceConst a b + 1) * (1 + Φ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hgoal : |W z θ| ≤ (zSliceConst a b + 1) * (1 + Φ) := by
      linarith [hbnd, hs1, hs2]
    show |W z θ| ≤ (zSliceConst a b + 1)
      * (1 + ∫ x in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W x θ)
    exact hgoal

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsWp.gRHS_abs_le_explicit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsWp

/-- Triangle inequality for four terms, with the first one negated (the shape in which the
sum `gRHS = -μ̄·AK + N₀ + N + N_*` appears). -/
private lemma abs_neg_add3_le (a b c d : ℝ) : |-a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |-a + b + c + d| ≤ |-a + b + c| + |d| := abs_add_le (-a + b + c) d
  have h2 : |-a + b + c| ≤ |-a + b| + |c| := abs_add_le (-a + b) c
  have h3 : |-a + b| ≤ |a| + |b| := by simpa [abs_neg] using abs_add_le (-a) b
  linarith [h1, h2, h3, abs_nonneg c, abs_nonneg d]

/-- Eleven nonnegative summands with total at most `B` are each at most `B`.  This is the
only place where the hypothesis `hbnd` (a bound on the *sum* of the eleven quantities) is
used: it delivers the eleven individual bounds. -/
private lemma le_of_eleven_sum_le {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 B : ℝ}
    (h : a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 ≤ B)
    (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3) (h4 : 0 ≤ a4) (h5 : 0 ≤ a5)
    (h6 : 0 ≤ a6) (h7 : 0 ≤ a7) (h8 : 0 ≤ a8) (h9 : 0 ≤ a9) (h10 : 0 ≤ a10)
    (h11 : 0 ≤ a11) :
    a1 ≤ B ∧ a2 ≤ B ∧ a3 ≤ B ∧ a4 ≤ B ∧ a5 ≤ B ∧ a6 ≤ B ∧ a7 ≤ B ∧ a8 ≤ B
      ∧ a9 ≤ B ∧ a10 ≤ B ∧ a11 ≤ B := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem gRHS_abs_le_explicit {α B μ lam : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 ≤ B)
    (hμ : |μ| ≤ 1 / 2) (hlam : |lam| ≤ 1) {F Φ g : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hbnd : |F z θ| + |Work.Spaces.pth F z θ| + |Work.Spaces.Dz F z θ| + |g z θ|
        + |Work.Spaces.Dz g z θ| + |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        + |Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ|
        + |Work.Construction.AK α z θ| ≤ B)
    (hL12Fstar : |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ B)
    (hL12g : |Work.Construction.L12 g z| ≤ B)
    (hmubar : |Work.Construction.mubar (Work.Construction.N0 α F g)
        (Work.Construction.N α F Φ)| ≤ B)
    (hFK : |Work.Construction.FK F z| ≤ B) :
    |Work.Construction.gRHS α μ lam F Φ g z θ| ≤
      B * B + (4 / α + 6) * B ^ 2 + 8 * B ^ 2 + 3 * B := by
  -- unpack `hbnd`: it bounds the *sum* of the eleven quantities, hence each of them
  obtain ⟨hF, hpF, hDzF, hg, hDzg, hpFs, hDzFs, hRop, hUop, hVop, hAK⟩ :=
    le_of_eleven_sum_le hbnd (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      (abs_nonneg _) (abs_nonneg _)
  -- the three summand bounds, from the dedicated helper modules
  have hN0 := Work.FTS.StrongEps.gRHSBound.abs_N0_le hα hB hL12Fstar hL12g hF hpF hDzF hg
    hDzg hpFs hDzFs
  have hN := Work.FTS.StrongEps.gRHSBound.abs_N_le hα hα1 hB hF hpF hDzF hRop hUop hVop hFK
  have hNs := Work.FTS.StrongEps.gRHSBound.abs_Nstar_le hB hμ hlam hg hDzg
  -- the `μ̄·AK` term
  have hmAK : |Work.Construction.mubar (Work.Construction.N0 α F g) (Work.Construction.N α F Φ)
      * Work.Construction.AK α z θ| ≤ B * B := by
    rw [abs_mul]
    exact mul_le_mul hmubar hAK (abs_nonneg _) hB
  -- assemble: `gRHS = -μ̄·AK + N₀ + N + N_*`
  have hsplit : |Work.Construction.gRHS α μ lam F Φ g z θ| ≤
      |Work.Construction.mubar (Work.Construction.N0 α F g) (Work.Construction.N α F Φ)
        * Work.Construction.AK α z θ|
      + |Work.Construction.N0 α F g z θ| + |Work.Construction.N α F Φ z θ|
      + |Work.Construction.Nstar μ lam g z θ| := by
    rw [Work.Construction.gRHS, neg_mul]
    exact abs_neg_add3_le _ _ _ _
  linarith [hsplit, hmAK, hN0, hN, hNs]

end Work.FTS.StrongEps.EpsWp
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.contDiffOn_two_of_fderivWithin_data =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

set_option autoImplicit false

theorem contDiffOn_two_of_fderivWithin_data {G A B A₁ A₂ B₁ B₂ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hcontA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontB : ContinuousOn (fun p : ℝ × ℝ => B p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontA₁ : ContinuousOn (fun p : ℝ × ℝ => A₁ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontA₂ : ContinuousOn (fun p : ℝ × ℝ => A₂ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontB₁ : ContinuousOn (fun p : ℝ × ℝ => B₁ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontB₂ : ContinuousOn (fun p : ℝ × ℝ => B₂ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hS0 : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, HasFDerivWithinAt (Function.uncurry G)
      (Work.FTS_EllLimOK.ellCop (A p.1 p.2) (B p.1 p.2)) (Work.FTS_EllLimOK.cbox a b) p)
    (hS1 : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, HasFDerivWithinAt (Function.uncurry A)
      (Work.FTS_EllLimOK.ellCop (A₁ p.1 p.2) (A₂ p.1 p.2)) (Work.FTS_EllLimOK.cbox a b) p)
    (hS2 : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, HasFDerivWithinAt (Function.uncurry B)
      (Work.FTS_EllLimOK.ellCop (B₁ p.1 p.2) (B₂ p.1 p.2)) (Work.FTS_EllLimOK.cbox a b) p) :
    ContDiffOn ℝ 2 (Function.uncurry G) (Work.FTS_EllLimOK.cbox a b) := by
  -- `A` is `C¹` within the box (with derivative `ellCop A₁ A₂`)
  have hA_c1 : ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => A y.1 y.2) (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    have haux : ContDiffWithinAt ℝ ((0 : ℕ∞ω) + 1) (fun y : ℝ × ℝ => A y.1 y.2)
        (Work.FTS_EllLimOK.cbox a b) q := by
      refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 0) (by simp)).mpr ?_
      refine ⟨insert q (Work.FTS_EllLimOK.cbox a b), self_mem_nhdsWithin, subset_rfl,
        fun h => absurd h (by simp),
        (fun y : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (A₁ y.1 y.2) (A₂ y.1 y.2)), ?_, ?_⟩
      · intro y hy
        have hy' : y ∈ Work.FTS_EllLimOK.cbox a b := by
          rcases Set.mem_insert_iff.mp hy with h | h
          · rw [h]; exact hq
          · exact h
        exact hS1 y hy'
      · refine (contDiffWithinAt_zero hq).2 ⟨Work.FTS_EllLimOK.cbox a b, self_mem_nhdsWithin, ?_⟩
        intro y hy
        exact Work.FTS_EllLimOK.continuousWithinAt_ellCop
          ((hcontA₁.continuousWithinAt hy.1).mono Set.inter_subset_left)
          ((hcontA₂.continuousWithinAt hy.1).mono Set.inter_subset_left)
    simpa using haux
  -- `B` is `C¹` within the box (with derivative `ellCop B₁ B₂`)
  have hB_c1 : ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => B y.1 y.2) (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    have haux : ContDiffWithinAt ℝ ((0 : ℕ∞ω) + 1) (fun y : ℝ × ℝ => B y.1 y.2)
        (Work.FTS_EllLimOK.cbox a b) q := by
      refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 0) (by simp)).mpr ?_
      refine ⟨insert q (Work.FTS_EllLimOK.cbox a b), self_mem_nhdsWithin, subset_rfl,
        fun h => absurd h (by simp),
        (fun y : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (B₁ y.1 y.2) (B₂ y.1 y.2)), ?_, ?_⟩
      · intro y hy
        have hy' : y ∈ Work.FTS_EllLimOK.cbox a b := by
          rcases Set.mem_insert_iff.mp hy with h | h
          · rw [h]; exact hq
          · exact h
        exact hS2 y hy'
      · refine (contDiffWithinAt_zero hq).2 ⟨Work.FTS_EllLimOK.cbox a b, self_mem_nhdsWithin, ?_⟩
        intro y hy
        exact Work.FTS_EllLimOK.continuousWithinAt_ellCop
          ((hcontB₁.continuousWithinAt hy.1).mono Set.inter_subset_left)
          ((hcontB₂.continuousWithinAt hy.1).mono Set.inter_subset_left)
    simpa using haux
  -- the derivative family `y ↦ ellCop (A y) (B y)` is `C¹` within the box
  have hf'_c1 : ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ContDiffWithinAt ℝ 1
        (fun u : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (A u.1 u.2) (B u.1 u.2))
        (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    have hpair : ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => (A y.1 y.2, B y.1 y.2))
        (Work.FTS_EllLimOK.cbox a b) q := (hA_c1 q hq).prodMk (hB_c1 q hq)
    have hg : ContDiffWithinAt ℝ 1 (fun w : ℝ × ℝ => Work.FTS_EllLimOK.copBilin w)
        (Set.univ : Set (ℝ × ℝ)) (A q.1 q.2, B q.1 q.2) :=
      (ContinuousLinearMap.contDiff Work.FTS_EllLimOK.copBilin).contDiffWithinAt
    have h2 : ContDiffWithinAt ℝ 1
        (fun y : ℝ × ℝ => Work.FTS_EllLimOK.copBilin (A y.1 y.2, B y.1 y.2))
        (Work.FTS_EllLimOK.cbox a b) q :=
      hg.comp q hpair (fun y _ => Set.mem_univ _)
    refine h2.congr (fun y _ => (Work.FTS_EllLimOK.copBilin_apply (A y.1 y.2) (B y.1 y.2)).symm)
      (Work.FTS_EllLimOK.copBilin_apply (A q.1 q.2) (B q.1 q.2)).symm
  -- the second-order conclusion, in the `n + 1` form
  have hmain : ∀ q ∈ Work.FTS_EllLimOK.cbox a b, ContDiffWithinAt ℝ ((1 : ℕ∞ω) + 1)
      (Function.uncurry G) (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 1) (by simp)).mpr ?_
    refine ⟨insert q (Work.FTS_EllLimOK.cbox a b), self_mem_nhdsWithin, subset_rfl,
      fun h => absurd h (by simp),
      (fun u : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (A u.1 u.2) (B u.1 u.2)), ?_, hf'_c1 q hq⟩
    intro y hy
    have hy' : y ∈ Work.FTS_EllLimOK.cbox a b := by
      rcases Set.mem_insert_iff.mp hy with h | h
      · rw [h]; exact hq
      · exact h
    exact hS0 y hy'
  intro p hp
  simpa [show ((1 : ℕ∞ω) + 1 : ℕ∞ω) = 2 from by norm_num] using hmain p hp

end Work.FTS_EllLimOK.BoxDataH
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.pinBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false
set_option maxHeartbeats 1600000
/-! ## The two slices, and the running primitive -/




/-! ## Continuity of the pieces on subintervals of the open quadrant -/



/-- The `θ`-slice of an open-quadrant-smooth `Ψ` is differentiable, with derivative `pth Ψ`. -/
theorem hasDerivAt_slice {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun s => Ψ z s) (Work.Spaces.pth Ψ z θ) θ := by
  have hs : ContDiffOn ℝ 1 (fun s => Ψ z s) (Set.Ioo 0 (π / 2)) :=
    (hsm.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have h2 : DifferentiableAt ℝ (fun s => Ψ z s) θ :=
    (hs.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  simpa only [Work.Spaces.pth] using h2.hasDerivAt








end Work.FTS_EllLimOK.PkgJets
end
end
