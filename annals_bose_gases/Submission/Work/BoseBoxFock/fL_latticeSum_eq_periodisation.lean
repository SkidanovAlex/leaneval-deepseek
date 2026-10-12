import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.farImageSum_eq_integral_farEven
import Submission.Work.BoseBoxFock.lowCut_invFT_scaled
import Submission.Work.BoseBoxFock.poissonEuclid3Summable
import Submission.Work.BoseBoxFock.sample_scaled_lowCut
import Submission.Work.BoseBoxFock.summable_shift_latVec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.fL_latticeSum_eq_periodisation`

The **periodisation (Poisson summation) identity for the low-momentum symbol** `fc.f(‖·‖/κ)`:
for `κ, ℓ > 0` and every shift `w ∈ ℝ³`,

    Σ'_m f(‖k_m‖/κ)·cos⟪k_m, w⟫ = ℓ³ Σ'_d (2π)⁻³ ∫_p cos⟪p, w + ℓ·v_d⟫·f(‖p‖/κ) dp ,

where `k_m = (2π/ℓ)·latVec m` is the sampling (dual) lattice of `(2π/ℓ)ℤ³`, `v_d = latVec d`,
and the right-hand side is `ℓ³` times the `ℓ`-periodisation of the kernel
`K(y) = (2π)⁻³∫_p f(‖p‖/κ)cos⟪p,y⟫dp` of the low-cut multiplier, evaluated at the shifted points
`w + ℓ·v_d`.

## Proof architecture

Let `c = 2π/ℓ`, `f₀ = symb fc κ` (the momentum symbol `p ↦ f(‖p‖/κ)`, a `C_c^∞` function) and

* `invT F q = ∫_p F p·e^{i⟪p,q⟫}dp` (the `p`-convention inverse transform; `invT F q` is
  `kinFT F (-q)` up to the order of the inner product);
* `h x = f₀(c·x)·e^{i⟪c·x,w⟫}` (the position-space test function, whose samples at the lattice
  `ℤ³` are the left-hand side up to the phase `e^{i⟪k_m,w⟫}`).

1. **Poisson summation** (`Work.BoseBoxFock.poissonEuclid3Summable`, the corpus's Poisson formula on
   `ℤ³` with the summability of the Fourier samples as the only convergence hypothesis) applied to
   `h` gives `Σ'_m h(v_m) = Σ'_m ∫_x h x·e^{-2πi⟪x,v_m⟫}dx`.
2. The **sample computation** (`Work.BoseBoxFock.sample_scaled_lowCut`, the linear change of
   variables `p = c·x`) identifies each sample with `c⁻³·invT f₀ (w - ℓ·v_m)`.
3. Reindexing by `d ↦ -d` (using `latVec (-d) = -latVec d`) turns this into
   `Σ'_m h(v_m) = c⁻³ Σ'_d invT f₀ (w + ℓ·v_d)`.
4. Both series are summable: the lattice samples of `h` are dominated by `(1+‖v_m‖)^{-4}`
   (`summable_one_add_norm_latVec_pow_inv`), while `‖invT f₀ q‖ ≤ C(1+‖q‖)^{-4}` is the Schwartz
   decay of the inverse transform of a `C_c^∞` symbol (`Work.OneBodyKin.kinFT_decay_le`), and the
   shift by `w` at scale `ℓ` is absorbed by `Work.BoseBoxFock.summable_shift_latVec`.
5. **Real parts**: `(h(v_m)).re = f(‖k_m‖/κ)cos⟪k_m,w⟫` and
   `(invT f₀ q).re = ∫_p cos⟪p,q⟫ f(‖p‖/κ)dp` (`fl_re_invT_lowCut`); taking real parts of the
   complex identity and using `c⁻³ = ℓ³(2π)⁻³` gives the statement.
-/

open MeasureTheory
namespace Work.BoseBoxFock

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Pointwise bounds on the low cut `f` -/

lemma lowCut_f_nonneg (fc : Work.BoseBoxFix.LowCut) (s : ℝ) : 0 ≤ fc.f s := by
  rcases le_or_gt s 2 with h | h
  · have h1 : fc.f 2 ≤ fc.f s := fc.anti h
    rw [fc.zero 2 le_rfl] at h1
    linarith
  · rw [fc.zero s (le_of_lt h)]

lemma lowCut_f_le_one (fc : Work.BoseBoxFix.LowCut) (s : ℝ) : fc.f s ≤ 1 := by
  rcases le_or_gt s 1 with h | h
  · rw [fc.one s h]
  · have h1 : fc.f s ≤ fc.f 1 := fc.anti (le_of_lt h)
    rwa [fc.one 1 le_rfl] at h1

/-! ## 1. The scaled low-cut symbol `p ↦ f(‖p‖/κ)` -/

/-- The **scaled low-cut symbol** `p ↦ f(‖p‖/κ)`, as a complex-valued function. -/
noncomputable def symb (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) : E3 → ℂ :=
  fun p => ((fc.f (‖p‖ / κ) : ℝ) : ℂ)

lemma symb_apply (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (p : E3) :
    symb fc κ p = ((fc.f (‖p‖ / κ) : ℝ) : ℂ) := rfl

lemma symb_eq_lowCutProf (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    symb fc κ = fun p => lowCutProf fc ((κ⁻¹ : ℝ) • p) := by
  funext p
  rw [symb_apply, lowCutProf, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hκ.le), inv_mul_eq_div]

lemma contDiff_symb (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ (⊤ : ℕ∞) (symb fc κ) := by
  rw [symb_eq_lowCutProf fc hκ]
  exact (contDiff_lowCutProf fc).comp (contDiff_const_smul (𝕜 := ℝ) (κ⁻¹ : ℝ))

lemma hasCompactSupport_symb (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (symb fc κ) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (2 * κ))
    (isCompact_closedBall 0 (2 * κ)) ?_
  intro p hp
  rw [Function.mem_support] at hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  rw [not_le] at hlt
  apply hp
  rw [symb_apply]
  have h2 : (2 : ℝ) ≤ ‖p‖ / κ := by rw [le_div_iff₀ hκ]; linarith
  rw [fc.zero _ h2, Complex.ofReal_zero]

lemma norm_symb_le_one (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (p : E3) :
    ‖symb fc κ p‖ ≤ 1 := by
  rw [symb_apply]
  have h : Complex.normSq (((fc.f (‖p‖ / κ) : ℝ)) : ℂ) = fc.f (‖p‖ / κ) * fc.f (‖p‖ / κ) :=
    Complex.normSq_ofReal _
  have h2 : ‖(((fc.f (‖p‖ / κ) : ℝ)) : ℂ)‖ ^ 2 = fc.f (‖p‖ / κ) * fc.f (‖p‖ / κ) := by
    rw [← Complex.normSq_eq_norm_sq, h]
  have h0 : 0 ≤ fc.f (‖p‖ / κ) := lowCut_f_nonneg fc _
  have h1 : fc.f (‖p‖ / κ) ≤ 1 := lowCut_f_le_one fc _
  nlinarith [norm_nonneg (((fc.f (‖p‖ / κ) : ℝ)) : ℂ)]

/-- `(e^{I θ}).re = cos θ`. -/
lemma fl_exp_I_re (θ : ℝ) : (Complex.exp (Complex.I * (θ : ℂ))).re = Real.cos θ := by
  rw [mul_comm Complex.I (θ : ℂ), Complex.exp_ofReal_mul_I_re]

/-- `‖e^{I θ}‖ = 1`. -/
lemma fl_norm_exp_I (θ : ℝ) : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal θ

/-- The real part of a summable series is the series of the real parts. -/
lemma fl_re_tsum {ι : Type*} {f : ι → ℂ} (hf : Summable f) :
    (∑' i, f i).re = ∑' i, (f i).re := by
  have h := ContinuousLinearMap.map_tsum Complex.reCLM hf
  simpa only [Complex.reCLM_apply] using h

/-! ## 2. The `p`-convention inverse transform `invT` -/

/-- The **inverse transform** `q ↦ ∫_p F p·e^{i⟪p,q⟫}dp` in the `p`-convention. -/
noncomputable def invT (F : E3 → ℂ) (q : E3) : ℂ :=
  ∫ p : E3, F p * Complex.exp (Complex.I * (inner ℝ p q : ℂ))

lemma invT_apply (F : E3 → ℂ) (q : E3) :
    invT F q = ∫ p : E3, F p * Complex.exp (Complex.I * (inner ℝ p q : ℂ)) := rfl

lemma invT_eq_kinFT_neg (F : E3 → ℂ) (q : E3) :
    invT F q = Submission.BoseGases.kinFT F (-q) := by
  rw [invT_apply, Submission.BoseGases.kinFT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have harg : (-(Complex.I * (inner ℝ (-q) p : ℂ))) = Complex.I * (inner ℝ p q : ℂ) := by
    rw [inner_neg_left]
    push_cast
    rw [real_inner_comm q p]
    ring
  show F p * Complex.exp (Complex.I * (inner ℝ p q : ℂ)) =
      Complex.exp (-(Complex.I * (inner ℝ (-q) p : ℂ))) * F p
  rw [harg, mul_comm]

/-- **Schwartz decay of the inverse transform of a smooth compactly supported symbol.** -/
lemma norm_invT_le (F : E3 → ℂ) (hFd : ContDiff ℝ (⊤ : ℕ∞) F) (hFs : HasCompactSupport F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : E3, ‖invT F q‖ ≤ C * (1 + ‖q‖) ^ (-(4 : ℤ)) := by
  obtain ⟨C, hC0, hC⟩ := Work.OneBodyKin.kinFT_decay_le 4 hFd hFs
  refine ⟨C, hC0, fun q => ?_⟩
  rw [invT_eq_kinFT_neg]
  have h := hC (-q)
  rw [norm_neg] at h
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, zpow_neg]
  rfl

/-- **The real part of the inverse transform of the scaled low-cut symbol.** -/
theorem fl_re_invT_lowCut (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (q : E3) :
    (∫ p : E3, ((fc.f (‖p‖ / κ) : ℝ) : ℂ) * Complex.exp (Complex.I * (inner ℝ p q : ℂ))).re
      = ∫ p : E3, Real.cos (inner ℝ p q) * fc.f (‖p‖ / κ) := by
  have hF0d : ContDiff ℝ (⊤ : ℕ∞) (symb fc κ) := contDiff_symb fc hκ
  have hF0s : HasCompactSupport (symb fc κ) := hasCompactSupport_symb fc hκ
  set F : E3 → ℂ := fun p => symb fc κ p * Complex.exp (Complex.I * (inner ℝ p q : ℂ))
    with hFdef
  have hcsF : HasCompactSupport
      (fun p : E3 => symb fc κ p * Complex.exp (Complex.I * (inner ℝ p q : ℂ))) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := tsupport (symb fc κ))
      hF0s.isCompact ?_
    intro p hp
    rw [Function.mem_support] at hp
    exact subset_tsupport (symb fc κ)
      (Function.mem_support.mpr fun h0 => hp (by rw [h0, zero_mul]))
  have hint : Integrable F := by
    rw [hFdef]
    exact (hF0d.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hcsF
  have h1 : (∫ p : E3, F p).re = ∫ p : E3, (F p).re :=
    (ContinuousLinearMap.integral_comp_comm Complex.reCLM hint).symm
  have h2 : ∀ p : E3, (F p).re = Real.cos (inner ℝ p q) * fc.f (‖p‖ / κ) := by
    intro p
    rw [hFdef]
    simp only [symb_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, fl_exp_I_re]
    exact mul_comm _ _
  change (∫ p : E3, F p).re = _
  rw [h1]
  exact integral_congr_ae (Filter.Eventually.of_forall h2)

/-! ## 3. The periodisation identity -/

theorem fL_latticeSum_eq_periodisation (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (w : EuclideanSpace ℝ (Fin 3)) :
    (∑' m : Fin 3 → ℤ,
        fc.f (‖(2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m‖ / κ)
          * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) w))
      = ℓ ^ 3 * (∑' d : Fin 3 → ℤ,
          ((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : EuclideanSpace ℝ (Fin 3),
                Real.cos (inner ℝ p (w + ℓ • Work.BoseBoxFock.latVec d)) * fc.f (‖p‖ / κ)) := by
  classical
  set c : ℝ := 2 * Real.pi / ℓ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hF0d : ContDiff ℝ (⊤ : ℕ∞) (symb fc κ) := contDiff_symb fc hκ
  have hF0s : HasCompactSupport (symb fc κ) := hasCompactSupport_symb fc hκ
  -- the position-space test function
  set h : E3 → ℂ := fun x => symb fc κ (c • x) *
    Complex.exp (Complex.I * (inner ℝ (c • x) w : ℂ)) with hhdef
  -- ## continuity
  have h_cont : Continuous h := by
    rw [hhdef]
    refine (hF0d.continuous.comp (continuous_const_smul c)).mul ?_
    fun_prop
  -- ## vanishing beyond the support of the symbol
  have h_zero_of_gt : ∀ x : E3, 2 * κ / c < ‖x‖ → h x = 0 := by
    intro x hx
    rw [hhdef]
    have h2 : 2 * κ < ‖c • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hcpos.le]
      rw [div_lt_iff₀ hcpos] at hx
      linarith
    have h3 : (2 : ℝ) ≤ ‖c • x‖ / κ := by rw [le_div_iff₀ hκ]; linarith
    show symb fc κ (c • x) * Complex.exp (Complex.I * (inner ℝ (c • x) w : ℂ)) = 0
    rw [symb_apply, fc.zero _ h3, Complex.ofReal_zero, zero_mul]
  -- ## compact support
  have h_cs : HasCompactSupport h := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (2 * κ / c))
      (isCompact_closedBall 0 (2 * κ / c)) ?_
    intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    rw [not_le] at hlt
    exact hx (h_zero_of_gt x hlt)
  -- ## norm bound
  have h_le_one : ∀ x : E3, ‖h x‖ ≤ 1 := by
    intro x
    rw [hhdef]
    calc ‖symb fc κ (c • x) * Complex.exp (Complex.I * (inner ℝ (c • x) w : ℂ))‖
        = ‖symb fc κ (c • x)‖ *
            ‖Complex.exp (Complex.I * (inner ℝ (c • x) w : ℂ))‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_symb_le_one fc κ (c • x))
          (le_of_eq (fl_norm_exp_I (inner ℝ (c • x) w))) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3, ‖h x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℤ)) := by
    refine ⟨(1 + 2 * κ / c) ^ 4, by positivity, fun x => ?_⟩
    rcases le_or_gt ‖x‖ (2 * κ / c) with hx | hx
    · have h1 : ‖h x‖ ≤ 1 := h_le_one x
      have h2 : (1 : ℝ) ≤ (1 + 2 * κ / c) ^ 4 * (1 + ‖x‖) ^ (-(4 : ℤ)) := by
        rw [zpow_neg]
        have hb : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
        have h4 : (1 + ‖x‖) ^ 4 ≤ (1 + 2 * κ / c) ^ 4 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 4
        calc (1 : ℝ) = (1 + ‖x‖) ^ 4 * ((1 + ‖x‖) ^ 4)⁻¹ := by
              rw [mul_inv_cancel₀ (ne_of_gt hb)]
          _ ≤ (1 + 2 * κ / c) ^ 4 * ((1 + ‖x‖) ^ 4)⁻¹ :=
              mul_le_mul_of_nonneg_right h4 (by positivity)
      linarith
    · rw [h_zero_of_gt x hx, norm_zero]
      positivity
  have h_dec : ∃ C : ℝ, ∀ x : E3, (1 + ‖x‖) ^ 4 * ‖h x‖ ≤ C := by
    obtain ⟨C, hC0, hC⟩ := h_bound
    refine ⟨C, fun x => ?_⟩
    have h2 : (1 + ‖x‖) ^ 4 * (C * (1 + ‖x‖) ^ (-(4 : ℤ))) = C := by
      rw [zpow_neg]
      field_simp
    calc (1 + ‖x‖) ^ 4 * ‖h x‖
        ≤ (1 + ‖x‖) ^ 4 * (C * (1 + ‖x‖) ^ (-(4 : ℤ))) :=
          mul_le_mul_of_nonneg_left (hC x) (by positivity)
      _ = C := h2
  -- ## the sample computation
  have hsample : ∀ m : Fin 3 → ℤ,
      (∫ x : E3, h x * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m) : ℂ))))
        = ((c ^ 3 : ℝ) : ℂ)⁻¹ * invT (symb fc κ) (w - ℓ • latVec m) := by
    intro m
    have hstep := sample_scaled_lowCut fc hκ hℓ w m
    have h1 : (∫ x : E3, h x *
          Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m) : ℂ))))
        = ∫ x : E3, ((fc.f (‖(2 * Real.pi / ℓ) • x‖ / κ) : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • x) w : ℂ))
            * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m) : ℂ))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hhdef, symb_apply, hcdef]
    have h2 : ((((2 * Real.pi / ℓ) ^ 3 : ℝ) : ℂ))⁻¹ * (∫ p : E3, ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ p (w - ℓ • latVec m) : ℂ)))
        = ((c ^ 3 : ℝ) : ℂ)⁻¹ * invT (symb fc κ) (w - ℓ • latVec m) := by
      rw [hcdef]
      rfl
    rw [h1, hstep, h2]
  -- ## summability of the sampled left-hand side
  obtain ⟨C₀, hC₀0, hC₀⟩ := norm_invT_le (symb fc κ) hF0d hF0s
  have hsum_pos : Summable (fun d : Fin 3 → ℤ => invT (symb fc κ) (w + ℓ • latVec d)) :=
    summable_shift_latVec hC₀0 hC₀ hℓ w
  have hsum_neg : Summable (fun m : Fin 3 → ℤ => invT (symb fc κ) (w - ℓ • latVec m)) := by
    refine ((Equiv.summable_iff (Equiv.neg (Fin 3 → ℤ))).mpr hsum_pos).congr fun m => ?_
    simp only [Function.comp_apply, Equiv.neg_apply, latVec_neg, smul_neg]
    abel
  have hsum_samples : Summable (fun m : Fin 3 → ℤ =>
      ∫ x : E3, h x * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m) : ℂ)))) :=
    (hsum_neg.mul_left (((c ^ 3 : ℝ)) : ℂ)⁻¹).congr fun m => (hsample m).symm
  -- ## Poisson summation
  have hpois0 := poissonEuclid3Summable h h_cont h_dec hsum_samples
  have hpois : (∑' m : Fin 3 → ℤ, h (latVec m))
      = ∑' m : Fin 3 → ℤ, ∫ x : E3,
          h x * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m) : ℂ))) :=
    hpois0
  -- ## reindexing
  have hreindex : (∑' m : Fin 3 → ℤ, invT (symb fc κ) (w - ℓ • latVec m))
      = ∑' d : Fin 3 → ℤ, invT (symb fc κ) (w + ℓ • latVec d) := by
    rw [← (Equiv.neg (Fin 3 → ℤ)).tsum_eq
      (fun m : Fin 3 → ℤ => invT (symb fc κ) (w - ℓ • latVec m))]
    refine tsum_congr fun m => ?_
    simp only [Equiv.neg_apply, latVec_neg, smul_neg]
    abel
  -- ## the complex identity
  have key : (∑' m : Fin 3 → ℤ, h (latVec m))
      = ((c ^ 3 : ℝ) : ℂ)⁻¹ * ∑' d : Fin 3 → ℤ, invT (symb fc κ) (w + ℓ • latVec d) := by
    rw [hpois, tsum_congr hsample, tsum_mul_left, hreindex]
  -- ## summability of the lattice samples
  have hsum_h : Summable (fun m : Fin 3 → ℤ => h (latVec m)) := by
    obtain ⟨C, hC0, hC⟩ := h_bound
    refine Summable.of_norm_bounded
      (g := fun m : Fin 3 → ℤ => C * ((1 + ‖latVec m‖) ^ 4)⁻¹) ?_ ?_
    · exact (summable_one_add_norm_latVec_pow_inv (N := 4) le_rfl).mul_left C
    · intro m
      refine (hC (latVec m)).trans (le_of_eq ?_)
      rw [zpow_neg]
      rfl
  -- ## real parts
  have hterm_L : ∀ m : Fin 3 → ℤ, (h (latVec m)).re
      = fc.f (‖(2 * Real.pi / ℓ) • latVec m‖ / κ)
          * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec m) w) := by
    intro m
    simp only [hhdef, symb_apply, hcdef, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, fl_exp_I_re]
  have hLHS_re : (∑' m : Fin 3 → ℤ, h (latVec m)).re
      = ∑' m : Fin 3 → ℤ, fc.f (‖(2 * Real.pi / ℓ) • latVec m‖ / κ)
          * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec m) w) := by
    rw [fl_re_tsum hsum_h]
    exact tsum_congr hterm_L
  have hsum_pos_re : Summable (fun d : Fin 3 → ℤ =>
      (invT (symb fc κ) (w + ℓ • latVec d)).re) := by
    refine Summable.of_norm_bounded hsum_pos.norm (fun d => ?_)
    simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (invT (symb fc κ) (w + ℓ • latVec d))
  have hterm_R : ∀ q : E3, (invT (symb fc κ) q).re
      = ∫ p : E3, Real.cos (inner ℝ p q) * fc.f (‖p‖ / κ) := by
    intro q
    simpa only [invT, symb_apply] using fl_re_invT_lowCut fc hκ q
  have hRHS_re : (∑' d : Fin 3 → ℤ, invT (symb fc κ) (w + ℓ • latVec d)).re
      = ∑' d : Fin 3 → ℤ, ∫ p : E3,
          Real.cos (inner ℝ p (w + ℓ • latVec d)) * fc.f (‖p‖ / κ) := by
    rw [fl_re_tsum hsum_pos]
    exact tsum_congr (fun d => hterm_R (w + ℓ • latVec d))
  -- ## the real part of the complex identity
  have hkey_re : (∑' m : Fin 3 → ℤ, h (latVec m)).re
      = ((c ^ 3 : ℝ))⁻¹ * (∑' d : Fin 3 → ℤ, invT (symb fc κ) (w + ℓ • latVec d)).re := by
    rw [key, Complex.mul_re, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hmain : (∑' m : Fin 3 → ℤ, fc.f (‖(2 * Real.pi / ℓ) • latVec m‖ / κ)
        * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec m) w))
      = ((c ^ 3 : ℝ))⁻¹ * ∑' d : Fin 3 → ℤ, ∫ p : E3,
          Real.cos (inner ℝ p (w + ℓ • latVec d)) * fc.f (‖p‖ / κ) := by
    rw [← hLHS_re, hkey_re, hRHS_re]
  have hcinv3 : ((c ^ 3 : ℝ))⁻¹ = ℓ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ := by
    rw [hcdef]
    field_simp
  rw [hmain, tsum_mul_left, hcinv3]
  ring

end

end Work.BoseBoxFock
