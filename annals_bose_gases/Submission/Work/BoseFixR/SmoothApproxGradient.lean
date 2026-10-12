import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Gradient.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Filter Metric
open scoped Convolution Topology Pointwise

namespace Work.BoseFixR

private abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about `gradient` -/

/-- The gradient is the Riesz representative of the Fréchet derivative. -/
lemma gradient_eq_toDual_symm (f : E3 → ℝ) (x : E3) :
    gradient f x = (InnerProductSpace.toDual ℝ E3).symm (fderiv ℝ f x) := by
  rw [← toDual_gradient (𝕜 := ℝ) (f := f) (x := x),
    LinearIsometryEquiv.symm_apply_apply]

/-- The norm of a difference of gradients is the operator norm of the difference of derivatives. -/
lemma norm_gradient_sub (f g : E3 → ℝ) (x : E3) :
    ‖gradient f x - gradient g x‖ = ‖fderiv ℝ f x - fderiv ℝ g x‖ := by
  have h : gradient f x - gradient g x
      = (InnerProductSpace.toDual ℝ E3).symm (fderiv ℝ f x - fderiv ℝ g x) := by
    rw [gradient_eq_toDual_symm f x, gradient_eq_toDual_symm g x, ← map_sub]
  rw [h, LinearIsometryEquiv.norm_map]

/-- `x ↦ gradient f x` is continuous as soon as `x ↦ fderiv ℝ f x` is. -/
lemma continuous_gradient_of_continuous_fderiv {f : E3 → ℝ} (hf : Continuous (fderiv ℝ f)) :
    Continuous (fun x => gradient f x) := by
  have h : (fun x => gradient f x)
      = fun x => (InnerProductSpace.toDual ℝ E3).symm (fderiv ℝ f x) :=
    funext fun x => gradient_eq_toDual_symm f x
  rw [h]
  exact (InnerProductSpace.toDual ℝ E3).symm.continuous.comp hf

/-- The gradient vanishes off the closed support. -/
lemma gradient_eq_zero_of_notMem_tsupport {f : E3 → ℝ} {x : E3} (hx : x ∉ tsupport f) :
    gradient f x = 0 := by
  rw [gradient_eq_toDual_symm, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx, map_zero]

/-- The support of `‖gradient f‖` is contained in the closed support of `f`. -/
lemma support_norm_gradient_subset_tsupport (f : E3 → ℝ) :
    Function.support (fun x => ‖gradient f x‖) ⊆ tsupport f := by
  intro x hx
  by_contra hxt
  rw [Function.mem_support] at hx
  exact hx (by simp [gradient_eq_zero_of_notMem_tsupport hxt])

/-! ## Uniform approximation by convolution with a normalized bump -/

/-- If `ψ` does not oscillate by more than `δ` on balls of radius `b.rOut`, then the convolution
with the normalized bump `b` is pointwise within `δ` of `ψ`. -/
theorem MollPointwiseBound {ψ : E3 → ℝ} (hψ : Continuous ψ) (b : ContDiffBump (0 : E3)) {δ : ℝ}
    (hδ : ∀ x y, dist y x ≤ b.rOut → |ψ y - ψ x| ≤ δ) :
    ∀ x, |MeasureTheory.convolution (b.normed volume) ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume x
      - ψ x| ≤ δ := by
  intro x
  have h := ContDiffBump.dist_normed_convolution_le (φ := b) (g := ψ) (μ := volume) (x₀ := x)
    (ε := δ) hψ.aestronglyMeasurable (fun y hy => by
      rw [Real.dist_eq]
      exact hδ x y (Metric.mem_ball.mp hy).le)
  rwa [Real.dist_eq] at h

/-! ## The derivative of the mollification -/

/-- The derivative of the mollification is the convolution with the derivative. This is the
computation of `HasCompactSupport.hasFDerivAt_convolution_right` together with
`convolution_precompR_apply`, giving the pointwise formula
`(fderiv (φ ⋆ ψ) x) h = ∫ t, φ t * (fderiv ψ (x - t)) h`. -/
theorem fderiv_moll_apply {ψ : E3 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (c : E3 → ℝ) (hc_li : LocallyIntegrable c volume) (x h : E3) :
    (fderiv ℝ (MeasureTheory.convolution c ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) h
      = ∫ t, c t * ((fderiv ℝ ψ (x - t)) h) ∂volume := by
  have hg_cont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hg_cs : HasCompactSupport (fderiv ℝ ψ) := hψc.fderiv ℝ
  rw [show fderiv ℝ (MeasureTheory.convolution c ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
      = MeasureTheory.convolution c (fderiv ℝ ψ)
          (ContinuousLinearMap.precompR E3 (ContinuousLinearMap.lsmul ℝ ℝ)) volume x from
      (HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
        hψc hc_li hψ x).fderiv]
  rw [MeasureTheory.convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (f := c) (g := fderiv ℝ ψ) hc_li hg_cs hg_cont x h]
  rw [MeasureTheory.convolution_lsmul]
  simp [smul_eq_mul]

/-- **The gradient of the mollification is close to the gradient of `ψ`.** If `fderiv ψ` does not
oscillate by more than `ω` on balls of radius `b.rOut`, then `fderiv (φ ⋆ ψ)` is uniformly within
`ω` (in operator norm) of `fderiv ψ`. -/
theorem MollGradientFDerivBound {ψ : E3 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (b : ContDiffBump (0 : E3)) {ω : ℝ}
    (hω : ∀ x y, dist y x ≤ b.rOut → ‖fderiv ℝ ψ y - fderiv ℝ ψ x‖ ≤ ω) :
    ∀ x, ‖fderiv ℝ (MeasureTheory.convolution (b.normed volume) ψ (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) x - fderiv ℝ ψ x‖ ≤ ω := by
  intro x
  set c : E3 → ℝ := b.normed volume with hc
  have hc_cont : Continuous c := by
    rw [hc]
    exact (ContDiffBump.contDiff_normed (f := b) (μ := volume) (n := (⊤ : ENat))).continuous
  have hc_li : LocallyIntegrable c volume := hc_cont.locallyIntegrable
  have hc_cs : HasCompactSupport c := by rw [hc]; exact b.hasCompactSupport_normed
  have hc_int : ∫ t, c t ∂volume = 1 := by rw [hc]; exact b.integral_normed
  have hc_nn : ∀ t, 0 ≤ c t := fun t => by rw [hc]; exact b.nonneg_normed t
  have hc_supp : Function.support c = Metric.ball (0 : E3) b.rOut := by
    rw [hc]; exact b.support_normed_eq
  have hc_intble : Integrable c volume := hc_cont.integrable_of_hasCompactSupport hc_cs
  have hg_cont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hω0 : 0 ≤ ω := by
    simpa using hω x x (by simp [b.rOut_pos.le])
  have key := fderiv_moll_apply hψ hψc c hc_li x
  refine ContinuousLinearMap.opNorm_le_bound _ hω0 (fun h => ?_)
  have hA := key h
  have hFcont : Continuous (fun t => ((fderiv ℝ ψ (x - t)) h) - ((fderiv ℝ ψ x) h)) :=
    (((hg_cont.comp (continuous_const.sub continuous_id)).clm_apply continuous_const)).sub
      continuous_const
  have hcontG : Continuous (fun t => (fderiv ℝ ψ (x - t)) h) :=
    (hg_cont.comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  have hIntG : Integrable (fun t => c t * ((fderiv ℝ ψ (x - t)) h)) volume :=
    (hc_cont.mul hcontG).integrable_of_hasCompactSupport (hc_cs.mul_right)
  have hIntB : Integrable (fun t => c t * ((fderiv ℝ ψ x) h)) volume :=
    hc_intble.mul_const ((fderiv ℝ ψ x) h)
  have hIntF : Integrable (fun t => c t * (((fderiv ℝ ψ (x - t)) h) - ((fderiv ℝ ψ x) h)))
      volume :=
    (hc_cont.mul hFcont).integrable_of_hasCompactSupport (hc_cs.mul_right)
  have hIntK : Integrable (fun t => c t * (ω * ‖h‖)) volume :=
    hc_intble.mul_const (ω * ‖h‖)
  -- rewrite the difference as a single integral of the pointwise difference
  have h2 : ∫ t, c t * (((fderiv ℝ ψ (x - t)) h) - ((fderiv ℝ ψ x) h)) ∂volume
      = ∫ t, c t * ((fderiv ℝ ψ (x - t)) h) ∂volume
        - ∫ t, c t * ((fderiv ℝ ψ x) h) ∂volume := by
    rw [← MeasureTheory.integral_sub hIntG hIntB]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    ring
  have hmain : (fderiv ℝ (MeasureTheory.convolution c ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) h
      - (fderiv ℝ ψ x) h
      = ∫ t, c t * (((fderiv ℝ ψ (x - t)) h) - ((fderiv ℝ ψ x) h)) ∂volume := by
    have h1' : (∫ t, c t * ((fderiv ℝ ψ x) h) ∂volume) = (fderiv ℝ ψ x) h := by
      rw [MeasureTheory.integral_mul_const, hc_int, one_mul]
    calc (fderiv ℝ (MeasureTheory.convolution c ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) h
          - (fderiv ℝ ψ x) h
        = (∫ t, c t * ((fderiv ℝ ψ (x - t)) h) ∂volume) - (fderiv ℝ ψ x) h := by rw [hA]
      _ = (∫ t, c t * ((fderiv ℝ ψ (x - t)) h) ∂volume)
            - (∫ t, c t * ((fderiv ℝ ψ x) h) ∂volume) := by rw [h1']
      _ = ∫ t, c t * (((fderiv ℝ ψ (x - t)) h) - ((fderiv ℝ ψ x) h)) ∂volume := h2.symm
  rw [sub_apply, hmain]
  have hpoint : ∀ t, ‖c t * (((fderiv ℝ ψ (x - t)) h) - ((fderiv ℝ ψ x) h))‖ ≤ c t * (ω * ‖h‖) := by
    intro t
    by_cases ht : t ∈ Function.support c
    · have ht' : ‖t‖ < b.rOut := by
        have := ht
        rw [hc_supp] at this
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hdist : dist (x - t) x ≤ b.rOut := by
        rw [dist_eq_norm]
        simpa using ht'.le
      have hF : ‖((fderiv ℝ ψ (x - t)) h) - ((fderiv ℝ ψ x) h)‖ ≤ ω * ‖h‖ := by
        rw [← sub_apply]
        calc ‖(fderiv ℝ ψ (x - t) - fderiv ℝ ψ x) h‖
            ≤ ‖fderiv ℝ ψ (x - t) - fderiv ℝ ψ x‖ * ‖h‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ ω * ‖h‖ := by gcongr; exact hω x (x - t) hdist
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc_nn t)]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hF) (hc_nn t)
    · have h0 : c t = 0 := Function.notMem_support.mp ht
      simp [h0]
  calc ‖∫ t, c t * (((fderiv ℝ ψ (x - t)) h) - ((fderiv ℝ ψ x) h)) ∂volume‖
      ≤ ∫ t, ‖c t * (((fderiv ℝ ψ (x - t)) h) - ((fderiv ℝ ψ x) h))‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t, c t * (ω * ‖h‖) ∂volume := integral_mono hIntF.norm hIntK hpoint
    _ = ω * ‖h‖ := by rw [MeasureTheory.integral_mul_const, hc_int, one_mul]

/-! ## The closed support of the mollification -/

/-- The closed support of a mollification with a bump of outer radius `≤ 1` is contained in
`tsupport ψ + closedBall 0 1`. -/
lemma tsupport_moll_subset {ψ : E3 → ℝ} (hψc : HasCompactSupport ψ)
    (b : ContDiffBump (0 : E3)) (hr : b.rOut ≤ 1) :
    tsupport (MeasureTheory.convolution (b.normed volume) ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      ⊆ tsupport ψ + Metric.closedBall (0 : E3) 1 := by
  have hK : IsCompact (tsupport ψ + Metric.closedBall (0 : E3) 1) :=
    hψc.isCompact.add (isCompact_closedBall 0 1)
  have h1 : Function.support (MeasureTheory.convolution (b.normed volume) ψ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      ⊆ Metric.ball (0 : E3) b.rOut + Function.support ψ := by
    refine (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)).trans ?_
    rw [b.support_normed_eq]
  have h2 : Metric.ball (0 : E3) b.rOut + Function.support ψ
      ⊆ tsupport ψ + Metric.closedBall (0 : E3) 1 := by
    rintro z ⟨a, ha, b', hb', rfl⟩
    refine ⟨b', subset_tsupport ψ hb', a, ?_, add_comm b' a⟩
    rw [mem_closedBall_zero_iff]
    exact (mem_ball_zero_iff.mp ha).le.trans hr
  calc tsupport (MeasureTheory.convolution (b.normed volume) ψ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      = closure (Function.support (MeasureTheory.convolution (b.normed volume) ψ
          (ContinuousLinearMap.lsmul ℝ ℝ) volume)) := rfl
    _ ⊆ closure (tsupport ψ + Metric.closedBall (0 : E3) 1) := closure_mono (h1.trans h2)
    _ = tsupport ψ + Metric.closedBall (0 : E3) 1 := hK.isClosed.closure_eq

/-! ## Two elementary integral limits -/

/-- Uniform convergence of `F n` to `g` with rate `(n+1)⁻¹`, together with a common compact support,
gives convergence of the integrals of the squares. -/
theorem TendstoIntegralSq {F : ℕ → E3 → ℝ} {g : E3 → ℝ} {K : Set E3} (hK : IsCompact K)
    (hFc : ∀ n, Continuous (F n)) (hgc : Continuous g)
    (hFs : ∀ n, Function.support (F n) ⊆ K) (hgs : Function.support g ⊆ K)
    (hb : ∀ n x, |F n x - g x| ≤ (n + 1 : ℝ)⁻¹) :
    Filter.Tendsto (fun n => ∫ x, (F n x) ^ 2) Filter.atTop (nhds (∫ x, (g x) ^ 2)) := by
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hgc.continuousOn
  set C : ℝ := max C₀ 0 with hCdef
  have hCbd : ∀ x ∈ K, |g x| ≤ C := fun x hx =>
    (by simpa [Real.norm_eq_abs] using hC₀ x hx : |g x| ≤ C₀).trans (le_max_left _ _)
  have hgsq : Integrable (fun x => (g x) ^ 2) volume := by
    refine (hgc.pow 2).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact hK fun x hx =>
      hgs (Function.mem_support.mpr fun h0 => hx (by simp [h0]))
  have hFsq : ∀ n, Integrable (fun x => (F n x) ^ 2) volume := fun n => by
    refine ((hFc n).pow 2).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact hK fun x hx =>
      hFs n (Function.mem_support.mpr fun h0 => hx (by simp [h0]))
  have hKint : Integrable (K.indicator (1 : E3 → ℝ)) volume :=
    (integrableOn_const (s := K) (μ := volume) (C := (1 : ℝ))
      hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hbd : ∀ n x, |(F n x) ^ 2 - (g x) ^ 2| ≤
      ((n + 1 : ℝ)⁻¹ * (2 * C + 1)) * K.indicator 1 x := by
    intro n x
    by_cases hx : x ∈ K
    · have h1 : |F n x - g x| ≤ (n + 1 : ℝ)⁻¹ := hb n x
      have h2 : |F n x| ≤ C + 1 := by
        have h : (n + 1 : ℝ)⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
        calc |F n x| = |(F n x - g x) + g x| := by congr 1; ring
          _ ≤ |F n x - g x| + |g x| := abs_add_le _ _
          _ ≤ (n + 1 : ℝ)⁻¹ + C := add_le_add h1 (hCbd x hx)
          _ ≤ 1 + C := by linarith
          _ = C + 1 := by ring
      have h4 : |F n x + g x| ≤ 2 * C + 1 := by
        calc |F n x + g x| ≤ |F n x| + |g x| := abs_add_le _ _
          _ ≤ (C + 1) + C := add_le_add h2 (hCbd x hx)
          _ = 2 * C + 1 := by ring
      rw [show (F n x) ^ 2 - (g x) ^ 2 = (F n x - g x) * (F n x + g x) by ring,
        abs_mul, Set.indicator_of_mem hx]
      simp only [Pi.one_apply, mul_one]
      exact mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
    · have hFx : F n x = 0 := by
        by_contra h
        exact hx (hFs n (Function.mem_support.mpr h))
      have hgx : g x = 0 := by
        by_contra h
        exact hx (hgs (Function.mem_support.mpr h))
      rw [hFx, hgx, Set.indicator_of_notMem hx]
      simp
  have hlim : Tendsto (fun n : ℕ => ((n + 1 : ℝ)⁻¹ * (2 * C + 1)) * volume.real K) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (nhds 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (h1.mul_const (2 * C + 1)).mul_const (volume.real K)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => norm_nonneg _) (fun n => ?_)
  rw [Real.norm_eq_abs, ← MeasureTheory.integral_sub (hFsq n) hgsq]
  calc |∫ x, ((F n x) ^ 2 - (g x) ^ 2) ∂volume|
      ≤ ∫ x, |(F n x) ^ 2 - (g x) ^ 2| ∂volume := abs_integral_le_integral_abs
    _ ≤ ∫ x, ((n + 1 : ℝ)⁻¹ * (2 * C + 1)) * K.indicator 1 x ∂volume :=
        integral_mono ((hFsq n).sub hgsq).abs (hKint.const_mul _) (hbd n)
    _ = ((n + 1 : ℝ)⁻¹ * (2 * C + 1)) * volume.real K := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_indicator_one hK.measurableSet]

/-- Uniform convergence of `F n` to `g` with rate `(n+1)⁻¹` gives convergence of `∫ W · F n` for
every integrable `W`. -/
theorem TendstoIntegralMul {W : E3 → ℝ} (hW : MeasureTheory.Integrable W)
    {F : ℕ → E3 → ℝ} {g : E3 → ℝ}
    (hFc : ∀ n, Continuous (F n)) (hgc : Continuous g)
    (hg : ∃ C : ℝ, ∀ x, |g x| ≤ C)
    (hb : ∀ n x, |F n x - g x| ≤ (n + 1 : ℝ)⁻¹) :
    Filter.Tendsto (fun n => ∫ x, W x * F n x) Filter.atTop (nhds (∫ x, W x * g x)) := by
  obtain ⟨C, hC⟩ := hg
  have hFint : ∀ n, Integrable (fun x => W x * F n x) volume := fun n =>
    hW.mul_bdd (hFc n).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        have h : (n + 1 : ℝ)⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
        calc |F n x| = |(F n x - g x) + g x| := by congr 1; ring
          _ ≤ |F n x - g x| + |g x| := abs_add_le _ _
          _ ≤ (n + 1 : ℝ)⁻¹ + C := add_le_add (hb n x) (hC x)
          _ ≤ 1 + C := by linarith
          _ = C + 1 := by ring)
  have hgint : Integrable (fun x => W x * g x) volume :=
    hW.mul_bdd hgc.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hmain : ∀ n, |(∫ x, W x * F n x) - (∫ x, W x * g x)|
      ≤ (n + 1 : ℝ)⁻¹ * ∫ x, |W x| := by
    intro n
    have h1 : Integrable (fun x => |W x * F n x - W x * g x|) volume :=
      ((hFint n).sub hgint).abs
    have h2 : Integrable (fun x => |W x| * (n + 1 : ℝ)⁻¹) volume := hW.abs.mul_const _
    have hpt : ∀ x, |W x * F n x - W x * g x| ≤ |W x| * (n + 1 : ℝ)⁻¹ := fun x => by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hb n x) (abs_nonneg _)
    have h3 : (∫ x, W x * F n x) - (∫ x, W x * g x)
        = ∫ x, (W x * F n x - W x * g x) ∂volume :=
      (MeasureTheory.integral_sub (hFint n) hgint).symm
    calc |(∫ x, W x * F n x) - (∫ x, W x * g x)|
        = |∫ x, (W x * F n x - W x * g x) ∂volume| := congrArg abs h3
      _ ≤ ∫ x, |W x * F n x - W x * g x| ∂volume := abs_integral_le_integral_abs
      _ ≤ ∫ x, |W x| * (n + 1 : ℝ)⁻¹ ∂volume := integral_mono h1 h2 hpt
      _ = (n + 1 : ℝ)⁻¹ * ∫ x, |W x| := by
          rw [MeasureTheory.integral_mul_const]; ring
  have hlim : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹ * ∫ x, |W x|) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (nhds 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h1.mul_const (∫ x, |W x|)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hmain n)

theorem SmoothApproxGradient {W ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∃ u : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ENat) (u n)) ∧
      (∀ n, HasCompactSupport (u n)) ∧
      (∀ n x, ‖u n x - ψ x‖ ≤ (n + 1 : ℝ)⁻¹) ∧
      Filter.Tendsto (fun n => ∫ x, ‖gradient (u n) x‖ ^ 2) Filter.atTop
        (nhds (∫ x, ‖gradient ψ x‖ ^ 2)) ∧
      Filter.Tendsto (fun n => ∫ x, W x * u n x) Filter.atTop
        (nhds (∫ x, W x * ψ x)) := by
  have hψcont : Continuous ψ := hψ.continuous
  have hgcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hgcs : HasCompactSupport (fderiv ℝ ψ) := hψc.fderiv ℝ
  have hψuc : UniformContinuous ψ :=
    hψcont.uniformContinuous_of_tendsto_cocompact hψc.is_zero_at_infty
  have hguc : UniformContinuous (fderiv ℝ ψ) :=
    hgcont.uniformContinuous_of_tendsto_cocompact hgcs.is_zero_at_infty
  -- for every `n` we find a radius on which both `ψ` and `fderiv ψ` oscillate by at most
  -- `(n+1)⁻¹`, and which is itself `≤ (n+1)⁻¹`
  have hex : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ r ≤ (n + 1 : ℝ)⁻¹ ∧
      (∀ x y : E3, dist y x ≤ r → |ψ y - ψ x| ≤ (n + 1 : ℝ)⁻¹) ∧
      (∀ x y : E3, dist y x ≤ r → ‖fderiv ℝ ψ y - fderiv ℝ ψ x‖ ≤ (n + 1 : ℝ)⁻¹) := by
    intro n
    have hε : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.uniformContinuous_iff.mp hψuc _ hε
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.uniformContinuous_iff.mp hguc _ hε
    refine ⟨min (min (δ₁ / 2) (δ₂ / 2)) (n + 1 : ℝ)⁻¹,
      lt_min (lt_min (by linarith) (by linarith)) hε,
      min_le_right _ _, fun x y hxy => ?_, fun x y hxy => ?_⟩
    · have h1 : dist y x ≤ δ₁ / 2 := hxy.trans ((min_le_left _ _).trans (min_le_left _ _))
      have h : dist y x < δ₁ := lt_of_le_of_lt h1 (by linarith)
      have hh := hδ₁ h
      rw [Real.dist_eq] at hh
      exact hh.le
    · have h1 : dist y x ≤ δ₂ / 2 := hxy.trans ((min_le_left _ _).trans (min_le_right _ _))
      have h : dist y x < δ₂ := lt_of_le_of_lt h1 (by linarith)
      have hh := hδ₂ h
      rw [dist_eq_norm] at hh
      exact hh.le
  choose r hr using hex
  -- the bump functions, their radii tending to `0`
  let b : ℕ → ContDiffBump (0 : E3) := fun n =>
    ⟨r n / 2, r n, by linarith [(hr n).1], by linarith [(hr n).1]⟩
  have hb_psi : ∀ n x y, dist y x ≤ (b n).rOut → |ψ y - ψ x| ≤ (n + 1 : ℝ)⁻¹ :=
    fun n x y h => (hr n).2.2.1 x y h
  have hb_grad : ∀ n x y, dist y x ≤ (b n).rOut →
      ‖fderiv ℝ ψ y - fderiv ℝ ψ x‖ ≤ (n + 1 : ℝ)⁻¹ :=
    fun n x y h => (hr n).2.2.2 x y h
  have hb_le1 : ∀ n, (b n).rOut ≤ 1 := fun n =>
    (hr n).2.1.trans (inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  let u : ℕ → E3 → ℝ := fun n =>
    MeasureTheory.convolution ((b n).normed volume) ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hu_smooth : ∀ n, ContDiff ℝ (⊤ : ENat) (u n) := fun n =>
    HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (ContDiffBump.hasCompactSupport_normed (b n))
      (ContDiffBump.contDiff_normed (f := b n) (μ := volume) (n := (⊤ : ENat)))
      hψcont.locallyIntegrable
  have hu_c1 : ∀ n, ContDiff ℝ 1 (u n) := fun n =>
    HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (ContDiffBump.hasCompactSupport_normed (b n))
      (ContDiffBump.contDiff_normed (f := b n) (μ := volume) (n := (1 : ENat)))
      hψcont.locallyIntegrable
  have hu_cs : ∀ n, HasCompactSupport (u n) := fun n =>
    HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      (ContDiffBump.hasCompactSupport_normed (b n)) hψc
  have hu_close : ∀ n x, ‖u n x - ψ x‖ ≤ (n + 1 : ℝ)⁻¹ := fun n x => by
    have h := MollPointwiseBound hψcont (b n) (δ := (n + 1 : ℝ)⁻¹) (hb_psi n)
    simpa [Real.norm_eq_abs, u] using h x
  have hu_grad : ∀ n x, ‖gradient (u n) x - gradient ψ x‖ ≤ (n + 1 : ℝ)⁻¹ := fun n x => by
    rw [norm_gradient_sub (u n) ψ x]
    exact MollGradientFDerivBound hψ hψc (b n) (ω := (n + 1 : ℝ)⁻¹) (hb_grad n) x
  have hK : IsCompact (tsupport ψ + Metric.closedBall (0 : E3) 1) :=
    hψc.isCompact.add (isCompact_closedBall 0 1)
  have hu_supp : ∀ n, Function.support (fun x => ‖gradient (u n) x‖)
      ⊆ tsupport ψ + Metric.closedBall (0 : E3) 1 := fun n =>
    (support_norm_gradient_subset_tsupport (u n)).trans
      (tsupport_moll_subset hψc (b n) (hb_le1 n))
  have hψ_supp : Function.support (fun x => ‖gradient ψ x‖)
      ⊆ tsupport ψ + Metric.closedBall (0 : E3) 1 :=
    (support_norm_gradient_subset_tsupport ψ).trans
      (fun a ha => ⟨a, ha, 0, by simp, by simp⟩)
  have hbdd : ∃ C : ℝ, ∀ x, |ψ x| ≤ C := by
    obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψcont
    refine ⟨max C 0, fun x => ?_⟩
    simpa [Real.norm_eq_abs] using (hC x).trans (le_max_left C 0)
  refine ⟨u, hu_smooth, hu_cs, hu_close, ?_, ?_⟩
  · exact TendstoIntegralSq (K := tsupport ψ + Metric.closedBall (0 : E3) 1) hK
      (fun n => (continuous_gradient_of_continuous_fderiv
        ((hu_c1 n).continuous_fderiv one_ne_zero)).norm)
      (continuous_gradient_of_continuous_fderiv hgcont).norm
      hu_supp hψ_supp (fun n x => (abs_norm_sub_norm_le _ _).trans (hu_grad n x))
  · exact TendstoIntegralMul (W := W) (F := u) (g := ψ) hW
      (fun n => (hu_smooth n).continuous) hψcont hbdd
      (fun n x => by simpa [Real.norm_eq_abs] using hu_close n x)

end Work.BoseFixR
