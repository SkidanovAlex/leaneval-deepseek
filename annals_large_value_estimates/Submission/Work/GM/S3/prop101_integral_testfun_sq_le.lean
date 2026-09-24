import Mathlib
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop101_defs
import Submission.Work.GM.S3.RtildeSq_continuous
import Submission.Work.GM.S3.RtildeSq_eq_zero_of_notMem
import Submission.Work.GM.S3.gSq_continuous
import Submission.Work.GM.S3.integral_psi2_sq_le

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun energy Separated hhat hfun Iterm Spart nzCount)

/-- **Weighted Cauchy--Schwarz for the Bochner integral.** If `w g : α → ℝ` are non-negative and
`w`, `w * g`, `w * g ^ 2` are integrable with respect to `μ`, then
`(∫ w g)² ≤ (∫ w) (∫ w g²)`.

Proof: `t ↦ ∫ x, w x * (g x - t) ^ 2` is non-negative for every real `t`; expanding the square
gives the quadratic `A - 2 t C + t² B` with `A = ∫ w g²`, `B = ∫ w`, `C = ∫ w g`.  If `B > 0`
evaluate at `t = C / B`; if `B = 0` then `w = 0` a.e., whence `A = C = 0` as well. -/
theorem prop101_weighted_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {w g : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hg : ∀ x, 0 ≤ g x) (hwi : Integrable w μ)
    (hwgi : Integrable (fun x => w x * g x) μ)
    (hwg2i : Integrable (fun x => w x * g x ^ 2) μ) :
    (∫ x, w x * g x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * (∫ x, w x * g x ^ 2 ∂μ) := by
  set B : ℝ := ∫ x, w x ∂μ with hB
  set C : ℝ := ∫ x, w x * g x ∂μ with hC
  set A : ℝ := ∫ x, w x * g x ^ 2 ∂μ with hA
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg hw
  have hquad : ∀ t : ℝ, 0 ≤ A - 2 * t * C + t ^ 2 * B := by
    intro t
    have h2 : 0 ≤ ∫ x, w x * (g x - t) ^ 2 ∂μ :=
      integral_nonneg fun x => mul_nonneg (hw x) (sq_nonneg _)
    have hexp : ∫ x, w x * (g x - t) ^ 2 ∂μ = A - 2 * t * C + t ^ 2 * B := by
      calc ∫ x, w x * (g x - t) ^ 2 ∂μ
          = ∫ x, (w x * g x ^ 2 - 2 * t * (w x * g x) + t ^ 2 * w x) ∂μ := by
            apply integral_congr_ae; filter_upwards with x; ring
        _ = ∫ x, (w x * g x ^ 2 - 2 * t * (w x * g x)) ∂μ + ∫ x, t ^ 2 * w x ∂μ :=
            integral_add (hwg2i.sub (hwgi.const_mul (2 * t))) (hwi.const_mul (t ^ 2))
        _ = (∫ x, w x * g x ^ 2 ∂μ - ∫ x, 2 * t * (w x * g x) ∂μ)
              + ∫ x, t ^ 2 * w x ∂μ := by
            rw [integral_sub hwg2i (hwgi.const_mul (2 * t))]
        _ = (A - 2 * t * C) + t ^ 2 * B := by
            rw [integral_const_mul, integral_const_mul, hA, hB, hC]
        _ = A - 2 * t * C + t ^ 2 * B := by ring
    linarith [h2, hexp]
  have hmain : C ^ 2 ≤ B * A := by
    rcases eq_or_lt_of_le hB0 with hBeq | hBpos
    · have hBz : B = 0 := hBeq.symm
      have hweq : w =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hw) hwi).mp (by rw [← hB]; exact hBz)
      have hC0 : C = 0 := by
        rw [hC]
        have hcongr : (fun x => w x * g x) =ᵐ[μ] (fun _ => 0) := by
          filter_upwards [hweq] with x hx
          simp [hx]
        rw [integral_congr_ae hcongr]; simp
      have hA0' : A = 0 := by
        rw [hA]
        have hcongr : (fun x => w x * g x ^ 2) =ᵐ[μ] (fun _ => 0) := by
          filter_upwards [hweq] with x hx
          simp [hx]
        rw [integral_congr_ae hcongr]; simp
      rw [hC0, hA0', hBz]; norm_num
    · have h := hquad (C / B)
      rw [div_pow] at h
      field_simp at h
      nlinarith [h, hBpos]
  simpa [hA, hB, hC] using hmain

/-- **Young's inequality for the convolution on `ℝ`, squared `L²` form.**  For non-negative
continuous compactly supported `w g : ℝ → ℝ`,

`∫_ℝ (∫_ℝ w (u - y) * g y dy)² du ≤ (∫_ℝ w)² * ∫_ℝ g²`

(that is `‖w ⋆ g‖₂ ≤ ‖w‖₁ ‖g‖₂`).  Proof: the pointwise weighted Cauchy--Schwarz inequality
`(∫ y, w (u - y) * g y)² ≤ (∫ y, w (u - y)) * (∫ y, w (u - y) * g y²) = (∫w) * ∫ y, w (u-y) g y²`,
then integrate in `u` and use Fubini together with translation invariance. -/
theorem prop101_sq_conv_le {w g : ℝ → ℝ} (hw : Continuous w) (hwcs : HasCompactSupport w)
    (hg : Continuous g) (hgcs : HasCompactSupport g) (hw0 : ∀ x, 0 ≤ w x) (hg0 : ∀ x, 0 ≤ g x) :
    ∫ u, (∫ y, w (u - y) * g y) ^ 2 ≤ (∫ z, w z) ^ 2 * ∫ y, g y ^ 2 := by
  have hwint : Integrable w volume := hw.integrable_of_hasCompactSupport hwcs
  have hgint : Integrable g volume := hg.integrable_of_hasCompactSupport hgcs
  have hg2cont : Continuous (fun y : ℝ => g y ^ 2) := hg.pow 2
  have hg2cs : HasCompactSupport (fun y : ℝ => g y ^ 2) := by
    refine HasCompactSupport.of_support_subset_isCompact hgcs.isCompact ?_
    intro y hy
    rw [Function.mem_support] at hy
    refine subset_closure ?_
    rw [Function.mem_support]
    intro h0
    exact hy (by rw [h0]; ring)
  have hg2int : Integrable (fun y : ℝ => g y ^ 2) volume :=
    hg2cont.integrable_of_hasCompactSupport hg2cs
  obtain ⟨Cw, hCw⟩ := HasCompactSupport.exists_bound_of_continuous hwcs hw
  set W₁ : ℝ := ∫ z, w z with hW₁
  set G₂ : ℝ := ∫ y, g y ^ 2 with hG₂
  -- the two convolution kernels
  set K : ℝ → ℝ := MeasureTheory.convolution w g (ContinuousLinearMap.mul ℝ ℝ) volume with hK
  set H : ℝ → ℝ := MeasureTheory.convolution w (fun y : ℝ => g y ^ 2)
    (ContinuousLinearMap.mul ℝ ℝ) volume with hH
  have hKswap : ∀ u, K u = ∫ y, w (u - y) * g y := by
    intro u
    rw [hK, MeasureTheory.convolution_mul_swap]
  have hHswap : ∀ u, H u = ∫ y, w (u - y) * g y ^ 2 := by
    intro u
    rw [hH, MeasureTheory.convolution_mul_swap]
  have hKcont : Continuous K := by
    rw [hK]
    exact hwcs.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hw hg.locallyIntegrable
  have hKcs : HasCompactSupport K := by
    rw [hK]
    exact HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℝ) hwcs hgcs
  have hHcont : Continuous H := by
    rw [hH]
    exact hwcs.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hw hg2cont.locallyIntegrable
  have hHcs : HasCompactSupport H := by
    rw [hH]
    exact HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℝ) hwcs hg2cs
  have hHint : Integrable H volume := hHcont.integrable_of_hasCompactSupport hHcs
  have hKsqi : Integrable (fun u => K u ^ 2) volume := by
    have hcs2 : HasCompactSupport (fun u => K u ^ 2) := by
      refine HasCompactSupport.of_support_subset_isCompact hKcs.isCompact ?_
      intro u hu
      rw [Function.mem_support] at hu
      refine subset_closure ?_
      rw [Function.mem_support]
      intro h0
      exact hu (by rw [h0]; ring)
    exact (hKcont.pow 2).integrable_of_hasCompactSupport hcs2
  -- integrability of the `y`-integrands, for each `u`
  have hint_prod : ∀ u, Integrable (fun y => w (u - y) * g y) volume := by
    intro u
    refine Integrable.mono' (hgint.norm.const_mul Cw) ?_ ?_
    · exact ((hw.comp (continuous_const.sub continuous_id)).mul hg).aestronglyMeasurable
    · filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hCw (u - y)) (norm_nonneg _)
  have hint_prod2 : ∀ u, Integrable (fun y => w (u - y) * g y ^ 2) volume := by
    intro u
    refine Integrable.mono' (hg2int.norm.const_mul Cw) ?_ ?_
    · exact ((hw.comp (continuous_const.sub continuous_id)).mul (hg.pow 2)).aestronglyMeasurable
    · filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hCw (u - y)) (norm_nonneg _)
  -- pointwise weighted Cauchy--Schwarz
  have hpt : ∀ u, K u ^ 2 ≤ W₁ * H u := by
    intro u
    have hcs := prop101_weighted_cs (μ := volume) (w := fun y => w (u - y)) (g := g)
      (fun y => hw0 (u - y)) hg0 (hwint.comp_sub_left u) (hint_prod u) (hint_prod2 u)
    rw [← hKswap u, ← hHswap u] at hcs
    have hweight : ∫ y, w (u - y) = W₁ := by
      rw [hW₁]
      exact integral_sub_left_eq_self w volume u
    rwa [hweight] at hcs
  -- integrate the pointwise bound
  have hmono : ∫ u, K u ^ 2 ≤ ∫ u, W₁ * H u :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => sq_nonneg _))
      (hHint.const_mul W₁) (Filter.Eventually.of_forall hpt)
  -- Fubini for `∫ u, H u`
  have hFint : Integrable (Function.uncurry (fun u y : ℝ => w (u - y) * g y ^ 2))
      (volume.prod volume) := by
    have hcontF : Continuous (fun p : ℝ × ℝ => w (p.1 - p.2) * g p.2 ^ 2) :=
      (hw.comp (continuous_fst.sub continuous_snd)).mul ((hg.pow 2).comp continuous_snd)
    have hFmeas : AEStronglyMeasurable
        (Function.uncurry (fun u y : ℝ => w (u - y) * g y ^ 2)) (volume.prod volume) :=
      hcontF.aestronglyMeasurable
    refine (MeasureTheory.integrable_prod_iff hFmeas).2 ⟨?_, ?_⟩
    · filter_upwards with u
      exact hint_prod2 u
    · have habsw : Continuous (fun x : ℝ => ‖w x‖) := hw.norm
      have hcsw : HasCompactSupport (fun x : ℝ => ‖w x‖) := hwcs.norm
      have hconvi : Integrable (MeasureTheory.convolution (fun x : ℝ => ‖w x‖)
          (fun y : ℝ => g y ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume) volume :=
        ((hcsw.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) habsw
            hg2cont.locallyIntegrable)).integrable_of_hasCompactSupport
          (HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℝ) hcsw hg2cs)
      refine hconvi.congr ?_
      filter_upwards with u
      rw [MeasureTheory.convolution_mul_swap]
      apply integral_congr_ae
      filter_upwards with y
      rw [show Function.uncurry (fun u y : ℝ => w (u - y) * g y ^ 2) (u, y)
            = w (u - y) * g y ^ 2 from rfl,
          norm_mul, Real.norm_of_nonneg (sq_nonneg (g y))]
  have hHint_eq : ∫ u, H u = ∫ y, ∫ u, w (u - y) * g y ^ 2 := by
    rw [show (∫ u, H u) = ∫ u, ∫ y, w (u - y) * g y ^ 2 from by
      apply integral_congr_ae
      filter_upwards with u
      rw [hHswap u]]
    exact integral_integral_swap hFint
  have hHval : ∫ u, H u = W₁ * G₂ := by
    rw [hHint_eq]
    have hinner : ∀ y : ℝ, ∫ u, w (u - y) * g y ^ 2 = W₁ * g y ^ 2 := by
      intro y
      rw [integral_mul_const]
      rw [hW₁, integral_sub_right_eq_self w y]
    rw [show (∫ y, ∫ u, w (u - y) * g y ^ 2) = ∫ y, W₁ * g y ^ 2 from by
      apply integral_congr_ae
      filter_upwards with y
      exact hinner y]
    rw [integral_const_mul, hG₂]
  calc ∫ u, (∫ y, w (u - y) * g y) ^ 2
      = ∫ u, K u ^ 2 := by
        apply integral_congr_ae
        filter_upwards with u
        rw [hKswap u]
    _ ≤ ∫ u, W₁ * H u := hmono
    _ = W₁ * (W₁ * G₂) := by rw [integral_const_mul, hHval]
    _ = (∫ z, w z) ^ 2 * ∫ y, g y ^ 2 := by rw [hW₁, hG₂]; ring

/-- **`L²` mass of the §10 test function** `f = testfun N W B ψ₁ ψ₂ ψ' = ψ'·RtildeSq W N B ψ₁ ψ₂`, with the constant *uniform* in `N, W, B, K`.  With `g u' = ψ₂ u' ‖Rfun W u'‖²` and the non-negative weight `w u' = (N B) ψ₁ ((N B)(u-u'))` (whose `u'`-integral is `∫ψ₁`), the weighted Cauchy--Schwarz inequality `(∫ w g)² ≤ (∫w)(∫ w g²)` gives
`RtildeSq u ² ≤ (∫ψ₁) · ∫ (N B) ψ₁((N B)(u-u')) ψ₂ u'² ‖Rfun W u'‖⁴ du'`,
and Fubini (all integrands non-negative) gives `∫_ℝ RtildeSq² ≤ (∫ψ₁)² ∫ ψ₂ u² ‖Rfun W u‖⁴ du ≤ (∫ψ₁)² (sup ψ₂)² ∫_{1/16}^{16}‖Rfun W v‖⁴ dv` since `supp ψ₂ ⊆ [1/16,16]`.  Multiplying by `ψ'` costs `(sup ψ')²`, so for an absolute `C > 0` (depending only on the three bumps) one has `∫_ℝ f² ≤ C·K` whenever `0 ≤ N B` and `∫_{1/16}^{16}‖Rfun W v‖⁴ dv ≤ K`. -/
theorem prop101_integral_testfun_sq_le (ψ₁ ψ₂ ψ' : ℝ → ℝ) (hψ₁ : IsBumpAtZero ψ₁ 16)
    (hψ₂ : IsBumpAtOne ψ₂ 16) (hψ' : IsBumpAtOne ψ' 16) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (W : Finset ℝ) (B K : ℝ),
      0 ≤ (N : ℝ) * B → (∫ v in (1 / 16 : ℝ)..16, ‖Submission.GM.Rfun W v‖ ^ 4 ≤ K) →
      ∫ u, (testfun N W B ψ₁ ψ₂ ψ' u) ^ 2 ≤ C * K := by
  -- the bounds `|ψ₂| ≤ c₂` and `|ψ'| ≤ c'` coming from the `j = 0` derivative bounds
  obtain ⟨c₂, hc₂0, hc₂⟩ := hψ₂.2.2.2.2 0
  simp only [iteratedDeriv_zero] at hc₂
  obtain ⟨c', hc'0, hc'⟩ := hψ'.2.2.2.2 0
  simp only [iteratedDeriv_zero] at hc'
  set S₁ : ℝ := ∫ x, ψ₁ x with hS₁def
  have hCnonneg : 0 ≤ c' ^ 2 * S₁ ^ 2 * c₂ ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg c') (sq_nonneg S₁)) (sq_nonneg c₂)
  refine ⟨c' ^ 2 * S₁ ^ 2 * c₂ ^ 2 + 1, by linarith, ?_⟩
  · intro N W B K hB0 hintK
    have hK0 : 0 ≤ K := by
      have h1 := intervalIntegral.integral_nonneg_of_forall (μ := volume) (a := (1 / 16 : ℝ))
        (b := 16) (by norm_num) (fun v : ℝ => pow_nonneg (norm_nonneg (Rfun W v)) 4)
      linarith
    by_cases hB : (N : ℝ) * B = 0
    · -- degenerate case: the kernel vanishes identically
      have hR : ∀ u : ℝ, RtildeSq W N B ψ₁ ψ₂ u = 0 := by
        intro u
        rw [RtildeSq]
        have hz : ∀ u' : ℝ,
            (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u')) * ψ₂ u' * ‖Rfun W u'‖ ^ 2 = 0 := by
          intro u'
          rw [hB]
          ring
        rw [show (fun u' : ℝ =>
              (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u')) * ψ₂ u' * ‖Rfun W u'‖ ^ 2)
            = (fun _ => (0 : ℝ)) from funext hz]
        simp
      have htf : ∀ u : ℝ, testfun N W B ψ₁ ψ₂ ψ' u = 0 := by
        intro u
        simp only [testfun, hR u, mul_zero]
      calc ∫ u, (testfun N W B ψ₁ ψ₂ ψ' u) ^ 2
          = ∫ u, (0 : ℝ) := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
            change testfun N W B ψ₁ ψ₂ ψ' u ^ 2 = (0 : ℝ)
            rw [htf u]
            ring
        _ = 0 := by simp
        _ ≤ (c' ^ 2 * S₁ ^ 2 * c₂ ^ 2 + 1) * K :=
            mul_nonneg (by linarith) hK0
    · have hBpos : 0 < (N : ℝ) * B := lt_of_le_of_ne hB0 (Ne.symm hB)
      -- the kernel `w` and the weight `g`
      set w : ℝ → ℝ := fun y => (N : ℝ) * B * ψ₁ ((N : ℝ) * B * y) with hwdef
      set g : ℝ → ℝ := fun y => ψ₂ y * ‖Rfun W y‖ ^ 2 with hgdef
      have hwcont : Continuous w := by
        rw [hwdef]
        exact (continuous_const : Continuous fun _ : ℝ => (N : ℝ) * B).mul
          (hψ₁.1.continuous.comp (continuous_const.mul continuous_id))
      have hwcs : HasCompactSupport w := by
        rw [hwdef]
        refine HasCompactSupport.intro
          (K := Set.Icc (-(16 / ((N : ℝ) * B))) (16 / ((N : ℝ) * B))) isCompact_Icc
          (fun y hy => ?_)
        have hzero : ψ₁ ((N : ℝ) * B * y) = 0 := by
          by_contra hne
          have h1 : |(N : ℝ) * B * y| ≤ 16 := hψ₁.2.2.1 _ hne
          rw [abs_mul, abs_of_pos hBpos] at h1
          have h2 : |y| ≤ 16 / ((N : ℝ) * B) := by
            rw [le_div_iff₀ hBpos]
            linarith
          exact hy (by
            rw [Set.mem_Icc]
            exact ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩)
        rw [hzero, mul_zero]
      have hw0 : ∀ y, 0 ≤ w y := by
        intro y
        rw [hwdef]
        exact mul_nonneg hB0 (hψ₁.2.1 _)
      have hgcont : Continuous g := by
        rw [hgdef]
        exact gSq_continuous ψ₂ 16 (by norm_num) hψ₂ W
      have hgcs : HasCompactSupport g := by
        rw [hgdef]
        refine HasCompactSupport.intro (K := Set.Icc (1 / 16 : ℝ) 16) isCompact_Icc
          (fun y hy => ?_)
        have hzero : ψ₂ y = 0 := by
          by_contra hne
          exact hy (hψ₂.2.2.1 y hne)
        rw [hzero, zero_mul]
      have hg0 : ∀ y, 0 ≤ g y := by
        intro y
        rw [hgdef]
        exact mul_nonneg (hψ₂.2.1 _) (pow_nonneg (norm_nonneg _) 2)
      -- pointwise identification of `RtildeSq` with the convolution of `w` and `g`
      have hpt : ∀ u : ℝ, RtildeSq W N B ψ₁ ψ₂ u = ∫ y, w (u - y) * g y := by
        intro u
        rw [RtildeSq]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        rw [hwdef, hgdef]
        ring
      -- `∫ w = ∫ ψ₁`
      have hwint : ∫ z, w z = S₁ := by
        rw [hwdef, hS₁def, integral_const_mul]
        rw [Measure.integral_comp_mul_left ψ₁ ((N : ℝ) * B)]
        rw [abs_of_pos (inv_pos.mpr hBpos), smul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ hBpos.ne', one_mul]
      -- `∫ g² = ∫ ψ₂² ‖R‖⁴`
      have hgsq : ∫ y, g y ^ 2 = ∫ y, ψ₂ y ^ 2 * ‖Rfun W y‖ ^ 4 := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        rw [hgdef]
        ring
      have hconv := prop101_sq_conv_le hwcont hwcs hgcont hgcs hw0 hg0
      have hstep1 : ∫ u, (RtildeSq W N B ψ₁ ψ₂ u) ^ 2
          = ∫ u, (∫ y, w (u - y) * g y) ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        simp only [hpt u]
      have hstep2 : ∫ y, g y ^ 2 ≤ c₂ ^ 2 * K := by
        rw [hgsq]
        exact (integral_psi2_sq_le ψ₂ hψ₂ c₂ hc₂0 hc₂ W).trans
          (mul_le_mul_of_nonneg_left hintK (sq_nonneg c₂))
      have hRsq : ∫ u, (RtildeSq W N B ψ₁ ψ₂ u) ^ 2 ≤ S₁ ^ 2 * (c₂ ^ 2 * K) := by
        rw [hstep1]
        refine hconv.trans ?_
        rw [hwint]
        exact mul_le_mul_of_nonneg_left hstep2 (sq_nonneg S₁)
      -- `RtildeSq` is continuous with compact support, so its square is integrable
      have hRcont : Continuous (fun u : ℝ => RtildeSq W N B ψ₁ ψ₂ u) :=
        RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂
      have hRzero : ∀ u ∉ Set.Icc (1 / 16 - 16 / ((N : ℝ) * B)) (16 + 16 / ((N : ℝ) * B)),
          RtildeSq W N B ψ₁ ψ₂ u = 0 :=
        fun u hu => RtildeSq_eq_zero_of_notMem (c := 16) (a := 1 / 16) (b := 16) (by norm_num)
          (fun x hx => hψ₁.2.2.1 x hx) (fun x hx => hψ₂.2.2.1 x hx) hBpos hu
      have hint2 : Integrable (fun u : ℝ => (RtildeSq W N B ψ₁ ψ₂ u) ^ 2) := by
        have hcs : HasCompactSupport (fun u : ℝ => (RtildeSq W N B ψ₁ ψ₂ u) ^ 2) :=
          HasCompactSupport.intro isCompact_Icc (fun u hu => by rw [hRzero u hu]; ring)
        exact (hRcont.pow 2).integrable_of_hasCompactSupport hcs
      -- multiply by `ψ'`
      have htest1 : ∫ u, (testfun N W B ψ₁ ψ₂ ψ' u) ^ 2
          ≤ ∫ u, c' ^ 2 * RtildeSq W N B ψ₁ ψ₂ u ^ 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => sq_nonneg _))
          (hint2.const_mul (c' ^ 2)) (Filter.Eventually.of_forall (fun u => ?_))
        have h1 := abs_le.mp (hc' u)
        have h2 : ψ' u ^ 2 ≤ c' ^ 2 := by nlinarith [h1.1, h1.2]
        simp only [testfun, mul_pow]
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      have htest : ∫ u, (testfun N W B ψ₁ ψ₂ ψ' u) ^ 2
          ≤ c' ^ 2 * ∫ u, (RtildeSq W N B ψ₁ ψ₂ u) ^ 2 :=
        htest1.trans (le_of_eq (integral_const_mul (c' ^ 2)
          (fun u : ℝ => RtildeSq W N B ψ₁ ψ₂ u ^ 2)))
      calc ∫ u, (testfun N W B ψ₁ ψ₂ ψ' u) ^ 2
          ≤ c' ^ 2 * ∫ u, (RtildeSq W N B ψ₁ ψ₂ u) ^ 2 := htest
        _ ≤ c' ^ 2 * (S₁ ^ 2 * (c₂ ^ 2 * K)) := mul_le_mul_of_nonneg_left hRsq (sq_nonneg c')
        _ = (c' ^ 2 * S₁ ^ 2 * c₂ ^ 2) * K := by ring
        _ ≤ (c' ^ 2 * S₁ ^ 2 * c₂ ^ 2 + 1) * K :=
            mul_le_mul_of_nonneg_right (by linarith) hK0

end Work.GM.S3
