import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cubic smooth box-localization function χ (Layer 5, brick B1)

The Fournais--Solovej box analysis (final_v2.tex, Appendix `sec:chiproperties`
and Section 5 onward) uses an explicit localization function `χ : ℝ³ → ℝ`
with

  (P1)  0 ≤ χ,   supp χ ⊆ [−1/2,1/2]³,   χ even;
  (P2)  ∫ χ² = 1   (L²-normalization ⇒ (χ*χ)(0) = 1);
  (P3)  χ is C^∞ on ℝ³  (in Lean: `ContDiff ℝ ∞ χ`; note `ContDiff ℝ ⊤` would mean real-analytic — NOT intended);
  (P4)  ∃ r₀ > 0, ∀ x with ‖x‖ ≤ r₀:  (χ*χ)(x) ≥ 1/2;
  (P5)  ∃ C ≥ 0, ∀ x,y in a neighbourhood of 0:
        |(χ*χ)(x) − (χ*χ)(y)| ≤ C·‖x−y‖ · max(‖x‖,‖y‖)
        (Lipschitz-type bound on the convolution at the origin, from
        smoothness of χ*χ — enough for the Taylor estimate
        |(χ*χ)(x) − 1| ≤ C′(R/ℓ)² on supp v ⊆ ball 0 R used in eq:W1-g).

All that matters for the kernel identities (eq:DefU, eq:w2int, eq:W1-g,
lem:Convolution) is that such a `χ` exists — no explicit formula is needed.
The classical construction: 1D `b(t) := c·exp(−1/(1−4t²))` on `|t| < 1/2`,
zero outside, rescaled so that ∫b² = 1 (or any even C^∞ bump with cubic
support), then `χ(x) := b(x₁)b(x₂)b(x₃)`.

This module packages the construction on `EuclideanSpace ℝ (Fin 3)`.  The
convolution is the Lebesgue convolution `(f*g)(x) := ∫ y, f(y)·g(x−y)`.
Constants are existential; no attempt is made to optimise them.

(Note: `χ(x/ℓ)` scalings and the `W₁ = g/(χ*χ(·/ℓ))` well-definedness follow
from P4 applied at `x/ℓ` with `ℓ` large — see the layer-5 notes.)
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real Convolution

namespace Submission.BoseGases

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Lebesgue convolution of two real functions on `ℝ³`. -/
noncomputable def conv3 (f g : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  ∫ y : ℝ³, f y * g (x - y)

noncomputable def chiBump : ContDiffBump (0 : ℝ³) :=
  { rIn := 1 / 4, rOut := 1 / 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

noncomputable def chiBase (x : ℝ³) : ℝ := chiBump x

noncomputable def chiNormSq : ℝ := ∫ x : ℝ³, (chiBase x) ^ 2

noncomputable def chi (x : ℝ³) : ℝ := chiBase x / Real.sqrt chiNormSq

-- ============ basic bump properties ============

lemma chiBase_nonneg (x : ℝ³) : 0 ≤ chiBase x := chiBump.nonneg

lemma chiBase_even (x : ℝ³) : chiBase (-x) = chiBase x := chiBump.neg x

lemma chiBase_eq_zero_of_norm_gt (x : ℝ³) (hx : 1 / 2 < ‖x‖) : chiBase x = 0 := by
  have hx' : chiBump.rOut ≤ dist x (0 : ℝ³) := by
    simpa [chiBump, dist_eq_norm] using le_of_lt hx
  exact chiBump.zero_of_le_dist hx' 

lemma chiBase_eq_one_of_norm_le {x : ℝ³} (hx : ‖x‖ ≤ 1 / 4) : chiBase x = 1 := by
  apply chiBump.one_of_mem_closedBall (x := x)
  simpa [chiBump, dist_eq_norm] using hx

lemma chiBase_zero : chiBase 0 = 1 := by
  simpa using (chiBase_eq_one_of_norm_le (x := 0) (by norm_num))

lemma chiBase_contDiff : ContDiff ℝ ∞ chiBase := chiBump.contDiff

lemma chiBase_continuous : Continuous chiBase := chiBump.continuous

lemma chiBase_hasCompactSupport : HasCompactSupport chiBase := chiBump.hasCompactSupport

lemma chiBase_sq_eq_one_of_norm_le {x : ℝ³} (hx : ‖x‖ ≤ 1 / 4) : (chiBase x) ^ 2 = 1 := by
  rw [chiBase_eq_one_of_norm_le hx]; norm_num

lemma chiBase_le_one (x : ℝ³) : chiBase x ≤ 1 := chiBump.le_one
-- ============ normalization (chiNormSq > 0) ============

lemma chiBase_sq_continuous : Continuous (fun x : ℝ³ => (chiBase x) ^ 2) := by
  exact chiBase_continuous.pow 2

lemma chiBase_sq_hasCompactSupport : HasCompactSupport (fun x : ℝ³ => (chiBase x) ^ 2) := by
  refine HasCompactSupport.mono chiBase_hasCompactSupport ?_
  intro x hx
  exact fun hb => hx (by simp [hb])

lemma chiBase_sq_zero_ne_zero : (fun x : ℝ³ => (chiBase x) ^ 2) 0 ≠ 0 := by
  simp [chiBase_zero]

lemma chiNormSq_pos : 0 < chiNormSq := by
  dsimp [chiNormSq]
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (f := fun x : ℝ³ => (chiBase x) ^ 2) (x := 0)
    chiBase_sq_continuous chiBase_sq_hasCompactSupport (by intro x; exact sq_nonneg (chiBase x))
    chiBase_sq_zero_ne_zero

lemma chiNormSq_ne_zero : chiNormSq ≠ 0 := ne_of_gt chiNormSq_pos

lemma chi_sqrt_ne_zero : Real.sqrt chiNormSq ≠ 0 := by
  have h : 0 < Real.sqrt chiNormSq := Real.sqrt_pos.mpr chiNormSq_pos
  exact ne_of_gt h

-- ============ properties of chi ============

lemma chi_nonneg (x : ℝ³) : 0 ≤ chi x := by
  unfold chi
  exact div_nonneg (chiBase_nonneg x) (le_of_lt (Real.sqrt_pos.mpr chiNormSq_pos))

lemma chi_even (x : ℝ³) : chi (-x) = chi x := by
  unfold chi
  rw [chiBase_even]

lemma chi_eq_zero_of_norm_gt (x : ℝ³) (hx : 1 / 2 < ‖x‖) : chi x = 0 := by
  unfold chi
  rw [chiBase_eq_zero_of_norm_gt x hx]
  ring

lemma chi_contDiff : ContDiff ℝ ∞ chi := by
  have hs : ContDiff ℝ ∞ (fun x : ℝ³ => (Real.sqrt chiNormSq)⁻¹ • chiBase x) :=
    ContDiff.const_smul (Real.sqrt chiNormSq)⁻¹ chiBase_contDiff
  convert hs using 1
  ext x
  simp [chi, div_eq_mul_inv, smul_eq_mul, mul_comm]

lemma chi_continuous : Continuous chi := chi_contDiff.continuous

lemma chi_hasCompactSupport : HasCompactSupport chi := by
  refine HasCompactSupport.mono chiBase_hasCompactSupport ?_
  intro x hx
  by_contra hb
  have hb0 : chiBase x = 0 := by simpa using hb
  exact hx (by simp [chi, hb0])

lemma chi_L2 : (∫ x : ℝ³, (chi x) ^ 2) = 1 := by
  have hZpos : 0 ≤ chiNormSq := le_of_lt chiNormSq_pos
  have hZ : (Real.sqrt chiNormSq) ^ 2 = chiNormSq := Real.sq_sqrt hZpos
  calc
    (∫ x : ℝ³, (chi x) ^ 2) = ∫ x : ℝ³, (chiBase x) ^ 2 / chiNormSq := by
      apply integral_congr_ae
      exact ae_of_all _ (by
        intro x
        dsimp
        rw [chi, div_pow, hZ])
    _ = (∫ x : ℝ³, (chiBase x) ^ 2) / chiNormSq := by
      rw [integral_div]
    _ = 1 := by
      dsimp [chiNormSq]
      exact div_self chiNormSq_ne_zero

lemma conv3_at_zero : conv3 chi chi 0 = 1 := by
  unfold conv3
  calc
    (∫ y : ℝ³, chi y * chi (0 - y)) = ∫ y : ℝ³, (chi y) ^ 2 := by
      apply integral_congr_ae
      exact ae_of_all _ (by intro y; simp [chi_even y, pow_two])
    _ = 1 := chi_L2


-- ============ convolution smoothness ============

lemma conv3_eq_convolution (f g : ℝ³ → ℝ) :
    conv3 f g = f ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g := by
  funext x
  unfold conv3
  rw [convolution_lsmul]
  apply integral_congr_ae
  exact ae_of_all _ (by intro y; simp)

lemma chi_locallyIntegrable : LocallyIntegrable chi := by
  exact chi_continuous.locallyIntegrable

lemma conv_contDiff : ContDiff ℝ ∞ (fun x : ℝ³ => conv3 chi chi x) := by
  have h := HasCompactSupport.contDiff_convolution_right
    (G := ℝ³) (E := ℝ) (E' := ℝ) (F := ℝ) (𝕜 := ℝ)
    (f := chi) (g := chi) (μ := volume)
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (n := ⊤)
    chi_hasCompactSupport chi_locallyIntegrable chi_contDiff
  simpa [conv3_eq_convolution chi chi] using h


-- ============ generic consequences (P4, P5) ============

lemma half_lower_ball_of_continuousAt_one {h : ℝ³ → ℝ} (hc : ContinuousAt h 0) (h0 : h 0 = 1) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ h x := by
  rw [Metric.continuousAt_iff] at hc
  rcases hc (1 / 2) (by norm_num) with ⟨δ, hδpos, hδ⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  intro x hx
  have hxδ : dist x 0 < δ := by
    have : ‖x‖ < δ := lt_of_le_of_lt hx (half_lt_self hδpos)
    simpa [dist_eq_norm] using this
  have hnear : dist (h x) (h 0) < 1 / 2 := hδ hxδ
  have habs : |h x - 1| < 1 / 2 := by simpa [h0, Real.dist_eq] using hnear
  have hgt : 1 / 2 < h x := by
    have := (abs_lt.mp habs).1
    linarith
  exact le_of_lt hgt

lemma lipschitz_ball_of_contDiffAt_one {h : ℝ³ → ℝ} (hcd : ContDiffAt ℝ 1 h 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r₁ : ℝ, 0 < r₁ ∧
      ∀ x y : ℝ³, ‖x‖ ≤ r₁ → ‖y‖ ≤ r₁ → |h x - h y| ≤ C * ‖x - y‖ := by
  rcases ContDiffAt.exists_lipschitzOnWith (f := h) (x := 0) hcd with ⟨K, t, ht, hlip⟩
  rcases (Metric.mem_nhds_iff.mp ht) with ⟨ε, hεpos, hball⟩
  refine ⟨(K : ℝ), K.2, ε / 2, by positivity, ?_⟩
  intro x y hx hy
  have hxε : ‖x‖ < ε := lt_of_le_of_lt hx (half_lt_self hεpos)
  have hyε : ‖y‖ < ε := lt_of_le_of_lt hy (half_lt_self hεpos)
  have hxt : x ∈ t := hball (by simpa [dist_eq_norm] using hxε)
  have hyt : y ∈ t := hball (by simpa [dist_eq_norm] using hyε)
  have hd := (lipschitzOnWith_iff_dist_le_mul.mp hlip) x hxt y hyt
  simpa [Real.dist_eq, dist_eq_norm] using hd

-- ============ main theorem ============

theorem exists_cubic_chi :
    ∃ χ : ℝ³ → ℝ,
      (∀ x, 0 ≤ χ x) ∧
      (∀ x, ‖x‖ > 1 / 2 → χ x = 0) ∧
      (∀ x, χ (-x) = χ x) ∧
      (∫ x : ℝ³, (χ x) ^ 2) = 1 ∧
      ContDiff ℝ ∞ χ ∧
      (conv3 χ χ 0 = 1) ∧
      (∃ r₀ : ℝ, 0 < r₀ ∧ ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 χ χ x) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∃ r₁ : ℝ, 0 < r₁ ∧
        ∀ x y : ℝ³, ‖x‖ ≤ r₁ → ‖y‖ ≤ r₁ →
          |conv3 χ χ x - conv3 χ χ y| ≤ C * ‖x - y‖) := by
  refine ⟨chi, chi_nonneg, chi_eq_zero_of_norm_gt, chi_even, chi_L2, chi_contDiff, conv3_at_zero, ?_, ?_⟩
  · refine half_lower_ball_of_continuousAt_one ?_ conv3_at_zero
    exact (conv_contDiff.continuous).continuousAt
  · refine lipschitz_ball_of_contDiffAt_one ?_
    have hca : ContDiffAt ℝ ∞ (fun x : ℝ³ => conv3 chi chi x) 0 :=
      (contDiff_iff_contDiffAt.mp conv_contDiff) 0
    exact ContDiffAt.of_le (m := 1) (n := ∞) hca (by norm_num)

end Submission.BoseGases
