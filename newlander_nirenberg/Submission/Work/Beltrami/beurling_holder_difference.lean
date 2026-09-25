/-
# Hölder (Schauder) estimate for the Beurling transform

The Beurling transform `beurling f` (`Submission/Work/Beltrami/Cauchy.lean`) is the
`∂`-derivative of the Cauchy potential; it is a Calderón–Zygmund operator with regularised
kernel `(f ζ - bumpC (ζ-z) f z) (ζ-z)⁻²`.  This file proves that it maps bounded `α`-Hölder
functions supported in the ball of radius `R` to `α`-Hölder functions, with constant
`C (M+K) (1+R)`.

The proof follows the classical Calderón–Zygmund scheme.  For `δ = ‖x-y‖ ≤ 1` one writes the
difference of the integrands as

  `(f ζ - f x) ((ζ-x)⁻² - (ζ-y)⁻²) + f x (W (ζ-x) - W (ζ-y)) - (f x - f y) bumpC (ζ-y) (ζ-y)⁻²`

where `W w = (1 - bumpC w) w⁻²` is the smooth regularised kernel.  The plane is split into the
two discs `B(x,2δ)`, `B(y,2δ)` (where the pointwise size of the integrand is used) and the far
region, where the three terms are estimated by
`Work.Beltrami.Holder.far_kernel_diff_bound`, `Work.Beltrami.Holder.W_translate_L1_bound` and
`Work.Beltrami.Holder.far_chi_term_bound` respectively.  For `δ ≥ 1` the pointwise bound
`Work.Beltrami.beurling_bounded` is used.
-/
import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.Wkernel
import Submission.Work.Beltrami.HolderAux
import Submission.Work.Beltrami.beurling_bounded
import Submission.Work.Beltrami.integrable_bI
import Submission.Work.Beltrami.norm_inv_sq_sub_inv_sq_le
import Submission.Work.Beltrami.integral_ball_norm_bI_le
import Submission.Work.CR.Flat.Cauchy.norm_cauchyTransform_sub_le
import Submission.Work.Beltrami.Holder.W_translate_L1_bound
import Submission.Work.Beltrami.Holder.far_chi_term_bound
import Submission.Work.Beltrami.Holder.far_kernel_diff_bound

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Work.Beltrami


/-- Bound for the norm of a set integral by an integrable pointwise majorant. -/
lemma norm_setIntegral_le_of_norm_le {s : Set ℂ} (hs : MeasurableSet s) {F : ℂ → ℂ}
    {g : ℂ → ℝ} (hg : IntegrableOn g s volume) (h : ∀ x ∈ s, ‖F x‖ ≤ g x) :
    ‖∫ x in s, F x‖ ≤ ∫ x in s, g x :=
  norm_integral_le_of_norm_le (μ := volume.restrict s) hg
    ((MeasureTheory.ae_restrict_iff' hs).mpr (Filter.Eventually.of_forall h))

/-- Schauder (Calderón–Zygmund) Hölder estimate for the Beurling transform
`Work.Beltrami.beurling` (defined with the smooth cutoff `bumpC`): for `f` bounded by `M`,
`α`-Hölder with constant `K` (`0 < α < 1`) and supported in the ball of radius `R`,
`‖beurling f x - beurling f y‖ ≤ C (M+K) (1+R) ‖x - y‖^α` with `C` depending only on `α`.

Suggested route for `δ = ‖x-y‖ ≤ 1`.  Write the difference of the integrands as
`(f u - f x) * ((u-x)⁻² - (u-y)⁻²) + f x * (W (u-x) - W (u-y)) - (f x - f y) * χ(u-y) * (u-y)⁻²`,
where `χ = bumpC` and `W w = (1 - χ w) * w⁻²`.
Split the plane into `{‖u-x‖ ≤ 2δ}` (near `x`), `{‖u-y‖ ≤ 2δ}` (near `y`) and the far region:
on the far region the first term is bounded by `6 K δ ‖u-x‖^{α-3}` (integral `≤ C K δ^α`), the
second by `M` times the difference of translates of `W` (bound `≤ C M δ` via the fundamental
identity `W (u-x) - W (u-y) = ∫_0^1 fderiv W (u-x+t(x-y)) (x-y) dt` and Tonelli with
`∫_ℂ ‖fderiv W‖ < ∞`), and the third by `K δ^α` times the mean-zero of `χ w * w⁻²` over the
annulus `{2δ ≤ ‖w‖ < 1}` (rotation argument: `(I*w)⁻² = -w⁻²` and `χ` is radial; note the existing
`Work.CR.Flat.Cauchy.integral_inv_sq_annulus`), plus the crude bound on the lens
`{2δ ≤ ‖u-y‖ < 1, ‖u-x‖ ≤ 2δ}`.  On the two near discs use `|G_x| + |G_y|` with the pointwise
bounds `‖G_z(u)‖ ≤ (K ‖u-z‖^α + M · 1{1/2 ≤ ‖u-z‖}) ‖u-z‖^{-2}`.  For `δ ≥ 1` combine the
pointwise bounds at `x` and at `y`.
Useful existing lemmas: `Work.CR.Flat.Cauchy.integral_norm_rpow_ball`,
`Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball`. -/
theorem beurling_holder_difference {α M K R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R)
    (f : ℂ → ℂ) (hM : ∀ z, ‖f z‖ ≤ M) (hK : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R < ‖z‖ → f z = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℂ,
      ‖Work.Beltrami.beurling f x - Work.Beltrami.beurling f y‖
        ≤ C * (M + K) * (1 + R) * ‖x - y‖ ^ α := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  have hK0 : 0 ≤ K := by
    have h := hK 0 1
    rw [show (0 : ℂ) - 1 = -(1 : ℂ) from by ring, norm_neg, norm_one, Real.one_rpow,
      mul_one] at h
    linarith [norm_nonneg (f 0 - f 1)]
  -- the three analytic ingredients
  obtain ⟨C₂, hC₂pos, hC₂⟩ := beurling_bounded hα hα1 hR f hM hK hsupp
  have hC₁ : ∀ z : ℂ, ∀ ρ : ℝ, 0 < ρ →
      ∫ ζ in Metric.ball z ρ,
          ‖(f ζ - (bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹‖ ∂volume
        ≤ 2 * Real.pi * K * ρ ^ α / α + 4 * Real.pi * M * ρ ^ 2 :=
    fun z ρ hρ => integral_ball_norm_bI_le (α := α) (K := K) (M := M) hα hK0 hM0 hM hK z hρ
  obtain ⟨C₃, hC₃pos, hC₃⟩ := Holder.W_translate_L1_bound
  -- the constants of the two regimes
  set Cnear : ℝ := 12 * Real.pi / α + 72 * Real.pi with hCnear
  set Cfar : ℝ := 12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi with hCfar
  have hCnear0 : 0 ≤ Cnear := by rw [hCnear]; positivity
  have hCfar0 : 0 ≤ Cfar := by rw [hCfar]; positivity
  refine ⟨max (Cnear + Cfar) (2 * C₂) + 1, by positivity, ?_⟩
  intro x y
  by_cases hxy : x = y
  · subst hxy
    have hzero : ‖x - x‖ ^ α = 0 := by
      rw [sub_self, norm_zero, Real.zero_rpow (ne_of_gt hα)]
    rw [sub_self, norm_zero, hzero, mul_zero]
  by_cases hδle : ‖x - y‖ ≤ 1
  · -- ================= main case: `δ ≤ 1` =================
    set δ : ℝ := ‖x - y‖ with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hδle1 : δ ≤ 1 := by rw [hδdef]; exact hδle
    have hδpowpos : 0 < δ ^ α := Real.rpow_pos_of_pos hδpos α
    have hδsq_le : δ ^ 2 ≤ δ ^ α := by
      have h1 : δ ≤ δ ^ α := by
        have h2 : δ ^ (1 : ℝ) ≤ δ ^ α :=
          Real.rpow_le_rpow_of_exponent_ge hδpos hδle1 hα1.le
        rwa [Real.rpow_one] at h2
      have h3 : δ ^ 2 ≤ δ := by nlinarith [hδpos, hδle1]
      linarith
    -- the two integrands
    set Ix : ℂ → ℂ := fun ζ => (f ζ - (bumpC (ζ - x) : ℂ) * f x) * ((ζ - x) ^ 2)⁻¹ with hIx
    set Iy : ℂ → ℂ := fun ζ => (f ζ - (bumpC (ζ - y) : ℂ) * f y) * ((ζ - y) ^ 2)⁻¹ with hIy
    have hIntIx : Integrable Ix volume := by
      rw [hIx]; exact integrable_bI hα hK0 hM0 hM hK hsupp x
    have hIntIy : Integrable Iy volume := by
      rw [hIy]; exact integrable_bI hα hK0 hM0 hM hK hsupp y
    have hbeur : ‖beurling f x - beurling f y‖
        = Real.pi⁻¹ * ‖(∫ ζ, Ix ζ ∂volume) - (∫ ζ, Iy ζ ∂volume)‖ := by
      have h1 : beurling f x - beurling f y
          = (-(Real.pi)⁻¹ : ℝ) • ((∫ ζ, Ix ζ ∂volume) - (∫ ζ, Iy ζ ∂volume)) := by
        rw [beurling_apply, beurling_apply, ← hIx, ← hIy, smul_sub]
      rw [h1, norm_smul]
      congr 1
      rw [Real.norm_eq_abs, abs_neg, abs_inv, abs_of_nonneg Real.pi_pos.le]
    -- the regions
    set S : Set ℂ := Metric.ball x (2 * δ) ∪ Metric.ball y (2 * δ) with hS
    have hSmeas : MeasurableSet S := by
      rw [hS]; exact measurableSet_ball.union measurableSet_ball
    have hspos : (0 : ℝ) < 2 * δ := by linarith
    have hSx : S ⊆ Metric.ball x (3 * δ) := by
      intro ζ hζ
      rw [hS] at hζ
      rw [Metric.mem_ball]
      rcases hζ with h | h
      · rw [Metric.mem_ball] at h; linarith
      · rw [Metric.mem_ball] at h
        rw [dist_eq_norm] at h ⊢
        have h1 : ‖ζ - x‖ ≤ ‖ζ - y‖ + ‖y - x‖ := by
          rw [show ζ - x = (ζ - y) + (y - x) from by ring]
          exact norm_add_le _ _
        rw [show ‖y - x‖ = δ from by rw [norm_sub_rev, ← hδdef]] at h1
        linarith
    have hSy : S ⊆ Metric.ball y (3 * δ) := by
      intro ζ hζ
      rw [hS] at hζ
      rw [Metric.mem_ball]
      rcases hζ with h | h
      · rw [Metric.mem_ball] at h
        rw [dist_eq_norm] at h ⊢
        have h1 : ‖ζ - y‖ ≤ ‖ζ - x‖ + ‖x - y‖ := by
          rw [show ζ - y = (ζ - x) + (x - y) from by ring]
          exact norm_add_le _ _
        rw [show ‖x - y‖ = δ from hδdef.symm] at h1
        linarith
      · rw [Metric.mem_ball] at h; linarith
    -- splitting of the integral
    have hsplit : (∫ ζ, Ix ζ ∂volume) - (∫ ζ, Iy ζ ∂volume)
        = (∫ ζ in S, (Ix ζ - Iy ζ) ∂volume) + (∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume) := by
      have h1 : (∫ ζ, Ix ζ ∂volume) - (∫ ζ, Iy ζ ∂volume) = ∫ ζ, (Ix ζ - Iy ζ) ∂volume :=
        (integral_sub hIntIx hIntIy).symm
      rw [h1]
      exact (integral_add_compl hSmeas (hIntIx.sub hIntIy)).symm
    -- ===== near part =====
    have hnear : ‖∫ ζ in S, (Ix ζ - Iy ζ) ∂volume‖ ≤ Cnear * (M + K) * δ ^ α := by
      have h1 : ‖∫ ζ in S, (Ix ζ - Iy ζ) ∂volume‖ ≤ ∫ ζ in S, ‖Ix ζ - Iy ζ‖ ∂volume :=
        norm_integral_le_integral_norm _
      have h2 : ∫ ζ in S, ‖Ix ζ - Iy ζ‖ ∂volume
          ≤ ∫ ζ in S, (‖Ix ζ‖ + ‖Iy ζ‖) ∂volume := by
        refine integral_mono (f := fun ζ => ‖Ix ζ - Iy ζ‖)
          (g := fun ζ => ‖Ix ζ‖ + ‖Iy ζ‖) (hIntIx.sub hIntIy).norm.integrableOn
          (hIntIx.norm.add hIntIy.norm).integrableOn ?_
        exact fun ζ => norm_sub_le (Ix ζ) (Iy ζ)
      have h3 : ∫ ζ in S, (‖Ix ζ‖ + ‖Iy ζ‖) ∂volume
          = (∫ ζ in S, ‖Ix ζ‖ ∂volume) + (∫ ζ in S, ‖Iy ζ‖ ∂volume) :=
        integral_add hIntIx.norm.integrableOn hIntIy.norm.integrableOn
      have h4 : ∫ ζ in S, ‖Ix ζ‖ ∂volume ≤ ∫ ζ in Metric.ball x (3 * δ), ‖Ix ζ‖ ∂volume :=
        setIntegral_mono_set hIntIx.norm.integrableOn
          (Filter.Eventually.of_forall fun ζ => norm_nonneg _)
          (Filter.Eventually.of_forall fun ζ hζ => hSx hζ)
      have h5 : ∫ ζ in S, ‖Iy ζ‖ ∂volume ≤ ∫ ζ in Metric.ball y (3 * δ), ‖Iy ζ‖ ∂volume :=
        setIntegral_mono_set hIntIy.norm.integrableOn
          (Filter.Eventually.of_forall fun ζ => norm_nonneg _)
          (Filter.Eventually.of_forall fun ζ hζ => hSy hζ)
      have h6 : ∫ ζ in Metric.ball x (3 * δ), ‖Ix ζ‖ ∂volume
          ≤ 2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2 := by
        have := hC₁ x (3 * δ) (by linarith)
        simpa only [hIx] using this
      have h7 : ∫ ζ in Metric.ball y (3 * δ), ‖Iy ζ‖ ∂volume
          ≤ 2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2 := by
        have := hC₁ y (3 * δ) (by linarith)
        simpa only [hIy] using this
      have h8 : 2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2
          + (2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2)
          ≤ Cnear * (M + K) * δ ^ α := by
        have hmul : (3 * δ) ^ α = 3 ^ α * δ ^ α := Real.mul_rpow (by norm_num) hδpos.le
        have h32 : (3 * δ) ^ 2 = 9 * δ ^ 2 := by ring
        rw [hCnear, hmul, h32]
        have h3a : (3 : ℝ) ^ α ≤ 3 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hα1.le
        have hA : 2 * Real.pi * K * (3 ^ α * δ ^ α) / α ≤ 6 * Real.pi * K * δ ^ α / α := by
          have hcoef : (0:ℝ) ≤ 2 * Real.pi * K * δ ^ α / α := by positivity
          have h1 : 2 * Real.pi * K * (3 ^ α * δ ^ α) / α
              = (2 * Real.pi * K * δ ^ α / α) * 3 ^ α := by
            rw [div_eq_mul_inv]; ring
          have h2 : (2 * Real.pi * K * δ ^ α / α) * 3 = 6 * Real.pi * K * δ ^ α / α := by
            rw [div_eq_mul_inv]; ring
          rw [h1, ← h2]
          exact mul_le_mul_of_nonneg_left h3a hcoef
        have hB : 4 * Real.pi * M * (9 * δ ^ 2) ≤ 36 * Real.pi * M * δ ^ α := by
          have hcoef : (0:ℝ) ≤ 4 * Real.pi * M * 9 := by positivity
          have h1 : 4 * Real.pi * M * (9 * δ ^ 2) = (4 * Real.pi * M * 9) * δ ^ 2 := by ring
          have h2 : (4 * Real.pi * M * 9) * δ ^ α = 36 * Real.pi * M * δ ^ α := by ring
          rw [h1, ← h2]
          exact mul_le_mul_of_nonneg_left hδsq_le hcoef
        have hfin : 12 * Real.pi * K * δ ^ α / α + 72 * Real.pi * M * δ ^ α
            ≤ (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α := by
          have hK' : K ≤ M + K := by linarith
          have hM' : M ≤ M + K := by linarith
          have h1 : 12 * Real.pi * K * δ ^ α / α ≤ 12 * Real.pi * (M + K) * δ ^ α / α := by
            have hcoef : (0:ℝ) < 12 * Real.pi * δ ^ α / α := by positivity
            have h3 : 12 * Real.pi * K * δ ^ α / α
                = (12 * Real.pi * δ ^ α / α) * K := by rw [div_eq_mul_inv]; ring
            have h4 : 12 * Real.pi * (M + K) * δ ^ α / α
                = (12 * Real.pi * δ ^ α / α) * (M + K) := by rw [div_eq_mul_inv]; ring
            rw [h3, h4]
            exact mul_le_mul_of_nonneg_left hK' hcoef.le
          have h2 : 72 * Real.pi * M * δ ^ α ≤ 72 * Real.pi * (M + K) * δ ^ α := by
            have hcoef : (0:ℝ) ≤ 72 * Real.pi * δ ^ α := by positivity
            have h3 : 72 * Real.pi * M * δ ^ α = (72 * Real.pi * δ ^ α) * M := by ring
            have h4 : 72 * Real.pi * (M + K) * δ ^ α = (72 * Real.pi * δ ^ α) * (M + K) := by ring
            rw [h3, h4]
            exact mul_le_mul_of_nonneg_left hM' hcoef
          have h3 : 12 * Real.pi * (M + K) * δ ^ α / α + 72 * Real.pi * (M + K) * δ ^ α
              = (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α := by
            rw [div_eq_mul_inv]; ring
          linarith
        calc 2 * Real.pi * K * (3 ^ α * δ ^ α) / α + 4 * Real.pi * M * (9 * δ ^ 2)
              + (2 * Real.pi * K * (3 ^ α * δ ^ α) / α + 4 * Real.pi * M * (9 * δ ^ 2))
            ≤ 2 * (6 * Real.pi * K * δ ^ α / α + 36 * Real.pi * M * δ ^ α) := by linarith [hA, hB]
          _ = 12 * Real.pi * K * δ ^ α / α + 72 * Real.pi * M * δ ^ α := by ring
          _ ≤ (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α := hfin
      calc ‖∫ ζ in S, (Ix ζ - Iy ζ) ∂volume‖
          ≤ ∫ ζ in S, ‖Ix ζ - Iy ζ‖ ∂volume := h1
        _ ≤ ∫ ζ in S, (‖Ix ζ‖ + ‖Iy ζ‖) ∂volume := h2
        _ = (∫ ζ in S, ‖Ix ζ‖ ∂volume) + (∫ ζ in S, ‖Iy ζ‖ ∂volume) := h3
        _ ≤ (∫ ζ in Metric.ball x (3 * δ), ‖Ix ζ‖ ∂volume)
              + (∫ ζ in Metric.ball y (3 * δ), ‖Iy ζ‖ ∂volume) := add_le_add h4 h5
        _ ≤ (2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2)
              + (2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2) :=
            add_le_add h6 h7
        _ ≤ Cnear * (M + K) * δ ^ α := h8
    -- ===== far part =====
    set T1 : ℂ → ℂ := fun ζ => (f ζ - f x) * (((ζ - x) ^ 2)⁻¹ - ((ζ - y) ^ 2)⁻¹) with hT1
    set T2 : ℂ → ℂ := fun ζ => f x * (W (ζ - x) - W (ζ - y)) with hT2
    set T3 : ℂ → ℂ := fun ζ => (f y - f x) * ((bumpC (ζ - y) : ℂ) * (((ζ - y) ^ 2)⁻¹)) with hT3
    have hdecomp : ∀ ζ ∈ Sᶜ, Ix ζ - Iy ζ = T1 ζ + T2 ζ + T3 ζ := by
      intro ζ hζ
      have hζx : ζ ≠ x := by
        intro h
        exact hζ (by rw [hS]; exact Or.inl (h ▸ Metric.mem_ball_self hspos))
      have hζy : ζ ≠ y := by
        intro h
        exact hζ (by rw [hS]; exact Or.inr (h ▸ Metric.mem_ball_self hspos))
      have ha : (ζ - x) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hζx)
      have hb : (ζ - y) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hζy)
      simp only [hIx, hIy, hT1, hT2, hT3, W_apply]
      field_simp
      ring
    have hcongr : ∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume
        = ∫ ζ in Sᶜ, (T1 ζ + T2 ζ + T3 ζ) ∂volume :=
      setIntegral_congr_fun hSmeas.compl hdecomp
    have hsubx : Sᶜ ⊆ {ζ : ℂ | 2 * δ ≤ ‖ζ - x‖} := by
      intro ζ hζ
      have h1 : ζ ∉ Metric.ball x (2 * δ) := fun h => hζ (by rw [hS]; exact Or.inl h)
      rwa [Metric.mem_ball, not_lt, dist_eq_norm] at h1
    have hsuby : Sᶜ ⊆ {ζ : ℂ | 2 * δ ≤ ‖ζ - y‖} := by
      intro ζ hζ
      have h1 : ζ ∉ Metric.ball y (2 * δ) := fun h => hζ (by rw [hS]; exact Or.inr h)
      rwa [Metric.mem_ball, not_lt, dist_eq_norm] at h1
    have hfmeas : Measurable f := (Work.CR.Flat.Cauchy.continuous_of_holder hα hK0 hK).measurable
    have hWmeas : Measurable W := W_contDiff.continuous.measurable
    have hIntT1 : IntegrableOn T1 Sᶜ volume := by
      have hmaj : IntegrableOn (fun ζ : ℂ => 6 * K * δ * ‖ζ - x‖ ^ (α - 3)) Sᶜ volume :=
        ((integrableOn_exterior_rpow_shift x hspos (by linarith : α - 3 < -2)).mono_set hsubx
          ).const_mul _
      refine hmaj.mono' ?_ ?_
      · have hm : Measurable fun ζ : ℂ => (f ζ - f x) *
            (((ζ - x) ^ 2)⁻¹ - ((ζ - y) ^ 2)⁻¹) :=
          (hfmeas.sub measurable_const).mul
            ((((measurable_id.sub measurable_const).pow_const 2).inv).sub
              (((measurable_id.sub measurable_const).pow_const 2).inv))
        simpa only [hT1] using hm.aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem hSmeas.compl] with ζ hζ
        have hw : 0 < ‖ζ - x‖ := lt_of_lt_of_le hspos (hsubx hζ)
        have h1 : ‖f ζ - f x‖ ≤ K * ‖ζ - x‖ ^ α := hK ζ x
        have h2 : ‖((ζ - x) ^ 2)⁻¹ - ((ζ - y) ^ 2)⁻¹‖ ≤ 6 * δ / ‖ζ - x‖ ^ 3 := by
          have h3 : 2 * ‖(ζ - x) - (ζ - y)‖ ≤ ‖ζ - x‖ := by
            have hxy' : (ζ - x) - (ζ - y) = y - x := by ring
            rw [hxy', show ‖y - x‖ = δ from by rw [norm_sub_rev, hδdef]]
            exact hsubx hζ
          have h4 := norm_inv_sq_sub_inv_sq_le (u := ζ - x) (v := ζ - y) h3
          rwa [show (ζ - x) - (ζ - y) = y - x from by ring,
            show ‖y - x‖ = δ from by rw [norm_sub_rev, hδdef]] at h4
        have h3 : (‖ζ - x‖ ^ 3 : ℝ)⁻¹ = ‖ζ - x‖ ^ (-3 : ℝ) := by
          rw [← Real.rpow_natCast ‖ζ - x‖ 3, ← Real.rpow_neg hw.le]
          norm_num
        have h4 : ‖ζ - x‖ ^ (α - 3) = ‖ζ - x‖ ^ α * ‖ζ - x‖ ^ (-3 : ℝ) := by
          have hexp : (α : ℝ) - 3 = α + (-3 : ℝ) := by ring
          rw [hexp, Real.rpow_add hw]
        rw [hT1, norm_mul]
        calc ‖f ζ - f x‖ * ‖((ζ - x) ^ 2)⁻¹ - ((ζ - y) ^ 2)⁻¹‖
            ≤ (K * ‖ζ - x‖ ^ α) * (6 * δ / ‖ζ - x‖ ^ 3) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = 6 * K * δ * ‖ζ - x‖ ^ (α - 3) := by
              rw [div_eq_mul_inv, h3, h4]
              ring
    have hIntT2 : IntegrableOn T2 Sᶜ volume := by
      have hmaj : IntegrableOn (fun ζ : ℂ => M * ‖W (ζ - x) - W (ζ - y)‖) Sᶜ volume :=
        (((hC₃ x y).1.norm).const_mul M).integrableOn
      refine hmaj.mono' ?_ ?_
      · have hm : Measurable fun ζ : ℂ => f x * (W (ζ - x) - W (ζ - y)) :=
          measurable_const.mul ((hWmeas.comp (measurable_id.sub measurable_const)).sub
            (hWmeas.comp (measurable_id.sub measurable_const)))
        simpa only [hT2] using hm.aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem hSmeas.compl] with ζ _
        show ‖f x * (W (ζ - x) - W (ζ - y))‖ ≤ M * ‖W (ζ - x) - W (ζ - y)‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    have hbumpmeas : Measurable fun ζ : ℂ => (bumpC (ζ - y) : ℂ) :=
      (Complex.continuous_ofReal.comp bumpC_contDiff.continuous).measurable.comp
        (measurable_id.sub measurable_const)
    have hInvmeas : Measurable fun ζ : ℂ => (((ζ - y) ^ 2)⁻¹) :=
      ((measurable_id.sub measurable_const).pow_const 2).inv
    have hIntT3 : IntegrableOn (fun ζ : ℂ => (bumpC (ζ - y) : ℂ) * (((ζ - y) ^ 2)⁻¹))
        Sᶜ volume := by
      have hbase : Integrable ((Metric.ball y 1).indicator (fun _ : ℂ => (1 : ℝ))) volume :=
        (integrableOn_const (s := Metric.ball y 1) (C := (1 : ℝ)) (by simp) (by norm_num)
          ).integrable_indicator measurableSet_ball
      have hmaj : IntegrableOn (fun ζ : ℂ => ((2 * δ) ^ 2)⁻¹ *
          (Metric.ball y 1).indicator (fun _ : ℂ => (1 : ℝ)) ζ) Sᶜ volume :=
        (hbase.const_mul ((2 * δ) ^ 2)⁻¹).integrableOn
      refine hmaj.mono' ?_ ?_
      · exact (hbumpmeas.mul hInvmeas).aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem hSmeas.compl] with ζ hζ
        have h1 : 2 * δ ≤ ‖ζ - y‖ := hsuby hζ
        by_cases h2 : ‖ζ - y‖ < 1
        · rw [Set.indicator_of_mem (by rw [Metric.mem_ball, dist_eq_norm]; exact h2), mul_one]
          have h3 : ‖(bumpC (ζ - y) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpC_nonneg _)]
            exact bumpC_le_one _
          have h4 : ‖(((ζ - y) ^ 2)⁻¹)‖ ≤ ((2 * δ) ^ 2)⁻¹ := by
            rw [norm_inv, norm_pow]
            have h5 : (2 * δ) ^ 2 ≤ ‖ζ - y‖ ^ 2 := by nlinarith
            exact inv_anti₀ (by positivity) h5
          rw [norm_mul]
          calc ‖(bumpC (ζ - y) : ℂ)‖ * ‖(((ζ - y) ^ 2)⁻¹)‖ ≤ 1 * ((2 * δ) ^ 2)⁻¹ :=
                mul_le_mul h3 h4 (norm_nonneg _) (by norm_num)
            _ = ((2 * δ) ^ 2)⁻¹ := one_mul _
        · have h3 : bumpC (ζ - y) = 0 := bumpC_eq_zero (le_of_not_gt h2)
          rw [Set.indicator_of_notMem (by rw [Metric.mem_ball, dist_eq_norm]; exact h2),
            mul_zero, h3, Complex.ofReal_zero, zero_mul, norm_zero]
    have hfar : ‖∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume‖ ≤ Cfar * (M + K) * δ ^ α := by
      rw [hcongr]
      have hsplit2 : ∫ ζ in Sᶜ, (T1 ζ + T2 ζ + T3 ζ) ∂volume
          = (∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume)
            + (∫ ζ in Sᶜ, T3 ζ ∂volume) := by
        have h1 : ∫ ζ in Sᶜ, (T1 ζ + T2 ζ + T3 ζ) ∂volume
            = ∫ ζ in Sᶜ, (((T1 + T2) + T3) ζ) ∂volume := by
          refine setIntegral_congr_fun hSmeas.compl (fun ζ _ => ?_)
          simp only [Pi.add_apply]
        have hInt12 : Integrable (T1 + T2) (volume.restrict Sᶜ) := by
          rw [show (T1 + T2) = fun ζ : ℂ => T1 ζ + T2 ζ from rfl]
          exact hIntT1.add hIntT2
        have hIntT3' : Integrable T3 (volume.restrict Sᶜ) := by
          rw [hT3]
          exact hIntT3.const_mul (f y - f x)
        have h2 : ∫ ζ in Sᶜ, (((T1 + T2) + T3) ζ) ∂volume
            = (∫ ζ in Sᶜ, ((T1 + T2) ζ) ∂volume) + (∫ ζ in Sᶜ, T3 ζ ∂volume) :=
          integral_add hInt12 hIntT3'
        have hIntT1' : Integrable T1 (volume.restrict Sᶜ) := by
          rw [hT1]; exact hIntT1
        have hIntT2' : Integrable T2 (volume.restrict Sᶜ) := by
          rw [hT2]; exact hIntT2
        have h3 : ∫ ζ in Sᶜ, ((T1 + T2) ζ) ∂volume
            = (∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume) :=
          integral_add hIntT1' hIntT2' 
        rw [h1, h2, h3]
      rw [hsplit2]
      have hT1b : ‖∫ ζ in Sᶜ, T1 ζ ∂volume‖
          ≤ 12 * Real.pi * 2 ^ (α - 1) / (1 - α) * (K * δ ^ α) := by
        have h := Holder.far_kernel_diff_bound hα1 hδpos hK (hδdef.symm)
        simpa only [hT1, hS] using h
      have hIntW2 : Integrable (fun ζ : ℂ => ‖W (ζ - x) - W (ζ - y)‖) volume :=
        (hC₃ x y).1.norm
      have hT2b : ‖∫ ζ in Sᶜ, T2 ζ ∂volume‖ ≤ M * (C₃ * δ) := by
        calc ‖∫ ζ in Sᶜ, T2 ζ ∂volume‖ ≤ ∫ ζ in Sᶜ, ‖T2 ζ‖ ∂volume :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ ζ in Sᶜ, M * ‖W (ζ - x) - W (ζ - y)‖ ∂volume := by
              refine integral_mono (f := fun ζ => ‖T2 ζ‖)
                (g := fun ζ => M * ‖W (ζ - x) - W (ζ - y)‖) hIntT2.norm
                (hIntW2.const_mul M).integrableOn ?_
              intro ζ
              show ‖f x * (W (ζ - x) - W (ζ - y))‖ ≤ M * ‖W (ζ - x) - W (ζ - y)‖
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
          _ = M * ∫ ζ in Sᶜ, ‖W (ζ - x) - W (ζ - y)‖ ∂volume := integral_const_mul M _
          _ ≤ M * ∫ ζ : ℂ, ‖W (ζ - x) - W (ζ - y)‖ ∂volume := by
              refine mul_le_mul_of_nonneg_left ?_ hM0
              rw [← integral_indicator hSmeas.compl]
              refine integral_mono (hIntW2.indicator hSmeas.compl) hIntW2 ?_
              intro ζ
              by_cases hζ : ζ ∈ Sᶜ
              · rw [Set.indicator_of_mem hζ]
              · rw [Set.indicator_of_notMem hζ]
                exact norm_nonneg _
          _ ≤ M * (C₃ * ‖x - y‖) := mul_le_mul_of_nonneg_left (hC₃ x y).2 hM0
          _ = M * (C₃ * δ) := by rw [hδdef]
      have hT3b : ‖∫ ζ in Sᶜ, T3 ζ ∂volume‖ ≤ (12 + Real.pi) * (K * δ ^ α) := by
        have h1 : ∫ ζ in Sᶜ, T3 ζ ∂volume
            = (f y - f x) * (∫ ζ in Sᶜ,
                (bumpC (ζ - y) : ℂ) * (((ζ - y) ^ 2)⁻¹) ∂volume) := by
          rw [hT3, ← integral_const_mul]
        have h2 : ‖∫ ζ in Sᶜ, (bumpC (ζ - y) : ℂ) * (((ζ - y) ^ 2)⁻¹) ∂volume‖
            ≤ 12 + Real.pi := by
          have h := Holder.far_chi_term_bound hδpos (hδdef.symm)
          simpa only [hS] using h
        have h3 : ‖f y - f x‖ ≤ K * δ ^ α := by
          have h := hK y x
          rw [show ‖y - x‖ = δ from by rw [norm_sub_rev, hδdef]] at h
          exact h
        rw [h1, norm_mul]
        calc ‖f y - f x‖ * ‖∫ ζ in Sᶜ,
              (bumpC (ζ - y) : ℂ) * (((ζ - y) ^ 2)⁻¹) ∂volume‖
            ≤ (K * δ ^ α) * (12 + Real.pi) :=
              mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
          _ = (12 + Real.pi) * (K * δ ^ α) := by ring
      have hcomb : ‖(∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume)
            + (∫ ζ in Sᶜ, T3 ζ ∂volume)‖
          ≤ (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * (K * δ ^ α) + M * (C₃ * δ)
            + (12 + Real.pi) * (K * δ ^ α) := by
        have h4 : ‖(∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume)
              + (∫ ζ in Sᶜ, T3 ζ ∂volume)‖
            ≤ ‖(∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume)‖
              + ‖∫ ζ in Sᶜ, T3 ζ ∂volume‖ := norm_add_le _ _
        have h5 : ‖(∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume)‖
            ≤ ‖∫ ζ in Sᶜ, T1 ζ ∂volume‖ + ‖∫ ζ in Sᶜ, T2 ζ ∂volume‖ := norm_add_le _ _
        linarith [h4, h5, hT1b, hT2b, hT3b]
      have harith : (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * (K * δ ^ α) + M * (C₃ * δ)
            + (12 + Real.pi) * (K * δ ^ α) ≤ Cfar * (M + K) * δ ^ α := by
        rw [hCfar]
        have hA0 : 0 ≤ 12 * Real.pi * 2 ^ (α - 1) / (1 - α) := by positivity
        have hC0 : 0 ≤ 12 + Real.pi := by positivity
        have hK' : K ≤ M + K := by linarith
        have hM' : M ≤ M + K := by linarith
        have hδa : δ ≤ δ ^ α := by
          have h2 : δ ^ (1 : ℝ) ≤ δ ^ α :=
            Real.rpow_le_rpow_of_exponent_ge hδpos hδle1 hα1.le
          rwa [Real.rpow_one] at h2
        have h1 : (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * (K * δ ^ α)
            ≤ (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * ((M + K) * δ ^ α) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK' hδpowpos.le) hA0
        have h2 : (12 + Real.pi) * (K * δ ^ α) ≤ (12 + Real.pi) * ((M + K) * δ ^ α) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK' hδpowpos.le) hC0
        have h3 : M * (C₃ * δ) ≤ C₃ * ((M + K) * δ ^ α) := by
          have h4 : M * δ ≤ (M + K) * δ ^ α := by
            calc M * δ ≤ (M + K) * δ := mul_le_mul_of_nonneg_right hM' hδpos.le
              _ ≤ (M + K) * δ ^ α := mul_le_mul_of_nonneg_left hδa (by positivity)
          calc M * (C₃ * δ) = C₃ * (M * δ) := by ring
            _ ≤ C₃ * ((M + K) * δ ^ α) := mul_le_mul_of_nonneg_left h4 hC₃pos.le
        have h5 : (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi) * (M + K) * δ ^ α
            = (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * ((M + K) * δ ^ α)
              + C₃ * ((M + K) * δ ^ α) + (12 + Real.pi) * ((M + K) * δ ^ α) := by
          ring
        linarith [h1, h2, h3, h5]
      linarith [hcomb, harith]
    -- ===== conclusion of the main case =====
    rw [hbeur, hsplit]
    have hsum : ‖(∫ ζ in S, (Ix ζ - Iy ζ) ∂volume) + (∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume)‖
        ≤ (Cnear + Cfar) * (M + K) * δ ^ α := by
      have h4 : ‖(∫ ζ in S, (Ix ζ - Iy ζ) ∂volume) + (∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume)‖
          ≤ ‖∫ ζ in S, (Ix ζ - Iy ζ) ∂volume‖ + ‖∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume‖ :=
        norm_add_le _ _
      have h5 : ‖∫ ζ in S, (Ix ζ - Iy ζ) ∂volume‖ + ‖∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume‖
          ≤ Cnear * (M + K) * δ ^ α + Cfar * (M + K) * δ ^ α := add_le_add hnear hfar
      have h6 : Cnear * (M + K) * δ ^ α + Cfar * (M + K) * δ ^ α
          = (Cnear + Cfar) * (M + K) * δ ^ α := by ring
      linarith [h4, h5, h6]
    have hfin : Real.pi⁻¹ * ((Cnear + Cfar) * (M + K) * δ ^ α)
        ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * (1 + R) * δ ^ α := by
      have hpi : Real.pi⁻¹ ≤ 1 := by
        rw [inv_le_one₀ Real.pi_pos]
        linarith [Real.pi_gt_three]
      have h1 : 0 ≤ (Cnear + Cfar) * (M + K) * δ ^ α := by positivity
      have h2 : 0 ≤ (M + K) * δ ^ α := by positivity
      have h3 : Cnear + Cfar ≤ max (Cnear + Cfar) (2 * C₂) + 1 := by
        have := le_max_left (Cnear + Cfar) (2 * C₂); linarith
      have h4 : (1 : ℝ) ≤ 1 + R := by linarith
      have h8 : 0 ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * δ ^ α := by positivity
      calc Real.pi⁻¹ * ((Cnear + Cfar) * (M + K) * δ ^ α)
          ≤ 1 * ((Cnear + Cfar) * (M + K) * δ ^ α) := mul_le_mul_of_nonneg_right hpi h1
        _ = (Cnear + Cfar) * (M + K) * δ ^ α := one_mul _
        _ ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * δ ^ α := by
            have h5 : (Cnear + Cfar) * ((M + K) * δ ^ α)
                ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * ((M + K) * δ ^ α) :=
              mul_le_mul_of_nonneg_right h3 h2
            linarith [h5]
        _ ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * (1 + R) * δ ^ α := by
            calc (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * δ ^ α
                = (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * δ ^ α * 1 := by ring
              _ ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * δ ^ α * (1 + R) :=
                  mul_le_mul_of_nonneg_left h4 h8
              _ = (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * (1 + R) * δ ^ α := by ring
    calc Real.pi⁻¹ * ‖(∫ ζ in S, (Ix ζ - Iy ζ) ∂volume) + (∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume)‖
        ≤ Real.pi⁻¹ * ((Cnear + Cfar) * (M + K) * δ ^ α) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * (1 + R) * δ ^ α := hfin
  · -- ================= case `δ > 1` =================
    have hδgt : 1 < ‖x - y‖ := lt_of_not_ge hδle
    have hδ1 : 1 ≤ ‖x - y‖ := le_of_lt hδgt
    have hδpow : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hδ1 hα.le
    have hcast : 2 * C₂ ≤ max (Cnear + Cfar) (2 * C₂) + 1 := by
      have := le_max_right (Cnear + Cfar) (2 * C₂); linarith
    have h1 : 2 * C₂ * (M + K) * (1 + R)
        ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * (1 + R) := by
      have h3 : 0 ≤ (M + K) * (1 + R) := by positivity
      nlinarith [hcast, h3]
    have h2 : (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * (1 + R)
        ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * (1 + R) * ‖x - y‖ ^ α := by
      have h4 : 0 ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * (1 + R) := by positivity
      nlinarith [h4, hδpow]
    calc ‖beurling f x - beurling f y‖
        ≤ ‖beurling f x‖ + ‖beurling f y‖ := norm_sub_le _ _
      _ ≤ C₂ * (M + K) * (1 + R) + C₂ * (M + K) * (1 + R) := add_le_add (hC₂ x) (hC₂ y)
      _ = 2 * C₂ * (M + K) * (1 + R) := by ring
      _ ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * (1 + R) := h1
      _ ≤ (max (Cnear + Cfar) (2 * C₂) + 1) * (M + K) * (1 + R) * ‖x - y‖ ^ α := h2

end Work.Beltrami
