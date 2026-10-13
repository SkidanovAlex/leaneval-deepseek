import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.CoercivityFix.Coer1T.GamL2.Prelim
import Submission.Work.FTS.CoercivityFix.Coer1T.GamL2.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `GammaL2Bnd`: the angular `L²`-estimate `|Γ/c − K|₂ ≤ 7/10`

`GammaL2Bnd α` is the paper's `(GammaAssumption)`: on `Iθ = [0,π/2]`,

  `∫_θ (Γ(θ)/c − K(θ))² ≤ (7/10)²`,

where `Γ(θ) = (sinθ cos²θ)^{α/3}`, `K(θ) = 3 sinθ cos²θ` and `c = ∫_θ Γ K`.

For `α → 0⁺` the weight `Γ/c` degenerates to `1`, so the estimate is a perturbation
of the identity `∫_θ (1 − K)² = π/2 − 2 + 9π/32 = 0.4543… ≤ 0.49` (using
`∫_θ K = 1`, `∫_θ sin²θcos⁴θ = π/32` and `∫_θ 1 = π/2`, all available).  Writing
`u = sinθ cos²θ` and `p = α/3`, the perturbation is controlled by

  `(u^p − 3u)² ≤ (1 − 3u)² + 6p(1 − u)`   (`0 ≤ u ≤ 1`, `0 < p`),

whose right-hand side integrates to `25π/32 − 2 + 6p(π/2)` (`int_F`), together with
the normalisation defect `c ≤ 1`, `1 − c ≤ 3p(π/2)`.  The final step splits

  `Γ/c − K = (Γ − K) + Γ·(1/c − 1)`,

uses `|Γ − K| ≤ 3`, `Γ ≤ 1` and `|1/c − 1| ≤ 6p(π/2) = 3πp` to bound the cross term,
and closes numerically: for `p ≤ 1/(3·10¹⁴)` the corrections are `≤ 10⁻¹²`, far
inside the margin `0.49 − 0.46094 = 0.029`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

open GamL2

theorem gammaL2Bnd_fts (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) :
    Work.Coercivity.GammaL2Bnd α := by
  have hα1' : α ≤ 1 := by
    have h : (1 : ℝ) / 10 ^ 14 ≤ 1 := by norm_num
    linarith
  set p : ℝ := α / 3 with hp
  have hp_bound : p ≤ 1 / (3 * 10 ^ 14) := by
    have h : (1 : ℝ) / 10 ^ 14 / 3 = 1 / (3 * 10 ^ 14) := by norm_num
    rw [hp, ← h]
    linarith
  have hp0 : 0 < p := by rw [hp]; linarith
  have hF := int_F α hα hα1'
  rw [← hp] at hF
  have hcle := c_le_one α hα hα1'
  have hcub := one_sub_c_le α hα hα1
  rw [← hp] at hcub
  have hcpos : 0 < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1').1
    linarith
  have hcl : (1 : ℝ) / 2 ≤ Work.Spaces.c α := by
    have h3 : 3 * p * (Real.pi / 2) ≤ 1 / 2 := by
      nlinarith [Real.pi_lt_d2, hp_bound, hp0]
    linarith
  have h1mc : |1 - Work.Spaces.c α| ≤ 3 * p * (Real.pi / 2) := by
    rw [abs_of_nonneg (by linarith [hcle])]
    exact hcub
  have he : |1 / Work.Spaces.c α - 1| ≤ 3 * Real.pi * p := by
    have hkey : 1 / Work.Spaces.c α - 1 = (1 - Work.Spaces.c α) / Work.Spaces.c α := by
      field_simp
    rw [hkey, abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
    have hprod : 3 * Real.pi * p * (1 / 2) ≤ 3 * Real.pi * p * Work.Spaces.c α :=
      mul_le_mul_of_nonneg_left hcl (by positivity)
    linarith [h1mc, hprod]
  -- the pointwise reduction to the `F`-part plus a constant
  set C : ℝ := 6 * |1 / Work.Spaces.c α - 1| + (1 / Work.Spaces.c α - 1) ^ 2 with hCdef
  have hpt2 : ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2
        ≤ (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2 + C := by
    intro θ hθ
    have hG0 := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hG1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hK0 := K_nonneg hθ
    have hK3 := K_le_three hθ
    have hcne : Work.Spaces.c α ≠ 0 := ne_of_gt hcpos
    have hkey : Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ
        = (Work.Spaces.Gam α θ - Work.Spaces.K θ)
          + Work.Spaces.Gam α θ * (1 / Work.Spaces.c α - 1) := by
      field_simp
      ring
    have hA3 : |Work.Spaces.Gam α θ - Work.Spaces.K θ| ≤ 3 := by
      rw [abs_le]; constructor <;> linarith
    have hE1 : 2 * |Work.Spaces.Gam α θ - Work.Spaces.K θ|
        * (Work.Spaces.Gam α θ * |1 / Work.Spaces.c α - 1|)
        ≤ 6 * |1 / Work.Spaces.c α - 1| := by
      have hπ0 : 0 ≤ |1 / Work.Spaces.c α - 1| := abs_nonneg _
      have h1 : 2 * |Work.Spaces.Gam α θ - Work.Spaces.K θ| ≤ 6 := by linarith
      have h2 : Work.Spaces.Gam α θ * |1 / Work.Spaces.c α - 1|
          ≤ |1 / Work.Spaces.c α - 1| := mul_le_of_le_one_left hπ0 hG1
      exact (mul_le_mul_of_nonneg_right h1 (mul_nonneg hG0 hπ0)).trans
        (mul_le_mul_of_nonneg_left h2 (by norm_num))
    have hE2 : (Work.Spaces.Gam α θ) ^ 2 * (1 / Work.Spaces.c α - 1) ^ 2
        ≤ (1 / Work.Spaces.c α - 1) ^ 2 := by
      have hg2 : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by nlinarith [hG0, hG1]
      exact mul_le_of_le_one_left (sq_nonneg (1 / Work.Spaces.c α - 1)) hg2
    calc (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2
        = ((Work.Spaces.Gam α θ - Work.Spaces.K θ)
            + Work.Spaces.Gam α θ * (1 / Work.Spaces.c α - 1)) ^ 2 := by rw [hkey]
      _ ≤ (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2
            + 2 * |Work.Spaces.Gam α θ - Work.Spaces.K θ|
              * |Work.Spaces.Gam α θ * (1 / Work.Spaces.c α - 1)|
            + (Work.Spaces.Gam α θ * (1 / Work.Spaces.c α - 1)) ^ 2 := sq_abs_add_le _ _
      _ = (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2
            + 2 * |Work.Spaces.Gam α θ - Work.Spaces.K θ|
              * (Work.Spaces.Gam α θ * |1 / Work.Spaces.c α - 1|)
            + (Work.Spaces.Gam α θ) ^ 2 * (1 / Work.Spaces.c α - 1) ^ 2 := by
          rw [abs_mul, abs_of_nonneg hG0]; ring
      _ ≤ (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2
            + 6 * |1 / Work.Spaces.c α - 1| + (1 / Work.Spaces.c α - 1) ^ 2 := by
          linarith [hE1, hE2]
      _ = (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2 + C := by rw [hCdef]; ring
  -- integrability and the integral inequality
  have hcontG : Continuous (fun θ : ℝ => Work.Spaces.Gam α θ) := continuous_Gam α hα
  have hA_int : IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2)
      Work.Spaces.Iθ := ((hcontG.sub cont_K).pow 2).integrableOn_Icc
  have hConst_int : IntegrableOn (fun _ : ℝ => C) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have hL_int : IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2)
      Work.Spaces.Iθ := (((hcontG.div_const _).sub cont_K).pow 2).integrableOn_Icc
  have hR_int : IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2 + C) Work.Spaces.Iθ :=
    hA_int.add hConst_int
  have hmono : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2 + C) :=
    integral_mono_ae hL_int hR_int
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ; exact hpt2 θ hθ)
  have hsplit : (∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2 + C))
      = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2)
        + C * (Real.pi / 2) := by
    rw [integral_add hA_int hConst_int, int_const]
  rw [hsplit] at hmono
  -- the size of the correction constant
  have hCbound : C ≤ 18 * Real.pi * p + 9 * Real.pi ^ 2 * p ^ 2 := by
    rw [hCdef]
    have h1 : 6 * |1 / Work.Spaces.c α - 1| ≤ 18 * Real.pi * p := by linarith [he]
    have h2 : (1 / Work.Spaces.c α - 1) ^ 2 ≤ 9 * Real.pi ^ 2 * p ^ 2 := by
      have h3 : (3 * Real.pi * p) ^ 2 = 9 * Real.pi ^ 2 * p ^ 2 := by ring
      rw [← h3]
      have hb := abs_le.mp he
      exact sq_le_sq' hb.1 hb.2
    linarith
  have hstep := mul_le_mul_of_nonneg_right hCbound (by positivity : (0 : ℝ) ≤ Real.pi / 2)
  -- final arithmetic
  have hπ2 : Real.pi ^ 2 ≤ 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hπ3 : Real.pi ^ 3 ≤ 31.255875 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [Work.Coercivity.GammaL2Bnd]
  have hfin : 25 * Real.pi / 32 - 2 + 6 * p * (Real.pi / 2)
      + (18 * Real.pi * p + 9 * Real.pi ^ 2 * p ^ 2) * (Real.pi / 2) ≤ (7 / 10 : ℝ) ^ 2 := by
    nlinarith [hπ2, hπ3, Real.pi_lt_d2, Real.pi_pos, hp_bound, le_of_lt hp0]
  linarith [hmono, hF, hstep, hfin]

end Work.FTS.CoercivityFix.Coer1T
