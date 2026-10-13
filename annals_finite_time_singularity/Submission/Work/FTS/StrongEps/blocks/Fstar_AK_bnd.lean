/-
# The block bound for the reference profile `F_*` and the projector kernel `AK`

The Galerkin/`ε`-scheme of the StrongEps chapter evaluates the vorticity equation on the
reference profile `F_*` of Elgindi's modulation (`F_* = α(Γ/c)·2z/(1+z)²`) and on the
correction `AK = (Γ/c)·2z²/(1+z)³`.  Every one of the explicit coefficients that is a
polynomial in `F_*`, `∂_θF_*`, `z∂_zF_*`, `AK` -- together with the angular datum `Γ` -- is
then bounded on any box `[c,d] × (0,∞)` with `0 < c ≤ d < π/2`, uniformly in `z`.

This module provides exactly that uniform bound:

* `|F_*|`, `|z∂_zF_*|` and `|AK|` are bounded by `20` on the box.  Each of them factors as
  `(Γ/c) · (an explicit rational function of z)`; the rational factors are
  `2z/(1+z)²`, `2z(1-z)/(1+z)³`, `2z²/(1+z)³` and are all bounded by `2` for `z ≥ 0`,
  while `Γ ∈ [0,1]` (`Spaces.Gam_bounds`) and `c ≥ 1/10` (`Spaces.c_bounds`) give
  `Γ/c ≤ 10`.
* `|∂_θF_*|` is bounded by `40/m` with `m := 2 sin c cos d > 0`.  Here the `z`-dependence is
  harmless again, but the angular derivative of `Γ` is `D_θΓ = α q Γ` with
  `D_θ = sin(2θ)∂_θ` (`Spaces.dthU_Gam`), so `∂_θΓ = α q Γ / sin(2θ)` and the box
  `[c,d] ⊂ (0,π/2)` bounds `sin(2θ) ≥ 2 sin c cos d > 0` from below
  (`sin` increasing and `cos` decreasing on `[0,π/2]`).  This is the only place where
  the hypothesis `d < π/2` (i.e. `θ` staying away from the angular singularity) is used.

The final constant is `61 + 40/m`; it depends on `c` and `d` (through `m`) and on `α` only
through the universal bounds above, so it is uniform in `α ∈ (0,1]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.blocks

theorem Fstar_AK_bnd {α c d : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, 0 < z → c ≤ θ → θ ≤ d →
      |Work.Construction.Fstar α z θ| + |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| + |Work.Construction.AK α z θ| ≤ C := by
  -- `m = 2 sin c cos d` is the uniform lower bound for `sin(2θ)` on the angular box.
  set m : ℝ := 2 * Real.sin c * Real.cos d with hm
  have hsin_c : 0 < Real.sin c :=
    Real.sin_pos_of_pos_of_lt_pi hc (by linarith [hcd, hd, Real.pi_pos])
  have hcos_d : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc, hcd], hd⟩
  have hm_pos : 0 < m := by rw [hm]; positivity
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
  have hsin2 : ∀ θ : ℝ, c ≤ θ → θ ≤ d → m ≤ Real.sin (2 * θ) := by
    intro θ hθc hθd
    rw [hm]
    have h1 : Real.sin c ≤ Real.sin θ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [hθd, hd]) hθc
    have h2 : Real.cos d ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [hd, Real.pi_pos]) hθd
    have hsθ : 0 ≤ Real.sin θ := le_trans hsin_c.le h1
    have hmul : Real.sin c * Real.cos d ≤ Real.sin θ * Real.cos θ :=
      mul_le_mul h1 h2 hcos_d.le hsθ
    rw [Real.sin_two_mul]
    linarith
  have hc10 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  -- The three explicit rational factors in `z` are bounded by `2` on `z ≥ 0`.
  have hFz : ∀ z : ℝ, 0 ≤ z → |Work.FM.Fstar z| ≤ 2 := by
    intro z hz
    have hnn : 0 ≤ 2 * z / (1 + z) ^ 2 := by positivity
    have hle : 2 * z / (1 + z) ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
      nlinarith [sq_nonneg z]
    rw [show Work.FM.Fstar z = 2 * z / (1 + z) ^ 2 from rfl, abs_of_nonneg hnn]
    exact hle
  have hDzfrac : ∀ z : ℝ, 0 ≤ z → |2 * z * (1 - z) / (1 + z) ^ 3| ≤ 2 := by
    intro z hz
    have h1z : (0 : ℝ) < 1 + z := by linarith
    have hden : (0 : ℝ) < (1 + z) ^ 3 := by positivity
    have h1 : |1 - z| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hz,
      abs_of_pos hden]
    have h2 : 2 * z * |1 - z| / (1 + z) ^ 3 ≤ 2 * z * (1 + z) / (1 + z) ^ 3 := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * z * (1 + z) / (1 + z) ^ 3 ≤ 2 := by
      rw [div_le_iff₀ hden]
      nlinarith [sq_nonneg z, hz, sq_nonneg (1 + z)]
    linarith
  have hAKfrac : ∀ z : ℝ, 0 ≤ z → |2 * z ^ 2 / (1 + z) ^ 3| ≤ 2 := by
    intro z hz
    have hnn : 0 ≤ 2 * z ^ 2 / (1 + z) ^ 3 := by positivity
    rw [abs_of_nonneg hnn]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 3)]
    nlinarith [sq_nonneg z, hz, sq_nonneg (1 + z)]
  refine ⟨61 + 40 / m, ?_, ?_⟩
  · have : 0 < 40 / m := div_pos (by norm_num) hm_pos
    linarith
  · intro z θ hz hθc hθd
    have hθI : θ ∈ Work.Spaces.Iθ :=
      ⟨le_trans hc.le hθc, le_of_lt (lt_of_le_of_lt hθd hd)⟩
    have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith, by linarith⟩
    obtain ⟨hGam0, hGam1⟩ := Work.Spaces.Gam_bounds α θ hα hθI
    have hq0 : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hGam0 hc0.le
    have hq10 : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
      rw [div_le_iff₀ hc0]; nlinarith [hGam1, hc10]
    have hm_le : m ≤ Real.sin (2 * θ) := hsin2 θ hθc hθd
    have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le hm_pos hm_le
    -- The angular derivative of `Γ`, through `D_θΓ = α q Γ` and `D_θ = sin(2θ)∂_θ`.
    have hderiv : |deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 2 * α / m := by
      have hdth := Work.Spaces.dthU_Gam α θ hα hθIoo
      rw [Work.Spaces.dthU_apply] at hdth
      have hdeq : deriv (fun t => Work.Spaces.Gam α t) θ
          = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Real.sin (2 * θ) := by
        rw [eq_div_iff (ne_of_gt hsinpos), mul_comm]
        exact hdth
      rw [hdeq, abs_div, abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hsinpos,
        abs_of_nonneg hGam0]
      have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
        rw [Work.Spaces.qfun_apply, abs_le]
        constructor <;> nlinarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
      have hnum : α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ ≤ 4 * α / 3 := by
        have h1 : α * |Work.Spaces.qfun θ| ≤ α * (4 / 3) :=
          mul_le_mul_of_nonneg_left hq hα.le
        have h2 := mul_le_mul h1 hGam1 hGam0 (by positivity : (0 : ℝ) ≤ α * (4 / 3))
        linarith
      rw [div_le_div_iff₀ hsinpos hm_pos]
      have hs1 : α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ * m ≤ (4 * α / 3) * m :=
        mul_le_mul_of_nonneg_right hnum hm_pos.le
      have hs2 : (4 * α / 3) * m ≤ (4 * α / 3) * Real.sin (2 * θ) :=
        mul_le_mul_of_nonneg_left hm_le (by positivity)
      have hs3 : (4 * α / 3) * Real.sin (2 * θ) ≤ 2 * α * Real.sin (2 * θ) := by
        have : (4 : ℝ) * α / 3 ≤ 2 * α := by linarith
        exact mul_le_mul_of_nonneg_right this hsinpos.le
      linarith
    have hpth : |Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ 40 / m := by
      rw [Work.Construction.pth_Fstar_eq hα]
      rw [abs_mul, abs_mul, abs_of_pos hα, abs_div, abs_of_pos hc0]
      have hcv : |deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α
          ≤ 10 * |deriv (fun t => Work.Spaces.Gam α t) θ| := by
        rw [div_le_iff₀ hc0]
        nlinarith [abs_nonneg (deriv (fun t => Work.Spaces.Gam α t) θ), hc10]
      have hstep : α * (|deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α)
            * |Work.FM.Fstar z| ≤ α * (10 * |deriv (fun t => Work.Spaces.Gam α t) θ|) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcv hα.le) (hFz z (le_of_lt hz))
          (abs_nonneg _) (by positivity)
      have hb : α * (10 * |deriv (fun t => Work.Spaces.Gam α t) θ|) * 2 ≤ 40 / m := by
        have h2 : α * (10 * |deriv (fun t => Work.Spaces.Gam α t) θ|) * 2
            = 20 * (α * |deriv (fun t => Work.Spaces.Gam α t) θ|) := by ring
        rw [h2]
        have h3 : α * |deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 2 * α ^ 2 / m := by
          calc α * |deriv (fun t => Work.Spaces.Gam α t) θ| ≤ α * (2 * α / m) :=
                mul_le_mul_of_nonneg_left hderiv hα.le
            _ = 2 * α ^ 2 / m := by ring
        have h4 : 2 * α ^ 2 / m ≤ 2 / m := by
          rw [div_le_div_iff₀ hm_pos hm_pos]
          nlinarith [hα2, hm_pos]
        calc 20 * (α * |deriv (fun t => Work.Spaces.Gam α t) θ|)
            ≤ 20 * (2 * α ^ 2 / m) := mul_le_mul_of_nonneg_left h3 (by norm_num)
          _ ≤ 20 * (2 / m) := mul_le_mul_of_nonneg_left h4 (by norm_num)
          _ = 40 / m := by ring
      linarith
    have hF : |Work.Construction.Fstar α z θ| ≤ 20 := by
      rw [Work.Construction.Fstar, abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hq0]
      calc α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * |Work.FM.Fstar z|
          ≤ 1 * 10 * 2 :=
            mul_le_mul (mul_le_mul hα1 hq10 hq0 (by norm_num)) (hFz z (le_of_lt hz))
              (abs_nonneg _) (by norm_num)
        _ = 20 := by norm_num
    have hDz : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 20 := by
      rw [Work.Construction.Dz_Fstar_eq hα (by linarith : (-1 : ℝ) < z)]
      rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hq0]
      calc α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * |2 * z * (1 - z) / (1 + z) ^ 3|
          ≤ 1 * 10 * 2 :=
            mul_le_mul (mul_le_mul hα1 hq10 hq0 (by norm_num)) (hDzfrac z (le_of_lt hz))
              (abs_nonneg _) (by norm_num)
        _ = 20 := by norm_num
    have hAK : |Work.Construction.AK α z θ| ≤ 20 := by
      rw [Work.Construction.AK, abs_mul, abs_of_nonneg hq0]
      calc Work.Spaces.Gam α θ / Work.Spaces.c α * |2 * z ^ 2 / (1 + z) ^ 3|
          ≤ 10 * 2 := mul_le_mul hq10 (hAKfrac z (le_of_lt hz)) (abs_nonneg _) (by norm_num)
        _ = 20 := by norm_num
    linarith [hF, hpth, hDz, hAK]

end Work.FTS.StrongEps.blocks
