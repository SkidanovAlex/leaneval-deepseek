/-
# The radial `ℋ⁶` bound for the `Γ`-term: `|(D_z^j ρ)(z)·w(z)| ≤ M/(1+z)²` for `j ≤ 6`

This file proves

`Work.Construction.H6N_GammaTerm_rho_bound`:
`∃ M > 0, ∀ j ≤ 6, ∀ z ≥ 0, |(Zop^[j] ρ)(z)·w(z)| ≤ M/(1+z)²`

where `ρ(z) = z²/(1+z)⁴` (`Work.Construction.rhoR`), `w(z) = (1+z)²/z²`
(`Work.Spaces.w`) and `Zop = D_z` is `z·∂_z` (`Work.Spaces.Zop`).  It is the
`ℋ⁶` companion of the `ℋ⁴` bound `Work.Construction.H4N_GammaTerm_rho_bound`, and is
consumed by `Work.Construction.H6N_GammaTerm_sep_le`.

The mathematical content is the explicit computation of the two extra `D_z`-iterates
of `ρ`,

`(Zop^[j] ρ)(z) = z²·N_j(z)/(1+z)^{4+j}`  (`z ≠ -1`),

with

* `N_5 = 32 - 684z + 2644z² - 2644z³ + 684z⁴ - 32z⁵` (coefficient `ℓ¹`-norm `6720`),
* `N_6 = 64 - 2276z + 14680z² - 26440z³ + 14680z⁴ - 2276z⁵ + 64z⁶`
  (coefficient `ℓ¹`-norm `60480`),

proved here in the companion steps `Zop_rhoR_step5`, `Zop_rhoR_step6` (the recursion
`N_{j+1} = (2N_j + zN_j')(1+z) - (4+j)zN_j`, i.e. `Zop (w²N_j(w)/(1+w)^{4+j})
= z²N_{j+1}(z)/(1+z)^{5+j}`), and the polynomial bounds
`|N_j(z)| ≤ ℓ¹(N_j)·(1+z)^j` on `z ≥ 0` (`rhoN5_bound`, `rhoN6_bound`, from
`z^k ≤ (1+z)^j` for `k ≤ j`).  The cases `j ≤ 4` use the `ℋ⁴` data
`H4N_rhoR_shape12/3/4` and `H4N_rhoR_numbound`.

The two computational facts (`Zop^[5] ρ`, `Zop^[6] ρ` in closed form, and the `ℓ¹`
bounds on `N_5`, `N_6`) are proved here in full so that this file is self-contained;
the same statements are also available as the public lemmas
`Work.Construction.H6N_rhoR_shape56` and `Work.Construction.H6N_rhoR_numbound`
(companion files written in parallel), should a consumer prefer to import them.

The single mechanism (lemma `rho_w_bound_of` below) is: for `z > 0`,

`|z²N(z)/(1+z)^{4+j} · (1+z)²/z²| = |N(z)|/(1+z)^{2+j} ≤ C(1+z)^j/(1+z)^{2+j}
  = C/(1+z)²`,

while `z = 0` is trivial because `w(0) = 0` (Lean's totalised division; `w` is not
continuous there, which is exactly why the `z = 0` case is split off).  The values
`840, 6720, 60480` are all dominated by `M = 60480`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Construction.H4N_GammaTerm_rho_bound
import Submission.Work.Construction.H4N_rhoR_shape12
import Submission.Work.Construction.H4N_rhoR_shape3
import Submission.Work.Construction.H4N_rhoR_shape4
import Submission.Work.Construction.H4N_rhoR_numbound
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.Construction

set_option autoImplicit false

/-! ## The fifth and sixth `D_z`-iterates of `ρ`

One step of `Zop` on the shape `w ↦ u w / (1+w)^m` is `Zop_div_pow` of
`H4N_rhoR_shape3`; all that is needed is `HasDerivAt` of the numerator. -/

private lemma Zop_rhoR_step5 (z : ℝ) (hz : z ≠ -1) :
    Work.Spaces.Zop (fun w : ℝ =>
        w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4) / (1+w)^8) z
      = z^2 * (32 - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5) / (1+z)^9 := by
  have h1z : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  have h2 : HasDerivAt (fun w : ℝ => 16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4)
      (-196 + 832*z - 588*z^2 + 64*z^3) z := by
    have hp0 : HasDerivAt (fun w : ℝ => 16 - 196*w) (-(196*1)) z :=
      ((hasDerivAt_id' z).const_mul (196:ℝ)).const_sub (16:ℝ)
    have hp1 : HasDerivAt (fun w : ℝ => 416*w^2) (416*(↑2*z^(2-1))) z :=
      (hasDerivAt_pow 2 z).const_mul (416:ℝ)
    have hp2 : HasDerivAt (fun w : ℝ => 196*w^3) (196*(↑3*z^(3-1))) z :=
      (hasDerivAt_pow 3 z).const_mul (196:ℝ)
    have hp3 : HasDerivAt (fun w : ℝ => 16*w^4) (16*(↑4*z^(4-1))) z :=
      (hasDerivAt_pow 4 z).const_mul (16:ℝ)
    have hA : HasDerivAt (fun w : ℝ => 16 - 196*w + 416*w^2)
        (-(196*1) + 416*(↑2*z^(2-1))) z := hp0.add hp1
    have hB : HasDerivAt (fun w : ℝ => 16 - 196*w + 416*w^2 - 196*w^3)
        (-(196*1) + 416*(↑2*z^(2-1)) - 196*(↑3*z^(3-1))) z := hA.sub hp2
    have hC : HasDerivAt (fun w : ℝ => 16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4)
        (-(196*1) + 416*(↑2*z^(2-1)) - 196*(↑3*z^(3-1)) + 16*(↑4*z^(4-1))) z :=
      hB.add hp3
    have he : (-(196*1) + 416*(↑2*z^(2-1)) - 196*(↑3*z^(3-1)) + 16*(↑4*z^(4-1)) : ℝ)
        = -196 + 832*z - 588*z^2 + 64*z^3 := by ring
    rwa [he] at hC
  have hderiv : HasDerivAt (fun w : ℝ =>
        w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4))
      (32*z - 588*z^2 + 1664*z^3 - 980*z^4 + 96*z^5) z := by
    have h' : HasDerivAt (fun w : ℝ =>
          w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4))
        ((↑2*z^(2-1)) * (16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4)
          + z^2 * (-196 + 832*z - 588*z^2 + 64*z^3)) z :=
      (hasDerivAt_pow 2 z).mul h2
    have he : ((↑2*z^(2-1)) * (16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4)
        + z^2 * (-196 + 832*z - 588*z^2 + 64*z^3) : ℝ)
        = 32*z - 588*z^2 + 1664*z^3 - 980*z^4 + 96*z^5 := by ring
    rwa [he] at h'
  have h := Zop_div_pow 8 (by norm_num)
    (fun w : ℝ => w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4))
    (32*z - 588*z^2 + 1664*z^3 - 980*z^4 + 96*z^5) z hderiv hz
  refine h.trans ?_
  field_simp
  ring

private lemma Zop_rhoR_step6 (z : ℝ) (hz : z ≠ -1) :
    Work.Spaces.Zop (fun w : ℝ =>
        w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5) / (1+w)^9) z
      = z^2 * (64 - 2276*z + 14680*z^2 - 26440*z^3 + 14680*z^4 - 2276*z^5 + 64*z^6)
          / (1+z)^10 := by
  have h1z : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  have h2 : HasDerivAt (fun w : ℝ => 32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5)
      (-684 + 5288*z - 7932*z^2 + 2736*z^3 - 160*z^4) z := by
    have hp0 : HasDerivAt (fun w : ℝ => 32 - 684*w) (-(684*1)) z :=
      ((hasDerivAt_id' z).const_mul (684:ℝ)).const_sub (32:ℝ)
    have hp1 : HasDerivAt (fun w : ℝ => 2644*w^2) (2644*(↑2*z^(2-1))) z :=
      (hasDerivAt_pow 2 z).const_mul (2644:ℝ)
    have hp2 : HasDerivAt (fun w : ℝ => 2644*w^3) (2644*(↑3*z^(3-1))) z :=
      (hasDerivAt_pow 3 z).const_mul (2644:ℝ)
    have hp3 : HasDerivAt (fun w : ℝ => 684*w^4) (684*(↑4*z^(4-1))) z :=
      (hasDerivAt_pow 4 z).const_mul (684:ℝ)
    have hp4 : HasDerivAt (fun w : ℝ => 32*w^5) (32*(↑5*z^(5-1))) z :=
      (hasDerivAt_pow 5 z).const_mul (32:ℝ)
    have hA : HasDerivAt (fun w : ℝ => 32 - 684*w + 2644*w^2)
        (-(684*1) + 2644*(↑2*z^(2-1))) z := hp0.add hp1
    have hB : HasDerivAt (fun w : ℝ => 32 - 684*w + 2644*w^2 - 2644*w^3)
        (-(684*1) + 2644*(↑2*z^(2-1)) - 2644*(↑3*z^(3-1))) z := hA.sub hp2
    have hC : HasDerivAt (fun w : ℝ => 32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4)
        (-(684*1) + 2644*(↑2*z^(2-1)) - 2644*(↑3*z^(3-1)) + 684*(↑4*z^(4-1))) z :=
      hB.add hp3
    have hD : HasDerivAt (fun w : ℝ =>
          32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5)
        (-(684*1) + 2644*(↑2*z^(2-1)) - 2644*(↑3*z^(3-1)) + 684*(↑4*z^(4-1))
          - 32*(↑5*z^(5-1))) z := hC.sub hp4
    have he : (-(684*1) + 2644*(↑2*z^(2-1)) - 2644*(↑3*z^(3-1)) + 684*(↑4*z^(4-1))
        - 32*(↑5*z^(5-1)) : ℝ) = -684 + 5288*z - 7932*z^2 + 2736*z^3 - 160*z^4 := by ring
    rwa [he] at hD
  have hderiv : HasDerivAt (fun w : ℝ =>
        w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5))
      (64*z - 2052*z^2 + 10576*z^3 - 13220*z^4 + 4104*z^5 - 224*z^6) z := by
    have h' : HasDerivAt (fun w : ℝ =>
          w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5))
        ((↑2*z^(2-1)) * (32 - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5)
          + z^2 * (-684 + 5288*z - 7932*z^2 + 2736*z^3 - 160*z^4)) z :=
      (hasDerivAt_pow 2 z).mul h2
    have he : ((↑2*z^(2-1)) * (32 - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5)
        + z^2 * (-684 + 5288*z - 7932*z^2 + 2736*z^3 - 160*z^4) : ℝ)
        = 64*z - 2052*z^2 + 10576*z^3 - 13220*z^4 + 4104*z^5 - 224*z^6 := by ring
    rwa [he] at h'
  have h := Zop_div_pow 9 (by norm_num)
    (fun w : ℝ => w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5))
    (64*z - 2052*z^2 + 10576*z^3 - 13220*z^4 + 4104*z^5 - 224*z^6) z hderiv hz
  refine h.trans ?_
  field_simp
  ring

/-- The closed form of the fifth `D_z`-iterate of `ρ`. -/
private lemma Zop_rhoR_shape5 (z : ℝ) (hz : z ≠ -1) :
    (Work.Spaces.Zop^[5] rhoR) z
      = z^2 * (32 - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5) / (1 + z)^9 := by
  have h4 : (Work.Spaces.Zop^[4] rhoR) =ᶠ[𝓝 z]
      (fun w : ℝ => w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4) / (1+w)^8) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact H4N_rhoR_shape4 w hw
  have h1 : Work.Spaces.Zop (Work.Spaces.Zop^[4] rhoR) z
      = Work.Spaces.Zop (fun w : ℝ =>
          w^2 * (16 - 196*w + 416*w^2 - 196*w^3 + 16*w^4) / (1+w)^8) z := by
    rw [Zop_apply, Zop_apply, h4.deriv_eq]
  rw [show (5 : ℕ) = 4 + 1 by norm_num, Function.iterate_succ_apply', h1]
  exact Zop_rhoR_step5 z hz

/-- The closed form of the sixth `D_z`-iterate of `ρ`. -/
private lemma Zop_rhoR_shape6 (z : ℝ) (hz : z ≠ -1) :
    (Work.Spaces.Zop^[6] rhoR) z
      = z^2 * (64 - 2276*z + 14680*z^2 - 26440*z^3 + 14680*z^4 - 2276*z^5 + 64*z^6)
          / (1 + z)^10 := by
  have h5 : (Work.Spaces.Zop^[5] rhoR) =ᶠ[𝓝 z]
      (fun w : ℝ => w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5)
        / (1+w)^9) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact Zop_rhoR_shape5 w hw
  have h1 : Work.Spaces.Zop (Work.Spaces.Zop^[5] rhoR) z
      = Work.Spaces.Zop (fun w : ℝ =>
          w^2 * (32 - 684*w + 2644*w^2 - 2644*w^3 + 684*w^4 - 32*w^5) / (1+w)^9) z := by
    rw [Zop_apply, Zop_apply, h5.deriv_eq]
  rw [show (6 : ℕ) = 5 + 1 by norm_num, Function.iterate_succ_apply', h1]
  exact Zop_rhoR_step6 z hz

/-! ## The polynomial bounds -/

/-- `z^k ≤ (1+z)^n` on `z ≥ 0` for `k ≤ n`. -/
private lemma pow_le_one_add_pow (z : ℝ) (hz : 0 ≤ z) {k n : ℕ} (hkn : k ≤ n) :
    z^k ≤ (1+z)^n := by
  calc z^k ≤ (1+z)^k := pow_le_pow_left₀ hz (by linarith) k
    _ ≤ (1+z)^n := pow_le_pow_right₀ (by linarith) hkn

/-- The `ℓ¹`-bound for `N_5`: `|N_5(z)| ≤ 6720(1+z)^5`. -/
private lemma rhoN5_bound (z : ℝ) (hz : 0 ≤ z) :
    |(32:ℝ) - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5| ≤ 6720*(1+z)^5 := by
  have h0 : z^0 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  have h1 : z^1 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  have h2 : z^2 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  have h3 : z^3 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  have h4 : z^4 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  have h5 : z^5 ≤ (1+z)^5 := pow_le_one_add_pow z hz (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith [h0, h1, h2, h3, h4, h5]

/-- The `ℓ¹`-bound for `N_6`: `|N_6(z)| ≤ 60480(1+z)^6`. -/
private lemma rhoN6_bound (z : ℝ) (hz : 0 ≤ z) :
    |(64:ℝ) - 2276*z + 14680*z^2 - 26440*z^3 + 14680*z^4 - 2276*z^5 + 64*z^6|
      ≤ 60480*(1+z)^6 := by
  have h0 : z^0 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h1 : z^1 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h2 : z^2 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h3 : z^3 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h4 : z^4 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h5 : z^5 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  have h6 : z^6 ≤ (1+z)^6 := pow_le_one_add_pow z hz (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith [h0, h1, h2, h3, h4, h5, h6]

/-! ## The single step, and the theorem -/

/-- If `Zop^[j] ρ = z²·N/(1+z)^{4+j}` at `z` and `|N(z)| ≤ C(1+z)^j`, then
`|Zop^[j] ρ (z) · w(z)| ≤ C/(1+z)²`. -/
private lemma rho_w_bound_of (j : ℕ) (N : ℝ → ℝ) (C z : ℝ) (hC : 0 < C) (hz : 0 ≤ z)
    (hshape : (Work.Spaces.Zop^[j] rhoR) z = z^2 * N z / (1 + z)^(4+j))
    (hnumb : |N z| ≤ C * (1 + z)^j) :
    |(Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z| ≤ C / (1 + z)^2 := by
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [Work.Spaces.w]
    norm_num
    positivity
  · have hz0 : z ≠ 0 := ne_of_gt hpos
    have h1z : (0:ℝ) < 1 + z := by linarith
    rw [hshape, Work.Spaces.w]
    have hp : (1 + z)^(4+j) = (1 + z)^(2+j) * (1+z)^2 := by
      rw [show (4:ℕ) + j = (2+j)+2 by omega, pow_add]
    rw [hp]
    have key : z^2 * N z / ((1+z)^(2+j)*(1+z)^2) * ((1+z)^2/z^2)
        = N z / (1+z)^(2+j) := by
      field_simp
    rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1+z)^(2+j))]
    have hp2 : (1+z)^(2+j) = (1+z)^2 * (1+z)^j := by
      rw [pow_add]
    rw [div_le_div_iff₀ (by positivity) (by positivity), hp2]
    have hfin : |N z| * (1+z)^2 ≤ C * (1+z)^j * (1+z)^2 :=
      mul_le_mul_of_nonneg_right hnumb (by positivity)
    nlinarith [hfin]

theorem H6N_GammaTerm_rho_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z| ≤ M / (1 + z) ^ 2 := by
  refine ⟨60480, by norm_num, ?_⟩
  intro j hj z hz
  interval_cases j
  · have h := rho_w_bound_of 0 (fun _ : ℝ => 1) 1 z (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[0] rhoR) z * Work.Spaces.w z| ≤ 1 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [Function.iterate_zero_apply]
      show rhoR z = z^2 * 1 / (1 + z)^(4+0)
      rw [rhoR]
      norm_num
    · simp
  · have h := rho_w_bound_of 1 (fun z : ℝ => 2 - 2*z) 840 z (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[1] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [H4N_rhoR_shape12.1 z (by linarith)]
    · exact H4N_rhoR_numbound.2.1 z hz
  · have h := rho_w_bound_of 2 (fun z : ℝ => 4 - 12*z + 4*z^2) 840 z (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[2] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [H4N_rhoR_shape12.2 z (by linarith)]
    · exact H4N_rhoR_numbound.2.2.1 z hz
  · have h := rho_w_bound_of 3 (fun z : ℝ => 8 - 52*z + 52*z^2 - 8*z^3) 840 z
      (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[3] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [H4N_rhoR_shape3 z (by linarith)]
    · exact H4N_rhoR_numbound.2.2.2.1 z hz
  · have h := rho_w_bound_of 4 (fun z : ℝ => 16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4) 840 z
      (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[4] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [H4N_rhoR_shape4 z (by linarith)]
    · exact H4N_rhoR_numbound.2.2.2.2 z hz
  · have h := rho_w_bound_of 5
      (fun z : ℝ => 32 - 684*z + 2644*z^2 - 2644*z^3 + 684*z^4 - 32*z^5) 6720 z
      (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[5] rhoR) z * Work.Spaces.w z| ≤ 6720 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            norm_num
    · rw [Zop_rhoR_shape5 z (by linarith)]
    · exact rhoN5_bound z hz
  · have h := rho_w_bound_of 6
      (fun z : ℝ => 64 - 2276*z + 14680*z^2 - 26440*z^3 + 14680*z^4 - 2276*z^5 + 64*z^6)
      60480 z (by norm_num) hz ?_ ?_
    · calc |(Work.Spaces.Zop^[6] rhoR) z * Work.Spaces.w z| ≤ 60480 / (1 + z) ^ 2 := h
        _ ≤ 60480 / (1 + z) ^ 2 := le_refl _
    · rw [Zop_rhoR_shape6 z (by linarith)]
    · exact rhoN6_bound z hz

end Work.Construction
