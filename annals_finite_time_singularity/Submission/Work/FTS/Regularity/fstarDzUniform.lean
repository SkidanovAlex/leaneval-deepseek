/-
# `Work.FTS.Regularity.fstarDzUniform` — the uniform `z`-derivative box of the static profile

The static profile of the self-similar ansatz is

  `F_*(z,θ) = 3α·(Γ(θ)/c(3α))·2z/(1+z)² = pExp α · (Γ(θ)/c) · Work.FM.Fstar z`

(`Work.Construction.Fstar (pExp α) z θ`).  Its `z`-derivative at fixed `θ` is therefore the
*constant in `z`* factor

  `∂_z F_*(z,θ) = pExp α · (Γ(θ)/c) · deriv Work.FM.Fstar z`

with `deriv Work.FM.Fstar z = 2(1-z)/(1+z)³` (`Work.FM.deriv_Fstar`).

This module proves that on the physical range `z ∈ [0,∞)` this derivative is *uniformly bounded*
over `θ ∈ Iθ` and `α`-Hölder, i.e. the **static half** of the `z`-regularity data that
`Work.FTS.Regularity.dzProfFullUniform` adds to the jet of the perturbation `g`.  The three
ingredients are

* the angular/`c`-coefficient bound `|pExp α·(Γ(θ)/c(3α))| ≤ 10·pExp α` for `θ ∈ Iθ`, from
  `Γ ∈ [0,1]` (`Work.Spaces.Gam_bounds`) and `1/10 ≤ c ≤ 10` (`Work.Spaces.c_bounds`);
* `|deriv F_*| ≤ 2` and `|deriv F_*(z) - deriv F_*(z')| ≤ 8|z-z'|` (the latter is
  `Work.FTS.Regularity.Moduli.fstarDerivLip`, the mean value theorem bound on the second
  derivative `4(z-2)/(1+z)⁴`);
* for the Hölder upgrade: `t ≤ t^α` for `0 ≤ t ≤ 1` and `1 ≤ t^α` for `t ≥ 1`, which converts the
  Lipschitz bound of the derivative into an `α`-Hölder bound.

Everything is uniform in the radius `R`: the constants `20·3α` and `80·3α` do not depend on `R`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.Moduli.fstarDerivLip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option autoImplicit false

namespace Work.FTS.Regularity

/-! ## The `z`-derivative of the static profile -/

/-- The `z`-derivative of the slice `z ↦ F_*(z,θ)` is the `z`-independent factor
`pExp α·(Γ(θ)/c)` times `deriv F_*`: the profile is a multiple of `Work.FM.Fstar`. -/
theorem deriv_fstar_z (α z θ : ℝ) :
    deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
      = (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
          * deriv Work.FM.Fstar z := by
  have hfun : (fun z' => Work.Construction.Fstar (pExp α) z' θ)
      = fun z' => (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
          * Work.FM.Fstar z' := by
    funext z'
    simp only [Work.Construction.Fstar]
  rw [hfun, deriv_const_mul_field]

/-- **The angular coefficient is uniformly bounded on `Iθ`.**  For `0 < α ≤ 1/3` and
`θ ∈ Iθ = [0,π/2]`,

  `|3α·(Γ(θ)/c(3α))| ≤ 10·3α ≤ 30`,

because `Γ ∈ [0,1]` and `1/10 ≤ c(3α) ≤ 10`.  This is what makes the constant of the
`z`-derivative box independent of `θ` (and hence of the radius `R`). -/
theorem fstarCoef_abs_le {α θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α))| ≤ 10 * pExp α := by
  have hp0 : 0 < pExp α := pExp_pos hα
  have hp1 : pExp α ≤ 1 := pExp_le_one hα13
  obtain ⟨hc1, _hc2⟩ := Work.Spaces.c_bounds (pExp α) hp0 hp1
  have hcpos : 0 < Work.Spaces.c (pExp α) := by linarith
  obtain ⟨hg0, hg1⟩ := Work.Spaces.Gam_bounds (pExp α) θ hp0 hθ
  have hgab : |Work.Spaces.Gam (pExp α) θ| ≤ 1 := by
    rw [abs_of_nonneg hg0]; exact hg1
  rw [abs_mul, abs_of_pos hp0]
  have h2 : |Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)| ≤ 10 := by
    rw [abs_div, abs_of_pos hcpos]
    have h3 : |Work.Spaces.Gam (pExp α) θ| / Work.Spaces.c (pExp α)
        ≤ 1 / Work.Spaces.c (pExp α) := div_le_div_of_nonneg_right hgab hcpos.le
    have h4 : 1 / Work.Spaces.c (pExp α) ≤ 10 := by
      rw [div_le_iff₀ hcpos]; linarith
    linarith
  calc pExp α * |Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)|
      ≤ pExp α * 10 := mul_le_mul_of_nonneg_left h2 hp0.le
    _ = 10 * pExp α := by ring

/-- **`|deriv F_*| ≤ 2` on the physical half-line `z ≥ 0`**: with `deriv F_*(z) = 2(1-z)/(1+z)³`,
the estimate is `2|1-z| ≤ 2(1+z) ≤ 2(1+z)³`. -/
theorem deriv_FM_Fstar_abs_le {z : ℝ} (hz : 0 ≤ z) : |deriv Work.FM.Fstar z| ≤ 2 := by
  rw [Work.FM.deriv_Fstar z (by linarith)]
  have hpos : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have h1 : |1 - z| ≤ 1 + z := by
    rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [h1, hz, sq_nonneg z]

/-! ## The two uniform constants -/

/-- The pointwise bound of the static `z`-derivative, in the multiplicative form used by the
two conjuncts of `fstarDzUniform`. -/
theorem fstarDz_abs_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
        * deriv Work.FM.Fstar z| ≤ 20 * pExp α := by
  have hp0 : 0 < pExp α := pExp_pos hα
  have h1 := fstarCoef_abs_le hα hα13 hθ
  have h2 := deriv_FM_Fstar_abs_le hz
  calc |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
          * deriv Work.FM.Fstar z|
      = |pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α))|
        * |deriv Work.FM.Fstar z| := abs_mul _ _
    _ ≤ (10 * pExp α) * 2 := mul_le_mul h1 h2 (abs_nonneg _) (by nlinarith [hp0])
    _ = 20 * pExp α := by ring

/-- **The `α`-Hölder estimate of the static `z`-derivative.**  Its coefficient in `z` is
`8`-Lipschitz (`Moduli.fstarDerivLip`) and bounded by `10·3α`; on a pair with `|z - z'| ≤ 1`
the Lipschitz modulus upgrades to the `α`-modulus (`t ≤ t^α` for `t ≤ 1`), and for
`|z - z'| ≥ 1` the two pointwise bounds `20·3α` suffice because `1 ≤ |z-z'|^α`. -/
theorem fstarDz_holder {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hα1 : α ≤ 1)
    {z z' θ : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (hθ : θ ∈ Work.Spaces.Iθ) :
    |deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
        - deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z'|
      ≤ 80 * pExp α * |z - z'| ^ α := by
  have hp0 : 0 < pExp α := pExp_pos hα
  have hpnn : 0 ≤ 80 * pExp α := by linarith
  rw [deriv_fstar_z, deriv_fstar_z, ← mul_sub, abs_mul]
  by_cases hle : |z - z'| ≤ 1
  · have hcoef := fstarCoef_abs_le hα hα13 hθ
    have hlip := Moduli.fstarDerivLip hz hz'
    have hkey : |pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α))|
          * |deriv Work.FM.Fstar z - deriv Work.FM.Fstar z'|
        ≤ (10 * pExp α) * (8 * |z - z'|) :=
      mul_le_mul hcoef hlip (abs_nonneg _) (by nlinarith [hp0])
    have hrpow : |z - z'| ≤ |z - z'| ^ α :=
      Real.self_le_rpow_of_le_one (abs_nonneg _) hle hα1
    calc |pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α))|
          * |deriv Work.FM.Fstar z - deriv Work.FM.Fstar z'|
        ≤ (10 * pExp α) * (8 * |z - z'|) := hkey
      _ = 80 * pExp α * |z - z'| := by ring
      _ ≤ 80 * pExp α * |z - z'| ^ α := mul_le_mul_of_nonneg_left hrpow hpnn
  · push_neg at hle
    have h1 := fstarDz_abs_le hα hα13 hz hθ
    have h2 := fstarDz_abs_le hα hα13 hz' hθ
    have hrpow : (1 : ℝ) ≤ |z - z'| ^ α := Real.one_le_rpow hle.le hα.le
    have hsplit : |pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α))|
          * |deriv Work.FM.Fstar z - deriv Work.FM.Fstar z'|
        = |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z
          - (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z'| := by
      rw [← abs_mul, ← mul_sub]
    have htri : |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z
          - (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z'|
        ≤ |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z|
          + |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z'| := by
      have h := abs_sub_le
        ((pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z) 0
        ((pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z')
      simpa using h
    rw [hsplit]
    calc |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z
          - (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z'|
        ≤ |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z|
          + |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z'| := htri
      _ ≤ 20 * pExp α + 20 * pExp α := add_le_add h1 h2
      _ = 40 * pExp α := by ring
      _ ≤ 80 * pExp α * |z - z'| ^ α := by nlinarith [hrpow, hp0]

/-! ## The theorem -/

theorem fstarDzUniform {α R : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hR : 0 ≤ R) :
    ∃ M0 N0 : ℝ, 0 ≤ M0 ∧ 0 ≤ N0 ∧
      (∀ z θ : ℝ, 0 ≤ z → z ≤ R → θ ∈ Work.Spaces.Iθ →
        |deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z| ≤ M0) ∧
      (∀ z z' θ : ℝ, 0 ≤ z → z ≤ R → 0 ≤ z' → z' ≤ R → θ ∈ Work.Spaces.Iθ →
        |deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
          - deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z'|
          ≤ N0 * |z - z'| ^ α) := by
  have hp0 : 0 < pExp α := pExp_pos hα
  have hα1 : α ≤ 1 := by linarith
  refine ⟨20 * pExp α, 80 * pExp α, by linarith, by linarith, ?_, ?_⟩
  · intro z θ hz _hzR hθ
    rw [deriv_fstar_z]
    exact fstarDz_abs_le hα hα13 hz hθ
  · intro z z' θ hz _hzR hz' _hz'R hθ
    exact fstarDz_holder hα hα13 hα1 hz hz' hθ

end Work.FTS.Regularity
