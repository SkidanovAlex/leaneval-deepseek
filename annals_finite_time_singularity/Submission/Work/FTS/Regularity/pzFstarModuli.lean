/-
# `Work.FTS.Regularity.pzFstarModuli` — the joint modulus of `∂_z F_*(3α)`

The `z`-derivative of the profile `F_*(3α)` factors as

  `∂_z F_*(3α)(z,θ) = C(θ) · F̂'(z)`,  `C(θ) = 3α·(Γ(θ)/c(3α))`,  `Γ = Gam (3α)`,
  `F̂ = Work.FM.Fstar = 2z/(1+z)²`

(`pzFstar_eq`), and each factor carries an elementary modulus:

* `|C(θ)| ≤ 10` on `Iθ` (`pzCoeff_abs_le`), from the normalisation `1/10 ≤ c(3α) ≤ 10`, the
  angular bound `0 ≤ Γ ≤ 1` and `3α ≤ 1`; and `C` is `α`-Hölder on `Iθ` with constant `30`
  (`pzCoeff_holder`), from the `3^α`-Hölder modulus of `Γ` (`gam_three_holder`, itself from
  `|sinθcos²θ - sinθ'cos²θ'| ≤ 3|θ - θ'|`);
* `|F̂'(z)| ≤ 2` for `z ≥ 0` (`deriv_fstar_abs_le`, from the explicit
  `F̂'(z) = 2(1-z)/(1+z)³`), and `F̂'` is `8`-Lipschitz there (`Moduli.fstarDerivLip`).

Combining the product rule with these bounds gives the target with the single constant
`C = 140`, which both bounds `∂_z F_*(3α)` on `[0,∞) × Iθ` and makes it `α`-Hölder for the
metric `|Δz| + |Δθ|`: the mixed modulus `80|Δz| + 60|Δθ|^α` is converted into a single
`α`-Hölder modulus by the exponent change `t ≤ t^α` in the small regime `t ≤ 1`
(`t = |Δz| + |Δθ|`) and by the crude `L^∞` bound `40` in the large regime `t ≥ 1`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.Moduli.fstarDerivLip
import Submission.Work.FTS.Regularity.Moduli.sinCosSqLip
import Submission.Work.FTS.Regularity.Moduli.rpow_abs_sub_le
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FTS.Regularity

/-! ## The angular coefficient of `∂_z F_*(3α)` -/

/-- The angular coefficient `C(θ) = 3α·(Γ(θ)/c(3α))` of the profile's `z`-derivative:
`F_*(3α)(z,θ) = C(θ)·F̂(z)` with `F̂ = Work.FM.Fstar`. -/
def pzCoeff (α : ℝ) (θ : ℝ) : ℝ :=
  (3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))

/-- The profile `F_*(3α)` is its angular coefficient times `F̂`. -/
theorem fstar_three_eq_coeff (α z θ : ℝ) :
    Work.Construction.Fstar (3 * α) z θ = pzCoeff α θ * Work.FM.Fstar z := by
  simp only [Work.Construction.Fstar, pzCoeff]

/-- **The `z`-derivative of the profile**: `∂_z F_*(3α)(z,θ) = C(θ)·F̂'(z)` for `z ≥ 0`. -/
theorem pzFstar_eq {α : ℝ} {z θ : ℝ} (hz : 0 ≤ z) :
    Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ
      = pzCoeff α θ * deriv Work.FM.Fstar z := by
  have hd : DifferentiableAt ℝ Work.FM.Fstar z :=
    (Work.FM.hasDerivAt_Fstar z (by linarith)).differentiableAt
  have hdef : Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ
      = deriv (fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ) z := rfl
  have hfun : (fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ)
      = fun z' : ℝ => pzCoeff α θ * Work.FM.Fstar z' := by
    funext z'
    exact fstar_three_eq_coeff α z' θ
  rw [hdef, hfun, deriv_const_mul _ hd]

/-! ## The two moduli of the radial factor `F̂'` -/

/-- **The uniform bound `|F̂'(z)| ≤ 2` for `z ≥ 0`**: `F̂'(z) = 2(1-z)/(1+z)³` and
`|1 - z| ≤ (1+z)³` there. -/
theorem deriv_fstar_abs_le {z : ℝ} (hz : 0 ≤ z) : |deriv Work.FM.Fstar z| ≤ 2 := by
  have hpos : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  rw [Work.FM.deriv_Fstar z (by linarith)]
  have h1 : |1 - z| ≤ (1 + z) ^ 3 := by
    have ha : |1 - z| ≤ 1 + z := by
      rw [abs_le]
      constructor <;> linarith
    have hb : 1 + z ≤ (1 + z) ^ 3 := by
      simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 1 + z by linarith)
        (show (1 : ℕ) ≤ 3 by norm_num)
    linarith
  rw [abs_div, abs_mul, abs_of_pos hpos, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_le_iff₀ hpos]
  linarith

/-! ## The two moduli of the angular factor `Γ(3α) = Gam (3α)` -/

/-- `Gam (3α)` is the `α`-th power of the base `sinθcos²θ`. -/
theorem gam_three_eq {α θ : ℝ} :
    Work.Spaces.Gam (3 * α) θ = (Real.sin θ * Real.cos θ ^ 2) ^ α := by
  have h3 : (3 * α) / 3 = α := mul_div_cancel_left₀ α (by norm_num : (3 : ℝ) ≠ 0)
  rw [Work.Spaces.Gam, h3]

theorem gam_three_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam (3 * α) θ := by
  rw [gam_three_eq]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  exact Real.rpow_nonneg (mul_nonneg h1 (sq_nonneg (Real.cos θ))) α

theorem gam_three_le_one {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam (3 * α) θ ≤ 1 := by
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h3 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.cos_sq_le_one θ, sq_nonneg (Real.cos θ)]
  have hb0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg h1 (sq_nonneg _)
  have hb1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [h1, h2, sq_nonneg (Real.cos θ), h3]
  rw [gam_three_eq]
  exact Real.rpow_le_one hb0 hb1 hα.le

/-- **The angular modulus of `Gam (3α)`**: it is `α`-Hölder on `Iθ` with constant `3^α`, from
the `3`-Lipschitz modulus of the base `sinθcos²θ` and the `α`-Hölder modulus of `x ↦ x^α` on
`[0,∞)`. -/
theorem gam_three_holder {α θ θ' : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ'| ≤ 3 ^ α * |θ - θ'| ^ α := by
  have hb0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    exact mul_nonneg h1 (sq_nonneg _)
  have hb0' : 0 ≤ Real.sin θ' * Real.cos θ' ^ 2 := by
    have h1 : 0 ≤ Real.sin θ' :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
    exact mul_nonneg h1 (sq_nonneg _)
  rw [gam_three_eq (α := α) (θ := θ), gam_three_eq (α := α) (θ := θ')]
  calc |(Real.sin θ * Real.cos θ ^ 2) ^ α - (Real.sin θ' * Real.cos θ' ^ 2) ^ α|
      ≤ |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ^ α :=
        Moduli.rpow_abs_sub_le hb0 hb0' hα (le_trans hα13 (by norm_num))
    _ ≤ (3 * |θ - θ'|) ^ α :=
        Real.rpow_le_rpow (abs_nonneg _) (Moduli.sinCosSqLip θ θ') hα.le
    _ = 3 ^ α * |θ - θ'| ^ α := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (abs_nonneg _)]

/-! ## The two moduli of the angular coefficient `C` -/

/-- **The uniform bound `|C(θ)| ≤ 10`** on `Iθ`, for `0 < α ≤ 1/3`. -/
theorem pzCoeff_abs_le {α θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) : |pzCoeff α θ| ≤ 10 := by
  have h3a : 0 < 3 * α := by linarith
  have h3a1 : 3 * α ≤ 1 := by linarith
  have hc := Work.Spaces.c_bounds (3 * α) h3a h3a1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by linarith [hc.1]
  have hG0 : 0 ≤ Work.Spaces.Gam (3 * α) θ := gam_three_nonneg hθ
  have hG1 : Work.Spaces.Gam (3 * α) θ ≤ 1 := gam_three_le_one hα hθ
  have hnonneg : 0 ≤ (3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) :=
    mul_nonneg h3a.le (div_nonneg hG0 hcpos.le)
  have hgoal : (3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) ≤ 10 := by
    rw [mul_div_assoc', div_le_iff₀ hcpos]
    nlinarith [hc.1, hG1, hG0, h3a.le, h3a1]
  calc |pzCoeff α θ|
      = |(3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))| := rfl
    _ = (3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) := abs_of_nonneg hnonneg
    _ ≤ 10 := hgoal

/-- The difference of the angular coefficients, with a common denominator. -/
theorem pzCoeff_sub (α θ θ' : ℝ) :
    pzCoeff α θ - pzCoeff α θ'
      = (3 * α) * ((Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ')
          / Work.Spaces.c (3 * α)) := by
  simp only [pzCoeff]
  rw [← mul_sub, div_sub_div_same]

/-- **The angular modulus of the coefficient `C`**: `C` is `α`-Hölder on `Iθ` with constant
`30`. -/
theorem pzCoeff_holder {α θ θ' : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |pzCoeff α θ - pzCoeff α θ'| ≤ 30 * |θ - θ'| ^ α := by
  have h3a : 0 < 3 * α := by linarith
  have h3a1 : 3 * α ≤ 1 := by linarith
  have hc := Work.Spaces.c_bounds (3 * α) h3a h3a1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by linarith [hc.1]
  have hG := gam_three_holder hα hα13 hθ hθ'
  have hpow0 : 0 ≤ |θ - θ'| ^ α := Real.rpow_nonneg (abs_nonneg _) α
  have hfac : (3 * α) / Work.Spaces.c (3 * α) * 3 ^ α ≤ 30 := by
    have h1 : (3 * α) / Work.Spaces.c (3 * α) ≤ 10 := by
      rw [div_le_iff₀ hcpos]
      linarith [hc.1, h3a1]
    have h1' : 0 ≤ (3 * α) / Work.Spaces.c (3 * α) := by positivity
    have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
    have h2 : (3 : ℝ) ^ α ≤ 3 := by
      have h3 : (3 : ℝ) ^ α ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num) hα1
      rwa [Real.rpow_one] at h3
    have h4 : 0 ≤ (3 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) α
    nlinarith [h1, h1', h2, h4]
  have hbound : (3 * α) * (|Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ'|
        / Work.Spaces.c (3 * α)) ≤ 30 * |θ - θ'| ^ α := by
    calc (3 * α) * (|Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ'|
          / Work.Spaces.c (3 * α))
        ≤ (3 * α) * (3 ^ α * |θ - θ'| ^ α / Work.Spaces.c (3 * α)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hG hcpos.le) h3a.le
      _ = ((3 * α) / Work.Spaces.c (3 * α) * 3 ^ α) * |θ - θ'| ^ α := by
          rw [div_eq_mul_inv]
          ring
      _ ≤ 30 * |θ - θ'| ^ α := mul_le_mul_of_nonneg_right hfac hpow0
  rw [pzCoeff_sub, abs_mul, abs_of_nonneg h3a.le, abs_div, abs_of_pos hcpos]
  exact hbound

/-! ## The target -/

theorem pzFstarModuli {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
        |Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ| ≤ C) ∧
      (∀ z z' θ θ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
        |Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ
          - Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z' θ'|
          ≤ C * (|z - z'| + |θ - θ'|) ^ α) := by
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  refine ⟨140, by norm_num, ?_, ?_⟩
  · intro z θ hz hθ
    rw [pzFstar_eq (α := α) (z := z) (θ := θ) hz, abs_mul]
    calc |pzCoeff α θ| * |deriv Work.FM.Fstar z|
        ≤ 10 * 2 := mul_le_mul (pzCoeff_abs_le hα hα13 hθ) (deriv_fstar_abs_le hz)
            (abs_nonneg _) (by norm_num)
      _ ≤ 140 := by norm_num
  · intro z z' θ θ' hz hz' hθ hθ'
    rw [pzFstar_eq (α := α) (z := z) (θ := θ) hz,
      pzFstar_eq (α := α) (z := z') (θ := θ') hz']
    have hkey : pzCoeff α θ * deriv Work.FM.Fstar z - pzCoeff α θ' * deriv Work.FM.Fstar z'
        = pzCoeff α θ * (deriv Work.FM.Fstar z - deriv Work.FM.Fstar z')
          + (pzCoeff α θ - pzCoeff α θ') * deriv Work.FM.Fstar z' := by ring
    have hB : |pzCoeff α θ * (deriv Work.FM.Fstar z - deriv Work.FM.Fstar z')|
        ≤ 80 * |z - z'| := by
      rw [abs_mul]
      calc |pzCoeff α θ| * |deriv Work.FM.Fstar z - deriv Work.FM.Fstar z'|
          ≤ 10 * (8 * |z - z'|) := mul_le_mul (pzCoeff_abs_le hα hα13 hθ)
              (Moduli.fstarDerivLip hz hz') (abs_nonneg _) (by norm_num)
        _ = 80 * |z - z'| := by ring
    have hC : |(pzCoeff α θ - pzCoeff α θ') * deriv Work.FM.Fstar z'|
        ≤ (30 * |θ - θ'| ^ α) * 2 := by
      rw [abs_mul]
      exact mul_le_mul (pzCoeff_holder hα hα13 hθ hθ') (deriv_fstar_abs_le hz')
        (abs_nonneg _) (mul_nonneg (by norm_num) (Real.rpow_nonneg (abs_nonneg _) α))
    have hLip : |pzCoeff α θ * deriv Work.FM.Fstar z - pzCoeff α θ' * deriv Work.FM.Fstar z'|
        ≤ 80 * |z - z'| + 60 * |θ - θ'| ^ α := by
      rw [hkey]
      calc |pzCoeff α θ * (deriv Work.FM.Fstar z - deriv Work.FM.Fstar z')
            + (pzCoeff α θ - pzCoeff α θ') * deriv Work.FM.Fstar z'|
          ≤ |pzCoeff α θ * (deriv Work.FM.Fstar z - deriv Work.FM.Fstar z')|
            + |(pzCoeff α θ - pzCoeff α θ') * deriv Work.FM.Fstar z'| := abs_add_le _ _
        _ ≤ 80 * |z - z'| + (30 * |θ - θ'| ^ α) * 2 := add_le_add hB hC
        _ = 80 * |z - z'| + 60 * |θ - θ'| ^ α := by ring
    have hBnd : |pzCoeff α θ * deriv Work.FM.Fstar z - pzCoeff α θ' * deriv Work.FM.Fstar z'|
        ≤ 40 := by
      have h1 : |pzCoeff α θ * deriv Work.FM.Fstar z| ≤ 10 * 2 := by
        rw [abs_mul]
        exact mul_le_mul (pzCoeff_abs_le hα hα13 hθ) (deriv_fstar_abs_le hz)
          (abs_nonneg _) (by norm_num)
      have h2 : |pzCoeff α θ' * deriv Work.FM.Fstar z'| ≤ 10 * 2 := by
        rw [abs_mul]
        exact mul_le_mul (pzCoeff_abs_le hα hα13 hθ') (deriv_fstar_abs_le hz')
          (abs_nonneg _) (by norm_num)
      calc |pzCoeff α θ * deriv Work.FM.Fstar z - pzCoeff α θ' * deriv Work.FM.Fstar z'|
          = |pzCoeff α θ * deriv Work.FM.Fstar z
              + -(pzCoeff α θ' * deriv Work.FM.Fstar z')| := by rw [sub_eq_add_neg]
        _ ≤ |pzCoeff α θ * deriv Work.FM.Fstar z|
            + |-(pzCoeff α θ' * deriv Work.FM.Fstar z')| := abs_add_le _ _
        _ = |pzCoeff α θ * deriv Work.FM.Fstar z|
            + |pzCoeff α θ' * deriv Work.FM.Fstar z'| := by rw [abs_neg]
        _ ≤ 10 * 2 + 10 * 2 := add_le_add h1 h2
        _ = 40 := by norm_num
    have ht0 : 0 ≤ |z - z'| + |θ - θ'| := by positivity
    have hp0 : 0 ≤ (|z - z'| + |θ - θ'|) ^ α := Real.rpow_nonneg ht0 α
    rcases le_total (|z - z'| + |θ - θ'|) 1 with hcase | hcase
    · have htα : |z - z'| + |θ - θ'| ≤ (|z - z'| + |θ - θ'|) ^ α := by
        rcases eq_or_lt_of_le ht0 with h0 | h0
        · rw [← h0, Real.zero_rpow (ne_of_gt hα)]
        · have h3 := Real.rpow_le_rpow_of_exponent_ge h0 hcase hα1
          rwa [Real.rpow_one] at h3
      have hzp : |z - z'| ≤ (|z - z'| + |θ - θ'|) ^ α :=
        le_trans (le_add_of_nonneg_right (abs_nonneg _)) htα
      have hθp : |θ - θ'| ^ α ≤ (|z - z'| + |θ - θ'|) ^ α :=
        Real.rpow_le_rpow (abs_nonneg _) (le_add_of_nonneg_left (abs_nonneg _)) hα.le
      calc |pzCoeff α θ * deriv Work.FM.Fstar z - pzCoeff α θ' * deriv Work.FM.Fstar z'|
          ≤ 80 * |z - z'| + 60 * |θ - θ'| ^ α := hLip
        _ ≤ 80 * (|z - z'| + |θ - θ'|) ^ α + 60 * (|z - z'| + |θ - θ'|) ^ α :=
            add_le_add (mul_le_mul_of_nonneg_left hzp (by norm_num))
              (mul_le_mul_of_nonneg_left hθp (by norm_num))
        _ = 140 * (|z - z'| + |θ - θ'|) ^ α := by ring
    · have ht1 : 1 ≤ (|z - z'| + |θ - θ'|) ^ α := Real.one_le_rpow hcase hα.le
      calc |pzCoeff α θ * deriv Work.FM.Fstar z - pzCoeff α θ' * deriv Work.FM.Fstar z'|
          ≤ 40 := hBnd
        _ ≤ 140 * (|z - z'| + |θ - θ'|) ^ α := by nlinarith [ht1, hp0]

end Work.FTS.Regularity
