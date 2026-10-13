import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.L12Sub4.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12Sub4

/-! ## Calculus of the log-coordinate angular weight `Glw`

`Glw ζ = κ(ζ) · K (arctan (e^ζ))` with `κ ζ = e^ζ/(1+e^{2ζ})` and `K θ = 3 sin θ cos²θ`.
Writing `θ = arctan (a)`, `a = e^ζ`, so that `sin θ = a/√(1+a²)` and `cos θ = 1/√(1+a²)`
(`Real.sin_arctan`, `Real.cos_arctan`), one gets the closed form

  `Glw ζ = 3 e^{2ζ} / (1 + e^{2ζ})^{5/2} = 3 e^{2ζ} / (√(1 + e^{2ζ}))^5`.

The statements below are the elementary consequences: continuity, positivity, and the
translation bounds used to control the mollifier shift `ζ ↦ ζ + q`. -/

/-- **Closed form of `Glw`**, written with `Real.sqrt` so that no fractional power (`rpow`) is
needed: `Glw ζ = 3 e^{2ζ} / (√(1 + e^{2ζ}))^5`. -/
theorem Glw_eq_sqrt (ζ : ℝ) :
    Glw ζ = 3 * Real.exp (2 * ζ) / (Real.sqrt (1 + Real.exp (2 * ζ))) ^ 5 := by
  have h1 : Real.exp (2 * ζ) = (Real.exp ζ) ^ 2 := by
    have := Real.exp_nat_mul (ζ) 2
    simpa using this
  unfold Glw Work.FTS.StrongEps.HkSqAux.kappa Work.Spaces.K
  rw [Real.sin_arctan, Real.cos_arctan]
  rw [h1]
  set s := Real.sqrt (1 + (Real.exp ζ) ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 + (Real.exp ζ) ^ 2 := by
    rw [hsdef]; exact Real.sq_sqrt (by positivity)
  have hs : s ≠ 0 := by positivity
  have h2 : Real.exp ζ ≠ 0 := Real.exp_ne_zero ζ
  field_simp
  ring_nf
  rw [hs2]

theorem continuous_Glw : Continuous Glw := by
  unfold Glw Work.FTS.StrongEps.HkSqAux.kappa Work.Spaces.K
  apply Continuous.mul
  · apply Continuous.div
    · exact Real.continuous_exp
    · fun_prop
    · intro ζ; positivity
  · fun_prop

theorem Glw_pos (ζ : ℝ) : 0 < Glw ζ := by
  rw [Glw_eq_sqrt ζ]
  positivity

/-- The comparison of the two `sqrt`-factors of the closed form of `Glw`: for `t ≥ 1`,
`√(1+x) ≤ √(1+tx)`. -/
private lemma sqrt_one_add_le (x t : ℝ) (hx : 0 < x) (ht : 1 ≤ t) :
    Real.sqrt (1 + x) ≤ Real.sqrt (1 + t * x) := by
  apply Real.sqrt_le_sqrt
  nlinarith [hx, ht]

/-- **Upper bound for the shift with `t ≥ 1`**: `t (√(1+x))^5 ≤ t^4 (√(1+tx))^5`. -/
private lemma Glw_key_ge_one (x t : ℝ) (hx : 0 < x) (ht : 1 ≤ t) :
    t * (Real.sqrt (1 + x)) ^ 5 ≤ t ^ 4 * (Real.sqrt (1 + t * x)) ^ 5 := by
  have h1 : Real.sqrt (1 + x) ≤ Real.sqrt (1 + t * x) := sqrt_one_add_le x t hx ht
  have h2 : t * (Real.sqrt (1 + x)) ^ 5 ≤ t * (Real.sqrt (1 + t * x)) ^ 5 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 5) (by linarith)
  have h3 : t ≤ t ^ 4 := by
    have := pow_le_pow_right₀ ht (by norm_num : (1 : ℕ) ≤ 4)
    simpa using this
  have h4 : t * (Real.sqrt (1 + t * x)) ^ 5 ≤ t ^ 4 * (Real.sqrt (1 + t * x)) ^ 5 :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  linarith

/-- **Upper bound for the shift with `0 < t ≤ 1`**: `t (√(1+x))^5 ≤ (t^4)⁻¹ (√(1+tx))^5`. -/
private lemma Glw_key_le_one (x t : ℝ) (hx : 0 < x) (ht : 0 < t) (ht1 : t ≤ 1) :
    t * (Real.sqrt (1 + x)) ^ 5 ≤ (t ^ 4)⁻¹ * (Real.sqrt (1 + t * x)) ^ 5 := by
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have hsl : t * Real.sqrt (1 + x) ≤ Real.sqrt (1 + t * x) := by
    have h1 : t * Real.sqrt (1 + x) = Real.sqrt (t ^ 2 * (1 + x)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt ht)]
    rw [h1]
    apply Real.sqrt_le_sqrt
    nlinarith [hx, ht2, ht1]
  have hpow : (t * Real.sqrt (1 + x)) ^ 5 ≤ (Real.sqrt (1 + t * x)) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hsl 5
  rw [le_inv_mul_iff₀ (by positivity : (0 : ℝ) < t ^ 4)]
  rw [show t ^ 4 * (t * (Real.sqrt (1 + x)) ^ 5) = (t * Real.sqrt (1 + x)) ^ 5 by
    rw [mul_pow]; ring]
  exact hpow

/-- **Third conjunct of `GlwFacts`**: shifting the log-coordinate by `q` changes the angular
weight by at most a factor `e^{8|q|}`. -/
theorem Glw_shift_le (ζ q : ℝ) : Glw (ζ + q) ≤ Real.exp (8 * |q|) * Glw ζ := by
  rw [Glw_eq_sqrt (ζ + q), Glw_eq_sqrt ζ]
  set x := Real.exp (2 * ζ) with hxdef
  set t := Real.exp (2 * q) with htdef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have htpos : 0 < t := by rw [htdef]; positivity
  have hexp : Real.exp (2 * (ζ + q)) = t * x := by
    rw [show (2 : ℝ) * (ζ + q) = 2 * ζ + 2 * q from by ring, Real.exp_add, ← hxdef, ← htdef]
    ring
  rw [hexp]
  have hsqx : 0 < (Real.sqrt (1 + x)) ^ 5 := by positivity
  have hsqt : 0 < (Real.sqrt (1 + t * x)) ^ 5 := by positivity
  by_cases hcase : 1 ≤ t
  · -- `q ≥ 0`: the ratio is at most `t`, and `e^{8q} = t^4`
    have hq0 : 0 ≤ q := by
      have h : 0 ≤ 2 * q := Real.one_le_exp_iff.mp (by rw [← htdef]; exact hcase)
      linarith
    have hE : Real.exp (8 * |q|) = t ^ 4 := by
      rw [abs_of_nonneg hq0]
      rw [show (8 : ℝ) * q = ((4 : ℕ) : ℝ) * (2 * q) from by push_cast; ring,
        Real.exp_nat_mul, ← htdef]
    rw [hE]
    have hkey := Glw_key_ge_one x t hxpos hcase
    rw [show t ^ 4 * (3 * x / (Real.sqrt (1 + x)) ^ 5)
          = (t ^ 4 * 3 * x) / (Real.sqrt (1 + x)) ^ 5 from by ring]
    rw [div_le_div_iff₀ hsqt hsqx]
    rw [show 3 * (t * x) * (Real.sqrt (1 + x)) ^ 5
          = (3 * x) * (t * (Real.sqrt (1 + x)) ^ 5) from by ring,
        show (t ^ 4 * 3 * x) * (Real.sqrt (1 + t * x)) ^ 5
          = (3 * x) * (t ^ 4 * (Real.sqrt (1 + t * x)) ^ 5) from by ring]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  · -- `q < 0`: the ratio is at most `t^{-4}`, and `e^{-8q} = (t^4)⁻¹`
    have ht1 : t < 1 := lt_of_not_ge hcase
    have hq0 : q < 0 := by
      have h : 2 * q < 0 := Real.exp_lt_one_iff.mp (by rw [← htdef]; exact ht1)
      linarith
    have hE : Real.exp (8 * |q|) = (t ^ 4)⁻¹ := by
      rw [abs_of_neg hq0]
      rw [show (8 : ℝ) * -q = -(((4 : ℕ) : ℝ) * (2 * q)) from by push_cast; ring, Real.exp_neg]
      congr 1
      rw [Real.exp_nat_mul, ← htdef]
    rw [hE]
    have hkey := Glw_key_le_one x t hxpos htpos (le_of_lt ht1)
    rw [show (t ^ 4)⁻¹ * (3 * x / (Real.sqrt (1 + x)) ^ 5)
          = ((t ^ 4)⁻¹ * 3 * x) / (Real.sqrt (1 + x)) ^ 5 from by ring]
    rw [div_le_div_iff₀ hsqt hsqx]
    rw [show 3 * (t * x) * (Real.sqrt (1 + x)) ^ 5
          = (3 * x) * (t * (Real.sqrt (1 + x)) ^ 5) from by ring,
        show ((t ^ 4)⁻¹ * 3 * x) * (Real.sqrt (1 + t * x)) ^ 5
          = (3 * x) * ((t ^ 4)⁻¹ * (Real.sqrt (1 + t * x)) ^ 5) from by ring]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- Basic calculus of the log-coordinate angular weight
`Glw ζ = κ(ζ) · K(arctan (e^ζ))` (`Work.FTS.StrongEps.L12Sub4.Glw`, `κ = HkSqAux.kappa`).

Hints for the prover: the clean form is `Glw ζ = 3 · e^{2ζ} / (1 + e^{2ζ})^{5/2}` (from
`Real.sin_arctan`, `Real.cos_arctan`, `K θ = 3 sinθ cos²θ` and `κ ζ = sinθ cosθ` for `θ = arctan (e^ζ)`;
equivalently `Glw ζ = 3 sin²θ cos³θ`); with `x = e^{2ζ}` and `t = e^{2q}` the ratio is
`Glw (ζ+q)/Glw ζ = t (1+x)^{5/2}/(1+tx)^{5/2}` which lies between `e^{-8|q|}` and `e^{8|q|}` for
`|q| ≤ 1`, giving the third conjunct with room to spare; the fourth follows from
`|Glw(ζ+q) - Glw ζ| = Glw ζ |R - 1|` with `|R-1| ≤ 8|q|e^8`. -/
theorem GlwFacts :
    Continuous Glw ∧ (∀ ζ : ℝ, 0 < Glw ζ) ∧
      (∀ ζ q : ℝ, Glw (ζ + q) ≤ Real.exp (8 * |q|) * Glw ζ) ∧
      (∀ ζ q : ℝ, |q| ≤ 1 → |Glw (ζ + q) - Glw ζ| ≤ 8 * Real.exp 8 * |q| * Glw ζ) := by
  refine ⟨continuous_Glw, Glw_pos, Glw_shift_le, ?_⟩
  intro ζ q hq
  have hb : 0 < Glw ζ := Glw_pos ζ
  have h1 : Glw (ζ + q) ≤ Real.exp (8 * |q|) * Glw ζ := Glw_shift_le ζ q
  have h2 : Glw ζ ≤ Real.exp (8 * |q|) * Glw (ζ + q) := by
    have h := Glw_shift_le (ζ + q) (-q)
    rwa [show ζ + q + -q = ζ from by ring, abs_neg] at h
  -- the two-sided bound `e^{-8|q|} Glw ζ ≤ Glw (ζ+q) ≤ e^{8|q|} Glw ζ`
  have h3 : Real.exp (-(8 * |q|)) * Glw ζ ≤ Glw (ζ + q) := by
    have h := mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos (-(8 * |q|))))
    have he : Real.exp (-(8 * |q|)) * Real.exp (8 * |q|) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc Real.exp (-(8 * |q|)) * Glw ζ
        ≤ Real.exp (-(8 * |q|)) * (Real.exp (8 * |q|) * Glw (ζ + q)) := h
      _ = Glw (ζ + q) := by rw [← mul_assoc, he, one_mul]
  have hub : Glw (ζ + q) - Glw ζ ≤ Glw ζ * (Real.exp (8 * |q|) - 1) := by
    nlinarith [h1]
  have h4 : 1 - Real.exp (-(8 * |q|)) ≤ Real.exp (8 * |q|) - 1 := by
    have h5 : 1 - Real.exp (-(8 * |q|)) ≤ 8 * |q| := by
      have := Real.add_one_le_exp (-(8 * |q|)); linarith
    have h6 : 8 * |q| ≤ Real.exp (8 * |q|) - 1 := by
      have := Real.add_one_le_exp (8 * |q|); linarith
    linarith
  have hdn : Glw ζ - Glw (ζ + q) ≤ Glw ζ * (Real.exp (8 * |q|) - 1) := by
    calc Glw ζ - Glw (ζ + q) ≤ Glw ζ - Real.exp (-(8 * |q|)) * Glw ζ := by linarith
      _ = Glw ζ * (1 - Real.exp (-(8 * |q|))) := by ring
      _ ≤ Glw ζ * (Real.exp (8 * |q|) - 1) := mul_le_mul_of_nonneg_left h4 (le_of_lt hb)
  have habs : |Glw (ζ + q) - Glw ζ| ≤ Glw ζ * (Real.exp (8 * |q|) - 1) := by
    rw [abs_sub_le_iff]
    exact ⟨hub, hdn⟩
  have hexp : Real.exp (8 * |q|) - 1 ≤ 8 * |q| * Real.exp 8 := by
    have hs0 : (0 : ℝ) ≤ 8 * |q| := by positivity
    have hx1 : Real.exp (8 * |q|) - 1 ≤ 8 * |q| * Real.exp (8 * |q|) := by
      have h5 : 1 - Real.exp (-(8 * |q|)) ≤ 8 * |q| := by
        have := Real.add_one_le_exp (-(8 * |q|)); linarith
      have hm := mul_le_mul_of_nonneg_left h5 (le_of_lt (Real.exp_pos (8 * |q|)))
      have he : Real.exp (8 * |q|) * Real.exp (-(8 * |q|)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith [hm, he]
    have hx2 : Real.exp (8 * |q|) ≤ Real.exp 8 :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg q, hq])
    calc Real.exp (8 * |q|) - 1 ≤ 8 * |q| * Real.exp (8 * |q|) := hx1
      _ ≤ 8 * |q| * Real.exp 8 := mul_le_mul_of_nonneg_left hx2 hs0
  calc |Glw (ζ + q) - Glw ζ| ≤ Glw ζ * (Real.exp (8 * |q|) - 1) := habs
    _ ≤ Glw ζ * (8 * |q| * Real.exp 8) := mul_le_mul_of_nonneg_left hexp (le_of_lt hb)
    _ = 8 * Real.exp 8 * |q| * Glw ζ := by ring

end Work.FTS.StrongEps.L12Sub4
