/-
# `Work.FTS.RegPkgGal.R2.angIntegral_le` — the angular integral bound

For `0 < α ≤ 1` the function `θ ↦ (sin θ · cos²θ)^α / sin 2θ = Γ(θ)/sin 2θ` is integrable on
`[a,b] ⊆ [0, π/2]` and satisfies `∫_a^b Γ/sin(2·) ≤ M·(b-a)^α`.

## The mathematics

Write `s = sin 2θ`, `δ = π/2 - θ`.  Two pointwise facts:

* `(sinθ cos²θ)^α / sin 2θ ≤ 2^{-α} (sin 2θ)^{α-1}` — multiply by `sin 2θ ≥ 0`; the claim is
  `(sinθ cos²θ)^α ≤ (sinθ cosθ)^α = 2^{-α}(sin 2θ)^α` (since `cos²θ ≤ cosθ ≤ 1` on `Iθ`).
* `(sin 2θ)^{α-1} ≤ (4/π)^{α-1}·(θ^{α-1} + δ^{α-1})` on `(0, π/2)`: on `θ ≤ π/4`,
  `sin 2θ ≥ (2/π)(2θ) = 4θ/π`; on `θ ≥ π/4`, `sin 2θ = sin(2δ) ≥ 4δ/π`; and the exponent `α-1`
  is negative, so the inequality reverses.

Both `θ^{α-1}` and `δ^{α-1}` are integrable on `[a,b]` (`-1 < α-1`), and with
`s ↦ s^α` subadditive (`Real.rpow_add_le_add_rpow`) for `0 < α ≤ 1`,
`b^α - a^α ≤ (b-a)^α` and `(π/2-a)^α - (π/2-b)^α ≤ (b-a)^α`.  Hence
`∫_a^b Γ/sin 2· ≤ 2·2^{-α}(4/π)^{α-1}/α · (b-a)^α`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R2

/-- The pointwise bound `(sinθ cos²θ)^α/sin 2θ ≤ 2^{-α}(sin 2θ)^{α-1}` (valid on all of
`[0, π/2]`; at the endpoints both sides are `0`). -/
private lemma fA {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) (Real.pi / 2)) :
    (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)
      ≤ 2 ^ (-α) * (Real.sin (2 * θ)) ^ (α - 1) := by
  have hsin2nn : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [hs, div_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (le_refl 0) _)
  · have hs2 : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hsin2nn (Ne.symm hs)
    have hsinθ : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])
    have hcosθ : 0 ≤ Real.cos θ := by
      by_contra h
      push Not at h
      have h2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
      nlinarith [hs2]
    have hcosle : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hc2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith
    have hAB : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * Real.cos θ :=
      mul_le_mul_of_nonneg_left hc2 hsinθ
    have h0A : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by positivity
    have hpow : (Real.sin θ * Real.cos θ ^ 2) ^ α ≤ (Real.sin θ * Real.cos θ) ^ α :=
      Real.rpow_le_rpow h0A hAB hα.le
    have key : (Real.sin θ * Real.cos θ) ^ α = 2 ^ (-α) * (Real.sin (2 * θ)) ^ α := by
      have hs2' : Real.sin (2 * θ) = 2 * (Real.sin θ * Real.cos θ) := by
        rw [Real.sin_two_mul]; ring
      rw [hs2', Real.mul_rpow (by norm_num) (mul_nonneg hsinθ hcosθ),
        Real.rpow_neg (x := 2) (by norm_num) α]
      rw [inv_mul_cancel_left₀ (Real.rpow_pos_of_pos (x := 2) (by norm_num) α).ne']
    rw [key] at hpow
    calc (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)
        ≤ 2 ^ (-α) * (Real.sin (2 * θ)) ^ α / Real.sin (2 * θ) :=
          div_le_div_of_nonneg_right hpow hsin2nn
      _ = 2 ^ (-α) * (Real.sin (2 * θ)) ^ (α - 1) := by
          rw [mul_div_assoc, Real.rpow_sub hs2 α 1, Real.rpow_one]

/-- `(sin 2θ)^{α-1} ≤ (4/π)^{α-1}·(θ^{α-1} + (π/2-θ)^{α-1})` on the open interval. -/
private lemma fB {α : ℝ} (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (α - 1)
      ≤ (4 / Real.pi) ^ (α - 1) * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1)) := by
  have hθ0 : 0 < θ := hθ.1
  have hδ : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hC : 0 < (4 / Real.pi) ^ (α - 1) := by positivity
  have hexp : α - 1 ≤ 0 := by linarith
  rcases le_or_gt θ (Real.pi / 4) with hle | hgt
  · have hs : 4 / Real.pi * θ ≤ Real.sin (2 * θ) := by
      have h2 : 0 ≤ 2 * θ := by linarith
      have h3 : 2 * θ ≤ Real.pi / 2 := by linarith
      have h := Real.mul_le_sin h2 h3
      have he : (2 : ℝ) / Real.pi * (2 * θ) = 4 / Real.pi * θ := by ring
      linarith [h, he]
    have hp : 0 < 4 / Real.pi * θ := by positivity
    have h1 : (Real.sin (2 * θ)) ^ (α - 1) ≤ (4 / Real.pi * θ) ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos hp hs hexp
    rw [Real.mul_rpow (by positivity) hθ0.le] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hδ.le _)) hC.le)
  · have hsin : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
      have h2 : 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ := by ring
      rw [h2, Real.sin_pi_sub]
    have hs : 4 / Real.pi * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
      rw [hsin]
      have hx0 : 0 ≤ 2 * (Real.pi / 2 - θ) := by linarith
      have hx1 : 2 * (Real.pi / 2 - θ) ≤ Real.pi / 2 := by linarith
      have h := Real.mul_le_sin hx0 hx1
      have he : (2 : ℝ) / Real.pi * (2 * (Real.pi / 2 - θ)) = 4 / Real.pi * (Real.pi / 2 - θ) := by
        ring
      linarith [h, he]
    have hp : 0 < 4 / Real.pi * (Real.pi / 2 - θ) := by positivity
    have h1 : (Real.sin (2 * θ)) ^ (α - 1) ≤ (4 / Real.pi * (Real.pi / 2 - θ)) ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos hp hs hexp
    rw [Real.mul_rpow (by positivity) hδ.le] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg hθ0.le _)) hC.le)

/-- The combined pointwise domination on `[0, π/2]`. -/
private lemma fpoint {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Icc (0:ℝ) (Real.pi / 2)) :
    (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)
      ≤ 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1)) := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hL : (Real.sin 0 * Real.cos 0 ^ 2) ^ α / Real.sin (2 * 0) = 0 := by
      rw [show (2:ℝ) * 0 = 0 from by norm_num, Real.sin_zero, Real.cos_zero, one_pow,
        zero_mul, Real.zero_rpow (x := α) hα.ne', div_zero]
    rw [hL, sub_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (add_nonneg (by positivity) (by positivity))
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · subst h2
      have hL : (Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2) ^ α
          / Real.sin (2 * (Real.pi / 2)) = 0 := by
        rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi, Real.cos_pi_div_two,
          zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, Real.zero_rpow (x := α) hα.ne', div_zero]
      rw [hL, sub_self]
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (add_nonneg (by positivity) (Real.rpow_nonneg le_rfl _))
    · have hA := fA hα hθ
      have hB := fB hα1 (show θ ∈ Ioo (0:ℝ) (Real.pi / 2) from ⟨h0, h2⟩)
      calc (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)
          ≤ 2 ^ (-α) * (Real.sin (2 * θ)) ^ (α - 1) := hA
        _ ≤ 2 ^ (-α) * ((4 / Real.pi) ^ (α - 1) * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1))) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
        _ = 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1)) := by
            ring

theorem angIntegral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      IntervalIntegrable
          (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          MeasureTheory.volume a b ∧
        (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          ≤ M * (b - a) ^ α := by
  refine ⟨2 * (2 ^ (-α) * (4 / Real.pi) ^ (α - 1)) / α, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt (mul_pos (by positivity) (by positivity))))
      hα.le
  · intro a b ha hab hb
    have hC : 0 < 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) := mul_pos (by positivity) (by positivity)
    have hr : (-1 : ℝ) < α - 1 := by linarith
    have h1i : IntervalIntegrable (fun θ : ℝ => θ ^ (α - 1)) volume a b :=
      intervalIntegral.intervalIntegrable_rpow' hr
    have h2i' : IntervalIntegrable (fun x : ℝ => x ^ (α - 1)) volume (Real.pi / 2 - a)
        (Real.pi / 2 - b) :=
      intervalIntegral.intervalIntegrable_rpow' hr
    have h2i : IntervalIntegrable (fun θ : ℝ => (Real.pi / 2 - θ) ^ (α - 1)) volume a b := by
      have h := h2i'.comp_sub_left (Real.pi / 2)
      simpa using h
    have hdom : IntervalIntegrable
        (fun θ : ℝ => 2 ^ (-α) * (4 / Real.pi) ^ (α - 1)
          * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1))) volume a b :=
      (h1i.add h2i).const_mul _
    have hf_meas : AEStronglyMeasurable
        (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
        (volume.restrict (uIoc a b)) := by
      refine Measurable.aestronglyMeasurable ?_
      have h1 : Measurable (fun x : ℝ => Real.sin x * Real.cos x ^ 2) :=
        Real.measurable_sin.mul (Real.measurable_cos.pow_const 2)
      have h2 : Measurable (fun x : ℝ => (Real.sin x * Real.cos x ^ 2) ^ α) :=
        h1.pow measurable_const
      have h3 : Measurable (fun x : ℝ => Real.sin (2 * x)) :=
        Real.measurable_sin.comp (measurable_id.const_mul 2)
      exact h2.div h3
    have hae : (fun x : ℝ => ‖(Real.sin x * Real.cos x ^ 2) ^ α / Real.sin (2 * x)‖)
        ≤ᵐ[volume.restrict (uIoc a b)]
        (fun θ : ℝ => 2 ^ (-α) * (4 / Real.pi) ^ (α - 1)
          * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1))) := by
      rw [uIoc_of_le hab]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1.le
      have hx1 : x ≤ Real.pi / 2 := le_trans hx.2 hb
      have hsinx : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_pos, hx0, hx1])
      have hsin2x : 0 ≤ Real.sin (2 * x) :=
        Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_pos, hx0, hx1])
      have hfnn : 0 ≤ (Real.sin x * Real.cos x ^ 2) ^ α / Real.sin (2 * x) :=
        div_nonneg (Real.rpow_nonneg (mul_nonneg hsinx (by positivity)) _) hsin2x
      rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
      exact fpoint hα hα1 ⟨hx0, hx1⟩
    have hf_int : IntervalIntegrable
        (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)) volume a b :=
      IntervalIntegrable.mono_fun' hdom hf_meas hae
    refine ⟨hf_int, ?_⟩
    have hmono : (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
        ≤ ∫ θ in a..b, 2 ^ (-α) * (4 / Real.pi) ^ (α - 1)
            * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1)) := by
      refine intervalIntegral.integral_mono_on hab hf_int hdom (fun x hx => ?_)
      exact fpoint hα hα1 ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
    have hval1 : ∫ θ in a..b, θ ^ (α - 1) = (b ^ α - a ^ α) / α := by
      rw [integral_rpow (Or.inl hr), show (α - 1) + 1 = α by ring]
    have hval2 : ∫ θ in a..b, (Real.pi / 2 - θ) ^ (α - 1)
        = ((Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α) / α := by
      rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (α - 1)) (Real.pi / 2),
        integral_rpow (Or.inl hr), show (α - 1) + 1 = α by ring]
    have hhint : ∫ θ in a..b, 2 ^ (-α) * (4 / Real.pi) ^ (α - 1)
          * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1))
        = 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) *
          (((b ^ α - a ^ α) / α) + (((Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α) / α)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1i h2i, hval1, hval2]
    have hb1 : b ^ α - a ^ α ≤ (b - a) ^ α := by
      have h := Real.rpow_add_le_add_rpow (p := α) (a := a) (b := b - a) ha (by linarith) hα.le hα1
      rw [show a + (b - a) = b from by ring] at h
      linarith
    have hb2 : (Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α ≤ (b - a) ^ α := by
      have h := Real.rpow_add_le_add_rpow (p := α) (a := Real.pi / 2 - b) (b := b - a)
        (by linarith : (0:ℝ) ≤ Real.pi / 2 - b) (by linarith : (0:ℝ) ≤ b - a) hα.le hα1
      rw [show Real.pi / 2 - b + (b - a) = Real.pi / 2 - a from by ring] at h
      linarith
    have hsum : (b ^ α - a ^ α) + ((Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α)
        ≤ 2 * (b - a) ^ α := by
      linarith
    have hdiv : ((b ^ α - a ^ α) / α) + (((Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α) / α)
        ≤ 2 * (b - a) ^ α / α := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hsum hα.le
    calc (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
        ≤ ∫ θ in a..b, 2 ^ (-α) * (4 / Real.pi) ^ (α - 1)
            * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1)) := hmono
      _ = 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) *
            (((b ^ α - a ^ α) / α) + (((Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α) / α)) :=
            hhint
      _ ≤ 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) * (2 * (b - a) ^ α / α) :=
            mul_le_mul_of_nonneg_left hdiv hC.le
      _ = 2 * (2 ^ (-α) * (4 / Real.pi) ^ (α - 1)) / α * (b - a) ^ α := by ring

end Work.FTS.RegPkgGal.R2
