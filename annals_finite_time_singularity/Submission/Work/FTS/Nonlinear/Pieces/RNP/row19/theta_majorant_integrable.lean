/-
# Row 19: the two angular majorants of the `ℋ⁴`-integrand

This file proves the integrability of the two angular factors that appear in the
`ℋ⁴`-integrand of the row-19 piece `N₃^{**} = -2α·V(Φ̃_*)·D_zF_*`:

`θ ↦ Γ(θ)² · sin(2θ)^{-η}`  and  `θ ↦ (Γ(θ) + (α + sin 2θ)·sin(2θ)^{α/5})² · sin(2θ)^{-γ(α)}`

on `Iθ = [0,π/2]`, where (`Work.Spaces.Defs`)

`Γ(θ) = Gam α θ = (sin θ cos²θ)^{α/3}`, `η = 99/100`, `γ(α) = gam α = 1 + α/10`.

## Mathematics

Write `X = sin(2θ) ∈ [0,1]` on `Iθ`.

* **First term.** `Work.Spaces.Gam_bounds` gives `0 ≤ Γ ≤ 1`, hence
  `Γ² X^{-η} ≤ X^{-η}`, and `X^{-η}` is integrable on `Iθ` because `-1 < -η ≤ 0`
  (`Work.Spaces.sin_two_rpow`).
* **Second term.** Here the exponent `-γ(α)` is *strictly* less than `-1`, so the
  vanishing of the bracket at the endpoints is essential.  The key pointwise input is
  `Work.FTS.LocData.Gam_le_sin_two_rpow`, `Γ ≤ X^{α/5}`.  Hence, because `X ≤ 1`,

  `Γ + (α + X)X^{α/5} ≤ X^{α/5} + (α + 1)X^{α/5} = (α+2)X^{α/5}`,

  and squaring and multiplying by the nonnegative factor `X^{-γ(α)}` gives

  `(Γ + (α + X)X^{α/5})² X^{-γ} ≤ (α+2)² X^{2α/5-γ} = (α+2)² X^{3α/10-1}`.

  Since `3α/10 - 1 > -1` for `α > 0`, the majorant is integrable on `Iθ`
  (the case of a positive exponent is handled by continuity on the compact interval,
  the case of a nonpositive one by `Work.Spaces.sin_two_rpow`).

The exponent bookkeeping is the one used downstream: `2α/5 - γ(α) = 2α/5 - 1 - α/10
= 3α/10 - 1` (compare `Submission/Work/FTS/H2/Transport3Aux/MzG/slot.lean`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.FTS.LocData.Gam_le_sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

/-! ## Elementary angular facts -/

/-- On `Iθ = [0,π/2]` the quantity `sin(2θ)` is nonnegative. -/
lemma sin_two_nonneg_of_mem_Iθ_R {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Real.sin_two_mul]
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
    (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)

/-- **Integrability of the angular powers for all exponents `> -1`.**

For `-1 < p` the function `θ ↦ sin(2θ)^p` is integrable on `Iθ`.  (The case `p ≤ 0` is
`Work.Spaces.sin_two_rpow`; for `p > 0` the function is continuous on the compact
interval `Iθ`.) -/
lemma integrableOn_sin_two_rpow_gt {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ := by
  rcases lt_or_ge p 0 with h | h
  · exact (Work.Spaces.sin_two_rpow p hp (le_of_lt h)).1
  · have hcont : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ p :=
      (Real.continuous_rpow_const h).comp (by fun_prop)
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc

/-- `X^a · X^{-b} ≤ X^{a-b}` for `X ≥ 0`, `a > 0`, `b > 0`.  (For `X > 0` this is
`Real.rpow_add`, and at `X = 0` both sides degenerate to `0` up to the harmless case
`a = b`.) -/
lemma rpow_mul_rpow_neg_le {X a b : ℝ} (hX : 0 ≤ X) (ha : 0 < a) (hb : 0 < b) :
    X ^ a * X ^ (-b) ≤ X ^ (a - b) := by
  rcases eq_or_lt_of_le hX with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt ha), Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt hb)),
      mul_zero]
    exact Real.rpow_nonneg le_rfl _
  · rw [← Real.rpow_add h, show a + -b = a - b by ring]

/-! ## The pointwise bound for the second majorant -/

/-- **The bracket vanishes fast enough to beat the weight `sin(2θ)^{-γ(α)}`:**

`(Γ + (α + sin 2θ) sin(2θ)^{α/5})² · sin(2θ)^{-γ(α)} ≤ (α+2)² · sin(2θ)^{3α/10-1}`
on `Iθ`, for every `α > 0`. -/
lemma theta_bracket_le_self {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10 - 1) := by
  have hX0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ_R hθ
  have hX1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hGX : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
    Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ
  have hXp0 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hX0 _
  -- the bracket is at most `(α+2)·sin(2θ)^{α/5}`
  have hbracket : Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
      ≤ (α + 2) * (Real.sin (2 * θ)) ^ (α / 5) := by
    have h2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
        ≤ (α + 1) * (Real.sin (2 * θ)) ^ (α / 5) :=
      mul_le_mul_of_nonneg_right (by linarith) hXp0
    calc Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
        ≤ (Real.sin (2 * θ)) ^ (α / 5) + (α + 1) * (Real.sin (2 * θ)) ^ (α / 5) :=
          add_le_add hGX h2
      _ = (α + 2) * (Real.sin (2 * θ)) ^ (α / 5) := by ring
  -- squaring
  have hbr0 : 0 ≤ Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    add_nonneg hG0 (mul_nonneg (by linarith) hXp0)
  have hsq := pow_le_pow_left₀ hbr0 hbracket 2
  have hsqX : (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (α / 5)
      = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [← Real.rpow_add' hX0 (by linarith : α / 5 + α / 5 ≠ 0)]
    congr 1
    ring
  have hrhs : ((α + 2) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    have h : ((α + 2) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        = (α + 2) ^ 2
          * ((Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
    rw [h, hsqX]
  have hXg0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hX0 _
  have hstep : (Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← hrhs]
    exact mul_le_mul_of_nonneg_right hsq hXg0
  -- the exponent bookkeeping `2α/5 - γ(α) = 3α/10 - 1`
  have hcore : (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (3 * α / 10 - 1) := by
    have h := rpow_mul_rpow_neg_le hX0 (show 0 < 2 * α / 5 by linarith)
      (show 0 < Work.Spaces.gam α by rw [Work.Spaces.gam]; linarith)
    refine le_trans h (le_of_eq ?_)
    congr 1
    rw [Work.Spaces.gam]
    ring
  refine le_trans hstep ?_
  calc (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (α + 2) ^ 2
        * ((Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        ring
    _ ≤ (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10 - 1) :=
        mul_le_mul_of_nonneg_left hcore (sq_nonneg _)

/-! ## The main lemma -/

theorem theta_majorant_integrable {α : ℝ} (hα : 0 < α) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Gam α θ
            + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- First conjunct: `Γ² sin(2θ)^{-η} ≤ sin(2θ)^{-η}`.
  have hInt1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
    refine integrableOn_sin_two_rpow_gt ?_
    rw [Work.Spaces.eta]
    norm_num
  have hpt1 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    have hX0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ_R hθ
    have hG2 : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by nlinarith
    exact mul_le_of_le_one_left (Real.rpow_nonneg hX0 _) hG2
  have hmeas1 : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  have hf1 : IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    hInt1.mono' hmeas1 (by
      filter_upwards [hpt1, ae_restrict_mem hIθ] with θ h1 h2
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ_R h2) _))]
      exact h1)
  refine ⟨hf1, ?_⟩
  -- Second conjunct: dominated by `(α+2)² sin(2θ)^{3α/10-1}`.
  have hInt2 : IntegrableOn
      (fun θ : ℝ => (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10 - 1))
      Work.Spaces.Iθ :=
    (integrableOn_sin_two_rpow_gt (by linarith : (-1 : ℝ) < 3 * α / 10 - 1)).const_mul _
  have hpt2 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (α + 2) ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10 - 1) := by
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    exact theta_bracket_le_self hα hθ
  have hmeas2 : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Gam α θ
          + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam, Work.Spaces.gam]
    fun_prop
  exact hInt2.mono' hmeas2 (by
    filter_upwards [hpt2, ae_restrict_mem hIθ] with θ h1 h2
    have hX0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ_R h2
    rw [Real.norm_of_nonneg
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hX0 _))]
    exact h1)

end Work.FTS.Nonlinear.Pieces.RNP.row19
