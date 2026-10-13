import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.Integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

open MeasureTheory

/-- Weighted pointwise `2ab ≤ a² + b²` estimate: if the weight `Q` is bounded by `c₁` times the
weight `Q₁` carrying `f` and by `c₂` times the weight `Q₂` carrying `g` (all weights nonnegative),
then `Q f g` is dominated by `c₁ (Q₁ f²) + c₂ (Q₂ g²)`. -/
private lemma abs_weight_mul_le {Q Q₁ Q₂ f g : ℝ × ℝ → ℝ} {c₁ c₂ : ℝ}
    (hQ0 : ∀ y, 0 ≤ Q y) (hQ10 : ∀ y, 0 ≤ Q₁ y) (hQ20 : ∀ y, 0 ≤ Q₂ y)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h1 : ∀ y, Q y ≤ c₁ * Q₁ y) (h2 : ∀ y, Q y ≤ c₂ * Q₂ y) (y : ℝ × ℝ) :
    |Q y * f y * g y| ≤ c₁ * (Q₁ y * f y ^ 2) + c₂ * (Q₂ y * g y ^ 2) := by
  have hQ : 0 ≤ Q y := hQ0 y
  have h2xy : 2 * |f y| * |g y| ≤ f y ^ 2 + g y ^ 2 := by
    nlinarith [sq_nonneg (|f y| - |g y|), sq_abs (f y), sq_abs (g y)]
  have hmain : Q y * |f y| * |g y| ≤ (Q y * f y ^ 2 + Q y * g y ^ 2) / 2 := by
    have h := mul_le_mul_of_nonneg_left h2xy hQ
    linarith [h]
  have hQf : Q y * f y ^ 2 ≤ c₁ * (Q₁ y * f y ^ 2) := by
    calc Q y * f y ^ 2 ≤ (c₁ * Q₁ y) * f y ^ 2 :=
          mul_le_mul_of_nonneg_right (h1 y) (sq_nonneg (f y))
      _ = c₁ * (Q₁ y * f y ^ 2) := by ring
  have hQg : Q y * g y ^ 2 ≤ c₂ * (Q₂ y * g y ^ 2) := by
    calc Q y * g y ^ 2 ≤ (c₂ * Q₂ y) * g y ^ 2 :=
          mul_le_mul_of_nonneg_right (h2 y) (sq_nonneg (g y))
      _ = c₂ * (Q₂ y * g y ^ 2) := by ring
  have hA : 0 ≤ c₁ * (Q₁ y * f y ^ 2) := mul_nonneg hc₁ (mul_nonneg (hQ10 y) (sq_nonneg (f y)))
  have hB : 0 ≤ c₂ * (Q₂ y * g y ^ 2) := mul_nonneg hc₂ (mul_nonneg (hQ20 y) (sq_nonneg (g y)))
  rw [abs_mul, abs_mul, abs_of_nonneg hQ]
  linarith [hmain, hQf, hQg, hA, hB]

/-- Integrability of a mixed product from two weighted `L²` bounds, when the cross weight `Q` is
controlled by the weights `Q₁`, `Q₂` attached to the two factors. -/
private lemma integrable_weight_cross {Q Q₁ Q₂ : ℝ × ℝ → ℝ} {c₁ c₂ : ℝ} {f g : ℝ × ℝ → ℝ}
    (hQm : Measurable Q) (hQ0 : ∀ y, 0 ≤ Q y) (hQ10 : ∀ y, 0 ≤ Q₁ y) (hQ20 : ∀ y, 0 ≤ Q₂ y)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h1 : ∀ y, Q y ≤ c₁ * Q₁ y) (h2 : ∀ y, Q y ≤ c₂ * Q₂ y)
    (hfm : Measurable f) (hgm : Measurable g)
    (hI1 : Integrable (fun y => Q₁ y * f y ^ 2))
    (hI2 : Integrable (fun y => Q₂ y * g y ^ 2)) :
    Integrable (fun y => Q y * f y * g y) := by
  refine Integrable.mono' ((hI1.const_mul c₁).add (hI2.const_mul c₂))
    ((hQm.mul hfm).mul hgm).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs]
  exact abs_weight_mul_le hQ0 hQ10 hQ20 hc₁ hc₂ h1 h2 y

theorem integrable_mixed_pair {Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) (p : ℝ × ℝ) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ (y - p) * G₂ y) ∧
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q (y - p) * G₁ (y - p) * G₂ y) ∧
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y * G₂ (y + p)) ∧
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y * G₂ (y - p)) := by
  have hE : (0 : ℝ) ≤ Real.exp (Cw * (|p.1| + |p.2|)) := Real.exp_nonneg _
  have hmsub : Measurable (fun y : ℝ × ℝ => y - p) := measurable_id.sub measurable_const
  have hmadd : Measurable (fun y : ℝ × ℝ => y + p) := measurable_id.add measurable_const
  have hG1sub : Measurable (fun y : ℝ × ℝ => G₁ (y - p)) := hG1m.comp hmsub
  have hG2sub : Measurable (fun y : ℝ × ℝ => G₂ (y - p)) := hG2m.comp hmsub
  have hG2add : Measurable (fun y : ℝ × ℝ => G₂ (y + p)) := hG2m.comp hmadd
  -- shifted weighted `L²` bounds, from translation invariance of Lebesgue measure on `ℝ × ℝ`
  have hI1sub : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q (y - p) * G₁ (y - p) ^ 2) := by
    simpa only [] using hI1.comp_sub_right p
  have hI2sub : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q (y - p) * G₂ (y - p) ^ 2) := by
    simpa only [] using hI2.comp_sub_right p
  have hI2add : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q (y + p) * G₂ (y + p) ^ 2) := by
    simpa only [] using hI2.comp_add_right p
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `∫ Q y G₁(y-p) G₂ y` : use the weight `Q(y-p)` for `G₁`, bounding `Q y ≤ e Q (y-p)`
    exact integrable_weight_cross (Q := Q) (Q₁ := fun y => Q (y - p)) (Q₂ := Q)
      (c₁ := Real.exp (Cw * (|p.1| + |p.2|))) (c₂ := 1)
      hQm hQ0 (fun y => hQ0 (y - p)) hQ0 hE (by norm_num)
      (fun y => by simpa using hQsh (y - p) p) (fun y => by simp)
      hG1sub hG2m hI1sub hI2
  · -- `∫ Q(y-p) G₁(y-p) G₂ y` : use the weight `Q(y-p)` for `G₂`, bounding `Q (y-p) ≤ e Q y`
    exact integrable_weight_cross (Q := fun y => Q (y - p)) (Q₁ := fun y => Q (y - p)) (Q₂ := Q)
      (c₁ := 1) (c₂ := Real.exp (Cw * (|p.1| + |p.2|)))
      (hQm.comp hmsub) (fun y => hQ0 (y - p)) (fun y => hQ0 (y - p)) hQ0 (by norm_num) hE
      (fun y => by simp) (fun y => by simpa using hQsh' (y - p) p)
      hG1sub hG2m hI1sub hI2
  · -- `∫ Q y G₁ y G₂(y+p)` : use the weight `Q(y+p)` for `G₂`, bounding `Q y ≤ e Q (y+p)`
    exact integrable_weight_cross (Q := Q) (Q₁ := Q) (Q₂ := fun y => Q (y + p))
      (c₁ := 1) (c₂ := Real.exp (Cw * (|p.1| + |p.2|)))
      hQm hQ0 hQ0 (fun y => hQ0 (y + p)) (by norm_num) hE
      (fun y => by simp) (fun y => by simpa using hQsh' y p)
      hG1m hG2add hI1 hI2add
  · -- `∫ Q y G₁ y G₂(y-p)` : use the weight `Q(y-p)` for `G₂`, bounding `Q y ≤ e Q (y-p)`
    exact integrable_weight_cross (Q := Q) (Q₁ := Q) (Q₂ := fun y => Q (y - p))
      (c₁ := 1) (c₂ := Real.exp (Cw * (|p.1| + |p.2|)))
      hQm hQ0 hQ0 (fun y => hQ0 (y - p)) (by norm_num) hE
      (fun y => by simp) (fun y => by simpa using hQsh (y - p) p)
      hG1m hG2sub hI1 hI2sub

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
