import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.integral_integral_tsum_mul`

Interchange of the iterated integral with a series of product form
`∑' j, a j * φ j x * ψ j y`, under the pointwise dominating bounds `|φ j x| ≤ Φ x` and
`|ψ j y| ≤ Ψ y` (with `Φ`, `Ψ` integrable) and summable coefficients `a`.

The two one-variable ingredients are proved as separate lemmas below:

* `integral_tsum_mul_of_norm_bound` — a series of integrable functions with summable
  coefficients and a uniform integrable dominator may be integrated term by term;
* `summable_mul_integral_of_norm_bound` — the coefficients times the integrals of the inner
  family remain summable (this is what makes the outer interchange legal).
-/

namespace Work.BoseRowsFS

open MeasureTheory

/-- **One-variable `tsum`/integral interchange.**  If `b` is summable, each `f j` is integrable
and the whole family is dominated by a single integrable function `B`, then the integral of the
series is the series of the integrals. -/
theorem integral_tsum_mul_of_norm_bound {ι : Type*} [Countable ι] {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {b : ι → ℝ} (hb : Summable b) {f : ι → α → ℝ}
    {B : α → ℝ} (hf : ∀ j, Integrable (f j) μ) (hB : Integrable B μ)
    (hbf : ∀ j y, |f j y| ≤ B y) :
    ∫ y, (∑' j, b j * f j y) ∂μ = ∑' j, b j * ∫ y, f j y ∂μ := by
  have hint : ∀ j, Integrable (fun y => b j * f j y) μ := fun j => (hf j).const_mul _
  have hsum : Summable fun j => ∫ y, ‖b j * f j y‖ ∂μ := by
    refine Summable.of_norm_bounded (hb.abs.mul_right (∫ y, B y ∂μ)) fun j => ?_
    have hpt : ∀ y, ‖b j * f j y‖ ≤ |b j| * B y := fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hbf j y) (abs_nonneg _)
    have hmono : ∫ y, ‖b j * f j y‖ ∂μ ≤ ∫ y, |b j| * B y ∂μ :=
      integral_mono (hint j).norm (hB.const_mul _) hpt
    rw [integral_const_mul] at hmono
    rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    exact hmono
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  exact tsum_congr fun j => integral_const_mul _ _

/-- **Summability of the smeared coefficients.**  If `a` is summable, each `f j` is integrable and
`|f j|` is dominated by an integrable `B`, then the family `j ↦ a j * ∫ y, f j y` is summable. -/
theorem summable_mul_integral_of_norm_bound {ι : Type*} [Countable ι] {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {a : ι → ℝ} (ha : Summable a) {f : ι → α → ℝ}
    {B : α → ℝ} (hf : ∀ j, Integrable (f j) μ) (hB : Integrable B μ)
    (hbf : ∀ j y, |f j y| ≤ B y) :
    Summable fun j => a j * ∫ y, f j y ∂μ := by
  refine Summable.of_norm_bounded (ha.abs.mul_right (∫ y, B y ∂μ)) fun j => ?_
  have hle : |∫ y, f j y ∂μ| ≤ ∫ y, B y ∂μ := by
    calc |∫ y, f j y ∂μ| ≤ ∫ y, |f j y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ y, B y ∂μ := integral_mono (hf j).abs hB (fun y => hbf j y)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

theorem integral_integral_tsum_mul {ι : Type*} [Countable ι] {a : ι → ℝ} (ha : Summable a)
    {φ ψ : ι → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ Ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ : ∀ j, MeasureTheory.Integrable (φ j)) (hψ : ∀ j, MeasureTheory.Integrable (ψ j))
    (hΦ : MeasureTheory.Integrable Φ) (hΨ : MeasureTheory.Integrable Ψ)
    (hΦ0 : ∀ x, 0 ≤ Φ x) (hΨ0 : ∀ y, 0 ≤ Ψ y)
    (hbφ : ∀ j x, |φ j x| ≤ Φ x) (hbψ : ∀ j y, |ψ j y| ≤ Ψ y) :
    (∫ x, ∫ y, ∑' j, a j * φ j x * ψ j y)
      = ∑' j, a j * (∫ x, φ j x) * (∫ y, ψ j y) := by
  have _hΦ0 := hΦ0
  have _hΨ0 := hΨ0
  -- coefficients of the inner interchange are summable: `|a j * φ j x| ≤ |a j| * Φ x`
  have hsumφ : ∀ x, Summable fun j => a j * φ j x := by
    intro x
    refine Summable.of_norm_bounded (ha.abs.mul_right (Φ x)) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hbφ j x) (abs_nonneg _)
  -- coefficients of the outer interchange are summable: `|∫ y, ψ j y| ≤ ∫ y, Ψ y`
  have hsumI : Summable fun j => a j * ∫ y, ψ j y :=
    summable_mul_integral_of_norm_bound ha hψ hΨ hbψ
  -- inner interchange, for every fixed `x`
  have hinner : ∀ x, ∫ y, (∑' j, a j * φ j x * ψ j y) = ∑' j, (a j * φ j x) * ∫ y, ψ j y :=
    fun x => integral_tsum_mul_of_norm_bound (hsumφ x) hψ hΨ hbψ
  -- outer interchange, after commuting the two factors pointwise
  have houter : ∫ x, (∑' j, (a j * φ j x) * (∫ y, ψ j y))
      = ∑' j, a j * (∫ x, φ j x) * (∫ y, ψ j y) := by
    have h2 : (fun x => ∑' j, (a j * φ j x) * (∫ y, ψ j y))
        = fun x => ∑' j, (a j * (∫ y, ψ j y)) * φ j x := by
      funext x
      exact tsum_congr fun j => by ring
    rw [h2, integral_tsum_mul_of_norm_bound hsumI hφ hΦ hbφ]
    exact tsum_congr fun j => by ring
  calc ∫ x, ∫ y, ∑' j, a j * φ j x * ψ j y
      = ∫ x, ∑' j, (a j * φ j x) * (∫ y, ψ j y) := by simp only [hinner]
    _ = ∑' j, a j * (∫ x, φ j x) * (∫ y, ψ j y) := houter

end Work.BoseRowsFS
