import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le
import Submission.Work.FTS.StrongEps.LocUnif.diffQuot_pointwise_le
import Submission.Work.FTS.StrongEps.LocUnif.DiffQuotFacts
import Submission.Work.FTS.StrongEps.LocUnif.ae_shift_measure_null
import Submission.Work.FTS.StrongEps.LocUnif.lintegral_lintegral_shift_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The backward difference-quotient weighted `L²` bound in the `θ`-variable

`diffQuot_backward_lintegral_le_theta`: the weighted `L²`-norm of the backward difference quotient
`θ ↦ (u z θ - u z (θ - h))/h` over `[a, b] × [c', d']` is bounded by `C` times the weighted
`L²`-norm of `∂_θu` over the larger rectangle `[a, b] × [c, d]`.

This is the `θ`-analogue of `Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le` (which
differentiates in `z`); it is the "second half" of the local-uniformity extraction, consumed by
`lintegral_backwardDiffQuot_majorant_le_liminf_theta`.

## Proof

The statement is the `z`-statement in the coordinates `(θ, z)` instead of `(z, θ)`: applying
`diffQuot_backward_lintegral_le` to the *swapped* integrand `u' z θ = u θ z` and the *swapped*
weight `w' z θ = w θ z` with the intervals `a ↦ c`, `b ↦ d`, `c ↦ a`, `d ↦ b` produces the claim
with both rectangles transposed.  Both the hypothesis `hmeas` and the two integrals are then
transported back along the coordinate swap `(z, θ) ↦ (θ, z)`:

* set integrals over a product of intervals are invariant under the swap
  (`setLIntegral_prod_swap`, from Tonelli's `MeasureTheory.lintegral_prod_swap` and
  `Measure.prod_restrict` / `Measure.volume_eq_prod`);
* a.e. measurability is invariant under the swap (`aemeasurable_restrict_prod_swap`, from
  `AEMeasurable.prod_swap`).

This is exactly the reduction recommended in the area notes
(`Submission/Work/FTS/StrongEps/LocUnif/NOTES_assembly_final.md`, item 2: "the `θ` direction
(mirror, or derived from the `z` version by the measure-preserving swap …)").
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Set

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- The product of the restricted Lebesgue measures on `ℝ` is the restriction of Lebesgue
measure on `ℝ × ℝ` to the product of the two sets. -/
theorem restrict_prod_volume (A B : Set ℝ) :
    (MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict B)
      = MeasureTheory.volume.restrict (A ×ˢ B) := by
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

/-- **Set integrals over a product of intervals are invariant under the swap of the two
coordinates.**  `∫⁻_{(x,y) ∈ A ×ˢ B} F y x = ∫⁻_{(x,y) ∈ B ×ˢ A} F x y`. -/
theorem setLIntegral_prod_swap {A B : Set ℝ} (F : ℝ → ℝ → ℝ≥0∞) :
    ∫⁻ p in A ×ˢ B, F p.2 p.1 = ∫⁻ p in B ×ˢ A, F p.1 p.2 := by
  have h := MeasureTheory.lintegral_prod_swap (μ := MeasureTheory.volume.restrict B)
    (ν := MeasureTheory.volume.restrict A) (f := fun p : ℝ × ℝ => F p.1 p.2)
  rw [restrict_prod_volume, restrict_prod_volume] at h
  exact h

/-- **Almost-everywhere measurability is invariant under the swap of the two coordinates**,
for the restrictions to a product of rectangles. -/
theorem aemeasurable_restrict_prod_swap {A B : Set ℝ} {F : ℝ → ℝ → ℝ≥0∞}
    (h : AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      (MeasureTheory.volume.restrict (A ×ˢ B))) :
    AEMeasurable (fun p : ℝ × ℝ => F p.2 p.1) (MeasureTheory.volume.restrict (B ×ˢ A)) := by
  have h' : AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict B)) := by
    rwa [restrict_prod_volume]
  have h2 := h'.prod_swap
  rwa [restrict_prod_volume] at h2

theorem diffQuot_backward_lintegral_le_theta {a b c d c' d' h C : ℝ}
    (hcc' : c < c') (hd'd : d' < d) (hh : 0 < h) (hah : h < c' - c) (hC : 1 ≤ C)
    {w : ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < w z θ)
    (hCw : ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, ∀ θ ∈ Set.Icc c d,
      |θ - y| ≤ h → (w z θ) ^ 2 ≤ C * (w z y) ^ 2)
    (hu_sm : ∀ z ∈ Set.Icc a b, ContDiffOn ℝ 1 (fun θ => u z θ) (Set.Ioo c d))
    (hu_c : ∀ z ∈ Set.Icc a b, ContinuousOn (fun θ => u z θ) (Set.Icc c d))
    (hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
        ENNReal.ofReal (((u p.1 p.2 - u p.1 (p.2 - h)) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ ENNReal.ofReal C * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2) := by
  -- The a.e. measurability of the `θ`-derivative energy, in the swapped coordinates.
  have hmeas' : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((deriv (fun z' => u p.2 z') p.1) ^ 2 * (w p.2 p.1) ^ 2))
      (volume.restrict (Set.Icc c d ×ˢ Set.Icc a b)) :=
    aemeasurable_restrict_prod_swap (F := fun x y =>
      ENNReal.ofReal ((deriv (fun θ' => u x θ') y) ^ 2 * (w x y) ^ 2)) (A := Set.Icc a b)
      (B := Set.Icc c d) hmeas
  -- The `z`-statement, in the swapped coordinates and with the intervals interchanged.
  have key := diffQuot_backward_lintegral_le (a := c) (b := d) (a' := c') (b' := d')
    (c := a) (d := b) (h := h) (C := C) (w := fun z θ => w θ z) (u := fun z θ => u θ z)
    hcc' hd'd hh hah hC
    (fun z hz θ hθ => hw θ hθ z hz)
    (fun Z hZ Y hY T hT habs => hCw T hT Y hY Z hZ habs)
    (fun θ hθ => hu_sm θ hθ)
    (fun θ hθ => hu_c θ hθ)
    hmeas'
  calc ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
        ENNReal.ofReal (((u p.1 p.2 - u p.1 (p.2 - h)) / h) ^ 2 * (w p.1 p.2) ^ 2)
      = ∫⁻ p in Set.Icc c' d' ×ˢ Set.Icc a b,
        ENNReal.ofReal (((u p.2 p.1 - u p.2 (p.1 - h)) / h) ^ 2 * (w p.2 p.1) ^ 2) :=
        (setLIntegral_prod_swap (A := Set.Icc c' d') (B := Set.Icc a b)
          (F := fun x y => ENNReal.ofReal (((u x y - u x (y - h)) / h) ^ 2 * (w x y) ^ 2))).symm
    _ ≤ ENNReal.ofReal C * ∫⁻ p in Set.Icc c d ×ˢ Set.Icc a b,
        ENNReal.ofReal ((deriv (fun z' => u p.2 z') p.1) ^ 2 * (w p.2 p.1) ^ 2) := key
    _ = ENNReal.ofReal C * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2) := by
        rw [setLIntegral_prod_swap (A := Set.Icc c d) (B := Set.Icc a b)
          (F := fun x y => ENNReal.ofReal ((deriv (fun θ' => u x θ') y) ^ 2 * (w x y) ^ 2))]

end Work.FTS.StrongEps.LocUnif
