import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS_RegExport.RXR7.VelLipAux

/-- **Two-variable Lipschitz bound from first partial-derivative bounds, with an explicit
constant.**  Let `Fz`, `Fθ` be functions of `(z,θ)` whose one-variable slices are differentiable
on the half-strip `(Lz,∞) × (0,π/2)`, with the four partial derivatives bounded there by `Mz`,
`Mθ`, `Nz`, `Nθ` respectively.  If `Mz + Mθ + Nz + Nθ ≤ K`, then the map
`p ↦ (Fz p.1 p.2, Fθ p.1 p.2)` into `ℝ × ℝ` (with the product/max norm) is `K`-Lipschitz on the
convex half-strip.

This is the same estimate as `lipschitz_pair_of_deriv_bounds` but with the constant exposed
(the consumer needs a `τ`-uniform constant and so cannot use an unspecified `∃ K`).

Proof: the two-step mean value inequality on the convex factors `Ioi Lz` and `Ioo 0 (π/2)`
(`Convex.norm_image_sub_le_of_norm_deriv_le` in the `θ`-direction with the `z` coordinate fixed,
then in the `z`-direction); add the two increments, use `|a|, |b| ≤ ‖(a,b)‖` (`Prod.norm_def`)
and `‖(z,θ)‖ = max |z| |θ|`, and finish with the hypothesis `hK` and
`lipschitzOnWith_iff_norm_sub_le`. -/
theorem lipschitz_pair_of_deriv_bounds_le {Fz Fθ : ℝ → ℝ → ℝ} {Lz Mz Mθ Nz Nθ : ℝ} {K : NNReal}
    (hLz : 0 < Lz) (hMz : 0 ≤ Mz) (hMθ : 0 ≤ Mθ) (hNz : 0 ≤ Nz) (hNθ : 0 ≤ Nθ)
    (hK : Mz + Mθ + Nz + Nθ ≤ (K : ℝ))
    (hdFz : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 →
      DifferentiableAt ℝ (fun z' => Fz z' θ) z ∧ DifferentiableAt ℝ (fun θ' => Fz z θ') θ)
    (hdFθ : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 →
      DifferentiableAt ℝ (fun z' => Fθ z' θ) z ∧ DifferentiableAt ℝ (fun θ' => Fθ z θ') θ)
    (h1 : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 → |deriv (fun z' => Fz z' θ) z| ≤ Mz)
    (h2 : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 → |deriv (fun θ' => Fz z θ') θ| ≤ Mθ)
    (h3 : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 → |deriv (fun z' => Fθ z' θ) z| ≤ Nz)
    (h4 : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 → |deriv (fun θ' => Fθ z θ') θ| ≤ Nθ) :
    LipschitzOnWith K (fun p : ℝ × ℝ => (Fz p.1 p.2, Fθ p.1 p.2))
      (Set.prod (Set.Ioi Lz) (Set.Ioo 0 (Real.pi / 2))) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro p hp q hq
  change p.1 ∈ Set.Ioi Lz ∧ p.2 ∈ Set.Ioo 0 (π / 2) at hp
  change q.1 ∈ Set.Ioi Lz ∧ q.2 ∈ Set.Ioo 0 (π / 2) at hq
  -- coordinate comparisons with `dist p q`
  have hd1 : |p.1 - q.1| ≤ dist p q := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ dist p q := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact le_max_right _ _
  -- `z`-increment of `Fz` at fixed `θ = p.2`
  have hA : |Fz p.1 p.2 - Fz q.1 p.2| ≤ Mz * |p.1 - q.1| := by
    have hdiff : ∀ w ∈ Set.Ioi Lz, DifferentiableAt ℝ (fun z' => Fz z' p.2) w :=
      fun w hw => (hdFz w p.2 hw hp.2.1 hp.2.2).1
    have hb : ∀ w ∈ Set.Ioi Lz, ‖deriv (fun z' => Fz z' p.2) w‖ ≤ Mz :=
      fun w hw => by rw [Real.norm_eq_abs]; exact h1 w p.2 hw hp.2.1 hp.2.2
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb (convex_Ioi Lz) hp.1 hq.1
    calc |Fz p.1 p.2 - Fz q.1 p.2| = ‖Fz q.1 p.2 - Fz p.1 p.2‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ Mz * ‖q.1 - p.1‖ := h
      _ = Mz * |p.1 - q.1| := by rw [Real.norm_eq_abs, abs_sub_comm]
  -- `θ`-increment of `Fz` at fixed `z = q.1`
  have hB : |Fz q.1 p.2 - Fz q.1 q.2| ≤ Mθ * |p.2 - q.2| := by
    have hdiff : ∀ w ∈ Set.Ioo (0 : ℝ) (π / 2),
        DifferentiableAt ℝ (fun θ' => Fz q.1 θ') w :=
      fun w hw => (hdFz q.1 w hq.1 hw.1 hw.2).2
    have hb : ∀ w ∈ Set.Ioo (0 : ℝ) (π / 2),
        ‖deriv (fun θ' => Fz q.1 θ') w‖ ≤ Mθ :=
      fun w hw => by rw [Real.norm_eq_abs]; exact h2 q.1 w hq.1 hw.1 hw.2
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb
      (convex_Ioo 0 (π / 2)) hp.2 hq.2
    calc |Fz q.1 p.2 - Fz q.1 q.2| = ‖Fz q.1 q.2 - Fz q.1 p.2‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ Mθ * ‖q.2 - p.2‖ := h
      _ = Mθ * |p.2 - q.2| := by rw [Real.norm_eq_abs, abs_sub_comm]
  -- `z`-increment of `Fθ` at fixed `θ = p.2`
  have hC : |Fθ p.1 p.2 - Fθ q.1 p.2| ≤ Nz * |p.1 - q.1| := by
    have hdiff : ∀ w ∈ Set.Ioi Lz, DifferentiableAt ℝ (fun z' => Fθ z' p.2) w :=
      fun w hw => (hdFθ w p.2 hw hp.2.1 hp.2.2).1
    have hb : ∀ w ∈ Set.Ioi Lz, ‖deriv (fun z' => Fθ z' p.2) w‖ ≤ Nz :=
      fun w hw => by rw [Real.norm_eq_abs]; exact h3 w p.2 hw hp.2.1 hp.2.2
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb (convex_Ioi Lz) hp.1 hq.1
    calc |Fθ p.1 p.2 - Fθ q.1 p.2| = ‖Fθ q.1 p.2 - Fθ p.1 p.2‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ Nz * ‖q.1 - p.1‖ := h
      _ = Nz * |p.1 - q.1| := by rw [Real.norm_eq_abs, abs_sub_comm]
  -- `θ`-increment of `Fθ` at fixed `z = q.1`
  have hD : |Fθ q.1 p.2 - Fθ q.1 q.2| ≤ Nθ * |p.2 - q.2| := by
    have hdiff : ∀ w ∈ Set.Ioo (0 : ℝ) (π / 2),
        DifferentiableAt ℝ (fun θ' => Fθ q.1 θ') w :=
      fun w hw => (hdFθ q.1 w hq.1 hw.1 hw.2).2
    have hb : ∀ w ∈ Set.Ioo (0 : ℝ) (π / 2),
        ‖deriv (fun θ' => Fθ q.1 θ') w‖ ≤ Nθ :=
      fun w hw => by rw [Real.norm_eq_abs]; exact h4 q.1 w hq.1 hw.1 hw.2
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb
      (convex_Ioo 0 (π / 2)) hp.2 hq.2
    calc |Fθ q.1 p.2 - Fθ q.1 q.2| = ‖Fθ q.1 q.2 - Fθ q.1 p.2‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ Nθ * ‖q.2 - p.2‖ := h
      _ = Nθ * |p.2 - q.2| := by rw [Real.norm_eq_abs, abs_sub_comm]
  have hFz : |Fz p.1 p.2 - Fz q.1 q.2| ≤ (Mz + Mθ + Nz + Nθ) * dist p q := by
    calc |Fz p.1 p.2 - Fz q.1 q.2|
        = |(Fz p.1 p.2 - Fz q.1 p.2) + (Fz q.1 p.2 - Fz q.1 q.2)| := by congr 1; ring
      _ ≤ |Fz p.1 p.2 - Fz q.1 p.2| + |Fz q.1 p.2 - Fz q.1 q.2| := abs_add_le _ _
      _ ≤ Mz * |p.1 - q.1| + Mθ * |p.2 - q.2| := add_le_add hA hB
      _ ≤ Mz * dist p q + Mθ * dist p q :=
            add_le_add (mul_le_mul_of_nonneg_left hd1 hMz) (mul_le_mul_of_nonneg_left hd2 hMθ)
      _ ≤ (Mz + Mθ + Nz + Nθ) * dist p q := by
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
  have hFθ : |Fθ p.1 p.2 - Fθ q.1 q.2| ≤ (Mz + Mθ + Nz + Nθ) * dist p q := by
    calc |Fθ p.1 p.2 - Fθ q.1 q.2|
        = |(Fθ p.1 p.2 - Fθ q.1 p.2) + (Fθ q.1 p.2 - Fθ q.1 q.2)| := by congr 1; ring
      _ ≤ |Fθ p.1 p.2 - Fθ q.1 p.2| + |Fθ q.1 p.2 - Fθ q.1 q.2| := abs_add_le _ _
      _ ≤ Nz * |p.1 - q.1| + Nθ * |p.2 - q.2| := add_le_add hC hD
      _ ≤ Nz * dist p q + Nθ * dist p q :=
            add_le_add (mul_le_mul_of_nonneg_left hd1 hNz) (mul_le_mul_of_nonneg_left hd2 hNθ)
      _ ≤ (Mz + Mθ + Nz + Nθ) * dist p q := by
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
  -- replace the explicit sum of the four bounds by the hypothesis constant `K`
  have hFz' : |Fz p.1 p.2 - Fz q.1 q.2| ≤ (K : ℝ) * dist p q :=
    le_trans hFz (mul_le_mul_of_nonneg_right hK dist_nonneg)
  have hFθ' : |Fθ p.1 p.2 - Fθ q.1 q.2| ≤ (K : ℝ) * dist p q :=
    le_trans hFθ (mul_le_mul_of_nonneg_right hK dist_nonneg)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le hFz' hFθ'

end Work.FTS_RegExport.RXR7.VelLipAux
