import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.aliasIdentity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aliasImageDefs` — the vocabulary of the image (Poisson) form

The image form of the first-moment deficit (`Work.BoseBoxFock.aliasImageIdentity`)

    `R1 − S1 = π⁻² Σ_{m ≠ 0} ∫_u 𝒢(u) ‖u − ℓ • latVec m‖⁻⁴ du`

is obtained from the heat form of the same deficit by the `t`-integration
`∫_0^∞ t^{-3/2} heatK t z dt = 2π^{-3/2}‖z‖⁻⁴`; the two objects that appear in the
intermediate steps are the *Riesz weight of the image* and the *heat image integral*:

* `imgW ℓ m u = (‖u − ℓ • latVec m‖⁴)⁻¹` for `m ≠ 0`, and `0` for `m = 0`
  (the `m = 0` term is genuinely absent: `‖u‖⁻⁴` is not integrable at `u = 0`);
* `heatImage ℓ g m t = ∫_u aliasKernel g u · heatK t (ℓ • latVec m − u)` (`m ≠ 0`), `0` for `m = 0`
  — the `m`-th summand of the right-hand side of `aliasIdentity`.

This file contains only the definitions and their elementary properties (it is `sorry`-free and
imports only the aliasing identity and the heat-kernel definitions), so that the many lemmas
about them can be proved in parallel.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The Riesz weight of the image `ℓ • latVec m`: `(‖u − ℓ • latVec m‖⁴)⁻¹` for `m ≠ 0`, and
`0` for `m = 0` (the `m = 0` term is singular at `u = 0` and is excluded by the aliasing
identity — it is cancelled by the continuum heat content). -/
noncomputable def imgW (ℓ : ℝ) (m : Fin 3 → ℤ) (u : E3) : ℝ :=
  if m = 0 then 0 else (‖u - ℓ • latVec m‖ ^ 4)⁻¹

/-- The `m`-th summand of the right-hand side of `aliasIdentity`: the heat image integral
`∫_u aliasKernel g u · heatK t (ℓ • latVec m − u)`, and `0` for `m = 0`. -/
noncomputable def heatImage (ℓ : ℝ) (g : E3 → ℂ) (m : Fin 3 → ℤ) (t : ℝ) : ℝ :=
  if m = 0 then 0 else ∫ u : E3, aliasKernel g u * heatK t (ℓ • latVec m - u)

@[simp] theorem imgW_zero (ℓ : ℝ) (u : E3) : imgW ℓ 0 u = 0 := rfl

@[simp] theorem imgW_ne_zero {ℓ : ℝ} {m : Fin 3 → ℤ} (hm : m ≠ 0) (u : E3) :
    imgW ℓ m u = (‖u - ℓ • latVec m‖ ^ 4)⁻¹ := by
  simp only [imgW, if_neg hm]

theorem imgW_nonneg (ℓ : ℝ) (m : Fin 3 → ℤ) (u : E3) : 0 ≤ imgW ℓ m u := by
  rw [imgW]
  split
  · exact le_refl 0
  · positivity

@[simp] theorem heatImage_zero (ℓ : ℝ) (g : E3 → ℂ) (t : ℝ) : heatImage ℓ g 0 t = 0 := rfl

@[simp] theorem heatImage_ne_zero {ℓ : ℝ} {g : E3 → ℂ} {m : Fin 3 → ℤ} (hm : m ≠ 0) (t : ℝ) :
    heatImage ℓ g m t = ∫ u : E3, aliasKernel g u * heatK t (ℓ • latVec m - u) := by
  simp only [heatImage, if_neg hm]

end Work.BoseBoxFock