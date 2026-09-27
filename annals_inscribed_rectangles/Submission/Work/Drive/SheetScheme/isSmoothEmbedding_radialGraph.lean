import Mathlib
import Submission.Work.Drive.PolarTwist.isSmoothEmbedding_of_injective_deriv_ne_zero
import Submission.Work.Drive.PolarTwist.radialGraph_isotopy
import Submission.Work.Drive.isSmoothEmbedding_sub_const
import Submission.Work.Drive.PolarTwist.reflection_isSmoothEmbedding

/-!
# Radial graphs of the plane are smooth embeddings

`Work.Drive.SheetScheme.isSmoothEmbedding_radialGraph`: for a parameter `c : ℝ × ℝ`, a positive
radius function `ρ` on the circle whose `Circle.exp`-parametrisation is `C^∞`, and an orientation
sign `ε = ±1`, the map

`x ↦ (c.1 + ρ x · re x, c.2 + ρ x · (ε · im x))`

is a smooth embedding `S¹ → ℝ²`.  Geometrically this is the curve obtained from the unit circle by
stretching radially by `ρ` (possibly reflecting the second coordinate when `ε = -1`) and then
translating by `c`; the proof splits accordingly:

* `isSmoothEmbedding_radialCore` is the untranslated, unreflected case `x ↦ (ρ x · re x, ρ x · im x)`,
  obtained from the already-proved `Work.Drive.PolarTwist.isSmoothEmbedding_slice` with both
  scalings equal to `1` (the injectivity input is `Work.Drive.radialGraphFamily_injective`);
* `isSmoothEmbedding_add_const` is translation invariance, from
  `Work.Drive.isSmoothEmbedding_sub_const`;
* the reflection `y ↦ (y.1, -y.2)` is `Work.Drive.PolarTwist.reflection_isSmoothEmbedding`, which
  handles the case `ε = -1`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Manifold

namespace Work.Drive.SheetScheme

noncomputable section

/-- The radial graph `x ↦ (ρ x · re x, ρ x · im x)` of a positive `C^∞` radius function is a smooth
embedding. -/
lemma isSmoothEmbedding_radialCore (ρ : Circle → ℝ) (hpos : ∀ x, 0 < ρ x)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ρ (Circle.exp t))) :
    Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Circle => (ρ x * (x : ℂ).re, ρ x * (x : ℂ).im)) := by
  have hinj : Function.Injective
      (fun x : Circle => (1 * (ρ x * (x : ℂ).re), 1 * (ρ x * (x : ℂ).im))) := by
    intro x y h
    exact Work.Drive.radialGraphFamily_injective ρ hpos ⟨le_refl 0, zero_le_one⟩
      (by simpa [Work.Drive.radialGraphFamily] using h)
  simpa using Work.Drive.PolarTwist.isSmoothEmbedding_slice hpos hsm one_pos one_pos hinj

/-- Translating the target of a smooth embedding of the circle in the plane preserves it. -/
lemma isSmoothEmbedding_add_const (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (c : ℝ × ℝ) :
    Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => γ x + c) := by
  have h := Work.Drive.isSmoothEmbedding_sub_const γ hγ (-c)
  simpa using h

theorem isSmoothEmbedding_radialGraph (c : ℝ × ℝ) (ρ : Circle → ℝ) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hpos : ∀ x, 0 < ρ x)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ρ (Circle.exp t))) :
    Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Circle => (c.1 + ρ x * (x : ℂ).re, c.2 + ρ x * (ε * (x : ℂ).im))) := by
  have hcore := isSmoothEmbedding_radialCore ρ hpos hsm
  rcases hε with rfl | rfl
  · -- `ε = 1`: this is the radial graph, translated by `c`
    have hfun : (fun x : Circle => (c.1 + ρ x * (x : ℂ).re, c.2 + ρ x * (1 * (x : ℂ).im)))
        = (fun x : Circle => (ρ x * (x : ℂ).re, ρ x * (x : ℂ).im) + c) := by
      funext x; ext <;> simp <;> ring
    rw [hfun]
    exact isSmoothEmbedding_add_const _ hcore c
  · -- `ε = -1`: this is the reflection of the radial graph, translated by `c`
    have hfun : (fun x : Circle => (c.1 + ρ x * (x : ℂ).re, c.2 + ρ x * (-1 * (x : ℂ).im)))
        = (fun x : Circle => ((ρ x * (x : ℂ).re, -(ρ x * (x : ℂ).im)) + c)) := by
      funext x; ext <;> simp <;> ring
    rw [hfun]
    exact isSmoothEmbedding_add_const _
      ((Work.Drive.PolarTwist.reflection_isSmoothEmbedding _ hcore).1) c

end

end Work.Drive.SheetScheme
