import Mathlib
import Submission.Work.PTGeometric.exists_regular_shift

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The parametric-Sard shift, in surjectivity form

`Work.PTGeometric.exists_regular_shift` produces a parameter `s ∈ (0, ε)` for which every *interior*
zero of the shifted function `y ↦ ρ y - c * ψ (y 0) - s * χ (y 0)` is a regular point of that
function, stated as `mfderiv … x ≠ 0`.

Downstream (see `exists_sourceRegionPhiInterior.lean`) the regularity is consumed through Mathlib's
`Manifold.IsSubmersionAt`, via `Work.PTGeometric.isSubmersionAt_of_surjective_mfderiv_real`, whose
hypothesis is `Function.Surjective (mfderiv … x)`.  This file provides that form.

The only point to note is the dictionary between the two: the target of `mfderiv` at an interior
point is the *one*-dimensional space `TangentSpace 𝓘(ℝ,ℝ) (F x)`, a type synonym for `ℝ`, and a
continuous linear map into a one-dimensional space is surjective exactly when it is not identically
zero (a nonzero value `f v` lets one solve `f (c • v) = r` by `c = r / f v`).  Since the codomain is
the tangent space — a non-reducible type synonym, so that type class inference does not accidentally
pick the wrong instances — the intermediate computations are performed on `ℝ` itself, transported by
the canonical identification `NormedSpace.fromTangentSpace` (whose underlying map is the identity).

So the statement here is not a weakening of `exists_regular_shift`, merely a re-reading of it.
-/

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Set MeasureTheory Filter Function

noncomputable section

/-- **A nonzero `mfderiv` of a real-valued function on the half-space is surjective.**

At a point `x` of the half-space model, the target of `mfderiv 𝓡∂ N 𝓘(ℝ,ℝ) F x` is the tangent
space of `ℝ` at `F x`, i.e. the one-dimensional space `ℝ`.  A continuous linear map into a
one-dimensional space is surjective exactly when it is nonzero: if `f v ≠ 0` then
`f ((r / f v) • v) = r`.

The proof of the nontrivial implication is carried out on `ℝ` rather than on the type synonym
`TangentSpace 𝓘(ℝ,ℝ) (F x)`, using `NormedSpace.fromTangentSpace`, whose underlying function is the
identity (and which therefore does not change the value of the derivative). -/
theorem surjective_mfderiv_of_ne_zero {N : ℕ} [NeZero N] (F : EuclideanHalfSpace N → ℝ)
    (x : EuclideanHalfSpace N)
    (h : mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ) F x ≠ 0) :
    Function.Surjective (mfderiv (modelWithCornersEuclideanHalfSpace N)
      (modelWithCornersSelf ℝ ℝ) F x) := by
  intro r
  -- a nonzero functional takes a nonzero value
  have hv : ∃ v, (mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      F x) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (ContinuousLinearMap.ext hcon)
  obtain ⟨v, hv⟩ := hv
  -- view the tangent space of the target through its canonical identification with `ℝ`
  let e := NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) (F x)
  -- the value `e (f v)` is `f v` itself, viewed as an element of `ℝ`
  have hev : e ((mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      F x) v) ≠ 0 := hv
  refine ⟨(e r / e ((mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      F x) v)) • v, ?_⟩
  apply e.injective
  simp only [map_smul]
  rw [smul_eq_mul]
  field_simp

/-- **Existence of a shift making the level set regular, surjectivity form.**

This is `Work.PTGeometric.exists_regular_shift` with the conclusion `mfderiv … x ≠ 0` replaced by
`Function.Surjective (mfderiv … x)`, which is the form in which the regularity is consumed by
`Work.PTGeometric.isSubmersionAt_of_surjective_mfderiv_real`.  The passage between the two is
`Work.PTGeometric.surjective_mfderiv_of_ne_zero`. -/
theorem exists_regular_shift_surj {N : ℕ} [NeZero N]
    (ρ : EuclideanHalfSpace N → ℝ)
    (hρ : ContMDiff (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ0 : ∀ t, 0 ≤ χ t) (hχpos : ∀ t, 0 < t → 0 < χ t)
    (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ s ∈ Set.Ioo (0:ℝ) ε, ∀ x : EuclideanHalfSpace N,
      ρ x - c * ψ (x.1 0) - s * χ (x.1 0) = 0 → 0 < x.1 0 →
      Function.Surjective (mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
        (fun y => ρ y - c * ψ (y.1 0) - s * χ (y.1 0)) x) := by
  obtain ⟨s, hsIoo, hs⟩ :=
    exists_regular_shift ρ hρ hρ0 ψ hψ χ hχ hχ0 hχpos c hc ε hε
  exact ⟨s, hsIoo, fun x hfx hx0 =>
    surjective_mfderiv_of_ne_zero (fun y => ρ y - c * ψ (y.1 0) - s * χ (y.1 0)) x
      (hs x hfx hx0)⟩

end

end Work.PTGeometric
