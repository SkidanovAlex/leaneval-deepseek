import Mathlib

namespace Work.Isotopy

/-!
# Smoothness of the inverse of a smooth local homeomorphism

Let `f : E → F` be `C^∞` on an open set `U` of a finite dimensional real normed space `E`, and
suppose that its derivative `fderiv ℝ f x` is invertible at every `x ∈ U`.  If `Θ` is an open
partial homeomorphism whose underlying function agrees with `f` (as a function `E → F`) and whose
source is contained in `U`, then `Θ.symm` is `C^∞` on `Θ.target`.

This is one of the "easy" halves of the inverse function theorem: we already know that `Θ.symm` is
the inverse of `Θ`; what is missing is smoothness.  Mathlib's
`OpenPartialHomeomorph.contDiffAt_symm` supplies exactly this: for `y ∈ Θ.target`, if `Θ` is `C^n`
at `x := Θ.symm y` and has an invertible (continuous linear equivalence) derivative there, then
`Θ.symm` is `C^n` at `y`.  The hypotheses above provide both: `x = Θ.symm y ∈ Θ.source ⊆ U`, so `f`
is `C^∞` at `x`, and `derivAt : IsInvertible` turns the derivative at `x` into a continuous linear
equivalence (this is where finite dimensionality is used).  Since `Θ.target` is open, smoothness
*at* each point of the target upgrades to smoothness *on* the target.

This is the local-inverse-function input for the isotopy extension / tubular neighbourhood
machinery used for Whitney's strong embedding theorem (see the module documentation in
`Submission.lean`).
-/

theorem contDiffOn_symm_of_contDiffOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hinv : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible)
    (Θ : OpenPartialHomeomorph E F) (hfun : ⇑Θ = f) (hsrc : Θ.source ⊆ U) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (⇑Θ.symm : F → E) Θ.target := by
  intro y hy
  -- `Θ.target` is open, so it suffices to be smooth *at* each of its points.
  refine ContDiffAt.contDiffWithinAt ?_
  have hx : Θ.symm y ∈ Θ.source := Θ.map_target hy
  have hxU : Θ.symm y ∈ U := hsrc hx
  -- `f` is `C^∞` at `Θ.symm y`, because `U` is a neighbourhood of it.
  have hfAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Θ.symm y) :=
    (hf _ hxU).contDiffAt (hU.mem_nhds hxU)
  -- `Θ` and `f` are the same function.
  have hfAtΘ : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (⇑Θ) (Θ.symm y) := by
    rw [hfun]
    exact hfAt
  -- the derivative of `f` at `Θ.symm y` is invertible, hence comes from a continuous linear
  -- equivalence.
  obtain ⟨e, he⟩ := hinv _ hxU
  have hfd : HasFDerivAt (⇑Θ) (e : E →L[ℝ] F) (Θ.symm y) := by
    have h1 : HasFDerivAt f (fderiv ℝ f (Θ.symm y)) (Θ.symm y) :=
      (hfAt.differentiableAt (by simp)).hasFDerivAt
    rw [← he] at h1
    rw [← hfun] at h1
    exact h1
  exact Θ.contDiffAt_symm hy hfd hfAtΘ

end Work.Isotopy
