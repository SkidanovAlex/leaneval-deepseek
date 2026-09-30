/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Normal (integrally closed) schemes

This file collects the scheme-theoretic consequences of `isIntegrallyClosed_of_smooth`: a scheme
which is smooth over a field — and integral — has integrally closed local rings at all of its
points.  The consumer-facing form is `Work.Normality.HasIntegrallyClosedStalks`.

* `Work.Normality.HasIntegrallyClosedStalks.of_isAffineOpen_cover`: a scheme covered by affine
  opens whose rings are domains and integrally closed has integrally closed stalks.  This is the
  form used for `Symⁿ C`, whose charts are the spectra of the invariant rings
  `(Γ(C,U)^{⊗n})^{S_n}`.
* `Work.Normality.hasIntegrallyClosedStalks_of_smooth`: a smooth integral scheme over a field has
  integrally closed stalks.  This is the form used for `Cⁿ`.
-/
import Mathlib
import Submission.Work.Normality.Basic
import Submission.Work.Normality.isIntegrallyClosed_of_smooth
import Submission.Work.Normality.isIntegrallyClosed_stalk_of_isAffineOpen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Work.Normality

noncomputable section

/-- If every point of an integral scheme `X` has an affine chart whose ring of sections is
standard smooth over the base field `K` (through some ring hom `K →+* Γ(X, V)`), then the local
rings of `X` are integrally closed.  This is the form of `hasIntegrallyClosedStalks_of_smooth`
which does not require `X` to be smooth over `K` *globally*: it suffices that it has smooth
charts. -/
theorem hasIntegrallyClosedStalks_of_isStandardSmooth_charts {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X]
    (h : ∀ x : X, ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V),
      ∃ (φ : K →+* Γ(X, V)), φ.IsStandardSmooth) :
    HasIntegrallyClosedStalks X := by
  intro x
  obtain ⟨V, hV, hxV, φ, hφ⟩ := h x
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI : IsDomain (X.presheaf.obj (Opposite.op V)) := inferInstance
  refine isIntegrallyClosed_stalk_of_isAffineOpen hV ?_ hxV
  letI : Algebra K Γ(X, V) := φ.toAlgebra
  haveI : Algebra.IsStandardSmooth K Γ(X, V) := hφ.toAlgebra
  exact isIntegrallyClosed_of_isStandardSmooth (K := K) (A := Γ(X, V))

/-- If `X` is covered by affine opens whose rings of sections are domains and integrally closed,
then every local ring of `X` is integrally closed. -/
theorem HasIntegrallyClosedStalks.of_isAffineOpen_cover {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i)
    (hdom : ∀ i, IsDomain (X.presheaf.obj (Opposite.op (U i))))
    (h : ∀ i, IsIntegrallyClosed (X.presheaf.obj (Opposite.op (U i)))) :
    HasIntegrallyClosedStalks X := by
  intro x
  obtain ⟨i, hi⟩ := hcov x
  haveI := hdom i
  exact isIntegrallyClosed_stalk_of_isAffineOpen (hU i) (h i) hi

/-- For a field `K`, the ring of sections of `Spec K` over a nonempty open is a field (indeed,
`Spec K` is a one-point space, so a nonempty open is `⊤` and `Γ(Spec K, ⊤) ≅ K`). -/
theorem isField_sections_spec (K : Type u) [Field K] (U : (Spec (CommRingCat.of K)).Opens)
    (hne : (U : Set (Spec (CommRingCat.of K))).Nonempty) : IsField Γ(Spec (CommRingCat.of K), U) := by
  have htop : U = ⊤ := by
    ext y
    exact ⟨fun _ => trivial, fun _ => by
      obtain ⟨z, hz⟩ := hne
      rwa [Subsingleton.elim z y] at hz⟩
  subst htop
  have e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  exact MulEquiv.isField (Field.toIsField K) e.toMulEquiv

end

end Work.Normality
