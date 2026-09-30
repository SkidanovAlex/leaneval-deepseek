/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Normality of `Symⁿ C`

This file records the statement `isIntegrallyClosed_stalk_sym` — that the symmetric powers of a
curve have integrally closed local rings — in the form in which it is *used*: area SY provides an
affine cover of `Symⁿ C` by spectra of invariant rings `(Γ(C, U)^{⊗n})^{S_n}`, and the two
ingredients

* `Work.Normality.isIntegrallyClosed_invariants`: the invariants of a finite group acting on an
  integrally closed domain are integrally closed, and
* `Work.Normality.isIntegrallyClosed_of_smooth_algebra`: a smooth algebra over a field which is a
  domain is integrally closed (applied to the tensor power `Γ(C, U)^{⊗n}`, which is smooth over
  `K` by base change since `C` is smooth),

show that each chart ring is integrally closed; `HasIntegrallyClosedStalks.of_isAffineOpen_cover`
then glues these chart-level statements to the scheme-level statement.

The scheme-level statements are

* `Work.Normality.isIntegrallyClosed_stalk_of_invariants`: for a single affine chart `V ⊆ X` whose
  ring is isomorphic to `(B^{⊗n})^{S_n}` with `B` a smooth `K`-domain, the local ring of `X` at a
  point of `V` is integrally closed;
* `Work.Normality.hasIntegrallyClosedStalks_of_invariants_charts`: the same for a whole cover,
  i.e. `HasIntegrallyClosedStalks X` for a scheme `X` (such as `Symⁿ C`) covered by charts of that
  form.
-/
import Mathlib
import Submission.Work.Normality.Basic
import Submission.Work.Normality.Scheme
import Submission.Work.Normality.isIntegrallyClosed_invariants
import Submission.Work.Normality.isIntegrallyClosed_of_smooth_algebra

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

/-- The chart ring of `Symⁿ C`: the fixed points of a finite group acting on an integrally closed
domain are again integrally closed.  Applied with `B = Γ(C, U)^{⊗n}` (a smooth `K`-algebra and a
domain, hence integrally closed by `Work.Normality.isIntegrallyClosed_of_smooth_algebra`) and
`G = S_n`, this is exactly the statement that the affine charts of `Symⁿ C` are integrally closed. -/
theorem isIntegrallyClosed_invariants_of_smooth {K : Type u} [Field K] {B : Type u} [CommRing B]
    [IsDomain B] [Algebra K B] [Algebra.Smooth K B] (G : Type u) [Group G] [Finite G]
    [MulSemiringAction G B] : IsIntegrallyClosed (FixedPoints.subring B G) := by
  haveI : IsIntegrallyClosed B := isIntegrallyClosed_of_smooth_algebra (K := K) (A := B)
  exact isIntegrallyClosed_invariants G

/-- If a chart `V` of a scheme `X` has ring of sections isomorphic to the fixed points of a finite
group acting on an integrally closed domain, then the local rings of `X` at points of `V` are
integrally closed. -/
theorem isIntegrallyClosed_stalk_of_invariants {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {B : Type u} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G B]
    (e : Γ(X, V) ≃+* ↥(FixedPoints.subring B G)) {x : X} (hx : x ∈ V) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  haveI : IsIntegrallyClosed ↥(FixedPoints.subring B G) := isIntegrallyClosed_invariants G
  haveI : IsIntegrallyClosed Γ(X, V) := IsIntegrallyClosed.of_equiv e.symm
  haveI : IsDomain ↥(FixedPoints.subring B G) := inferInstance
  haveI : IsDomain Γ(X, V) := Function.Injective.isDomain e.toRingHom e.injective
  exact isIntegrallyClosed_stalk_of_isAffineOpen hV ‹IsIntegrallyClosed Γ(X, V)› hx

/-- `isIntegrallyClosed_stalk_sym`, in the form in which SY's chart cover of `Symⁿ C` is used: if
`X` is covered by affine charts whose rings of sections are invariant rings `(B^{⊗n})^{S_n}` of
smooth domains `B` over `K`, then every local ring of `X` — in particular every local ring of
`Symⁿ C` — is integrally closed. -/
theorem hasIntegrallyClosedStalks_of_invariants_charts {K : Type u} [Field K] {X : Scheme.{u}}
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i)
    {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, Algebra K (B i)]
    [∀ i, Algebra.Smooth K (B i)] (G : ι → Type u) [∀ i, Group (G i)] [∀ i, Finite (G i)]
    [∀ i, MulSemiringAction (G i) (B i)]
    (e : ∀ i, Γ(X, U i) ≃+* ↥(FixedPoints.subring (B i) (G i))) :
    HasIntegrallyClosedStalks X := by
  intro x
  obtain ⟨i, hi⟩ := hcov x
  haveI : IsDomain ↥(FixedPoints.subring (B i) (G i)) := inferInstance
  haveI : IsIntegrallyClosed ↥(FixedPoints.subring (B i) (G i)) :=
    isIntegrallyClosed_invariants_of_smooth (K := K) (B := B i) (G i)
  haveI : IsDomain Γ(X, U i) := Function.Injective.isDomain (e i).toRingHom (e i).injective
  haveI : IsIntegrallyClosed Γ(X, U i) := IsIntegrallyClosed.of_equiv (e i).symm
  exact isIntegrallyClosed_stalk_of_isAffineOpen (hU i) ‹IsIntegrallyClosed Γ(X, U i)› hi

/-- `isIntegrallyClosed_stalk_sym`: the local rings of `Symⁿ C` are integrally closed.  The literal
statement for `Sym C n` becomes available once area SY provides the scheme `Sym C n` together with
its affine chart cover by spectra of the rings `(Γ(C,U)^{⊗n})^{S_n}` (each of which is an invariant
ring of a smooth `K`-domain, so integrally closed by
`Work.Normality.isIntegrallyClosed_invariants_of_smooth`): it is then the immediate application of
this lemma to that cover.  The present form is the same statement with the chart cover as an
explicit hypothesis, so that nothing blocks on SY: for any scheme `X` covered by affine charts
whose rings of sections are invariant rings `(B_i^{⊗n})^{S_n}` of smooth `K`-domains `B_i`, all
local rings of `X` are integrally closed. -/
theorem isIntegrallyClosed_stalk_sym {K : Type u} [Field K] {X : Scheme.{u}}
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i)
    {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, Algebra K (B i)]
    [∀ i, Algebra.Smooth K (B i)] (G : ι → Type u) [∀ i, Group (G i)] [∀ i, Finite (G i)]
    [∀ i, MulSemiringAction (G i) (B i)]
    (e : ∀ i, Γ(X, U i) ≃+* ↥(FixedPoints.subring (B i) (G i))) :
    HasIntegrallyClosedStalks X :=
  hasIntegrallyClosedStalks_of_invariants_charts (K := K) U hU hcov G e

end

end Work.Normality

