import Mathlib
import Submission.Work.ClassFieldTower.Defs

/-!
# `Work.ClassFieldTower.not_hasMinimalPresentation_of_not_finiteDimensional`

A group which admits a minimal presentation by finitely many generators and relators is a
quotient of a free group on a *finite* type, hence **countable**.

On the other hand, for a Galois extension `K/F` which is *not* finite dimensional, the Galois
group `Gal(K/F) = K ≃ₐ[F] K` is **uncountable**: it carries the Krull topology, in which it is a
compact Hausdorff topological group; a compact Hausdorff space that is countable has an isolated
point (Baire category theorem), and in a topological group an isolated point forces the topology
to be discrete, hence -- by compactness -- the group to be finite; finally, in the Krull topology
`{1}` is open if and only if `K` is finite dimensional over `F`.

Consequently `Gal(K/F)` has no minimal presentation with `d` generators and `r` relators at all.

This is the reason the *abstract* presentation interface `HasMinimalPresentation` of
`Work.ClassFieldTower.Defs` is unusable for an infinite class field tower (see the module
docstring of `Work.ClassFieldTower.ProTwoDefs`): the certificate built on it is vacuous.
-/

set_option linter.style.haveILetI false

open scoped Classical

namespace Work.ClassFieldTower

/-- **A Galois group of an infinite dimensional Galois extension has no finite presentation.**

`HasMinimalPresentation G d r` requires `G` to be isomorphic to a quotient of `FreeGroup α` with
`α` a finite type, so that `G` is countable.  But `K ≃ₐ[F] K` is a compact Hausdorff topological
group for the Krull topology, hence finite or uncountable; a countable one would have an isolated
point, be discrete, and therefore be finite, which in the Krull topology forces
`FiniteDimensional F K`. -/
theorem not_hasMinimalPresentation_of_not_finiteDimensional {F K : Type*} [Field F] [Field K]
    [Algebra F K] [IsGalois F K] (h : ¬ FiniteDimensional F K) (d r : ℕ) :
    ¬ HasMinimalPresentation (K ≃ₐ[F] K) d r := by
  intro hpres
  obtain ⟨α, hα, hdec, rel, _, _, ⟨e⟩, _⟩ := hpres
  -- `K ≃ₐ[F] K` is isomorphic to a quotient of the free group on the finite type `α`,
  -- hence countable.
  letI := hα
  letI := hdec
  have hcountQ : Countable (FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) :=
    Quotient.countable
  have hcount : Countable (K ≃ₐ[F] K) := (Equiv.countable_iff e.toEquiv).mpr hcountQ
  haveI := hcount
  -- A countable compact Hausdorff space is a Baire space, so one of its (countably many,
  -- closed) singletons has nonempty interior: the space has an isolated point.
  obtain ⟨g, hg⟩ := nonempty_interior_of_iUnion_of_closed
    (X := K ≃ₐ[F] K) (f := fun g : K ≃ₐ[F] K => ({g} : Set (K ≃ₐ[F] K)))
    (fun g => isClosed_singleton) (by ext x; simp)
  have hgopen : IsOpen ({g} : Set (K ≃ₐ[F] K)) := by
    obtain ⟨x, hx⟩ := hg
    have hxg : x = g := by simpa using (interior_subset hx)
    rw [hxg] at hx
    have hI : interior ({g} : Set (K ≃ₐ[F] K)) = {g} :=
      le_antisymm interior_subset (Set.singleton_subset_iff.mpr hx)
    rw [← hI]
    exact isOpen_interior
  -- Being a topological group, an isolated point means that `{1}` is open.
  have h1open : IsOpen ({(1 : K ≃ₐ[F] K)} : Set (K ≃ₐ[F] K)) := by
    have hpre : (fun x : K ≃ₐ[F] K => g * x) ⁻¹' ({g} : Set (K ≃ₐ[F] K)) = {1} := by
      ext x
      simp
    rw [← hpre]
    exact hgopen.preimage (continuous_const.mul continuous_id)
  -- In the Krull topology, the subgroup fixing `⊤` is `⊥ = {1}`, and it is open only if `K`
  -- is finite dimensional over `F`.
  have hfd : FiniteDimensional F ↥(⊤ : IntermediateField F K) := by
    refine (InfiniteGalois.isOpen_iff_finite (⊤ : IntermediateField F K)).mp ?_
    convert h1open using 2
    ext x
    simp
  exact h (Module.Finite.equiv (IntermediateField.topEquiv (F := F) (E := K)).toLinearEquiv)

end Work.ClassFieldTower
