/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The level obstruction is a *finite* intersection of localisation kernels

The level obstruction `NK.HassePrinciple.levelObstruction p U L` is, by definition, the
intersection

`⨅ (A : OverFinitePrime K K'), (locLevel p U A.1 L).hom.ker`

of the kernels of the level-wise localisation maps, the infimum running over *all* the places of
`K'` over a finite prime of `K`.  The index type `OverFinitePrime K K'` is typically infinite, so
this is a priori an infinite intersection.

The present file proves that it is in fact a **finite** intersection (and hence, in particular, a
closed/definable condition, and one that can be checked on finitely many places):

`∃ s : Finset (OverFinitePrime K K'), levelObstruction p U L = ⨅ A ∈ s, (locLevel p U A.1 L).hom.ker`

The mathematical content is only that the ambient group of the intersection is *finite*: the level
cohomology `LevelH2 p U L = H²(U/(U ⊓ Gal(K'/L)), Z/p)` is the second cohomology of a finite group
with coefficients in the finite module `Z/p`, and a finite group has only finitely many submodules.
The intersection of an arbitrary family of submodules of a finite module is therefore the
intersection of the (finite) set of submodules that actually occur in the family.

The two ingredients are isolated as lemmas:

* `NK.HassePrinciple.finite_H2` — `H²(G, Z/p)` is finite for a finite group `G` and `p ≠ 0`
  (the cohomology is a quotient of the 2-cocycles `Z²(G, Z/p) ⊆ (G × G → Z/p)`, via the epimorphism
  `groupCohomology.H2π`);
* `NK.HassePrinciple.exists_finset_iInf_eq` — in any complete lattice whose elements form a finite
  type, an arbitrary infimum equals the infimum over a finite set of indices.

For the statement of the finiteness of the level cohomology we need `ZMod p` to be finite, i.e.
`p ≠ 0`; this is exactly why the prime hypothesis `hp : p.Prime` appears in the statement of the
main theorem.
-/

import Mathlib
import Submission.NK.HassePrinciple.Obstruction
import Submission.NK.HassePrinciple.finite_levelGroup
import Submission.NK.BrauerHasse.Profinite

open CategoryTheory

set_option linter.style.haveILetI false

namespace NK.HassePrinciple

open NK.BrauerHasse

universe u

/-! ## Finiteness of the level cohomology -/

/-- **The second cohomology of a finite group with coefficients in `Z/p` is finite.**

The cohomology `H²(G, Z/p) = groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 2` is, by
`groupCohomology.H2π`, a quotient of the `2`-cocycles `cocycles₂`, which form a submodule of the
finite module `G × G → Z/p`.  Note the hypothesis `NeZero p`: without it `ZMod p` is infinite (for
`p = 0` it is `ℤ`). -/
lemma finite_H2 (p : ℕ) [NeZero p] (G : Type u) [Group G] [Finite G] : Finite (H2 p G) := by
  haveI : Finite (Coeff.{u} p) := inferInstance
  let A := Rep.trivial (Coeff.{u} p) G (Coeff.{u} p)
  have h : Finite (groupCohomology.cocycles₂ A) := inferInstance
  exact Finite.of_surjective (groupCohomology.H2π A).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- **The level cohomology of a finite level is finite.**

`LevelH2 p U L = H²(U/(U ⊓ Gal(K'/L)), Z/p)` and `U/(U ⊓ Gal(K'/L))` is finite
(`NK.HassePrinciple.finite_levelGroup`). -/
lemma finite_levelH2 {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) [NeZero p] (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    Finite (LevelH2 p U L) :=
  finite_H2 p (LevelGroup U L)

/-! ## Infima in a finite complete lattice -/

/-- **An arbitrary infimum in a finite complete lattice is a finite infimum.**

If the elements of a complete lattice `β` form a finite type, then for any family `f : α → β` there
is a finite set `s` of indices with `⨅ a, f a = ⨅ a ∈ s, f a`: take one index for each value in the
(finite) range of `f`. -/
lemma exists_finset_iInf_eq {α : Type*} {β : Type u} [CompleteLattice β] (f : α → β) [Finite β] :
    ∃ s : Finset α, (⨅ a, f a) = (⨅ a ∈ s, f a) := by
  classical
  haveI : Fintype (Set.range f) := Fintype.ofFinite _
  -- one index for every value of `f`, chosen by `Classical.choose`
  let s : Finset α := Finset.univ.image (fun N : Set.range f => N.2.choose)
  refine ⟨s, ?_⟩
  -- `⨅ a, f a ≤ ⨅ a ∈ s, f a` is trivial; for the reverse inequality it suffices to produce, for
  -- a given index `a`, an element `b ∈ s` with `f b = f a`.
  refine le_antisymm (le_iInf fun a => le_iInf fun _ => iInf_le f a) (le_iInf fun a => ?_)
  have hmem : f a ∈ f '' (s : Set α) := by
    refine ⟨(⟨f a, ⟨a, rfl⟩⟩ : Set.range f).2.choose, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨f a, ⟨a, rfl⟩⟩, Finset.mem_univ _, rfl⟩
    · exact (⟨f a, ⟨a, rfl⟩⟩ : Set.range f).2.choose_spec
  obtain ⟨b, hb, hbf⟩ := hmem
  calc (⨅ a, ⨅ (_ : a ∈ s), f a) ≤ ⨅ (_ : b ∈ s), f b := iInf_le _ b
    _ ≤ f b := iInf_le _ hb
    _ = f a := hbf

/-! ## The main result -/

set_option maxHeartbeats 1600000 in
theorem exists_finset_levelObstruction {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) (U : Subgroup (K' ≃ₐ[K] K')) (L : FiniteGaloisIntermediateField K K') : ∃ (s : Finset (NK.BrauerHasse.OverFinitePrime K K')), NK.HassePrinciple.levelObstruction p U L = ⨅ A ∈ s, (NK.BrauerHasse.locLevel p U A.1 L).hom.ker := by
  classical
  -- `ZMod p` is finite because `p` is a prime (in particular non-zero)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- the level cohomology is finite, so the complete lattice of submodules is finite
  haveI : Finite (LevelH2 p U L) := finite_levelH2 p U L
  let f : OverFinitePrime K K' → Submodule (Coeff p) (LevelH2 p U L) :=
    fun A => (locLevel p U A.1 L).hom.ker
  obtain ⟨s, hs⟩ := exists_finset_iInf_eq f
  refine ⟨s, ?_⟩
  rw [levelObstruction]
  exact hs

end NK.HassePrinciple
