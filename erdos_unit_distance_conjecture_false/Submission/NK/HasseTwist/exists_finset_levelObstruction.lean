/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The twisted level obstruction is a *finite* intersection of localisation kernels

The level obstruction

`NK.HasseTwist.levelObstruction p U L = ⨅ (A : OverFinitePrime K K'), (locLevel p U A.1 L).hom.ker`

is, by definition, the intersection of the kernels of the level-wise localisation maps, the infimum
running over *all* the places of `K'` over a finite prime of `K`.  The index type
`NK.BrauerTwist.OverFinitePrime K K'` is typically infinite, so this is a priori an infinite
intersection.

The present file proves that it is in fact a **finite** intersection:

`∃ s : Finset (OverFinitePrime K K'), levelObstruction p U L = ⨅ A ∈ s, (locLevel p U A.1 L).hom.ker`

(in particular it is a closed/definable condition, and one that can be checked on finitely many
places — the form consumed by the Chebotarev step of the Neukirch–Uchida development, where one
wants to choose a prime outside a *finite* set of bad places).

The mathematical content is only that the ambient module of the intersection is *finite*: the level
cohomology

`LevelH2 p U L = H²(U ⧸ (U ⊓ Gal(K'/L)), μ_p(L))`

is the second cohomology of a finite group (`NK.BrauerHasse.LevelGroup U L`, the level group)
with coefficients in the finite module `μ_p(L) ⊆ (K')ˣ`, and a finite module has only finitely many
submodules.  The intersection of an arbitrary family of submodules of a finite module is therefore
the intersection of the (finite) set of submodules that actually occur in the family.

This is the `μ_p`-twisted counterpart of
`Submission/Work/HassePrinciple/exists_finset_levelObstruction.lean`, which does the same for the
trivial coefficient module `Z/p`.

## Main results

* `NK.HasseTwist.finite_levelGroup` — the level group `U ⧸ (U ⊓ Gal(K'/L))` is finite;
* `NK.HasseTwist.finite_muLevel`, `NK.HasseTwist.finite_muRep_V` — the coefficient module
  `μ_p(L)` is finite when `p ≠ 0` (it is a subgroup of the `p`-th roots of unity of the field
  `K'`, of which there are at most `p`);
* `NK.HasseTwist.finite_LevelH2` — the level cohomology `H²(U ⧸ (U ⊓ Gal(K'/L)), μ_p(L))` is
  finite: it is a quotient of the `2`-cocycles `Z² ⊆ (G × G → μ_p(L))`, a submodule of a finite
  module (`groupCohomology.H2π`);
* `NK.HasseTwist.exists_finset_iInf_eq` — in any complete lattice whose elements form a finite
  type, an arbitrary infimum equals the infimum over a finite set of indices;
* `NK.HasseTwist.exists_finset_levelObstruction` — the level obstruction is a finite
  intersection of localisation kernels.

For the finiteness statements we need `ZMod p`/`μ_p` to be finite, i.e. `p ≠ 0`; this is exactly
why the prime hypothesis `hp : p.Prime` appears in the statement of the main theorem.
-/

import Mathlib
import Submission.NK.HasseTwist.Localisation

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

/-! ## Finiteness of the twisted level cohomology -/

section Finiteness

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K']

/-- **The level group is finite.**  `NK.BrauerHasse.LevelGroup U L = U ⧸ (U ⊓ Gal(K'/L))`: the
restriction map `AlgEquiv.restrictNormalHom L : Gal(K'/K) →* Gal(L/K)` has kernel
`L.fixingSubgroup`, so restricting it to `U` gives an *injection*
`U ⧸ (U ⊓ Gal(K'/L)) →* Gal(L/K)` into the (finite) Galois group of the finite extension `L/K`. -/
theorem finite_levelGroup (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    Finite (NK.BrauerHasse.LevelGroup U L) := by
  -- The restriction map to the finite Galois group of the finite level `L`.
  let g : ↥U →* Gal(L/K) := (AlgEquiv.restrictNormalHom L).comp U.subtype
  -- Its kernel is exactly the normal subgroup that is quotiented out in `LevelGroup U L`.
  have hker : L.fixingSubgroup.subgroupOf U = MonoidHom.ker g := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact FiniteGaloisIntermediateField.mem_fixingSubgroup_iff _ _
  change Finite (↥U ⧸ L.fixingSubgroup.subgroupOf U)
  rw [hker]
  exact Finite.of_injective (QuotientGroup.kerLift g) (QuotientGroup.kerLift_injective g)

variable [IsSepClosure K K']

/-- **The level module `μ_p(L)` is finite** for `p ≠ 0`: it is a subgroup of the `p`-th roots of
unity of the field `K'`, and `X ^ p - 1` has at most `p` roots in an integral domain. -/
instance finite_muLevel (p : ℕ) [NeZero p] (L : FiniteGaloisIntermediateField K K') :
    Finite ↥(muLevel p L) := inferInstance

/-- The additive group underlying the level representation of `Gal(K'/K)` on `μ_p(L)` is finite;
stated for `muRep` itself so that typeclass search can see it through the abbreviation
`NK.BrauerTwist.levelRep = Rep.res (levelGroupHom U L) (muRep p L)`. -/
instance finite_muRep_V (p : ℕ) [NeZero p] (L : FiniteGaloisIntermediateField K K') :
    Finite (muRep p L).V := by
  change Finite (Additive ↥(muLevel p L))
  infer_instance

/-- **The twisted level cohomology is finite.**  `LevelH2 p U L = H²(G, μ_p(L))` with
`G = NK.BrauerHasse.LevelGroup U L` finite and `μ_p(L)` finite: by `groupCohomology.H2π` the
cohomology is a quotient of the `2`-cocycles, which form a submodule of the finite module
`G × G → μ_p(L)`. -/
theorem finite_LevelH2 (p : ℕ) [NeZero p] (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : Finite (LevelH2 p U L) := by
  haveI : Finite (NK.BrauerHasse.LevelGroup U L) := finite_levelGroup U L
  haveI : Finite (levelRep p U L).V := inferInstance
  haveI : Finite (groupCohomology.cocycles₂ (levelRep p U L)) := inferInstance
  exact Finite.of_surjective (groupCohomology.H2π (levelRep p U L)).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

end Finiteness

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

/-- **The level obstruction is a finite intersection of localisation kernels.**  By definition
`levelObstruction p U L` is the infimum of the kernels `(locLevel p U A.1 L).hom.ker` over *all*
places `A` of `K'` over a finite prime of `K`.  Its ambient module `LevelH2 p U L` is finite
(`finite_LevelH2`, using `p ≠ 0`), so a complete lattice of submodules with finitely many elements,
and an arbitrary infimum there is the infimum over the finite set of submodules that actually
occur (`exists_finset_iInf_eq`). -/
theorem exists_finset_levelObstruction (p : ℕ) (hp : p.Prime) {K K' : Type u} [Field K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    ∃ s : Finset (NK.BrauerTwist.OverFinitePrime K K'),
      NK.HasseTwist.levelObstruction p U L =
        ⨅ A ∈ s, (NK.BrauerTwist.locLevel p U A.1 L).hom.ker := by
  classical
  -- `μ_p` is finite because `p` is a prime (in particular non-zero)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- the level cohomology is finite, so the complete lattice of submodules is finite
  haveI : Finite (LevelH2 p U L) := finite_LevelH2 p U L
  let f : OverFinitePrime K K' → Submodule CoeffInt (LevelH2 p U L) :=
    fun A => (locLevel p U A.1 L).hom.ker
  obtain ⟨s, hs⟩ := exists_finset_iInf_eq f
  refine ⟨s, ?_⟩
  rw [levelObstruction]
  exact hs

end NK.HasseTwist
