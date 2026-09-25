/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neukirch's (9.2.1) from an inert place

Umbrella development: `Submission/Work/HassePrinciple/`.

The input `NK.HassePrinciple.NSWSInput` (Neukirch's surjectivity (9.2.1) together with the local
computations of local class field theory) requires, for every closed `U ≤ Gal(K'/K)` isomorphic to
`Gal(κ'/κ)`, a finite prime `𝔭` of `K` such that

* every local group `V = U ⊓ D_A` over `𝔭` satisfies `p ≤ |H²(V, Z/p)|`, and
* the localisation `H²(U, Z/p) → ∏_{V ∈ localGroupsOver U 𝔭} H²(V, Z/p)` is **surjective**.

This module shows that both are *formal consequences* of the weaker datum that every place `A` over
`𝔭` has `U ≤ D_A` (`hinert`) together with the local computation `|H²(U, Z/p)| = p` at `U`
(`hcard`):

* if `U ≤ D_A` for every place `A` over `𝔭`, then every local group over `𝔭` **is** `U`
  (`U ⊓ D_A = U`), so the cardinality bound reduces to `p ≤ |H²(U, Z/p)| = p`;
* the index set `localGroupsOver U 𝔭` is then a singleton, and the localisation at the unique local
  group `U` is the localisation at the place `localGroupPlace ⟨U, _⟩`, which is *bijective* by
  `NK.HassePrinciple.locAt_bijective_of_le_stabSubgroup`.  Hence `localGroupLoc` is surjective.

The corresponding *global* statement is `NK.HassePrinciple.nswsInput_of_le_stabSubgroup`: Neukirch's
input follows from `NK.HassePrinciple.rankInput_of_inert_of_card`-style data, i.e. from the
existence of an inert place for every labelled closed subgroup together with the local computation
`|H²(U, Z/p)| = p`.
-/

import Mathlib
import Submission.NK.HassePrinciple.LocalGroupInputDefs
import Submission.NK.HassePrinciple.locAt_bijective_of_le_stabSubgroup

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u v

namespace NK.HassePrinciple

open NK.BrauerHasse

section Helpers

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The two transports along an equality of types and its inverse cancel. -/
lemma nsws_cast_cast_symm {α β : Type v} (h : α = β) (a : β) : cast h (cast h.symm a) = a := by
  cases h
  rfl

/-- **If every place over `𝔭` has decomposition group containing `U`, then `U` is the only local
group over `𝔭`.**  A member of `localGroupsOver U 𝔭` is `U ⊓ D_A` for some place `A` over `𝔭`, and
`U ⊓ D_A = U` because `U ≤ D_A`. -/
theorem eq_of_mem_localGroupsOver_of_forall_le_stabSubgroup {U V : Subgroup Gal(K'/K)}
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hle : ∀ A : PlacesOverPrime K K' 𝔭, U ≤ stabSubgroup A.1)
    (hV : V ∈ localGroupsOver (K := K) (K' := K') U 𝔭) : V = U := by
  obtain ⟨A, hA⟩ := hV
  exact hA.symm.trans (inf_eq_left.mpr (hle A))

/-- **Neukirch's surjectivity at an inert place.**  If every place `A` over the finite prime `𝔭` has
decomposition group containing `U`, the local groups over `𝔭` are all equal to `U`; the localisation
to the (unique) local group is the localisation at the place realising it, which is bijective by
`NK.HassePrinciple.locAt_bijective_of_le_stabSubgroup`.  Hence `localGroupLoc` is surjective. -/
theorem surjective_localGroupLoc_of_forall_le_stabSubgroup (p : ℕ) {U : Subgroup Gal(K'/K)}
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hle : ∀ A : PlacesOverPrime K K' 𝔭, U ≤ stabSubgroup A.1) :
    Function.Surjective (localGroupLoc (K := K) (K' := K') p U 𝔭) := by
  classical
  intro f
  obtain ⟨V₀, hV₀mem⟩ := localGroupsOver_nonempty (K := K) (K' := K') U 𝔭
  have hV₀U : V₀ = U := eq_of_mem_localGroupsOver_of_forall_le_stabSubgroup hle hV₀mem
  -- the place realising the unique local group, and the bijectivity of its localisation
  have hbij := locAt_bijective_of_le_stabSubgroup (K := K) (K' := K') p
    (localGroupPlace (U := U) ⟨V₀, hV₀mem⟩).toOverFinitePrime
    (hle (localGroupPlace (U := U) ⟨V₀, hV₀mem⟩))
  -- hit the value at the unique index, transported back to the local cohomology of `U ⊓ D_A`
  obtain ⟨x, hx⟩ := hbij.2
    (cast (congrArg (fun W : Subgroup Gal(K'/K) => H2Profinite (K := K) (K' := K') p W)
        (localGroupPlace_spec (U := U) ⟨V₀, hV₀mem⟩)).symm (f ⟨V₀, hV₀mem⟩))
  refine ⟨x, ?_⟩
  funext V
  have hVeq : V = ⟨V₀, hV₀mem⟩ :=
    Subtype.ext ((eq_of_mem_localGroupsOver_of_forall_le_stabSubgroup hle V.2).trans hV₀U.symm)
  rw [hVeq, localGroupLoc_apply, hx]
  exact nsws_cast_cast_symm _ _

end Helpers

/-- **Neukirch's (9.2.1) from an inert place.**  Suppose that the local computation
`|H²(U, Z/p)| = p` holds at every closed subgroup `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)`
(`hcard`), and that every such `U` is contained in the decomposition group of every place over some
finite prime `𝔭` of `K` (`hinert`).  Then `NK.HassePrinciple.NSWSInput` holds: at that prime the
local groups over `𝔭` are all `U`, so the localisation to them is the (bijective, hence surjective)
localisation at an inert place.

The arithmetic content is exactly the hypothesis `hinert`; the rest is the formal algebra of
`localGroupsOver`. -/
theorem nswsInput_of_le_stabSubgroup {p : ℕ} (hp : p.Prime) {K K' κ κ' : Type u}
    [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (hcard : ∀ U : Subgroup Gal(K'/K), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) →
      Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) = p)
    (hinert : ∀ U : Subgroup Gal(K'/K), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) →
      ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ∀ A : NK.HassePrinciple.PlacesOverPrime K K' 𝔭,
          U ≤ NK.BrauerHasse.stabSubgroup A.1) :
    NK.HassePrinciple.NSWSInput (K := K) (K' := K') (κ := κ) (κ' := κ') p := by
  refine ⟨hp, hcard, ?_⟩
  intro U hU hκ
  obtain ⟨𝔭, hle⟩ := hinert U hU hκ
  refine ⟨𝔭, ?_, ?_⟩
  · intro V hV
    rw [eq_of_mem_localGroupsOver_of_forall_le_stabSubgroup hle hV, hcard U hU hκ]
  · exact surjective_localGroupLoc_of_forall_le_stabSubgroup (K := K) (K' := K') p hle

end NK.HassePrinciple
