/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The reduction of Neukirch's (9.2.1) to the Hasse principle

Umbrella development: `Submission/Work/HassePrinciple/` (README §18).

`Submission/Work/HassePrinciple/LocalGroupInputDefs.lean` defines the local groups `U ⊓ D_A` over a
prime `𝔭` (`NK.HassePrinciple.localGroupsOver`), the localisation to them
(`NK.HassePrinciple.localGroupLoc`) and the input `NK.HassePrinciple.NSWSInput` — Neukirch's
(9.2.1) (NSW (9.2.1)) together with the local computations of local class field theory.  The rank
count `NK.HassePrinciple.subsingleton_localGroupsOver_of_surjective` converts the surjectivity
into the statement that all the local groups over `𝔭` coincide.

This module assembles the reduction to the chapter's interfaces:

* `NK.HassePrinciple.rankInput_of_nswsInput` — `NSWSInput → RankInput`;
* `NK.HassePrinciple.sha2Vanishing_of_nswsInput` — `NSWSInput → Sha2Vanishing`, the target of the
  chapter;
* `NK.HassePrinciple.localCharacterisation_of_nswsInput` — `NSWSInput` (together with the local
  Brauer input and the local finishing step) gives Neukirch's local characterisation of the
  decomposition groups (README §17).

The last step of the rank count: once the local groups over `𝔭` coincide, the localisation
`localGroupLoc` has a *subsingleton* index type, so its single component is surjective; the
component is (by construction) the localisation at the place `localGroupPlace V` of the unique local
group `V`, written in the local cohomology `LocalH2`.  The order comparison is the local computation
`p ≤ |H²(V, Z/p)|` of the input, together with `|H²(U, Z/p)| = p`.
-/

import Mathlib
import Submission.NK.HassePrinciple.LocalGroupInputDefs
import Submission.NK.HassePrinciple.subsingleton_localGroupsOver_of_surjective
import Submission.NK.HassePrinciple.LocalCharacterisation

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The reduction of Neukirch's (9.2.1) to the rank input.**  The input `NSWSInput` — the
surjectivity of the localisation to the local groups over some prime, together with the local
computations `|H²(U, Z/p)| = p` and `p ≤ |H²(V, Z/p)|` at the local groups — implies
`NK.HassePrinciple.RankInput`: at the (unique, by the rank count) local group over `𝔭` the
localisation is bijective.

Proof.  By `NK.HassePrinciple.subsingleton_localGroupsOver_of_surjective` all the local groups over
`𝔭` coincide, so the index set of the product defining `localGroupLoc` is a subsingleton and the
component at the local group `V₀` is surjective; its target is `H2Profinite p V₀ = LocalH2 p U A₀`
for the chosen place `A₀ = localGroupPlace V₀`, and the order comparison is `p ≤ |H²(V₀, Z/p)|`. -/
theorem rankInput_of_nswsInput (h : NSWSInput (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p where
  hp := h.hp
  card_global := fun U hU hκ =>
    (Nat.card_ne_zero.mp (by rw [h.card_global U hU hκ]; exact h.hp.ne_zero)).2
  rank := fun U hU hκ _ => by
    obtain ⟨𝔭, hloc, hsurj⟩ := h.prime_surj U hU hκ
    have hcard := h.card_global U hU hκ
    obtain ⟨V₀, hV₀mem⟩ := localGroupsOver_nonempty (K := K) (K' := K') U 𝔭
    have hsingle := subsingleton_localGroupsOver_of_surjective (K := K) (K' := K') h.hp U 𝔭
      hcard hloc hsurj
    classical
    -- the target of the localisation is a product over a subsingleton index type, so its single
    -- component is surjective
    have hcomp : Function.Surjective (fun x : H2Profinite p U =>
        localGroupLoc (K := K) (K' := K') p U 𝔭 x ⟨V₀, hV₀mem⟩) := by
      intro y
      let hfam : ∀ V : ↥(localGroupsOver (K := K) (K' := K') U 𝔭),
          H2Profinite (K := K) (K' := K') p V.1 := fun V =>
        if hh : V = ⟨V₀, hV₀mem⟩ then
          cast (congrArg (fun W : Subgroup Gal(K'/K) =>
            H2Profinite (K := K) (K' := K') p W)
            (congrArg (fun W : ↥(localGroupsOver (K := K) (K' := K') U 𝔭) => W.1) hh).symm) y
        else 0
      obtain ⟨x, hx⟩ := hsurj hfam
      refine ⟨x, ?_⟩
      show localGroupLoc (K := K) (K' := K') p U 𝔭 x ⟨V₀, hV₀mem⟩ = y
      rw [congrFun hx ⟨V₀, hV₀mem⟩]
      simp only [hfam, dif_pos rfl, congrArg, cast_eq]
    -- the component is, by construction, a cast of the localisation at the chosen place
    have hsurjLoc : Function.Surjective (locAt (K := K) (K' := K') p U
        (localGroupPlace (U := U) ⟨V₀, hV₀mem⟩).toOverFinitePrime) := by
      have e : H2Profinite (K := K) (K' := K') p
            (U ⊓ stabSubgroup (localGroupPlace (U := U) ⟨V₀, hV₀mem⟩).toOverFinitePrime.1) =
          H2Profinite (K := K) (K' := K') p V₀ :=
        congrArg (fun W : Subgroup Gal(K'/K) => H2Profinite (K := K) (K' := K') p W)
          (localGroupPlace_spec (U := U) ⟨V₀, hV₀mem⟩)
      have hthis : (fun x : H2Profinite p U => localGroupLoc (K := K) (K' := K') p U 𝔭 x
            ⟨V₀, hV₀mem⟩) = fun x => cast e (locAt (K := K) (K' := K') p U
              (localGroupPlace (U := U) ⟨V₀, hV₀mem⟩).toOverFinitePrime x) := rfl
      have hcomp' : Function.Surjective (fun x => cast e (locAt (K := K) (K' := K') p U
          (localGroupPlace (U := U) ⟨V₀, hV₀mem⟩).toOverFinitePrime x)) := by
        rw [← hthis]
        exact hcomp
      intro z
      obtain ⟨x, hx⟩ := hcomp' (cast e z)
      exact ⟨x, (cast_inj e).mp hx⟩
    refine ⟨(localGroupPlace (U := U) ⟨V₀, hV₀mem⟩).toOverFinitePrime, hsurjLoc, ?_⟩
    have heq : LocalH2 (K := K) (K' := K') p U
          (localGroupPlace (U := U) ⟨V₀, hV₀mem⟩).toOverFinitePrime.1 =
        H2Profinite (K := K) (K' := K') p V₀ := by
      rw [show (localGroupPlace (U := U) ⟨V₀, hV₀mem⟩).toOverFinitePrime.1 =
          (localGroupPlace (U := U) ⟨V₀, hV₀mem⟩).1 from rfl]
      rw [LocalH2_eq_H2Profinite, localGroupPlace_spec]
    rw [hcard, heq]
    exact hloc V₀ hV₀mem

/-- **The Hasse principle from Neukirch's (9.2.1) and local class field theory.** -/
theorem sha2Vanishing_of_nswsInput (h : NSWSInput (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_rankInput (rankInput_of_nswsInput h)

/-- **Neukirch's local characterisation of the decomposition groups from his (9.2.1).**  The input
`NSWSInput` — Neukirch's surjectivity at a prime, plus the local computations of local class field
theory — together with the local Brauer input and the local finishing step of the Neukirch argument,
yields the statement that every closed self-normalising subgroup isomorphic to `Gal(κ'/κ)` is
contained in the decomposition group of a place over a finite prime (README §17). -/
theorem localCharacterisation_of_nswsInput (h : NSWSInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hLoc : LocalH2Input p K K' κ κ') (hStep : LocalDecompositionCriterion p K K' κ κ')
    (U : Subgroup Gal(K'/K)) (hU : IsClosed (U : Set Gal(K'/K)))
    (hN : Subgroup.normalizer U = U) (hκ : Nonempty (U ≃* Gal(κ'/κ))) :
    ∃ A : OverFinitePrime K K', U ≤ stabSubgroup A.1 :=
  localCharacterisation_of_sha2Vanishing p hLoc hStep (sha2Vanishing_of_nswsInput h) U hU hN hκ

end NK.HassePrinciple
