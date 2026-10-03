/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The final step of [JZLA20, Theorem 6.1]: `U = D_{K[G],U}`

Two facts about *epic* homomorphisms into a `∗`-regular ring:

* if `φ : R →+* U` is epic and `U` is `∗`-regular, then the `∗`-regular closure of `φ(R)` is all
  of `U` (`starRegularClosure_eq_top_of_isEpic`) — the paper's argument:
  `R(φ(R),U) ↪ U` is epic and its source is `∗`-regular, so it is surjective by Stenström XI.1.4;
* consequently, if in addition the division closure `D` of `φ(K[G])` in `U` is a division ring, then
  `D = U` (`eq_divisionClosure_of_isEpic`), because the `∗`-regular closure is contained in `D`
  once `D` is a division ring closed under `star`.

This is the last step of [JZLA20, Theorem 6.1]: it upgrades "`D` is a division ring" to "`U` is a
division ring", which is the statement of the theorem.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.surjective_of_isEpic_of_vonNeumannRegular
import Submission.Work.ORHughesFree.Epic.starRegularClosure_le_divisionClosure_of_isDivisionRing
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_isStarRegular

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ORHughesFree

/-- **Epicity of a `∗`-homomorphism into a `∗`-regular ring forces the `∗`-regular closure to be
everything** ([JZLA20, §2.3]).

The inclusion `R(φ(R),U) ↪ U` is epic (it composes with `R → R(φ(R),U)` to `φ`), and its source is
`∗`-regular, hence von Neumann regular; by Stenström XI.1.4 an epic homomorphism from a von Neumann
regular ring is surjective. -/
theorem starRegularClosure_eq_top_of_isEpic {R : Type} [Ring R] {U : Type} [Ring U] [StarRing U]
    [IsStarRegular U] (φ : R →+* U) (hepic : IsEpic φ) :
    (starRegularClosure (starSubringClosure (Set.range φ)) : Set U) = Set.univ := by
  set S : StarSubring U := starRegularClosure (starSubringClosure (Set.range φ)) with hS
  haveI : IsStarRegular ↥S := StarRegular.starRegularClosure_isStarRegular _
  have hφS : ∀ x : R, φ x ∈ (S : Set U) := fun x =>
    subset_starRegularClosure _ (subset_starSubringClosure _ ⟨x, rfl⟩)
  let φ' : R →+* ↥S := φ.codRestrict S.toSubring hφS
  let ι : ↥S →+* U := Subring.subtype S.toSubring
  have hcomp : ι.comp φ' = φ := RingHom.ext fun _ => rfl
  have hι : IsEpic ι := IsEpic.of_comp (hcomp ▸ hepic)
  have hsurj : Function.Surjective ι := Epic.surjective_of_isEpic_of_vonNeumannRegular ι hι
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  obtain ⟨y, hy⟩ := hsurj x
  rw [← hy]
  exact y.2

/-- **The final step of [JZLA20, Theorem 6.1].**  If `φ : K[G] →+* U` is epic into a `∗`-regular
ring `U`, and the division closure `D` of `φ(K[G])` in `U` is a division ring (and closed under
`star`), then `D = U`. -/
theorem eq_divisionClosure_of_isEpic {K : Type} [Field K] {G : Type} [Group G] {U : Type}
    [Ring U] [StarRing U] [IsStarRegular U] (φ : MonoidAlgebra K G →+* U)
    (hstar : ∀ x : U, x ∈ (divisionClosure (Set.range φ) : Subring U) →
      star x ∈ (divisionClosure (Set.range φ) : Subring U))
    (hepic : IsEpic φ) (hD : IsDivisionRing ↥(divisionClosure (Set.range φ))) :
    (divisionClosure (Set.range φ) : Set U) = Set.univ := by
  have h1 : (starRegularClosure (starSubringClosure (Set.range φ)) : Set U) = Set.univ :=
    starRegularClosure_eq_top_of_isEpic φ hepic
  have h2 := Epic.starRegularClosure_le_divisionClosure_of_isDivisionRing φ hstar hD
  rw [h1] at h2
  exact Set.eq_univ_iff_forall.mpr fun x => h2 (Set.mem_univ x)

end Work.ORHughesFree
