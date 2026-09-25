import Mathlib
import Submission.Work.TameArithmetic.Defs
import Submission.Work.TameArithmetic.card_le_of_generating_presentedGroup
import Submission.Work.TameArithmetic.residuallyFiniteTwoGroup_galoisGroup_tame
import Submission.Work.ClassFieldTower.isPGroup_two_of_residuallyFiniteTwo_of_finite
import Submission.GroupTheory.GolodShafarevichFromCommons

/-!
# `Work.TameArithmetic.infinite_galoisGroup_of_presentation`

**The Golod--Shafarevich seam of the tame route.**  If `K` is a maximal tame pro-`2` extension of
`ℚ` for `S = primesS = {17,41,73,89,97}` (`IsMaximalTamePro2 K`) and `P` is a pro-`2`
presentation of `Γ = Gal(K/ℚ) = K ≃ₐ[ℚ] K` by **five generators and at most six relators**
(`TamePro2Presentation K`), then `Γ` is **infinite**.

## The argument

The group-theoretic input is Chapter B, the finite `p`-group Golod--Shafarevich inequality
`Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons 2`, consumed through the
corrected criterion `Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich`:

> a group `G` presented as `FreeGroup α ⧸ ⟪rel⟫` with `α` a minimal generating set, all of whose
> finite quotients are `p`-groups, and with `4 * rel.card ≤ card α ^ 2`, is infinite.

We apply it to `G = presentedGroup P = FreeGroup (Fin 5) ⧸ ⟪P.rel⟫` and argue **by contradiction**,
`¬ Infinite Γ`:

* `Finite Γ` makes `K/ℚ` finite dimensional (`IsGalois.finiteDimensional_of_finite`), hence `K` is
  a number field; the sub-clause `TameSubClause K` applied to `K` itself then gives
  `IsPGroup 2 Γ` -- a finite Galois extension of `ℚ` whose Galois group is pro-`2` is
  a `2`-group at the finite level;
* `P.ker_eq` makes the presentation map `FreeGroup.lift P.gen` descend to an **injective**
  `ψ : presentedGroup P →* Γ`, so `presentedGroup P` is finite
  (`Finite.of_injective`) and a `2`-group (`IsPGroup.of_injective`); every finite quotient of
  `presentedGroup P` is therefore a `2`-group (`IsPGroup.of_surjective`);
* `α = Fin 5` is a minimal generating set of `presentedGroup P`
  (`card_le_of_generating_presentedGroup`, the multiquadratic certificate `d ≥ |S| = 5`) and
  `4 * P.rel.card ≤ 4 * 6 = 24 ≤ 25 = 5 ^ 2` (`four_mul_le_sq_of_rel_card_le_six`);
* the criterion therefore yields `Infinite (presentedGroup P)`, contradicting its finiteness.

Note what is *not* needed: the abstract-model condition `IsProTwoModel K (presentedGroup P)`
would only be required to know *unconditionally* that every finite quotient of
`presentedGroup P` is a `2`-group.  Under the contradiction hypothesis `Finite Γ` this is free,
which is why the lemma needs nothing beyond `IsMaximalTamePro2 K` and `P`.  (Without the
finiteness assumption it is genuinely false that all finite quotients of the abstract group are
`2`-groups: `ℤ` is a dense subgroup of `ℤ₂` but has the quotient `ℤ/3`.)
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical

namespace Work.TameArithmetic

theorem infinite_galoisGroup_of_presentation {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (hmax : Work.TameArithmetic.IsMaximalTamePro2 K)
    (P : Work.TameArithmetic.TamePro2Presentation K) : Infinite (K ≃ₐ[ℚ] K) := by
  classical
  by_contra hcon
  -- `Finite Γ`, so `K/ℚ` is finite dimensional and `K` is a number field
  haveI hfinK : Finite (K ≃ₐ[ℚ] K) := not_infinite_iff_finite.mp hcon
  haveI hfdK : FiniteDimensional ℚ K := IsGalois.finiteDimensional_of_finite ℚ K
  haveI hnumK : NumberField K := NumberField.of_module_finite ℚ K
  -- a finite Galois extension of `ℚ` with pro-`2` Galois group is a finite `2`-group
  have hpgK : IsPGroup 2 (K ≃ₐ[ℚ] K) :=
    (hmax.2.2 K (AlgHom.id ℚ K) (fun _ _ h => h)).1
  -- the presentation map descends to an injection `presentedGroup P →* Γ`
  have hle : Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin 5))) ≤
      MonoidHom.ker (FreeGroup.lift P.gen) := by rw [P.ker_eq]
  let ψ : Work.TameArithmetic.presentedGroup P →* (K ≃ₐ[ℚ] K) :=
    QuotientGroup.lift (Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin 5))))
      (FreeGroup.lift P.gen) hle
  have hψ : Function.Injective ψ := by
    show Function.Injective
      (QuotientGroup.lift (Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin 5))))
        (FreeGroup.lift P.gen) hle)
    rw [QuotientGroup.injective_lift_iff]
    exact P.ker_eq.symm
  have hfinP : Finite (Work.TameArithmetic.presentedGroup P) := Finite.of_injective ψ hψ
  haveI : Finite (Work.TameArithmetic.presentedGroup P) := hfinP
  have hpgP : IsPGroup 2 (Work.TameArithmetic.presentedGroup P) := hpgK.of_injective ψ hψ
  -- every finite quotient of `presentedGroup P` is a `2`-group
  have hpg : ∀ (N : Subgroup (Work.TameArithmetic.presentedGroup P)) [N.Normal],
      Finite (Work.TameArithmetic.presentedGroup P ⧸ N) →
        IsPGroup 2 (Work.TameArithmetic.presentedGroup P ⧸ N) := by
    intro N _
    exact fun _ => hpgP.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  -- `Fin 5` is a minimal generating set: `d ≥ |S| = 5`
  have hmin : ∀ S : Finset (Work.TameArithmetic.presentedGroup P),
      Subgroup.closure (S : Set (Work.TameArithmetic.presentedGroup P)) = ⊤ →
        Fintype.card (Fin 5) ≤ S.card := by
    intro S hS
    simpa using Work.TameArithmetic.card_le_of_generating_presentedGroup hmax P S hS
  -- the counting `4 · 6 ≤ 5²`
  have hineq : 4 * P.rel.card ≤ Fintype.card (Fin 5) * Fintype.card (Fin 5) := by
    simpa using Work.TameArithmetic.four_mul_le_sq_of_rel_card_le_six P.rel_card
  -- the corrected Golod--Shafarevich criterion
  have hinf : Infinite (Work.TameArithmetic.presentedGroup P) :=
    Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich
      (Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons 2)
      P.rel (by simp)
      ⟨MulEquiv.refl (FreeGroup (Fin 5) ⧸
        Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin 5))))⟩
      hmin hpg hineq
  exact (not_infinite_iff_finite.mpr hfinP) hinf

end Work.TameArithmetic
