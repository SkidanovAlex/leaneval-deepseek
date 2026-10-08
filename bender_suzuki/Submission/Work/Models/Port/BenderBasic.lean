/-
**The easy direction of the Bender–Suzuki classification.**

The challenge theorem `Submission.bender_suzuki` states that a finite simple group with a
strongly embedded subgroup is isomorphic to one of `PSL(2,2ⁿ)`, `Sz(2^(2n+1))`, `PSU(3,2ⁿ)`.

This file records the converse implication, which is completely formalised in this workspace:
*every* Bender group (that is, every group in one of the three families) is simple and has a
strongly embedded subgroup.  This shows that the hypotheses of the challenge theorem are
satisfied by each of the three families, i.e. the classification is tight.

Contents:
* `isStronglyEmbedded_of_mulEquiv` — strong embedding is transported along a group isomorphism
  (obtained from the general commons lemma
  `Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective` applied to a
  bijection, whose kernel is trivial).
* `isSimpleGroup_of_isSimpleBenderGroup` — every Bender group is simple, using the simplicity of
  `PSL(2,2ⁿ)` (`PSL2Model_isSimpleGroup`), `Sz(2^(2n+1))` (`Submission.Sz.isSimpleGroup_SzModel`)
  and `PSU(3,2ⁿ)` (`Submission.PSU3.isSimpleGroup_PSU3Model`).
* `exists_isStronglyEmbedded_of_isSimpleBenderGroup` — every Bender group has a strongly embedded
  subgroup, using `PSL2Model_exists_isStronglyEmbedded`,
  `Submission.Sz.szBorel_stronglyEmbedded` and
  `Submission.PSU3.PSU3Model_exists_isStronglyEmbedded`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSL2Model
import Submission.Work.Models.Port.PSU3.Main
import Submission.Work.Models.Port.PSU3.Simple
import Submission.Work.Models.Port.Sz.Main
import Submission.Work.Models.Port.Sz.Simple
import Submission.Work.Models.Port.Commons.GroupTheory.IsSimpleGroup.of_mulEquiv
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs

namespace Submission

/-- Strong embedding is preserved by a group isomorphism. -/
theorem isStronglyEmbedded_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (M : Subgroup X) (hM : IsStronglyEmbedded M) (e : X ≃* Y) :
    IsStronglyEmbedded (M.map e.toMonoidHom) := by
  obtain ⟨hne, heven, hodd⟩ := hM
  have hkerbot : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  have hker : e.toMonoidHom.ker ≤ M := by rw [hkerbot]; exact bot_le
  have hkercenter : e.toMonoidHom.ker ≤ Subgroup.center X := by rw [hkerbot]; exact bot_le
  have hkerodd : Odd (Nat.card e.toMonoidHom.ker) := by
    rw [hkerbot]
    have h1 : Nat.card ↥(⊥ : Subgroup X) = 1 := Nat.card_unique
    rw [h1]
    norm_num
  exact Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective
    e.toMonoidHom e.surjective M hne heven hodd hker hkercenter hkerodd

/-- Every Bender group is simple. -/
theorem isSimpleGroup_of_isSimpleBenderGroup {X : Type*} [Group X] [Finite X]
    (h : IsSimpleBenderGroup X) : IsSimpleGroup X := by
  cases h with
  | isPSL2 n hn e =>
      exact Commons.GroupTheory.IsSimpleGroup.of_mulEquiv e.symm (PSL2Model_isSimpleGroup n hn)
  | isSuzuki n hn e =>
      exact Commons.GroupTheory.IsSimpleGroup.of_mulEquiv e.symm
        (Submission.Sz.isSimpleGroup_SzModel n hn)
  | isPSU3 n hn e =>
      exact Commons.GroupTheory.IsSimpleGroup.of_mulEquiv e.symm
        (Submission.PSU3.isSimpleGroup_PSU3Model n hn)

/-- Every Bender group has a strongly embedded subgroup. -/
theorem exists_isStronglyEmbedded_of_isSimpleBenderGroup {X : Type*} [Group X] [Finite X]
    (h : IsSimpleBenderGroup X) : ∃ M : Subgroup X, IsStronglyEmbedded M := by
  cases h with
  | isPSL2 n hn e =>
      obtain ⟨M, hM⟩ := PSL2Model_exists_isStronglyEmbedded n hn
      exact ⟨M.map e.symm.toMonoidHom, isStronglyEmbedded_of_mulEquiv M hM e.symm⟩
  | isSuzuki n hn e =>
      have hM : IsStronglyEmbedded (Submission.Sz.szBorelS n) :=
        Submission.Sz.szBorel_stronglyEmbedded n hn
      exact ⟨(Submission.Sz.szBorelS n).map e.symm.toMonoidHom,
        isStronglyEmbedded_of_mulEquiv _ hM e.symm⟩
  | isPSU3 n hn e =>
      obtain ⟨M, hM⟩ := Submission.PSU3.PSU3Model_exists_isStronglyEmbedded n hn
      exact ⟨M.map e.symm.toMonoidHom, isStronglyEmbedded_of_mulEquiv M hM e.symm⟩

/-- The two properties that characterise the hypothesis side of the Bender–Suzuki
classification: a Bender group is simple and admits a strongly embedded subgroup. -/
theorem isSimpleBenderGroup_iff_necessary {X : Type*} [Group X] [Finite X]
    (h : IsSimpleBenderGroup X) :
    IsSimpleGroup X ∧ ∃ M : Subgroup X, IsStronglyEmbedded M :=
  ⟨isSimpleGroup_of_isSimpleBenderGroup h, exists_isStronglyEmbedded_of_isSimpleBenderGroup h⟩

end Submission
