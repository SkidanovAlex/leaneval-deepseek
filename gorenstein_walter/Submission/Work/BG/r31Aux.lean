import Mathlib
import Submission.Work.BG.CharBridge
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.rem31Structure
import Submission.Work.BG.indexTwoCliffordRestrict
import Submission.Work.BG.restrictEqOfInvariantConstituent
import Submission.Work.BG.restrictConjBySubgroupOf
import Submission.Work.BG.conjByEqSelfOfSupZpowersEqTop

/-! Auxiliary lemmas for `Work.BG.rem31Shape`. -/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

section Helpers

variable {Y : Type*} [Group Y]

lemma closure_union_singleton_eq_top (A : Subgroup Y) (x : Y)
    (h : A ⊔ Subgroup.zpowers x = ⊤) : Subgroup.closure ((A : Set Y) ∪ {x}) = ⊤ := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  exact h

end Helpers

section Helpers2

variable {H K : Type*} [Group H] [Group K]

lemma compHom_injective (f : H →* K) (hf : Function.Surjective f) :
    Function.Injective (fun φ : ClassFunction K ℂ => ClassFunction.compHom f φ) := by
  intro φ ψ hfg
  ext k
  obtain ⟨y, rfl⟩ := hf k
  exact congrFun (congrArg (fun z : ClassFunction H ℂ => (z : H → ℂ)) hfg) y

lemma compHom_add (f : H →* K) (φ ψ : ClassFunction K ℂ) :
    ClassFunction.compHom f (φ + ψ) = ClassFunction.compHom f φ + ClassFunction.compHom f ψ := by
  ext x
  simp [ClassFunction.compHom_apply]

lemma compHom_compHom (f : K →* H) (g : H →* K) (φ : ClassFunction H ℂ) :
    ClassFunction.compHom g (ClassFunction.compHom f φ)
      = ClassFunction.compHom (f.comp g) φ := by
  ext x
  simp [ClassFunction.compHom_apply]

lemma compHom_id (φ : ClassFunction K ℂ) :
    ClassFunction.compHom (MonoidHom.id K) φ = φ := by
  ext x
  simp [ClassFunction.compHom_apply]

end Helpers2

section InnerHelpers

variable {Y : Type*} [Group Y] [Finite Y] [Fintype Y] [Invertible (Nat.card Y : ℂ)]

lemma inner_self_eq_one (a : ClassFunction Y ℂ) (ha : IsIrreducibleCharacter a) :
    ClassFunction.inner a a = 1 := by
  rw [irreducibleCharacter_inner_eq_ite ⟨a, ha⟩ ⟨a, ha⟩, if_pos rfl]

lemma inner_add_self_ne_zero (a b : ClassFunction Y ℂ) (ha : IsIrreducibleCharacter a)
    (hb : IsIrreducibleCharacter b) : ClassFunction.inner (a + b) a ≠ 0 := by
  rw [ClassFunction.inner_add_left, inner_self_eq_one a ha,
    irreducibleCharacter_inner_eq_ite ⟨b, hb⟩ ⟨a, ha⟩]
  split_ifs <;> norm_num

lemma inner_add_add_eq_two (a b : ClassFunction Y ℂ) (ha : IsIrreducibleCharacter a)
    (hb : IsIrreducibleCharacter b) (hne : (⟨a, ha⟩ : IrreducibleCharacter Y) ≠ ⟨b, hb⟩) :
    ClassFunction.inner (a + b) (a + b) = 2 := by
  rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right, ClassFunction.inner_add_right,
    irreducibleCharacter_inner_eq_ite ⟨a, ha⟩ ⟨a, ha⟩,
    irreducibleCharacter_inner_eq_ite ⟨a, ha⟩ ⟨b, hb⟩,
    irreducibleCharacter_inner_eq_ite ⟨b, hb⟩ ⟨a, ha⟩,
    irreducibleCharacter_inner_eq_ite ⟨b, hb⟩ ⟨b, hb⟩,
    if_pos rfl, if_neg hne, if_neg (fun h => hne h.symm), if_pos rfl]
  norm_num

end InnerHelpers

section RestrictHelpers

variable {Y : Type*} [Group Y]

lemma restrict_add (A : Subgroup Y) (φ ψ : ClassFunction Y ℂ) :
    ClassFunction.restrict A (φ + ψ) = ClassFunction.restrict A φ + ClassFunction.restrict A ψ := by
  ext x
  simp

end RestrictHelpers

end Work.BG
