/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eigenvectors, characteristic roots and rootless traces in `SL(2,F)`
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.Count.Defs

open scoped MatrixGroups
open Matrix Polynomial

namespace Work.L2F.Count

variable {F : Type*} [Field F]

/-- An eigenvector of `M` over `F` is a root of the characteristic polynomial. -/
theorem hasEigenvector_iff_charpoly_isRoot (M : Matrix (Fin 2) (Fin 2) F) :
    HasEigenvector F M ↔ ∃ μ : F, M.charpoly.IsRoot μ := by
  have key : ∀ μ : F, Module.End.HasEigenvalue (Matrix.toLin' M) μ ↔
      ∃ v : Fin 2 → F, v ≠ 0 ∧ M *ᵥ v = μ • v := by
    intro μ
    rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
    constructor
    · rintro ⟨v, hv, hne⟩
      exact ⟨v, hne, by rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv⟩
    · rintro ⟨v, hne, hv⟩
      exact ⟨v, by rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply], hne⟩
  constructor
  · rintro ⟨v, hv, μ, hμ⟩
    refine ⟨μ, ?_⟩
    have h : Module.End.HasEigenvalue (Matrix.toLin' M) μ := (key μ).mpr ⟨v, hv, hμ⟩
    rwa [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin'] at h
  · rintro ⟨μ, hμ⟩
    obtain ⟨v, hv, hμv⟩ := (key μ).mp (by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']; exact hμ)
    exact ⟨v, hv, μ, hμv⟩

/-- The characteristic polynomial of an element of `SL(2,F)` is `X² - tr(X) X + 1`. -/
theorem charpoly_sl (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    (x : Matrix (Fin 2) (Fin 2) F).charpoly = quad F ((x : Matrix (Fin 2) (Fin 2) F).trace) := by
  rw [Matrix.charpoly_fin_two, quad, x.2]
  simp

/-- `x ∈ SL(2,F)` has no eigenvector over `F` exactly when `X² - tr(x) X + 1` has no root in
`F`. -/
theorem not_hasEigenvector_iff_rootless (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    ¬ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F) ↔
      Rootless F ((x : Matrix (Fin 2) (Fin 2) F).trace) := by
  rw [hasEigenvector_iff_charpoly_isRoot, charpoly_sl, not_exists, rootless_iff]

/-- The sum of the `0`/`1` indicator over a finite type is the cardinality of the corresponding
subtype. -/
theorem sum_indicator {α : Type*} [Fintype α] (p : α → Prop) :
    ∑ x : α, indicator (p x) = Nat.card {x : α // p x} := by
  classical
  have h1 : Nat.card {x : α // p x} = (Finset.univ.filter p).card :=
    (Nat.card_eq_fintype_card (α := {x : α // p x})).trans
      (Fintype.card_ofFinset (p := {x | p x}) (Finset.univ.filter p) (fun x => by simp))
  rw [h1, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : p x
  · rw [indicator_eq_one h, if_pos h]
  · rw [indicator_eq_zero h, if_neg h]


/-- `Nat.card` of a subtype is the cardinality of the corresponding filtered finite set. -/
theorem natCard_subtype_eq_filter_card {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {x : α // p x} = (Finset.univ.filter p).card :=
  (Nat.card_eq_fintype_card (α := {x : α // p x})).trans
    (Fintype.card_ofFinset (p := {x | p x}) (Finset.univ.filter p) (fun x => by simp))

/-- `{x : {y // p y} // q x.1} ≃ {x // p x ∧ q x}`. -/
def subtypeSubtypeEquiv {α : Type*} (p q : α → Prop) :
    {x : {x : α // p x} // q x.1} ≃ {x : α // p x ∧ q x} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := rfl
  right_inv x := rfl

/-- `Set.ncard` of a set is the `Nat.card` of the corresponding subtype. -/
theorem set_ncard_eq_natCard {α : Type*} (s : Set α) [Fintype s] :
    s.ncard = Nat.card s :=
  (Set.ncard_eq_toFinset_card' s).trans
    ((Set.toFinset_card s).trans (Nat.card_eq_fintype_card).symm)

end Work.L2F.Count
