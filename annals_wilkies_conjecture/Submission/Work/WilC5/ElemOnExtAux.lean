/-
  WilC5 — auxiliary material for the extension step `elemOn_extend`.

  Given a partial elementary map `τ : B → M` (`B ⊆ N`) and a point `m ∈ M` outside the range of
  `τ`, the extension step adjoins a point `n ∈ N \ B` with `τ' n = m`.  The proof compares the
  complete type of `m` over `B` (as a set of *bounded* formulas `L.BoundedFormula B 1`, i.e.
  formulas with parameters in `B` and one free variable) with the type of a realization `n` in a
  `κ`-saturated `N`.

  This file collects the small combinatorial devices used to pass between the two presentations of
  the type:

  * `insertSum B n : ↥(insert n B) → B ⊕ Fin 1` — the identification of the adjoined point `n`
    with the free variable slot of a one-variable type;
  * `extendFun_eq_comp` and `subtypeVal_eq_comp` — the compatibility of `insertSum` with
    `PEM.extendFun` and with the inclusion of `insert n B` into `N`.
-/
import Mathlib
import Submission.Work.WilC5.ExtSatAux

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language

/-- `Formula.Realize` in the `BoundedFormula` presentation used by `IsSaturated`: a formula with
no free variables is realized by an assignment `v` iff it is realized by the bounded-formula
semantics at `v` and the (unique) empty tuple. -/
theorem formulaRealize_iff_bounded {L : FirstOrder.Language} {M : Type} [L.Structure M] {α : Type}
    (φ : L.Formula α) (v : α → M) :
    φ.Realize v ↔ @BoundedFormula.Realize L M _ α 0 φ v (fun i : Fin 0 => i.elim0) := by
  unfold Formula.Realize
  exact iff_of_eq (congrArg (fun u : Fin 0 → M => @BoundedFormula.Realize L M _ α 0 φ v u)
    (show (default : Fin 0 → M) = (fun i : Fin 0 => i.elim0) from by
      funext i
      exact i.elim0))

/-- The identification of `↥(insert n B)` with `B ⊕ Fin 1`: an element of `B` is sent to
`Sum.inl` and the adjoined point `n` to the single free variable `Sum.inr 0`.  When `n ∉ B` this
is a bijection. -/
def insertSum {N : Type} (B : Set N) (n : N) : ↥(insert n B) → B ⊕ Fin 1 :=
  fun a => if h : (a : N) ∈ B then Sum.inl ⟨a, h⟩ else Sum.inr 0

@[simp]
theorem insertSum_apply_of_mem {N : Type} {B : Set N} {n : N} (a : ↥(insert n B))
    (h : (a : N) ∈ B) : insertSum B n a = Sum.inl ⟨(a : N), h⟩ := dite_eq_left h

@[simp]
theorem insertSum_apply_of_not_mem {N : Type} {B : Set N} {n : N} (a : ↥(insert n B))
    (h : (a : N) ∉ B) : insertSum B n a = Sum.inr 0 := dite_eq_right h

/-- An element of `insert n B` which is not in `B` is the adjoined point. -/
theorem eq_of_mem_insert_of_not_mem {N : Type} {B : Set N} {n : N} {a : ↥(insert n B)}
    (h : (a : N) ∉ B) : (a : N) = n :=
  (Set.mem_insert_iff.mp a.2).resolve_right h

/-- `insertSum` is compatible with the extension of a partial map by the pair `n ↦ m`. -/
theorem extendFun_eq_comp {M N : Type} {B : Set N} {n : N} (τ : B → M) (m : M) :
    (Sum.elim τ (fun _ : Fin 1 => m)) ∘ insertSum B n = PEM.extendFun τ n m := by
  funext a
  rw [Function.comp_apply]
  by_cases ha : (a : N) ∈ B
  · rw [insertSum_apply_of_mem a ha, Sum.elim_inl, PEM.extendFun_apply_of_mem]
  · rw [insertSum_apply_of_not_mem a ha, Sum.elim_inr,
      PEM.extendFun_apply_of_not_mem (τ := τ) (n := n) (m := m) a ha]

/-- `insertSum` is compatible with the inclusion of `insert n B` into `N`. -/
theorem subtypeVal_eq_comp {N : Type} {B : Set N} {n : N} :
    (Sum.elim (Subtype.val : B → N) (fun _ : Fin 1 => n)) ∘ insertSum B n =
      (Subtype.val : ↥(insert n B) → N) := by
  funext a
  rw [Function.comp_apply]
  by_cases ha : (a : N) ∈ B
  · rw [insertSum_apply_of_mem a ha, Sum.elim_inl]
  · rw [insertSum_apply_of_not_mem a ha, Sum.elim_inr]
    exact (eq_of_mem_insert_of_not_mem ha).symm

end Work.WilC5
