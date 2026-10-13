import Mathlib
import Submission.Work.WilC5.ElemOnExtendAux

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5
open FirstOrder Language

theorem elemOn_insert_of_type {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N] {B : Set N} {τ : B → M} {m : M} {x : Fin 1 → N}
    (hx : ∀ ψ : L.Formula (B ⊕ Fin 1),
      ψ.Realize (Sum.elim τ (fun _ : Fin 1 => m)) ↔
        ψ.Realize (Sum.elim (Subtype.val : B → N) x)) :
    @ElemOn L M N _ _ (insert (x 0) B) (PEM.extendFun τ (x 0) m) := by
  intro φ
  set g : ↥(insert (x 0) B) → B ⊕ Fin 1 :=
    fun y => if h : (y : N) ∈ B then Sum.inl ⟨y.1, h⟩ else Sum.inr 0 with hg
  have hg_inl : ∀ (y : ↥(insert (x 0) B)) (h : (y : N) ∈ B),
      g y = Sum.inl (⟨y.1, h⟩ : B) := by
    intro y h; show (if h' : (y : N) ∈ B then Sum.inl (⟨y.1, h'⟩ : B) else Sum.inr 0) = _
    split_ifs <;> rfl
  have hg_inr : ∀ y : ↥(insert (x 0) B), (y : N) ∉ B → g y = Sum.inr 0 := by
    intro y h; show (if h' : (y : N) ∈ B then Sum.inl (⟨y.1, h'⟩ : B) else Sum.inr 0) = _
    split_ifs <;> rfl
  have ha1 : (Sum.elim (Subtype.val : B → N) x) ∘ g = (Subtype.val : ↥(insert (x 0) B) → N) := by
    funext y
    by_cases h : (y : N) ∈ B
    · rw [Function.comp_apply, hg_inl y h]; simp only [Sum.elim_inl]
    · rw [Function.comp_apply, hg_inr y h]; simp only [Sum.elim_inr]
      rcases Set.mem_insert_iff.mp y.2 with h' | h'
      · exact h'.symm
      · exact absurd h' h
  have ha2 : (Sum.elim τ (fun _ : Fin 1 => m)) ∘ g = PEM.extendFun τ (x 0) m := by
    funext y
    by_cases h : (y : N) ∈ B
    · rw [Function.comp_apply, hg_inl y h]; simp only [Sum.elim_inl]
      exact (PEM.extendFun_apply_of_mem τ y h).symm
    · rw [Function.comp_apply, hg_inr y h]; simp only [Sum.elim_inr]
      exact (PEM.extendFun_apply_of_not_mem τ y h).symm
  have hφ1 : (φ.relabel g).Realize (Sum.elim (Subtype.val : B → N) x) ↔
      φ.Realize (Subtype.val : ↥(insert (x 0) B) → N) := by
    rw [Formula.realize_relabel]
    exact iff_of_eq (congrArg (fun w' : ↥(insert (x 0) B) → N => φ.Realize w') ha1)
  have hφ2 : (φ.relabel g).Realize (Sum.elim τ (fun _ : Fin 1 => m)) ↔
      φ.Realize (PEM.extendFun τ (x 0) m) := by
    rw [Formula.realize_relabel]
    exact iff_of_eq (congrArg (fun w' : ↥(insert (x 0) B) → M => φ.Realize w') ha2)
  exact hφ1.symm.trans ((hx (φ.relabel g)).symm.trans hφ2)

end Work.WilC5
