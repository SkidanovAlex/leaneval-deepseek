import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

/-- The fibre of a definable set at a point is definable over the old parameters together with that
point: if `G ⊆ M²` is `A`-definable then the set of `y` with `(y, u) ∈ G` is `(A ∪ {u})`-definable.

This is a relabelling of the defining formula: the second variable is replaced by a parameter slot
carrying `u`. -/
theorem fibre_definable {M : Type} [WilkiesDesign.CG.LRc.Structure M] {A : Set M}
    {G : Set (Fin 2 → M)} (hG : A.Definable WilkiesDesign.CG.LRc G) {u : M} :
    (A ∪ {u}).Definable WilkiesDesign.CG.LRc
      {v : Fin 1 → M | (fun i : Fin 2 => if i = 0 then v 0 else u) ∈ G} := by
  classical
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hG
  -- The reindexing map: parameters from `A` stay parameters, the first variable stays the
  -- variable `v 0`, and the second variable is replaced by the new parameter `u`.
  let f : (↥A ⊕ Fin 2) → (↥(A ∪ {u}) ⊕ Fin 1) :=
    Sum.elim (fun a => Sum.inl ⟨(a : M), Or.inl a.2⟩)
      (fun i => if i = 0 then Sum.inr 0 else Sum.inl ⟨u, Or.inr rfl⟩)
  refine Set.definable_iff_exists_formula_sum.mpr ⟨φ.relabel f, ?_⟩
  have key : ∀ v : Fin 1 → M,
      (Sum.elim (Subtype.val : ↥(A ∪ {u}) → M) v) ∘ f
        = Sum.elim (Subtype.val : ↥A → M) (fun i : Fin 2 => if i = 0 then v 0 else u) := by
    intro v
    funext y
    rcases y with a | i
    · simp only [f, Sum.elim_inl, Function.comp_apply]
    · fin_cases i <;> simp [f]
  apply Set.ext
  intro v
  simp only [Set.mem_ofPred_eq, Formula.realize_relabel]
  rw [key v, hφ]
  simp

end Work.WilC2
