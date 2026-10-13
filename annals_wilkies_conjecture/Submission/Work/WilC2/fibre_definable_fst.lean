import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.fibre_definable

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

/-- The fibre of a definable set in its **first** coordinate is definable over the old parameters
together with the point: if `G ⊆ M²` is `A`-definable then the set of `x` with `(u, x) ∈ G` is
`(A ∪ {u})`-definable.

This is the mirror image of `Work.WilC2.fibre_definable` (which fixes the second coordinate) and is
again just a relabelling of the defining formula. -/
theorem fibre_definable_fst {M : Type} [WilkiesDesign.CG.LRc.Structure M] {A : Set M}
    {G : Set (Fin 2 → M)} (hG : A.Definable WilkiesDesign.CG.LRc G) {u : M} :
    (A ∪ {u}).Definable WilkiesDesign.CG.LRc
      {v : Fin 1 → M | (fun i : Fin 2 => if i = 0 then u else v 0) ∈ G} := by
  classical
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hG
  -- The reindexing map: parameters from `A` stay parameters, the second variable stays the
  -- variable `v 0`, and the first variable is replaced by the new parameter `u`.
  let f : (↥A ⊕ Fin 2) → (↥(A ∪ {u}) ⊕ Fin 1) :=
    Sum.elim (fun a => Sum.inl ⟨(a : M), Or.inl a.2⟩)
      (fun i => if i = 0 then Sum.inl ⟨u, Or.inr rfl⟩ else Sum.inr 0)
  refine Set.definable_iff_exists_formula_sum.mpr ⟨φ.relabel f, ?_⟩
  have key : ∀ v : Fin 1 → M,
      (Sum.elim (Subtype.val : ↥(A ∪ {u}) → M) v) ∘ f
        = Sum.elim (Subtype.val : ↥A → M) (fun i : Fin 2 => if i = 0 then u else v 0) := by
    intro v
    funext y
    rcases y with a | i
    · simp only [f, Sum.elim_inl, Function.comp_apply]
    · fin_cases i <;> simp [f]
  apply Set.ext
  intro v
  simp only [Set.mem_setOf_eq, Formula.realize_relabel]
  rw [key v, hφ]
  simp

end Work.WilC2
