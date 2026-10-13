import Mathlib
import Submission.Work.WilC5.ExtSatAux

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5
open FirstOrder Language
open scoped FirstOrder

theorem elemOn_range_of_helem {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N] {A : L.Substructure M} {σ : L.Embedding A N}
    (helem : ∀ (φ : L.Formula (A ⊕ Fin 0)),
      (φ.Realize (Sum.elim Subtype.val (fun i : Fin 0 => i.elim0)) ↔
        φ.Realize (Sum.elim (fun a : A => (σ a : N)) (fun i : Fin 0 => i.elim0)))) :
    @ElemOn L M N _ _ (Set.range σ)
      (fun y : Set.range σ => (Classical.choose (show ∃ a : A, σ a = (y : N) from y.2) : A)) := by
  intro φ
  have hspec : ∀ y : Set.range σ,
      σ (Classical.choose (show ∃ a : A, σ a = (y : N) from y.2)) = (y : N) :=
    fun y => Classical.choose_spec (show ∃ a : A, σ a = (y : N) from y.2)
  have h := helem (φ.relabel (fun y : Set.range σ =>
      Sum.inl (Classical.choose (show ∃ a : A, σ a = (y : N) from y.2))))
  simpa [Formula.realize_relabel, Function.comp_def, hspec] using h.symm

end Work.WilC5
