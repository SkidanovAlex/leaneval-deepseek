import Mathlib
import Submission.Work.DSG4a.Data
import Submission.Work.DSG4a.FreePres
import Submission.Work.DSG4a.exists_present_modelModule

namespace Work.DSG4a

open CategoryTheory
open Module
universe u
-- `IsFreeModel` (Submission/Work/DSG4a/Data.lean) gives `Module.Finite A (P.X j)` and
-- `Module.Free A (P.X j)` for every `j`, hence bases `b₀ : P.X 0 ≃ₗ (Fin m → A)`,
-- `b₁ : P.X (-1) ≃ₗ (Fin n → A)`; then `Work.DSG4a.exists_present_modelModule P b₀ b₁` gives
-- `present D ≃ₗ Criterion.modelModule P`, which is the `φ` field of
-- `Work.DSG4a.FreePres A (Criterion.modelModule P)`.
-- Proof hint (from review): `Module.finBasis` needs `StrongRankCondition A`, which is NOT
-- available without `[Nontrivial A]`; use instead
-- `(Module.Free.chooseBasis A (P.X 0)).reindex (Fintype.equivFin _)` together with
-- `Module.Free.ChooseBasisIndex.fintype` (needs only `Module.Finite`), then `Basis.equivFun`.
theorem freePres_modelModule {A : Type u} [CommRing A] {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (h : Work.DSG4a.IsFreeModel A P) :
    Nonempty (Work.DSG4a.FreePres A (Work.DSG4a.Criterion.modelModule P)) := by
  obtain ⟨hfin, hfree, -⟩ := h
  have : Module.Finite A (P.X 0) := hfin 0
  have : Module.Finite A (P.X (-1)) := hfin (-1)
  have : Module.Free A (P.X 0) := hfree 0
  have : Module.Free A (P.X (-1)) := hfree (-1)
  let b0 : P.X 0 ≃ₗ[A] (Fin (Fintype.card (Module.Free.ChooseBasisIndex A (P.X 0))) → A) :=
    ((Module.Free.chooseBasis A (P.X 0)).reindex (Fintype.equivFin _)).equivFun
  let b1 : P.X (-1) ≃ₗ[A]
      (Fin (Fintype.card (Module.Free.ChooseBasisIndex A (P.X (-1)))) → A) :=
    ((Module.Free.chooseBasis A (P.X (-1))).reindex (Fintype.equivFin _)).equivFun
  obtain ⟨Φ, _⟩ := Work.DSG4a.exists_present_modelModule P b0 b1
  exact ⟨
    { m := Fintype.card (Module.Free.ChooseBasisIndex A (P.X 0))
      n := Fintype.card (Module.Free.ChooseBasisIndex A (P.X (-1)))
      D := fun i j => b0 ((P.d (-1) 0).hom (b1.symm (Pi.single j 1))) i
      φ := Φ }⟩

end Work.DSG4a
