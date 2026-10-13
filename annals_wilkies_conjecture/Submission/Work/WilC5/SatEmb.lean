/-
  WilC5 — the canonical `L[[M]]`-structure on the term hull.

  The term hull of a model of the total theory models the elementary diagram of `M` when each
  constant `m` is interpreted by the value of the constant `Sum.inl m` of the total language.
-/
import Mathlib
import Submission.Work.WilC5.SatHull
import Submission.Work.WilC5.SatStrong

open FirstOrder Language
open scoped FirstOrder

attribute [local implicit_reducible] FirstOrder.Language.withConstants Work.WilC5.SatC

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

variable (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M] (κ : Cardinal.{0})

/-- The carrier of a chosen model of the total theory. -/
noncomputable def SatNC (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M]
    (κ : Cardinal.{0}) (hM : Nonempty M) : Type :=
  (SatTotSat (L := L) (M := M) (κ := κ) hM).some.Carrier

/-- The structure on that carrier. -/
noncomputable def SatNstruc (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M]
    (κ : Cardinal.{0}) (hM : Nonempty M) :
    (SatLang L (SatCt L M κ)).Structure (SatNC L M κ hM) :=
  (SatTotSat (L := L) (M := M) (κ := κ) hM).some.struc

/-- The chosen model models the total theory. -/
theorem SatNmodel (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M]
    (κ : Cardinal.{0}) (hM : Nonempty M) :
    @Theory.Model (SatLang L (SatCt L M κ)) (SatNC L M κ hM) (SatNstruc L M κ hM)
      (SatTot L M κ) :=
  (SatTotSat (L := L) (M := M) (κ := κ) hM).some.is_model

/-- The canonical map from `M` into the term hull of the chosen model, sending `m` to the value of
the constant `Sum.inl m`. -/
noncomputable def SatEmbFun (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M]
    (κ : Cardinal.{0}) (hM : Nonempty M) :
    M → ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) :=
  fun m => ⟨@SatConVal L (SatCt L M κ) (SatNC L M κ hM) (SatNstruc L M κ hM) (Sum.inl m),
    letI : (SatLang L (SatCt L M κ)).Structure (SatNC L M κ hM) := SatNstruc L M κ hM
    letI : L.Structure (SatNC L M κ hM) := SatReduct L M κ (SatNC L M κ hM)
    @FirstOrder.Language.Substructure.subset_closure L (SatNC L M κ hM)
      (SatReduct L M κ (SatNC L M κ hM))
      (Set.range (fun c : SatCt L M κ =>
        @SatConVal L (SatCt L M κ) (SatNC L M κ hM) (SatNstruc L M κ hM) c))
      _ ⟨Sum.inl m, rfl⟩⟩

/-- The `L[[M]]`-structure on the hull in which each constant `m` is interpreted by the value of the
constant `Sum.inl m` of the total language, and whose `L`-part is the hull's structure. -/
noncomputable def SatEmbStruct (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M]
    (κ : Cardinal.{0}) (hM : Nonempty M) :
    (SatLang L M).Structure ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) :=
  letI : (SatLang L (SatCt L M κ)).Structure (SatNC L M κ hM) := SatNstruc L M κ hM
  letI : L.Structure (SatNC L M κ hM) := SatReduct L M κ (SatNC L M κ hM)
  letI : L.Structure ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) :=
    FirstOrder.Language.Substructure.inducedStructure
      (S := @SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM))
  letI : (FirstOrder.Language.constantsOn M).Structure
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) :=
    FirstOrder.Language.constantsOn.structure (SatEmbFun L M κ hM)
  FirstOrder.Language.sumStructure L (FirstOrder.Language.constantsOn M) _

end Work.WilC5
