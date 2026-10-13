import Submission.Work.DSMap.Map
import Submission.Work.DSG4b.Defs
import Submission.Work.DSG4b.Reduction
import Submission.Work.DSG4b.gonflement_complete_regular_local

/-!
# DSG4b — gonflement: the frozen statement, proved

`DSMap.area_G4b_gonflement_proved` is `DSMap.area_G4b_gonflement`.

The mathematical content (EGA 0_III 10.3.1; Česnavičius, *Purity for the Brauer group*, 5.1) is
delegated to `Work.DSG4b.gonflement_complete_regular_local`, the case where the regular ring is
local (and completed).  The passage from a general regular ring `A` and a maximal ideal `m` to the
local case is `Work.DSG4b.isGonflement_of_localization`: localisation at `m` is flat and its
maximal ideal lies over `m`, so precomposing a gonflement of `Localization.AtPrime m` with
`algebraMap A _` gives a gonflement of `A` at `m`.

The alternative route through `Work.DSG4b.exists_regularLocal_algClosed_residue` (residue field
enlargement *without* completeness) plus `m`-adic completion is recorded in
`Submission/Work/DSG4b/AssemblyAux.lean`.
-/

namespace DSMap

open IsLocalRing

universe u

/-- **G4b** gonflement: `A_m → ` complete regular local with algebraically closed residue field,
flat over `A`, lying over `m`. -/
theorem area_G4b_gonflement_proved.{a} (A : Type a) [CommRing A] [IsRegularRing A] (m : Ideal A)
    (hm : m.IsMaximal) :
    ∃ (A' : Type a) (_ : CommRing A') (_ : IsRegularLocalRing A') (ψ : A →+* A'),
      IsAdicComplete (maximalIdeal A') A' ∧ IsAlgClosed (ResidueField A') ∧ ψ.Flat ∧
      (maximalIdeal A').comap ψ = m := by
  haveI : m.IsPrime := hm.isPrime
  haveI : IsRegularLocalRing (Localization.AtPrime m) := inferInstance
  obtain ⟨A', hComm, hReg, ψ, hadic, halg, hflat, hcomap⟩ :=
    Work.DSG4b.gonflement_complete_regular_local (Localization.AtPrime m)
  -- localisation at `m` is flat, and its maximal ideal lies over `m`
  have hloc : RingHom.Flat (algebraMap A (Localization.AtPrime m)) := by
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat (Localization.AtPrime m) m.primeCompl
  refine ⟨A', hComm, hReg, ψ.comp (algebraMap A (Localization.AtPrime m)),
    hadic, halg, RingHom.Flat.comp hloc hflat, ?_⟩
  rw [← Ideal.comap_comap, hcomap]
  exact Localization.AtPrime.under_maximalIdeal

/-- The proved theorem has the frozen interface's *type*, definitionally. -/
example : type_of% @DSMap.area_G4b_gonflement_proved.{u} =
    type_of% @DSMap.area_G4b_gonflement.{u} := rfl

/-- ... equivalently: the proved theorem inhabits the frozen statement verbatim. -/
example : ∀ (A : Type u) [CommRing A] [IsRegularRing A] (m : Ideal A) (hm : m.IsMaximal),
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsRegularLocalRing A') (ψ : A →+* A'),
      IsAdicComplete (maximalIdeal A') A' ∧ IsAlgClosed (ResidueField A') ∧ ψ.Flat ∧
      (maximalIdeal A').comap ψ = m :=
  DSMap.area_G4b_gonflement_proved

end DSMap

