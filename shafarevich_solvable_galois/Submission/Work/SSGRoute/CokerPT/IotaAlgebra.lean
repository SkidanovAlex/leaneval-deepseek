import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.g1plus_iota

open CategoryTheory
open SSGRoute.PTExt

namespace Work.SSGRoute.PT

/-- **`PT.iotaLift` is additive.**  The chosen orbit-supported idèle lift of a local `H²`-class is
characterised by its localisation and its vanishing off the orbit (`PT.iotaLift_spec`), and both
properties are additive (`SSGRoute.PTExt.extLoc_add`), so the sum satisfies the characterisation of
the sum and `PT.eq_iotaLift_of_spec` applies. -/
theorem iotaLift_add {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L)
    (z z' : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := L) r) 2) :
    iotaLift (k := k) (L := L) r (z + z') =
      iotaLift (k := k) (L := L) r z + iotaLift (k := k) (L := L) r z' := by
  refine (eq_iotaLift_of_spec (k := k) (L := L) r (z + z') _ ?_ ?_).symm
  · rw [SSGRoute.PTExt.extLoc_add k L r,
      (iotaLift_spec (k := k) (L := L) r z).1,
      (iotaLift_spec (k := k) (L := L) r z').1]
    rfl
  · intro v hv
    rw [SSGRoute.PTExt.extLoc_add k L v,
      (iotaLift_spec (k := k) (L := L) r z).2 v hv,
      (iotaLift_spec (k := k) (L := L) r z').2 v hv, add_zero]

/-- **`PT.iotaLift` kills the zero class** (the zero class is orbit-supported, so the uniqueness
characterisation pins the chosen lift). -/
theorem iotaLift_zero {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (r : NK.GlobalCFT.Place L) :
    iotaLift (k := k) (L := L) r
        (0 : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := L) r) 2) = 0 := by
  refine (eq_iotaLift_of_spec (k := k) (L := L) r 0 0 ?_ ?_).symm
  · rw [SSGRoute.PTExt.extLoc_zero k L r]
    rfl
  · intro v hv
    rw [SSGRoute.PTExt.extLoc_zero k L v]

/-- **The orbit-placement map `ι_w` is additive** (clause (1) of `G1⁺` consumes exactly this). -/
theorem iota_add {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L)
    (z z' : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := L) r) 2) :
    iota (k := k) (L := L) r (z + z') =
      iota (k := k) (L := L) r z + iota (k := k) (L := L) r z' := by
  show SSGRoute.PTExt.extToClasses (k := k) (K := L)
      (iotaLift (k := k) (L := L) r (z + z')) =
    SSGRoute.PTExt.extToClasses (k := k) (K := L) (iotaLift (k := k) (L := L) r z) +
      SSGRoute.PTExt.extToClasses (k := k) (K := L) (iotaLift (k := k) (L := L) r z')
  rw [iotaLift_add, SSGRoute.PTExt.extToClasses_add]

/-- **The orbit-placement map `ι_w` kills the zero class.** -/
theorem iota_zero {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (r : NK.GlobalCFT.Place L) :
    iota (k := k) (L := L) r
        (0 : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := L) r) 2) = 0 := by
  show SSGRoute.PTExt.extToClasses (k := k) (K := L)
      (iotaLift (k := k) (L := L) r 0) = 0
  rw [iotaLift_zero, SSGRoute.PTExt.extToClasses_zero]

end Work.SSGRoute.PT

/-! ## Axiom audit -/

#print axioms Work.SSGRoute.PT.iotaLift_add
#print axioms Work.SSGRoute.PT.iotaLift_zero
#print axioms Work.SSGRoute.PT.iota_add
#print axioms Work.SSGRoute.PT.iota_zero
