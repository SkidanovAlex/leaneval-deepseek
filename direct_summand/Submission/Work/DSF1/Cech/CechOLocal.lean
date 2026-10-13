import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Cech.CechQo
import Submission.Work.DSF1.Cech.CechDefs
import Submission.Work.DSF1.Cech.exists_cechZ_lift

/-!
# The Čech complex of a family of opens of `Spec R`, and its localization at one open

This file collects the (ab)breviations used in the statement of
`cechAffineCover_quasiIso` and in the lemmas leading to it, so that later statements can
mention the basic objects without re-doing the (expensive) instance search for the
products in `ModuleCat R`.

* `cechO R U` is the Čech complex of the structure sheaf of `Spec R` (as a presheaf of
  `R`-modules) along the family of opens `U`, in `ℕ`-degrees;
* `cechOQ R U V` is the Čech complex of the presheaf `W ↦ 𝒪 (W ⊓ V)`;
* `locO R U V : cechO R U ⟶ cechOQ R U V` is induced by the restriction `W ↦ W ⊓ V`;
* `coaugO R U : R ⟶ cechO R U` is the coaugmentation `R ⟶ Č⁰`.

All of these are definitionally the corresponding objects of `DSMap`/`Work.DSF1.Cech`
(`DSMap.cech R (spec R) (𝟙 (spec R)) U = cechO R U`, and likewise).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Work.DSF1.Cech

universe u

/-- The Čech complex of the structure sheaf of `Spec R` along the family of opens `U`,
in `ℕ`-degrees.  This is `DSMap.cech R (Spec R) (𝟙) U`. -/
noncomputable abbrev cechO (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (cechComplexFunctor U).obj (specPresheaf R)

/-- The Čech complex of the presheaf `W ↦ 𝒪 (W ⊓ V)` along the family of opens `U`. -/
noncomputable abbrev cechOQ (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens)
    (V : (spec R).Opens) : CochainComplex (ModuleCat.{u} R) ℕ :=
  (cechComplexFunctor U).obj (Qo (specPresheaf R) V)

/-- The comparison map `cechO R U ⟶ cechOQ R U V` induced by the restriction
`𝒪 (W) ⟶ 𝒪 (W ⊓ V)`. -/
noncomputable def locO (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens)
    (V : (spec R).Opens) : cechO R U ⟶ cechOQ R U V :=
  (cechComplexFunctor U).map (etaO (specPresheaf R) V)

/-- The coaugmentation `R ⟶ Č⁰` of the Čech complex of `U`.  This is
`DSMap.coaug0 R (Spec R) (𝟙 (Spec R)) U`. -/
noncomputable abbrev coaugO (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens) :
    ModuleCat.of R R ⟶ (cechO R U).X 0 :=
  DSMap.coaug0 R (spec R) (𝟙 (spec R)) U

/-- The coaugmentation as a chain map `R[0] ⟶ cechO R U` in `ℕ`-degrees. -/
noncomputable def coaugMapO (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens) :
    (CochainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R R) ⟶ cechO R U :=
  (CochainComplex.fromSingle₀Equiv (cechO R U) (ModuleCat.of R R)).symm
    ⟨coaugO R U, coaug0_cech_d R (spec R) (𝟙 (spec R)) U⟩

/-- The degree zero component of the coaugmentation chain map is the coaugmentation. -/
lemma coaugMapO_f_zero (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens) :
    (coaugMapO R U).f 0 = coaugO R U :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero (coaugO R U)
    (coaug0_cech_d R (spec R) (𝟙 (spec R)) U)

end Work.DSF1.Cech
