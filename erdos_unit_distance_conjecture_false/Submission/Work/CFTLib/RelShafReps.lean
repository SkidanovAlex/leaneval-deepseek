import Mathlib
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.classGroupMulEquiv_trans
import Submission.Work.CFTLib.clEquiv_one
import Submission.Work.CFTLib.NKIdeles

/-!
# The Galois modules of the relative Shafarevich bound

`Work.CFTLib.clInvariantChar` is the space of `G`-invariant characters of `Cl(𝓞 K)`,
`G = Gal(K/F)`.  This file installs

* the Galois module structure on `Cl(𝓞 K)` (`clRep`),
* the Galois module structure on `𝒪_Kˣ` (`oUnitsRep`),
* the unit idèles `J_K = ∏_w 𝒪_{K_w}ˣ` (`jRep`, re-exported from `NK.GlobalCFTdeep`),

together with the functoriality lemmas for `clEquiv` that make `clRep` a genuine
`ℤ[G]`-module.  These are the coefficients of the exact sequence
`1 → 𝒪_Kˣ → J_K → C_K → Cl(𝓞 K) → 1` of `G`-modules.
-/

open scoped Classical
open NumberField CategoryTheory

noncomputable section

namespace Work.CFTLib

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-! ## Functoriality of the Galois action on `𝓞 K` -/

lemma mapAlgEquiv_mul (g h : K ≃ₐ[F] K) :
    NumberField.RingOfIntegers.mapAlgEquiv (L := K) (g * h) =
      (NumberField.RingOfIntegers.mapAlgEquiv (L := K) h).trans
        (NumberField.RingOfIntegers.mapAlgEquiv (L := K) g) := by
  ext x; simp only [AlgEquiv.trans_apply]; rfl

lemma mapAlgEquiv_one :
    NumberField.RingOfIntegers.mapAlgEquiv (L := K) (1 : K ≃ₐ[F] K) = AlgEquiv.refl := by
  ext x; rfl

lemma mapAlgEquiv_toRingEquiv_trans (g h : K ≃ₐ[F] K) :
    ((NumberField.RingOfIntegers.mapAlgEquiv (L := K) h).trans
        (NumberField.RingOfIntegers.mapAlgEquiv (L := K) g)).toRingEquiv =
      (NumberField.RingOfIntegers.mapAlgEquiv (L := K) h).toRingEquiv.trans
        (NumberField.RingOfIntegers.mapAlgEquiv (L := K) g).toRingEquiv := rfl

/-- The action law for the canonical action on the class group. -/
lemma clEquiv_mul (g h : K ≃ₐ[F] K) (c : ClassGroup (𝓞 K)) :
    clEquiv F K (g * h) c = clEquiv F K g (clEquiv F K h c) := by
  show ClassGroup.mulEquiv ((NumberField.RingOfIntegers.mapAlgEquiv (L := K) (g*h)).toRingEquiv) c = _
  rw [mapAlgEquiv_mul, mapAlgEquiv_toRingEquiv_trans]
  rw [classGroupMulEquiv_trans]
  rfl

/-! ## `Cl(𝓞 K)` as a Galois module -/

noncomputable instance instMulDistribMulActionClassGroup :
    MulDistribMulAction (K ≃ₐ[F] K) (ClassGroup (𝓞 K)) where
  smul g c := clEquiv F K g c
  one_smul c := clEquiv_one c
  mul_smul g h c := clEquiv_mul F K g h c
  smul_mul g c c' := map_mul (clEquiv F K g) c c'
  smul_one g := map_one (clEquiv F K g)

/-- `Cl(𝓞 K)` as a `ℤ[Gal(K/F)]`-module. -/
noncomputable def clRep : Rep ℤ (K ≃ₐ[F] K) :=
  Rep.ofMulDistribMulAction (K ≃ₐ[F] K) (ClassGroup (𝓞 K))

@[simp] lemma clRep_rho (g : K ≃ₐ[F] K) (c : ClassGroup (𝓞 K)) :
    (clRep F K).ρ g (Additive.ofMul c) = Additive.ofMul (clEquiv F K g c) := rfl

/-! ## `𝒪_Kˣ` as a Galois module -/

/-- `NumberField.RingOfIntegers.mapAlgEquiv` as a monoid homomorphism. -/
def mapAlgEquivMonoidHom : (K ≃ₐ[F] K) →* (𝓞 K ≃ₐ[𝓞 F] 𝓞 K) where
  toFun g := NumberField.RingOfIntegers.mapAlgEquiv (L := K) g
  map_one' := mapAlgEquiv_one F K
  map_mul' g h := by
    rw [mapAlgEquiv_mul]
    ext x; rfl

noncomputable instance instMulDistribMulActionOUnits :
    MulDistribMulAction (K ≃ₐ[F] K) (𝓞 K)ˣ :=
  MulDistribMulAction.compHom ((𝓞 K)ˣ) (mapAlgEquivMonoidHom F K)

/-- `𝒪_Kˣ` as a `ℤ[Gal(K/F)]`-module. -/
noncomputable def oUnitsRep : Rep ℤ (K ≃ₐ[F] K) :=
  Rep.ofDistribMulAction ℤ (K ≃ₐ[F] K) (Additive (𝓞 K)ˣ)

/-! ## The unit idèles -/

/-- The unit idèles `J_K = ∏_w 𝒪_{K_w}ˣ` (= `Idele.integralIdeles K`), as a `ℤ[Gal(K/F)]`-module. -/
noncomputable def jRep : Rep ℤ (K ≃ₐ[F] K) :=
  NK.GlobalCFTdeep.localUnitIdelesRep (K := F) (L := K)

end Work.CFTLib
