import Mathlib
import Submission.NK.CFTLib.ARLAlt.Setup
import Submission.NK.CFTLib.ARLAlt.CellAbelian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclotomic cell at an auxiliary field

Given a finite Galois extension `L/K` of number fields, a modulus `M` and an auxiliary field
`E ⊆ Ω = L(ζ_M)` with `E ⊔ ℚ(ζ_M) = Ω` (so that `Ω/E` is cyclotomic of level `M` and `E·L/E` is a
subextension of it), the kernel containment `ker ψ ⊆ P(m)·𝔑(m)` holds for the abelian (in fact
cyclic) extension `E·L/E` — this is the "cell" that Artin's transfer argument applies at the
auxiliary field.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.ARLAlt

/-- **The cyclotomic cell at the auxiliary field `E`.** -/
theorem cellAtAuxField (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M] (E : IntermediateField K (CyclotomicField M L))
    (hsup : (E.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
      ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
        Set (CyclotomicField M L))) = ⊤)
    [IsMulCommutative
      (Gal(↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) le_sup_left)/↥E))]
    (m : ℕ) (hm : 0 < m) (hM : M ∣ m)
    (hram : ∀ q : NK.Chebotarev.PrimeIdeal ↥E,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
        (L := ↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) le_sup_left)) q →
      (m : NumberField.RingOfIntegers ↥E) ∈ q.asIdeal) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := ↥E)
        (L := ↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) le_sup_left))
        (fun a b => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay ↥E m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay ↥E
            (↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) le_sup_left)) m := by
  haveI hcyc : IsCyclotomicExtension {M} ↥E (CyclotomicField M L) :=
    isCyclotomicExtension_of_sup_adjoin_zeta (K := K) (L := L) M E hsup
  haveI hgal : IsGalois ↥E (CyclotomicField M L) :=
    IsCyclotomicExtension.isGalois {M} ↥E (CyclotomicField M L)
  haveI hfin : FiniteDimensional ↥E (CyclotomicField M L) :=
    IsCyclotomicExtension.finiteDimensional {M} ↥E (CyclotomicField M L)
  haveI hgalC : IsGalois ↥E ↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) le_sup_left) :=
    isGalois_ofLe_sup (K := K) (L := L) M E
  exact cyclotomicCellKernelLe_abelian ↥E (CyclotomicField M L) M
    (ofLe E (E ⊔ LImage (K := K) (L := L) M) le_sup_left) m hm hM hram

end NK.CFTLib.ARLAlt
