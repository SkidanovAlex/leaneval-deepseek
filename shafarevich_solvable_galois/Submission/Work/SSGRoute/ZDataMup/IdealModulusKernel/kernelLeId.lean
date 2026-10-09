import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.IdealModulusKernel.TransferId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lang's conductor theorem for an ideal modulus (the kernel of the ideal-theoretic Artin map)

For a finite cyclic (Galois) extension `L/K` of number fields and an ideal modulus `𝔪 ≠ ⊥` which is
admissible in Lang's sense (`IsAdmissibleId`) and contains every ramified prime
(`ContainsRamified`), every fractional ideal `A` of `K` coprime to `𝔪` whose Artin symbol is trivial
lies in `P(𝔪)·𝔑(𝔪)`.

The proof is the transfer argument, carried out in
`Submission/Work/SSGRoute/ZDataMup/IdealModulusKernel/TransferId.lean` as `kernelLeIdTransfer`:

* `MupAux.auxFieldHypId` — Artin's lemma at an ideal modulus (the auxiliary field `E`);
* `cyclotomicCellKernelLeId` (proved in `CyclotomicCellId.lean` from the clash-free
  `CycloPrincipalId` and the index theorem `IndexLeIdId`) — the cyclotomic cell `L𝔭E𝔭/E𝔭`;
* `MupAux.principalRayId_map_relNormUnit_le` and `normRayId_cell_descent` — the descents of the
  principal and norm rays along the relative norm `N_{E𝔭/K}`.

Every ingredient is proved outright and the theorem rests only on `propext`, `Classical.choice` and
`Quot.sound`.
-/

namespace Work.SSGRoute.ZDataMup.IdealModulusKernel

theorem kernelLeId {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissibleId (K := K) (L := L) 𝔪)
    (hram : NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪 A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 :=
  kernelLeIdTransfer (K := K) (L := L) hcomm 𝔪 h𝔪 hadm hram

end Work.SSGRoute.ZDataMup.IdealModulusKernel
