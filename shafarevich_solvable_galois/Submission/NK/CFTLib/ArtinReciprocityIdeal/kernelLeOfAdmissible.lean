import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.exists_admissible
import Submission.NK.CFTLib.ArtinReciprocityIdeal.CyclotomicSubextension
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexPrincipalRaySupNormRayLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.kernelLeOfAdmissibleViaArtinLemma
import Submission.NK.CFTLib.ARL.auxField_exists_B
import Submission.NK.CFTLib.ARL.kernelLe_of_auxField_B
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ArtinReciprocityIdeal

theorem kernelLeOfAdmissible (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))]
    [IsMulCommutative (Gal(L/K))] (m : ℕ) (hm : 0 < m)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : Gal(L/K) => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
  -- Lang's Theorem 2 for cyclic `L/K`, via Artin's lemma and the per-prime transfer.
  NK.CFTLib.ArtinReciprocityIdeal.kernelLeOfAdmissibleViaArtinLemma K L m hm hadm hram

end NK.CFTLib.ArtinReciprocityIdeal
