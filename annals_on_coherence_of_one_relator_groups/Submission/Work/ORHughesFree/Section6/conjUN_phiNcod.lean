import Mathlib
import Submission.Work.Section6.StepA
import Submission.Work.ORHughesFree.Section6.ConjKN
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecompAux
import Submission.Work.ORHughesFree.Section6.conjRingEquiv_phiN

set_option linter.style.haveILetI false

namespace Work.ORHughesFree.Section6

theorem conjUN_phiNcod {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    [StarRing U] [Work.ORHughesFree.IsStarRegular U]
    (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H) (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    (hstar : star ((φ.comp (Work.ORHughesFree.inducedMapRing (K := K) H))
        (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (Work.ORHughesFree.inducedMapRing (K := K) H))
        (MonoidAlgebra.single t⁻¹ (1 : K))) :
    letI := Work.ORHughesFree.Section6.conjAction (K := K) htN
    ∀ b : MonoidAlgebra K N,
      Work.Section6.conjUN φ H N hN t hstar (Work.Section6.phiNcod φ H N b) =
        Work.Section6.phiNcod φ H N ((Multiplicative.ofAdd (1 : ℤ)) • b) := by
  letI := Work.ORHughesFree.Section6.conjAction (K := K) htN
  haveI := Work.ORHughesFree.Section6.conjAction_smulCommClass (K := K) htN
  intro b
  apply Subtype.ext
  rw [Work.Section6.conjUN_apply, Work.Section6.phiNcod_apply, Work.Section6.phiNcod_apply,
    Work.Section6.uUnit_val, Work.Section6.uUnit_inv_val]
  exact Work.Section6.conj_uUnit_phiN_key (K := K) htN
    (Work.ORHughesFree.Section6.conjAction_hact (K := K) htN) φ b

end Work.ORHughesFree.Section6
