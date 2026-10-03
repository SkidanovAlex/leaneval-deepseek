import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.Magnus
import Submission.Work.ORLyndon.foxD_pow

namespace Work.ORLyndon

/-- The Fox derivative vector of the relator `r = u ^ l` is the norm element of `u` times the
Fox derivative vector of the root `u`, transported to `K[⟨X | r⟩]`. -/
theorem relatorVec_t {X : Type*} [DecidableEq X] {K : Type*} [Field K] {r u : FreeGroup X}
    {l : ℕ} (h : Work.ORLyndon.LyndonIdentity K X r u l) (t : X) :
    Work.ORLyndon.relatorVec K r t =
      Work.ORLyndon.normElem K l (Work.ORLyndon.presentRho r u) *
        ((Work.ORLyndon.presentAlg K r) (Work.ORLyndon.foxD (K := K) t u)) := by
  have hmap : (presentAlg K r) (∑ i ∈ Finset.range l, ((MonoidAlgebra.of K (FreeGroup X)) u) ^ i) =
      normElem K l (presentRho r u) := by
    rw [normElem, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_pow, presentAlg_of])
  rw [relatorVec_apply, show foxD (K := K) t r = foxD (K := K) t (u ^ l) from by rw [h.hpow],
    foxD_pow, map_mul, hmap]

end Work.ORLyndon
