import Mathlib
import Submission.NK.HassePrinciple.MuColimAdd

universe u

namespace NK.HassePrinciple

theorem muColimNeg_add_cancel {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K')) (x : NK.HassePrinciple.MuColim p V) :
    NK.HassePrinciple.muJoinAdd p V (NK.HassePrinciple.muColimNeg p V x) x =
      NK.HassePrinciple.muColimZero p V := by
  obtain ⟨L, a, rfl⟩ := (muLevelSystem p V).ofLevel_surjective x
  rw [muColimNeg_ofLevel, muJoinAdd_ofLevel_self, neg_add_cancel]
  exact muColimZero_ofLevel p V L

end NK.HassePrinciple
