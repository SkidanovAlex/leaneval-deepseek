import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Port.PSL2Model
import Submission.Work.Models.Abstract.inf_conj_w

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ZassenhausPSL2.Model

theorem psl2_isSplitRankOne (n : ℕ) (hn : 2 ≤ n) :
    Submission.Blueprint.IsSplitRankOne (Submission.PSL2.pSL2BenderPair n hn).B
      (Submission.PSL2.pSL2BenderPair n hn).U (Submission.PSL2.pSL2BenderPair n hn).w := by
  classical
  set P := Submission.PSL2.pSL2BenderPair n hn with hP
  -- The two-point stabiliser of `B` and `w` is the torus `T = B ⊓ B^w`.
  have hD : Submission.Blueprint.twoPoint P.B P.w = P.T := Work.Models.Abstract.inf_conj_w P
  -- The Weyl element is an involution, and it is not in `B`.
  have hww : P.w * P.w = 1 := Submission.PSL2.weylPSL_mul_self
  have hwne : P.w ≠ 1 := by
    intro h
    exact P.hwB (by rw [h]; exact P.B.one_mem)
  have hinvol : orderOf P.w = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by simpa [pow_two] using hww) hwne
  exact ⟨P.hSemb, P.isMultiplyPretransitive_two, hinvol, P.hwB, P.U_le_B,
    le_of_eq P.normalizer_U.symm, by rw [hD]; exact P.hUT, by rw [hD]; exact P.hB.symm⟩

end Work.ZassenhausPSL2.Model
