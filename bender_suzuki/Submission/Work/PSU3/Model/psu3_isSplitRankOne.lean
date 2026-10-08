import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.Models.Port.BenderPairModels

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `PSU(3,2ⁿ)` is a split rank-one group

The Bender pair `Submission.PSU3.psu3BenderPair n hn` of `PSU(3,2ⁿ)` (built in
`Submission/Work/Models/Port/BenderPairModels.lean`) packages the data of a rank-one
`(B,N)`-pair of characteristic two: the Borel `B̄ = psu3B n`, its unipotent radical
`Ū = psu3U n`, a complement `T̄ = psu3T n` of `Ū` in `B̄`, and a Weyl element `w̄`.
Here we check that this is a `Submission.Blueprint.IsSplitRankOne` datum, i.e. that
`H = B̄`, `Q = Ū`, `t = w̄` satisfy Peterfalvi's set-up after Theorems A and D
(II, Ch. VII §1): `H` strongly embedded, `G` 2-transitive on `G ⧸ H`, `H = Q ⋊ D` with
`Q ⊴ H` regular on the other points, where `D = H ⊓ H^t = twoPoint H t`.

The two structural ingredients are
* `w̄² = 1` (the Weyl element of `SU(3,2ⁿ)` is an involution, `suSgM_mul_self`), and
* `B̄ ⊓ B̄^{w̄} = T̄` (`psu3B_inf_map_conj_psu3W_eq_psu3T`), i.e. `twoPoint B̄ w̄ = T̄`,
  which turns `B̄ = Ū ⊔ T̄` and `Ū ⊓ T̄ = ⊥` into the split rank-one axioms.
-/

namespace Work.PSU3.Model

open Submission.Blueprint

/-- The Weyl element `w̄` of `PSU(3,2ⁿ)` is an involution. -/
lemma psu3Weyl_mul_self (n : ℕ) : Submission.PSU3.psu3Weyl n * Submission.PSU3.psu3Weyl n = 1 := by
  have h := congrArg (Submission.PSU3.psu3Hom n) (Submission.PSU3.suSgM_mul_self n)
  simpa [Submission.PSU3.psu3Weyl] using h

/-- `orderOf w̄ = 2`. -/
lemma orderOf_psu3Weyl (n : ℕ) : orderOf (Submission.PSU3.psu3Weyl n) = 2 := by
  refine orderOf_eq_prime (by rw [pow_two]; exact psu3Weyl_mul_self n) ?_
  intro h
  exact Submission.PSU3.psu3W_notMem_psu3B n
    (by rw [Submission.PSU3.psu3W_eq_weyl n, h]; exact Subgroup.one_mem _)

/-- **The two-point stabiliser of `w̄` in `B̄` is the maximal torus `T̄`.**  This is
`B̄ ⊓ B̄^{w̄} = T̄` (`psu3B_inf_map_conj_psu3W_eq_psu3T`), rewritten through the definitions
`twoPoint H t = H ⊓ H^t` and `H^t = H.map (MulAut.conj t).toMonoidHom`. -/
lemma twoPoint_psu3B_psu3Weyl (n : ℕ) :
    twoPoint (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n) = Submission.PSU3.psu3T n :=
  Submission.PSU3.psu3B_inf_map_conj_psu3W_eq_psu3T n

theorem psu3_isSplitRankOne (n : ℕ) (hn : 2 ≤ n) :
    Submission.Blueprint.IsSplitRankOne (Submission.PSU3.psu3BenderPair n hn).B
      (Submission.PSU3.psu3BenderPair n hn).U (Submission.PSU3.psu3BenderPair n hn).w := by
  change Submission.Blueprint.IsSplitRankOne (Submission.PSU3.psu3B n) (Submission.PSU3.psu3U n)
    (Submission.PSU3.psu3Weyl n)
  have htwo := twoPoint_psu3B_psu3Weyl n
  refine ⟨(Submission.PSU3.psu3BenderPair n hn).hSemb,
    (Submission.PSU3.psu3BenderPair n hn).isMultiplyPretransitive_two,
    orderOf_psu3Weyl n, (Submission.PSU3.psu3BenderPair n hn).hwB,
    (Submission.PSU3.psu3BenderPair n hn).U_le_B, ?_, ?_, ?_⟩
  · rw [show Subgroup.normalizer (Submission.PSU3.psu3U n) = Submission.PSU3.psu3B n from
      (Submission.PSU3.psu3BenderPair n hn).normalizer_U]
  · rw [htwo]; exact Submission.PSU3.psu3U_inf_psu3T n
  · rw [htwo, Submission.PSU3.psu3B_eq_sup_psu3T n]

end Work.PSU3.Model
