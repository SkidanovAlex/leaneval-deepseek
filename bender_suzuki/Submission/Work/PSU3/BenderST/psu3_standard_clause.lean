import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.Models.ModelData.psu3ModelData_data
import Submission.Work.PSU3.BenderST.psu3_std_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.BenderST

open LeanEval.GroupTheory.Defs

/-- The `PSU(3,2ⁿ)` clause of `BenderSTProp` for the standard split rank-one datum
`(P.B, P.U, P.w)` of `P := psu3BenderPair n hn`.  `structureIdentity` (Peterfalvi II Ch. V §2
Lemma 1 b) says the pair `(s, r⁻¹)` with `s ∈ P.U`, `orderOf s = 2`, `r⁻¹ ∈ P.U` and
`P.w * s * P.w = r⁻¹ * P.w * r` is *unique*, so it suffices to exhibit one such pair
`(s₀, ρ₀) = (psu3Hom n (suUg n 0 1), same)` and compute `(s₀ * P.w)³ = 1`
(the matrix identity `t s t = s t s`).  See `Submission/Work/PSU3/BenderST/ROUTE.md`. -/
theorem psu3_standard_clause (n : ℕ) (hn : 2 ≤ n)
    (hstd : Submission.Blueprint.IsSplitRankOne (Submission.PSU3.psu3BenderPair n hn).B
      (Submission.PSU3.psu3BenderPair n hn).U (Submission.PSU3.psu3BenderPair n hn).w)
    (s r : ↥(LeanEval.GroupTheory.Defs.PSU3Model n))
    (hs : s ∈ (Submission.PSU3.psu3BenderPair n hn).U)
    (hs2 : orderOf s = 2) (hr : r ∈ (Submission.PSU3.psu3BenderPair n hn).U)
    (hsr : (Submission.PSU3.psu3BenderPair n hn).w * s * (Submission.PSU3.psu3BenderPair n hn).w
      = r⁻¹ * (Submission.PSU3.psu3BenderPair n hn).w * r) :
    orderOf (s * (Submission.PSU3.psu3BenderPair n hn).w) = 3 ∧
      Nat.card (Submission.PSU3.psu3BenderPair n hn).U =
        ((Submission.Blueprint.involutions
          ((Submission.PSU3.psu3BenderPair n hn).B :
            Set ↥(LeanEval.GroupTheory.Defs.PSU3Model n))).ncard + 1) ^ 3 ∧
      ∃ x ∈ Submission.Blueprint.twoPoint (Submission.PSU3.psu3BenderPair n hn).B
            (Submission.PSU3.psu3BenderPair n hn).w, x ≠ 1 ∧
        ∀ u ∈ Submission.Blueprint.involutions
              ((Submission.PSU3.psu3BenderPair n hn).B :
                Set ↥(LeanEval.GroupTheory.Defs.PSU3Model n)),
          x * u = u * x := by
  classical
  -- The Weyl element is an involution, so `w⁻¹ = w`
  have hww : Submission.PSU3.psu3Weyl n * Submission.PSU3.psu3Weyl n = 1 :=
    Work.PSU3.Model.psu3Weyl_mul_self n
  have hwi : (Submission.PSU3.psu3Weyl n)⁻¹ = Submission.PSU3.psu3Weyl n :=
    inv_eq_of_mul_eq_one_right hww
  -- the standard solution `(u(0,1), u(0,1))` of the structure identity
  obtain ⟨hstdU, hstd2⟩ := psu3_std_involution n
  obtain ⟨hstdSt, hstd3⟩ := psu3_std_struct n
  -- the datum rewritten in terms of the model subgroups
  have hstd' : Submission.Blueprint.IsSplitRankOne (Submission.PSU3.psu3B n)
      (Submission.PSU3.psu3U n) (Submission.PSU3.psu3Weyl n) := hstd
  -- `(s, r⁻¹)` and `(u(0,1), u(0,1))` are both solutions; the pair is unique
  obtain ⟨p, _hp, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hstd')
  have hpair_s : (s, r⁻¹) = p := by
    refine huniq (s, r⁻¹) ⟨?_, hs2, ?_, ?_⟩
    · change s ∈ Submission.PSU3.psu3U n
      exact hs
    · exact Subgroup.inv_mem _ hr
    · rw [hwi, inv_inv]
      exact hsr
  have hpair_std : (psu3Std n, psu3Std n) = p :=
    huniq (psu3Std n, psu3Std n) ⟨hstdU, hstd2, hstdU, hstdSt⟩
  have hs_eq : s = psu3Std n := congrArg Prod.fst (hpair_s.trans hpair_std.symm)
  refine ⟨?_, ?_, ?_⟩
  · change orderOf (s * Submission.PSU3.psu3Weyl n) = 3
    rw [hs_eq]
    exact hstd3
  · change Nat.card ↥(Submission.PSU3.psu3U n) =
        ((Submission.Blueprint.involutions
          (Submission.PSU3.psu3B n : Set (PSU3Model n))).ncard + 1) ^ 3
    have hU : Nat.card ↥(Submission.PSU3.psu3U n) = 2 ^ (3 * n) := by
      rw [Submission.card_psu3U n hn, Submission.PSU3.card_suUS n (by omega)]
    have hI : (Submission.Blueprint.involutions
        (Submission.PSU3.psu3B n : Set (PSU3Model n))).ncard = 2 ^ n - 1 :=
      Work.Models.ModelData.ncard_involutions_psu3B n hn
    rw [hU, hI, Nat.sub_add_cancel Nat.one_le_two_pow]
    conv_rhs => rw [← pow_mul]
    rw [Nat.mul_comm n 3]
  · obtain ⟨x, hx, hx1, hxc⟩ := psu3_twoPoint_centralizes n hn
    refine ⟨x, ?_, hx1, ?_⟩
    · change x ∈ Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
        (Submission.PSU3.psu3Weyl n)
      exact hx
    · intro u hu
      exact hxc u hu

end Work.PSU3.BenderST
