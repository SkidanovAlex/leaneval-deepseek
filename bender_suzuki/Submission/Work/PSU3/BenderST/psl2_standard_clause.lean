import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.Models.ModelData.pSL2ModelData
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `PSL(2,2ⁿ)` standard-datum clause

For `K = GF(2ⁿ)` let `u₀ = unipotentPSLHom K (ofAdd 1) ∈ PSL(2,K)` be the image of the
unipotent matrix `!![1,1;0,1]` and `w = weylPSL K` the Weyl element `!![0,1;1,0]`.  The two
elementary matrix computations behind the `PSL(2,2ⁿ)` clause of `BenderSTProp` are

* `w · u₀ · w = u₀ · w · u₀` (so `(u₀, u₀)` is a solution of the structure identity
  `w * s * w = r⁻¹ * w * r`), and
* `(u₀ · w)³ = 1`, `u₀ · w ≠ 1` (so `orderOf (u₀ · w) = 3`),

together with `orderOf u₀ = 2`.  Since `structureIdentity` (Peterfalvi II Ch. V §2 Lemma 1 b)
says that the pair `(s, r⁻¹)` of the clause is *unique*, the clause follows: any `s ∈ U` of
order `2` in a solution of `w s w = r⁻¹ w r` must equal `u₀`.
-/

set_option maxHeartbeats 1000000

namespace Work.PSU3.BenderST

open LeanEval.GroupTheory.Defs

/-- In `PSL(2, 2ⁿ)` the unipotent element `u₀ = unip 1` (the image of the matrix
`!![1,1;0,1]`) has order two: `(K,+)` has exponent `2`. -/
lemma psl2_orderOf_unipotent_one (n : ℕ) :
    orderOf (Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
      (Multiplicative.ofAdd (1 : GaloisField 2 n))) = 2 := by
  have hinj := Commons.GroupTheory.SL2.unipotentPSLHom_injective
    (K := GaloisField 2 n) (show CharP (GaloisField 2 n) 2 from inferInstance)
  rw [orderOf_injective (Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)) hinj]
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero]
  · intro h
    have h1 : (1 : GaloisField 2 n) = 0 := by
      simpa using congrArg Multiplicative.toAdd h
    exact one_ne_zero h1

/-- The structure identity for the pair `(u₀, u₀)` in `PSL(2, 2ⁿ)`:
`w · u₀ · w = u₀ · w · u₀`.  Both sides are the image of `!![1,0;1,1] ∈ SL(2,K)`. -/
lemma psl2_weyl_conj_unipotent_one (n : ℕ) :
    Submission.PSL2.weylPSL (GaloisField 2 n) *
        Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
          (Multiplicative.ofAdd (1 : GaloisField 2 n)) *
        Submission.PSL2.weylPSL (GaloisField 2 n) =
      Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
          (Multiplicative.ofAdd (1 : GaloisField 2 n)) *
        Submission.PSL2.weylPSL (GaloisField 2 n) *
        Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
          (Multiplicative.ofAdd (1 : GaloisField 2 n)) := by
  have hSL : Submission.PSL2.weylSL (GaloisField 2 n) *
        Commons.GroupTheory.SL2.transvectionSL (GaloisField 2 n) (1 : GaloisField 2 n) *
        Submission.PSL2.weylSL (GaloisField 2 n) =
      Commons.GroupTheory.SL2.transvectionSL (GaloisField 2 n) (1 : GaloisField 2 n) *
        Submission.PSL2.weylSL (GaloisField 2 n) *
        Commons.GroupTheory.SL2.transvectionSL (GaloisField 2 n) (1 : GaloisField 2 n) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Submission.PSL2.weylSL_coe,
      Submission.PSL2.transvectionSL_coe]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  have h' := congrArg (QuotientGroup.mk'
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)))) hSL
  simp only [map_mul] at h'
  exact h'

/-- `u₀ · w` has order `3` in `PSL(2, 2ⁿ)`: its `SL(2,K)` lift `!![1,1;0,1] · !![0,1;1,0]`
cubes to `1` but differs from `1`, and in characteristic two the centre of `SL(2,K)` is
trivial, so the quotient map is injective. -/
lemma psl2_orderOf_unipotent_one_mul_weyl (n : ℕ) :
    orderOf (Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
        (Multiplicative.ofAdd (1 : GaloisField 2 n)) *
      Submission.PSL2.weylPSL (GaloisField 2 n)) = 3 := by
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  have hinj : Function.Injective
      (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk',
      Commons.GroupTheory.SL2.center_specialLinearGroup_two_eq_bot hchar]
  have hmk_tv : (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))))
      (Commons.GroupTheory.SL2.transvectionSL (GaloisField 2 n) (1 : GaloisField 2 n)) =
      Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
        (Multiplicative.ofAdd (1 : GaloisField 2 n)) := rfl
  have hmk_w : (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))))
      (Submission.PSL2.weylSL (GaloisField 2 n)) = Submission.PSL2.weylPSL (GaloisField 2 n) :=
    rfl
  have hAne : Commons.GroupTheory.SL2.transvectionSL (GaloisField 2 n) (1 : GaloisField 2 n) *
      Submission.PSL2.weylSL (GaloisField 2 n) ≠ 1 := by
    intro h
    have h01 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) =>
      (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 0 1) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Submission.PSL2.weylSL_coe, Submission.PSL2.transvectionSL_coe] at h01
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne] at h01
  have hA3 : (Commons.GroupTheory.SL2.transvectionSL (GaloisField 2 n) (1 : GaloisField 2 n) *
      Submission.PSL2.weylSL (GaloisField 2 n)) ^ 3 = 1 := by
    rw [show (3:ℕ) = 2+1 from rfl, pow_succ, pow_two]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Submission.PSL2.weylSL_coe,
      Submission.PSL2.transvectionSL_coe, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  have hne : Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
        (Multiplicative.ofAdd (1 : GaloisField 2 n)) *
      Submission.PSL2.weylPSL (GaloisField 2 n) ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))))
        (Commons.GroupTheory.SL2.transvectionSL (GaloisField 2 n) (1 : GaloisField 2 n) *
          Submission.PSL2.weylSL (GaloisField 2 n)) = 1 := by
      rw [map_mul, hmk_tv, hmk_w]
      exact h
    exact hAne (hinj h1)
  have h3 : (Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
        (Multiplicative.ofAdd (1 : GaloisField 2 n)) *
      Submission.PSL2.weylPSL (GaloisField 2 n)) ^ 3 = 1 := by
    change ((QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))))
        (Commons.GroupTheory.SL2.transvectionSL (GaloisField 2 n) (1 : GaloisField 2 n) *
          Submission.PSL2.weylSL (GaloisField 2 n))) ^ 3 = 1
    rw [← map_pow, hA3, map_one]
  exact orderOf_eq_prime h3 hne

/-- The `PSL(2,2ⁿ)` clause of `BenderSTProp` for the standard split rank-one datum
`(P.B, P.U, P.w)` of `P := pSL2BenderPair n hn`.  `structureIdentity` (Peterfalvi II Ch. V §2
Lemma 1 b) says the pair `(s, r⁻¹)` with `s ∈ P.U`, `orderOf s = 2`, `r⁻¹ ∈ P.U` and
`P.w * s * P.w = r⁻¹ * P.w * r` is *unique*, so it suffices to exhibit one such pair `(s₀,ρ₀)`
and compute `(s₀ * P.w)³ = 1`; take `s₀ = ρ₀ =` the image of `unip 1`.  See
`Submission/Work/PSU3/BenderST/ROUTE.md`. -/
theorem psl2_standard_clause (n : ℕ) (hn : 2 ≤ n)
    (hstd : Submission.Blueprint.IsSplitRankOne (Submission.PSL2.pSL2BenderPair n hn).B
      (Submission.PSL2.pSL2BenderPair n hn).U (Submission.PSL2.pSL2BenderPair n hn).w)
    (s r : LeanEval.GroupTheory.Defs.PSL2Model n)
    (hs : s ∈ (Submission.PSL2.pSL2BenderPair n hn).U)
    (hs2 : orderOf s = 2) (hr : r ∈ (Submission.PSL2.pSL2BenderPair n hn).U)
    (hsr : (Submission.PSL2.pSL2BenderPair n hn).w * s * (Submission.PSL2.pSL2BenderPair n hn).w
      = r⁻¹ * (Submission.PSL2.pSL2BenderPair n hn).w * r) :
    orderOf (s * (Submission.PSL2.pSL2BenderPair n hn).w) = 3 ∧
      Submission.Blueprint.IsAbelianSubgroup (Submission.PSL2.pSL2BenderPair n hn).U ∧
      Nat.card (Submission.PSL2.pSL2BenderPair n hn).U =
        (Submission.Blueprint.involutions
          ((Submission.PSL2.pSL2BenderPair n hn).B :
            Set (LeanEval.GroupTheory.Defs.PSL2Model n))).ncard + 1 := by
  classical
  -- the candidate solution `(u₀, u₀)` of the structure identity
  let u₀ := Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
      (Multiplicative.ofAdd (1 : GaloisField 2 n))
  have hu₀ord : orderOf u₀ = 2 := psl2_orderOf_unipotent_one n
  have hu₀U : u₀ ∈ (Submission.PSL2.pSL2BenderPair n hn).U :=
    MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (1 : GaloisField 2 n), rfl⟩
  have hwi : (Submission.PSL2.pSL2BenderPair n hn).w⁻¹
      = (Submission.PSL2.pSL2BenderPair n hn).w :=
    inv_eq_of_mul_eq_one_right
      (Submission.PSL2.weylPSL_mul_self (K := GaloisField 2 n))
  have hu₀inv : u₀⁻¹ = u₀ := by
    apply inv_eq_of_mul_eq_one_right
    have h := pow_orderOf_eq_one u₀
    rw [hu₀ord] at h
    simpa [pow_two] using h
  -- `(s, r⁻¹)` is a solution, and so is `(u₀, u₀)`; the pair is unique
  obtain ⟨p, _hp, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hstd)
  have hpair_s : (s, r⁻¹) = p := by
    refine huniq (s, r⁻¹) ⟨hs, hs2, Subgroup.inv_mem _ hr, ?_⟩
    simpa [hwi] using hsr
  have hpair_u : (u₀, u₀) = p := by
    refine huniq (u₀, u₀) ⟨hu₀U, hu₀ord, hu₀U, ?_⟩
    rw [hwi, hu₀inv]
    exact psl2_weyl_conj_unipotent_one n
  have hs_eq : s = u₀ := congrArg Prod.fst (hpair_s.trans hpair_u.symm)
  refine ⟨?_, ?_, ?_⟩
  · rw [hs_eq]
    exact psl2_orderOf_unipotent_one_mul_weyl n
  · -- `U` is the image of `(K,+)`, hence abelian
    exact Work.Models.ModelData.psl2UnipotentComm n
  · -- `|U| = 2ⁿ` and `#Inv(B) = 2ⁿ - 1`
    have hU : Nat.card ↥(Submission.PSL2.pSL2BenderPair n hn).U = 2 ^ n :=
      Submission.PSL2.card_unipotentPSLHom_range n (by omega)
    have hI : (Submission.Blueprint.involutions
        (((Submission.PSL2.pSL2BenderPair n hn).B : Subgroup (PSL2Model n)) :
          Set (PSL2Model n))).ncard = 2 ^ n - 1 :=
      Work.Models.ModelData.psl2NcardInvolutionsStab n hn
    rw [hU, hI]
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

end Work.PSU3.BenderST
