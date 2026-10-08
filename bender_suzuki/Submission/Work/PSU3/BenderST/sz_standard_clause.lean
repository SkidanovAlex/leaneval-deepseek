import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.Models.ModelData.szModelData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs

namespace Work.PSU3.BenderST

/-! ## The root elements of the Suzuki `2`-group inside `SzModel n` -/

/-- The root element `u(a,b)` of `Sz(2^(2n+1))` viewed inside `SzModel n`. -/
noncomputable def szUgS (n : ℕ) (a b : Submission.Sz.SzField n) :
    LeanEval.GroupTheory.Defs.SzModel n :=
  ⟨Submission.Sz.szUg n a b, Submission.Sz.szUg_mem_szModel n a b⟩

@[simp] lemma szUgS_coe (n : ℕ) (a b : Submission.Sz.SzField n) :
    ((szUgS n a b : LeanEval.GroupTheory.Defs.SzModel n) :
      GL (Fin 4) (Submission.Sz.SzField n)) = Submission.Sz.szUg n a b := rfl

lemma szUgS_mem_U (n : ℕ) (a b : Submission.Sz.SzField n) :
    szUgS n a b ∈ Submission.Sz.szTwoGroupS n :=
  Subgroup.mem_subgroupOf.mpr ⟨a, b, rfl⟩

lemma szUgS_zero (n : ℕ) : szUgS n 0 0 = (1 : LeanEval.GroupTheory.Defs.SzModel n) := by
  apply Subtype.ext
  rw [szUgS_coe, Subgroup.coe_one, Submission.Sz.szUg_zero]

lemma szUgS_inv (n : ℕ) (a b : Submission.Sz.SzField n) :
    (szUgS n a b)⁻¹ = szUgS n a (b + a ^ (1 + 2 ^ (n + 1))) := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, szUgS_coe, szUgS_coe]
  exact (Submission.Sz.szUg_inv n a b).symm

lemma szUgS_mul (n : ℕ) (a b c d : Submission.Sz.SzField n) :
    szUgS n a b * szUgS n c d
      = szUgS n (a + c) (b + d + a * c ^ (2 ^ (n + 1))) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, szUgS_coe, szUgS_coe, szUgS_coe]
  exact Submission.Sz.szUg_mul n a b c d

/-- A root element `u(0,b)` with `b ≠ 0` is an involution. -/
lemma orderOf_szUgS_zero (n : ℕ) {b : Submission.Sz.SzField n} (hb : b ≠ 0) :
    orderOf (szUgS n 0 b) = 2 := by
  refine orderOf_eq_prime_iff.mpr ⟨?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, szUgS_coe, Subgroup.coe_one, Submission.Sz.szUg_sq,
      zero_pow (by positivity), Submission.Sz.szUg_zero]
  · intro h
    have h1 : Submission.Sz.szUg n 0 b = 1 := by
      have := congrArg (fun z : LeanEval.GroupTheory.Defs.SzModel n =>
        (z : GL (Fin 4) (Submission.Sz.SzField n))) h
      simpa [szUgS_coe] using this
    have h2 : ((0 : Submission.Sz.SzField n), b) = ((0 : Submission.Sz.SzField n), 0) :=
      Submission.Sz.szUg_injective n (by
        show Submission.Sz.szUg n 0 b = Submission.Sz.szUg n 0 0
        rw [h1, Submission.Sz.szUg_zero])
    exact hb (Prod.ext_iff.mp h2).2

/-! ## The Suzuki field power map `a ↦ a^(1+2^(n+1))` is injective -/

lemma sz_pow_injective (n : ℕ) :
    Function.Injective (fun a : Submission.Sz.SzField n => a ^ (1 + 2 ^ (n + 1))) := by
  intro x y hxy
  change x ^ (1 + 2 ^ (n + 1)) = y ^ (1 + 2 ^ (n + 1)) at hxy
  have hk : 1 + 2 ^ (n + 1) ≠ 0 := by positivity
  rcases eq_or_ne x 0 with rfl | hx0
  · have hy : y ^ (1 + 2 ^ (n + 1)) = 0 := by
      have h := hxy
      rw [zero_pow hk] at h
      exact h.symm
    exact ((pow_eq_zero_iff hk).mp hy).symm
  rcases eq_or_ne y 0 with rfl | hy0
  · have hx : x ^ (1 + 2 ^ (n + 1)) = 0 := by
      have h := hxy
      rw [zero_pow hk] at h
      exact h
    exact (pow_eq_zero_iff hk).mp hx
  have huv : (Units.mk0 x hx0) ^ (1 + 2 ^ (n + 1))
      = (Units.mk0 y hy0) ^ (1 + 2 ^ (n + 1)) := by
    apply Units.ext
    simpa using hxy
  have h1 : (Units.mk0 x hx0 * (Units.mk0 y hy0)⁻¹) ^ (1 + 2 ^ (n + 1)) = 1 := by
    rw [mul_pow, huv, inv_pow, mul_inv_cancel]
  have hdvd1 : orderOf (Units.mk0 x hx0 * (Units.mk0 y hy0)⁻¹) ∣ 1 + 2 ^ (n + 1) :=
    orderOf_dvd_iff_pow_eq_one.mpr h1
  have hdvd2 : orderOf (Units.mk0 x hx0 * (Units.mk0 y hy0)⁻¹) ∣ 2 ^ (2 * n + 1) - 1 := by
    have h := orderOf_dvd_natCard (Units.mk0 x hx0 * (Units.mk0 y hy0)⁻¹)
    rwa [Nat.card_units, Submission.Sz.card_szField] at h
  have hcop : Nat.Coprime (1 + 2 ^ (n + 1)) (2 ^ (2 * n + 1) - 1) := by
    have h := Commons.NumberTheory.Nat.coprime_two_pow_succ_add_one_two_pow_sub_one n
    rwa [Nat.add_comm] at h
  have hone : orderOf (Units.mk0 x hx0 * (Units.mk0 y hy0)⁻¹) = 1 := by
    have hg : orderOf (Units.mk0 x hx0 * (Units.mk0 y hy0)⁻¹) ∣ 1 := by
      have h := Nat.dvd_gcd hdvd1 hdvd2
      rwa [hcop.gcd_eq_one] at h
    exact Nat.dvd_one.mp hg
  have huv1 : Units.mk0 x hx0 * (Units.mk0 y hy0)⁻¹ = 1 := orderOf_eq_one_iff.mp hone
  have huv_eq : Units.mk0 x hx0 = Units.mk0 y hy0 := mul_inv_eq_one.mp huv1
  have := congrArg (fun z : (Submission.Sz.SzField n)ˣ => (z : Submission.Sz.SzField n)) huv_eq
  simpa using this

/-! ## The Weyl element and `u(0,1)` -/

/-- The matrix identity `w · u(0,1) · w = u(1,1) · w · u(1,0)`. -/
lemma szWg_conj_szUg_zero_one (n : ℕ) :
    Submission.Sz.szWg n * Submission.Sz.szUg n 0 1 * Submission.Sz.szWg n =
      Submission.Sz.szUg n 1 1 * Submission.Sz.szWg n * Submission.Sz.szUg n 1 0 := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, Submission.Sz.szWg_coe, Submission.Sz.szUg_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Submission.Sz.szU, Submission.Sz.szW, Matrix.mul_apply, Fin.sum_univ_four,
      CharTwo.add_self_eq_zero]

lemma szUg_zero_one_mul_szWg_pow_five (n : ℕ) :
    (Submission.Sz.szUg n 0 1 * Submission.Sz.szWg n) ^ 5 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Submission.Sz.szWg_coe, Submission.Sz.szUg_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four, Submission.Sz.szU, Submission.Sz.szW,
      CharTwo.add_self_eq_zero]

lemma szUg_zero_one_mul_szWg_ne_one (n : ℕ) :
    Submission.Sz.szUg n 0 1 * Submission.Sz.szWg n ≠ 1 := by
  intro h
  have h01 := congrFun (congrFun (congrArg
    (fun u : GL (Fin 4) (Submission.Sz.SzField n) =>
      ((u : Matrix (Fin 4) (Fin 4) (Submission.Sz.SzField n)))) h) 0) 1
  simp [Submission.Sz.szWg_coe, Submission.Sz.szUg_coe, Submission.Sz.szU, Submission.Sz.szW,
    Matrix.mul_apply, Fin.sum_univ_four] at h01

lemma orderOf_szUg_zero_one_mul_szWg (n : ℕ) :
    orderOf (Submission.Sz.szUg n 0 1 * Submission.Sz.szWg n) = 5 := by
  have hdvd : orderOf (Submission.Sz.szUg n 0 1 * Submission.Sz.szWg n) ∣ 5 :=
    orderOf_dvd_iff_pow_eq_one.mpr (szUg_zero_one_mul_szWg_pow_five n)
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) (szUg_zero_one_mul_szWg_ne_one n)
  · exact h

/-! ## The three numerical / structural model facts -/

lemma sz_U_not_abelian (n : ℕ) (hn : 1 ≤ n) :
    ¬ Submission.Blueprint.IsAbelianSubgroup (Submission.Sz.szTwoGroupS n) := by
  intro hab
  obtain ⟨x, hx⟩ := Commons.FieldTheory.FiniteField.exists_pow_two_pow_ne_self n hn
  have hmem1 : szUgS n x 0 ∈ Submission.Sz.szTwoGroupS n := szUgS_mem_U n x 0
  have hmem2 : szUgS n 1 0 ∈ Submission.Sz.szTwoGroupS n := szUgS_mem_U n 1 0
  have hcomm : szUgS n x 0 * szUgS n 1 0 = szUgS n 1 0 * szUgS n x 0 := hab _ hmem1 _ hmem2
  have h2 : Submission.Sz.szUg n x 0 * Submission.Sz.szUg n 1 0
      = Submission.Sz.szUg n 1 0 * Submission.Sz.szUg n x 0 := by
    have := congrArg (fun z : LeanEval.GroupTheory.Defs.SzModel n =>
      (z : GL (Fin 4) (Submission.Sz.SzField n))) hcomm
    simpa [szUgS_coe] using this
  rw [Submission.Sz.szUg_mul, Submission.Sz.szUg_mul] at h2
  have hcomp2 : (x + 1, 0 + 0 + x * 1 ^ (2 ^ (n + 1)))
      = (1 + x, 0 + 0 + 1 * x ^ (2 ^ (n + 1))) := Submission.Sz.szUg_injective n h2
  have hcomp := (Prod.ext_iff.mp hcomp2).2
  simp at hcomp
  exact hx hcomp.symm

lemma sz_U_card_eq (n : ℕ) :
    Nat.card ↥(Submission.Sz.szTwoGroupS n) =
      ((Submission.Blueprint.involutions
        (Submission.Sz.szBorelS n : Set (LeanEval.GroupTheory.Defs.SzModel n))).ncard + 1) ^ 2 := by
  rw [Submission.Sz.card_szTwoGroupS, Work.Models.Sz.ncard_involutions_szBorelS]
  have h1 : 1 ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
  rw [Nat.sub_add_cancel h1, ← pow_mul]
  congr 1
  ring

lemma sz_equal_squares (n : ℕ) :
    ∀ x ∈ Submission.Sz.szTwoGroupS n, ∀ y ∈ Submission.Sz.szTwoGroupS n,
      x ^ 2 = y ^ 2 →
      x * y⁻¹ ∈ Subgroup.closure (Submission.Blueprint.involutions
        (Submission.Sz.szTwoGroupS n : Set (LeanEval.GroupTheory.Defs.SzModel n))) := by
  intro x hx y hy hxy
  obtain ⟨a, b, hab⟩ := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨c, d, hcd⟩ := Subgroup.mem_subgroupOf.mp hy
  have hx2 : (Submission.Sz.szUg n a b) ^ 2 = (Submission.Sz.szUg n c d) ^ 2 := by
    have h := congrArg (fun z : LeanEval.GroupTheory.Defs.SzModel n =>
      (z : GL (Fin 4) (Submission.Sz.SzField n))) hxy
    simp only [Subgroup.coe_pow] at h
    rw [hab, hcd] at h
    exact h
  rw [Submission.Sz.szUg_sq, Submission.Sz.szUg_sq] at hx2
  have hk : a ^ (1 + 2 ^ (n + 1)) = c ^ (1 + 2 ^ (n + 1)) := by
    have hp : ((0 : Submission.Sz.SzField n), a ^ (1 + 2 ^ (n + 1)))
        = ((0 : Submission.Sz.SzField n), c ^ (1 + 2 ^ (n + 1))) :=
      Submission.Sz.szUg_injective n hx2
    exact (Prod.ext_iff.mp hp).2
  have hac : a = c := sz_pow_injective n hk
  have hxy_eq : x * y⁻¹ = szUgS n 0 (b + d) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, szUgS_coe]
    rw [hab, hcd, ← hac]
    rw [← Submission.Sz.szUg_inv n a d, Submission.Sz.szUg_mul]
    have hp : ((a + a, b + (d + a ^ (1 + 2 ^ (n + 1))) + a * a ^ (2 ^ (n + 1))) :
        Submission.Sz.SzField n × Submission.Sz.SzField n) = (0, b + d) := by
      have hpow : a * a ^ (2 ^ (n + 1)) = a ^ (1 + 2 ^ (n + 1)) := by
        rw [← pow_succ' a (2 ^ (n + 1))]
        congr 1
        omega
      have h1 : a + a = (0 : Submission.Sz.SzField n) := CharTwo.add_self_eq_zero a
      have h2 : b + (d + a ^ (1 + 2 ^ (n + 1))) + a ^ (1 + 2 ^ (n + 1)) = b + d := by
        have hd : (d + a ^ (1 + 2 ^ (n + 1))) + a ^ (1 + 2 ^ (n + 1)) = d := by
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        rw [add_assoc, hd]
      rw [hpow, h1, h2]
    exact congrArg (fun p : Submission.Sz.SzField n × Submission.Sz.SzField n =>
      Submission.Sz.szUg n p.1 p.2) hp
  rw [hxy_eq]
  by_cases hbd : b + d = 0
  · rw [hbd, szUgS_zero]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨szUgS_mem_U n 0 (b + d), orderOf_szUgS_zero n hbd⟩

/-- The `Sz(2^(2n+1))` clause of `BenderSTProp` for the standard split rank-one datum
`(P.B, P.U, P.w)` of `P := szBenderPair n hn`.  `structureIdentity` (Peterfalvi II Ch. V §2
Lemma 1 b) says the pair `(s, r⁻¹)` with `s ∈ P.U`, `orderOf s = 2`, `r⁻¹ ∈ P.U` and
`P.w * s * P.w = r⁻¹ * P.w * r` is *unique*, so it suffices to exhibit one such pair
`(s₀, ρ₀) = (szUg n 0 1, szUg n 1 1)` (as elements of `SzModel n`) and compute
`(s₀ * P.w)⁵ = 1`.  See `Submission/Work/PSU3/BenderST/ROUTE.md`. -/
theorem sz_standard_clause (n : ℕ) (hn : 1 ≤ n)
    (hstd : Submission.Blueprint.IsSplitRankOne (Submission.Sz.szBenderPair n hn).B
      (Submission.Sz.szBenderPair n hn).U (Submission.Sz.szBenderPair n hn).w)
    (s r : ↥(LeanEval.GroupTheory.Defs.SzModel n))
    (hs : s ∈ (Submission.Sz.szBenderPair n hn).U)
    (hs2 : orderOf s = 2) (hr : r ∈ (Submission.Sz.szBenderPair n hn).U)
    (hsr : (Submission.Sz.szBenderPair n hn).w * s * (Submission.Sz.szBenderPair n hn).w
      = r⁻¹ * (Submission.Sz.szBenderPair n hn).w * r) :
    orderOf (s * (Submission.Sz.szBenderPair n hn).w) = 5 ∧
      ¬ Submission.Blueprint.IsAbelianSubgroup (Submission.Sz.szBenderPair n hn).U ∧
      Nat.card (Submission.Sz.szBenderPair n hn).U =
        ((Submission.Blueprint.involutions
          ((Submission.Sz.szBenderPair n hn).B :
            Set ↥(LeanEval.GroupTheory.Defs.SzModel n))).ncard + 1) ^ 2 ∧
      ∀ x ∈ (Submission.Sz.szBenderPair n hn).U, ∀ y ∈ (Submission.Sz.szBenderPair n hn).U,
        x ^ 2 = y ^ 2 → x * y⁻¹ ∈ Subgroup.closure (Submission.Blueprint.involutions
          ((Submission.Sz.szBenderPair n hn).U :
            Set ↥(LeanEval.GroupTheory.Defs.SzModel n))) := by
  classical
  have hdata : Work.ThmF.IsSplitRankOneData (LeanEval.GroupTheory.Defs.SzModel n)
      (Submission.Sz.szBenderPair n hn).B (Submission.Sz.szBenderPair n hn).U
      (Submission.Sz.szBenderPair n hn).w := Work.ThmF.IsSplitRankOne.toData hstd
  obtain ⟨p, _hp, huniq⟩ := Work.ThmF.ChV12.structureIdentity hdata
  have hww : (Submission.Sz.szBenderPair n hn).w * (Submission.Sz.szBenderPair n hn).w = 1 := by
    have h : (Submission.Sz.szBenderPair n hn).w ^ 2 = 1 := by
      have := pow_orderOf_eq_one (Submission.Sz.szBenderPair n hn).w
      rw [hstd.invol] at this
      simpa using this
    simpa [pow_two] using h
  have hwinv : (Submission.Sz.szBenderPair n hn).w⁻¹ = (Submission.Sz.szBenderPair n hn).w :=
    inv_eq_of_mul_eq_one_right hww
  have hsol1 : (Submission.Sz.szBenderPair n hn).w * s
        * ((Submission.Sz.szBenderPair n hn).w)⁻¹
      = r⁻¹ * (Submission.Sz.szBenderPair n hn).w * (r⁻¹)⁻¹ := by
    rw [hwinv, inv_inv]
    exact hsr
  have h1 : (s, r⁻¹) = p :=
    huniq (s, r⁻¹) ⟨hs, hs2, ((Submission.Sz.szBenderPair n hn).U).inv_mem hr, hsol1⟩
  have hs0U : szUgS n 0 1 ∈ (Submission.Sz.szBenderPair n hn).U := szUgS_mem_U n 0 1
  have hr0U : szUgS n 1 1 ∈ (Submission.Sz.szBenderPair n hn).U := szUgS_mem_U n 1 1
  have hs02 : orderOf (szUgS n 0 1) = 2 := orderOf_szUgS_zero n one_ne_zero
  have hr0inv : (szUgS n 1 1)⁻¹ = szUgS n 1 0 := by
    rw [szUgS_inv, one_pow]
    congr 1
    exact CharTwo.add_self_eq_zero 1
  have hsol2 : (Submission.Sz.szBenderPair n hn).w * szUgS n 0 1
        * ((Submission.Sz.szBenderPair n hn).w)⁻¹
      = szUgS n 1 1 * (Submission.Sz.szBenderPair n hn).w * (szUgS n 1 1)⁻¹ := by
    rw [hwinv, hr0inv]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, szUgS_coe]
    exact szWg_conj_szUg_zero_one n
  have h2 : (szUgS n 0 1, szUgS n 1 1) = p :=
    huniq (szUgS n 0 1, szUgS n 1 1) ⟨hs0U, hs02, hr0U, hsol2⟩
  have hs_eq : s = szUgS n 0 1 := congrArg Prod.fst (h1.trans h2.symm)
  have hord : orderOf (s * (Submission.Sz.szBenderPair n hn).w) = 5 := by
    rw [hs_eq, ← Subgroup.orderOf_coe (szUgS n 0 1 * (Submission.Sz.szBenderPair n hn).w),
      Subgroup.coe_mul, szUgS_coe]
    exact orderOf_szUg_zero_one_mul_szWg n
  exact ⟨hord, sz_U_not_abelian n hn, sz_U_card_eq n,
    fun x hx' y hy' hxy => sz_equal_squares n x hx' y hy' hxy⟩

end Work.PSU3.BenderST
