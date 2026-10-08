import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.Models.ModelData.psu3ModelData_data
import Submission.Work.Models.Port.PSU3.Isotropic
import Submission.Work.Models.Port.PSU3.Torus
import Submission.Work.Models.Port.PSU3.Involutions
import Submission.Work.Models.Port.PSU3.Stabilizer
import Submission.Work.Models.Port.PSU3.BNPairQuotient
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open Matrix
open Submission.PSU3

namespace Work.BSLit.BenderFacts2

open LeanEval.GroupTheory.Defs Submission.Blueprint

/-- A `2`-power-order element of `G` lies in a normal subgroup of odd index. -/
theorem mem_of_orderOf_eq_two_pow_of_odd_index {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hodd : Odd N.index) {k : ℕ} {x : G} (hx : orderOf x = 2 ^ k) : x ∈ N := by
  have hxpow : x ^ (2 ^ k) = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
  set y := (QuotientGroup.mk' N) x with hy
  have hy2 : y ^ (2 ^ k) = 1 := by rw [hy, ← map_pow, hxpow, map_one]
  have hdvd2 : orderOf y ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hy2
  have hdvd_index : orderOf y ∣ N.index := by
    rw [Subgroup.index_eq_card]; exact orderOf_dvd_natCard y
  have hcop : Nat.Coprime (2 ^ k) N.index := (hodd.coprime_two_left).pow_left k
  have hone : orderOf y ∣ 1 := by
    rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hdvd2 hdvd_index
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)

/-- The stabiliser of the coset `xH` under the left action of `G` on `G ⧸ H`. -/
theorem stabilizer_mk_eq {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    MulAction.stabilizer G (QuotientGroup.mk x : G ⧸ H) = H.map (MulAut.conj x).toMonoidHom := by
  have h1 : (QuotientGroup.mk x : G ⧸ H) = x • (QuotientGroup.mk (1 : G) : G ⧸ H) := by
    rw [show x • (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk (x * 1) from rfl, mul_one]
  rw [h1, MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient]

/-- **A non-trivial three-point stabiliser refutes `IsZassenhaus`.** -/
theorem not_isZassenhaus_of_threePts {G : Type*} [Group G] (H : Subgroup G) {x y w : G}
    (hx : x ∉ H) (hy : y ∉ H) (hxy : x⁻¹ * y ∉ H)
    (hwH : w ∈ H) (hwx : x⁻¹ * w * x ∈ H) (hwy : y⁻¹ * w * y ∈ H)
    (hw1 : w ≠ 1) : ¬ IsZassenhaus H := by
  intro hZ
  have h1 : w • (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk (1 : G) := by
    rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
    simpa using hwH
  have h2 : w • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x := by
    rw [← MulAction.mem_stabilizer_iff, stabilizer_mk_eq H x,
      Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff]
    exact hwx
  have h3 : w • (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk y := by
    rw [← MulAction.mem_stabilizer_iff, stabilizer_mk_eq H y,
      Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff]
    exact hwy
  have hab : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ QuotientGroup.mk x := by
    intro h
    exact hx (by rw [QuotientGroup.eq] at h; simpa using h)
  have hac : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ QuotientGroup.mk y := by
    intro h
    exact hy (by rw [QuotientGroup.eq] at h; simpa using h)
  have hbc : (QuotientGroup.mk x : G ⧸ H) ≠ QuotientGroup.mk y := by
    intro h
    exact hxy (by rw [QuotientGroup.eq] at h; exact h)
  exact hw1 (hZ _ _ _ hab hac hbc w h1 h2 h3)



section Geo

variable {n : ℕ}

lemma suSg_mulVec_v0 : (↑(suSg n) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = ![0,0,1] := by
  rw [suSg_mulVec]; simp [suE0]

lemma suSg_mulVec_v2 :
    (↑(suSg n) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ (![0,0,1] : Fin 3 → F n) = ![1,0,0] := by
  rw [suSg_mulVec]; simp

lemma suSg_mulVec_v02 :
    (↑(suSg n) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ (![1,0,1] : Fin 3 → F n) = ![1,0,1] := by
  rw [suSg_mulVec]; simp

lemma suSg_inv_mat : (↑((suSg n)⁻¹) : Matrix (Fin 3) (Fin 3) (F n)) =
    (↑(suSg n) : Matrix (Fin 3) (Fin 3) (F n)) := by
  rw [show (suSg n)⁻¹ = suSg n from inv_eq_of_mul_eq_one_right (suSg_mul_self n)]

lemma suUmat01_mulVec_v2 :
    (suUmat n 0 1) *ᵥ (![0,0,1] : Fin 3 → F n) = ![1,0,1] := by
  rw [suUmat]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma suTg_mulVec_v2 (a : (F n)ˣ) :
    (↑(suTg n a) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ (![0,0,1] : Fin 3 → F n) =
      (((a : F n) ^ (2 ^ n))⁻¹) • ![0,0,1] := by
  rw [suTg_coe, suTmat]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

lemma suTg_mulVec_v02 (a : (F n)ˣ) (ha : a ^ (2 ^ n + 1) = 1) :
    (↑(suTg n a) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ (![1,0,1] : Fin 3 → F n) =
      (a : F n) • ![1,0,1] := by
  have hval : ((a : F n) ^ (2 ^ n))⁻¹ = (a : F n) := by
    have h1 : (a : F n) ^ (2 ^ n) * (a : F n) = 1 := by
      have := congrArg (fun z : (F n)ˣ => (z : F n)) (show a ^ (2 ^ n) * a = 1 from by
        rw [← pow_succ, ha])
      simpa using this
    exact inv_eq_of_mul_eq_one_right h1
  rw [suTg_coe, suTmat]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, hval]

/-- `suE0 + e₂ = ![1,0,1]`. -/
lemma suE0_add_e2 : suE0 n + (![0,0,1] : Fin 3 → F n) = ![1,0,1] := by
  ext i; fin_cases i <;> simp [suE0]

lemma suE0_eq_v10 : (![1,0,0] : Fin 3 → F n) = suE0 n := by
  ext i; fin_cases i <;> simp [suE0]

lemma suY_mulVec_v0 : (↑(suUg n 0 1 * suSg n) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n =
    ![1,0,1] := by
  rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, suSg_mulVec_v0, suUg_coe,
    suUmat01_mulVec_v2]

lemma suXinvY_mulVec_v0 :
    (↑((suSg n)⁻¹ * (suUg n 0 1 * suSg n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n =
      ![1,0,1] := by
  rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, suY_mulVec_v0, suSg_inv_mat,
    suSg_mulVec_v02]

lemma suXinvSX_mulVec_v0 (a : (F n)ˣ) :
    (↑((suSg n)⁻¹ * suTg n a * suSg n) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n =
      (((a : F n) ^ (2 ^ n))⁻¹) • suE0 n := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, suSg_mulVec_v0, suTg_mulVec_v2,
    Matrix.mulVec_smul, suSg_inv_mat, suSg_mulVec_v2, suE0_eq_v10]

lemma suYinvSY_mulVec_v0 (a : (F n)ˣ) (ha : a ^ (2 ^ n + 1) = 1) :
    (↑((suUg n 0 1 * suSg n)⁻¹ * suTg n a * (suUg n 0 1 * suSg n)) :
        Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = (a : F n) • suE0 n := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, suY_mulVec_v0, suTg_mulVec_v02 a ha,
    Matrix.mulVec_smul]
  congr 1
  rw [← suY_mulVec_v0, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]


lemma suUg01_mem_SU3 (n : ℕ) : suUg n 0 1 ∈ SU3 n :=
  suUg_isSU3 n 0 1 (by
    rw [one_pow, zero_pow (by positivity)]
    exact CharTwo.add_self_eq_zero 1)

lemma suY_mem_SU3 (n : ℕ) : suUg n 0 1 * suSg n ∈ SU3 n :=
  (SU3 n).mul_mem (suUg01_mem_SU3 n) (suSg_mem_SU3 n)

lemma suXinvY_mem_SU3 (n : ℕ) : (suSg n)⁻¹ * (suUg n 0 1 * suSg n) ∈ SU3 n :=
  (SU3 n).mul_mem ((SU3 n).inv_mem (suSg_mem_SU3 n)) (suY_mem_SU3 n)

lemma suXinvSX_mem_SU3 (n : ℕ) (a : (F n)ˣ) :
    (suSg n)⁻¹ * suTg n a * suSg n ∈ SU3 n :=
  (SU3 n).mul_mem ((SU3 n).mul_mem ((SU3 n).inv_mem (suSg_mem_SU3 n)) (suTg_isSU3 n a))
    (suSg_mem_SU3 n)

lemma suYinvSY_mem_SU3 (n : ℕ) (a : (F n)ˣ) :
    (suUg n 0 1 * suSg n)⁻¹ * suTg n a * (suUg n 0 1 * suSg n) ∈ SU3 n :=
  (SU3 n).mul_mem ((SU3 n).mul_mem ((SU3 n).inv_mem (suY_mem_SU3 n)) (suTg_isSU3 n a))
    (suY_mem_SU3 n)

theorem suSg_notMem_suB (n : ℕ) : suSg n ∉ suB n := by
  intro h
  obtain ⟨lam, hlam, hEq⟩ := (mem_suB_iff_smul n (suSg n) (suSg_mem_SU3 n)).mp h
  have h2 := congrFun hEq 2
  rw [suSg_mulVec_v0] at h2
  simp [suE0, Pi.smul_apply] at h2

theorem suY_notMem_suB (n : ℕ) : suUg n 0 1 * suSg n ∉ suB n := by
  intro h
  obtain ⟨lam, hlam, hEq⟩ := (mem_suB_iff_smul n _ (suY_mem_SU3 n)).mp h
  have h2 := congrFun hEq 2
  rw [suY_mulVec_v0] at h2
  simp [suE0, Pi.smul_apply] at h2

theorem suXinvY_notMem_suB (n : ℕ) : (suSg n)⁻¹ * (suUg n 0 1 * suSg n) ∉ suB n := by
  intro h
  obtain ⟨lam, hlam, hEq⟩ := (mem_suB_iff_smul n _ (suXinvY_mem_SU3 n)).mp h
  have h2 := congrFun hEq 2
  rw [suXinvY_mulVec_v0] at h2
  simp [suE0, Pi.smul_apply] at h2

theorem suTg_mem_suB (n : ℕ) (a : (F n)ˣ) : suTg n a ∈ suB n :=
  Subgroup.mem_sup_right ⟨a, rfl⟩

theorem suXinvSX_mem_suB (n : ℕ) (a : (F n)ˣ) :
    (suSg n)⁻¹ * suTg n a * suSg n ∈ suB n :=
  (mem_suB_iff_smul n _ (suXinvSX_mem_SU3 n a)).mpr
    ⟨((a : F n) ^ (2 ^ n))⁻¹, inv_ne_zero (pow_ne_zero _ (Units.ne_zero a)),
      suXinvSX_mulVec_v0 a⟩

theorem suYinvSY_mem_suB (n : ℕ) (a : (F n)ˣ) (ha : a ^ (2 ^ n + 1) = 1) :
    (suUg n 0 1 * suSg n)⁻¹ * suTg n a * (suUg n 0 1 * suSg n) ∈ suB n :=
  (mem_suB_iff_smul n _ (suYinvSY_mem_SU3 n a)).mpr
    ⟨(a : F n), Units.ne_zero a, suYinvSY_mulVec_v0 a ha⟩

end Geo

/-- The `SU(3,2ⁿ)`-element `u(0,1)·w`. -/
noncomputable def suYSU (n : ℕ) : ↥(SU3 n) := ⟨suUg n 0 1 * suSg n, suY_mem_SU3 n⟩

@[simp] lemma suYSU_val (n : ℕ) : ((suYSU n : ↥(SU3 n)) : GL (Fin 3) (F n)) =
    suUg n 0 1 * suSg n := rfl

/-- **Membership in the Borel of `PSU(3,2ⁿ)` is membership of the lift in `SU(3,2ⁿ)`'s Borel.** -/
lemma mem_psu3B_iff' (n : ℕ) (Z : ↥(SU3 n)) :
    psu3Hom n Z ∈ psu3B n ↔ (Z : GL (Fin 3) (F n)) ∈ suB n := by
  have h1 : psu3Hom n Z ∈ psu3B n ↔ Z ∈ suBS n := by
    constructor
    · intro h
      obtain ⟨W, hW, hWy⟩ := Subgroup.mem_map.mp h
      have hmem : Z⁻¹ * W ∈ (psu3Hom n).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hWy, inv_mul_cancel]
      have h2 : Z⁻¹ * W ∈ suBS n := psu3Hom_ker_le_borel n hmem
      have h3 : Z = W * (Z⁻¹ * W)⁻¹ := by group
      rw [h3]
      exact (suBS n).mul_mem hW ((suBS n).inv_mem h2)
    · intro h
      exact Subgroup.mem_map.mpr ⟨Z, h, rfl⟩
  rw [h1, Subgroup.mem_subgroupOf]


/-- `p · u(0,1) · w · p⁻¹` as an element of `SU(3,2ⁿ)` has underlying matrix `p * (u(0,1)*w) * p⁻¹`. -/
lemma conj_suSgM_suYSU_val (n : ℕ) :
    ((((suSgM n)⁻¹ * suYSU n) : ↥(SU3 n)) : GL (Fin 3) (F n)) =
      (suSg n)⁻¹ * (suUg n 0 1 * suSg n) := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv, suYSU_val]
  rfl

lemma conj_suSgM_suTgSU_suSgM_val (n : ℕ) (a : (F n)ˣ) :
    (((((suSgM n)⁻¹ * suTgSU n a) * suSgM n) : ↥(SU3 n)) : GL (Fin 3) (F n)) =
      (suSg n)⁻¹ * suTg n a * suSg n := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rfl

lemma conj_suYSU_suTgSU_suYSU_val (n : ℕ) (a : (F n)ˣ) :
    (((((suYSU n)⁻¹ * suTgSU n a) * suYSU n) : ↥(SU3 n)) : GL (Fin 3) (F n)) =
      (suUg n 0 1 * suSg n)⁻¹ * suTg n a * (suUg n 0 1 * suSg n) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, suYSU_val]
  rfl

lemma suTgSU_notMem_ker (n : ℕ) {a : (F n)ˣ} (ha3 : a ^ 3 ≠ 1) :
    psu3Hom n (suTgSU n a) ≠ 1 := by
  intro h
  exact ha3 ((Work.Models.ModelData.suTgSU_mem_ker_iff n a).mp (MonoidHom.mem_ker.mpr h)).2


section Main

theorem exists_unit_pow_eq_one_and_pow_three_ne_one (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : (F n)ˣ, a ^ (2 ^ n + 1) = 1 ∧ a ^ 3 ≠ 1 := by
  refine ⟨gen n ^ (2 ^ n - 1), ?_, ?_⟩
  · rw [← pow_mul, two_pow_sub_one_mul_add_one n, ← orderOf_gen n (by omega),
      pow_orderOf_eq_one]
  · intro h3
    have hdvd : orderOf (gen n) ∣ 3 * (2 ^ n - 1) := by
      rw [orderOf_dvd_iff_pow_eq_one, mul_comm 3 (2 ^ n - 1), pow_mul]
      exact h3
    rw [orderOf_gen n (by omega), ← two_pow_sub_one_mul_add_one n] at hdvd
    have hpos : 0 < 3 * (2 ^ n - 1) := by
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have hlt : 3 * (2 ^ n - 1) < (2 ^ n - 1) * (2 ^ n + 1) := by
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      nlinarith [h4]
    exact Nat.not_dvd_of_pos_of_lt hpos hlt hdvd

theorem psu3B_triple (n : ℕ) (hn : 2 ≤ n) :
    ∃ x y w : PSU3Model n, x ∉ psu3B n ∧ y ∉ psu3B n ∧ x⁻¹ * y ∉ psu3B n ∧
      w ∈ psu3B n ∧ x⁻¹ * w * x ∈ psu3B n ∧ y⁻¹ * w * y ∈ psu3B n ∧ w ≠ 1 := by
  obtain ⟨a, ha1, ha3⟩ := exists_unit_pow_eq_one_and_pow_three_ne_one n hn
  refine ⟨psu3Hom n (suSgM n), psu3Hom n (suYSU n), psu3Hom n (suTgSU n a),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_psu3B_iff' n]; exact suSg_notMem_suB n
  · rw [mem_psu3B_iff' n]; simpa only [suYSU_val] using suY_notMem_suB n
  · rw [show (psu3Hom n (suSgM n))⁻¹ * psu3Hom n (suYSU n) =
        psu3Hom n ((suSgM n)⁻¹ * suYSU n : ↥(SU3 n)) from by rw [← map_inv, ← map_mul],
      mem_psu3B_iff' n, conj_suSgM_suYSU_val n]
    exact suXinvY_notMem_suB n
  · rw [mem_psu3B_iff' n]; simpa only [suTgSU_val] using suTg_mem_suB n a
  · rw [show (psu3Hom n (suSgM n))⁻¹ * psu3Hom n (suTgSU n a) * psu3Hom n (suSgM n) =
        psu3Hom n (((suSgM n)⁻¹ * suTgSU n a) * suSgM n : ↥(SU3 n)) from by
          rw [← map_inv, ← map_mul, ← map_mul],
      mem_psu3B_iff' n, conj_suSgM_suTgSU_suSgM_val n a]
    exact suXinvSX_mem_suB n a
  · rw [show (psu3Hom n (suYSU n))⁻¹ * psu3Hom n (suTgSU n a) * psu3Hom n (suYSU n) =
        psu3Hom n (((suYSU n)⁻¹ * suTgSU n a) * suYSU n : ↥(SU3 n)) from by
          rw [← map_inv, ← map_mul, ← map_mul],
      mem_psu3B_iff' n, conj_suYSU_suTgSU_suYSU_val n a]
    exact suYinvSY_mem_suB n a ha1
  · exact suTgSU_notMem_ker n ha3

theorem not_isZassenhaus_psu3B (n : ℕ) (hn : 2 ≤ n) : ¬ IsZassenhaus (psu3B n) := by
  obtain ⟨x, y, w, hx, hy, hxy, hw, hwx, hwy, hw1⟩ := psu3B_triple n hn
  exact not_isZassenhaus_of_threePts (psu3B n) hx hy hxy hw hwx hwy hw1

theorem psu3U_pow_four (n : ℕ) {x : PSU3Model n} (hx : x ∈ psu3U n) : x ^ 4 = 1 := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, c, hc, hbc⟩ := (Subgroup.mem_subgroupOf.mp hu : ((u : ↥(SU3 n)) : GL (Fin 3) (F n)) ∈ suU n)
  have h4 : (u : ↥(SU3 n)) ^ 4 = 1 := by
    apply Subtype.ext
    have hGL : (((u : ↥(SU3 n)) : GL (Fin 3) (F n))) ^ 4 = 1 := by
      rw [hbc]
      have h2 : (suUg n b c) ^ 2 = suUg n 0 (b ^ (2 ^ n + 1)) := by
        rw [pow_two, suUg_mul_self]
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, pow_two, suUg_mul_self,
        zero_pow (show 2 ^ n + 1 ≠ 0 by positivity), suUg_zero]
    simpa using hGL
  rw [← map_pow, h4, map_one]

theorem psu3B_twoElement (n : ℕ) (hn : 2 ≤ n) :
    ∀ x ∈ psu3B n, (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1 := by
  intro x hxB hk
  have hn1 : 1 ≤ n := by omega
  have hle : psu3U n ≤ psu3B n := by
    rw [psu3B_eq_sup_psu3T n]; exact le_sup_left
  have hnorm : psu3B n ≤ Subgroup.normalizer (psu3U n : Set (PSU3Model n)) := by
    rw [psu3B_eq_sup_psu3T n]
    exact sup_le Subgroup.le_normalizer (psu3T_le_normalizer_psu3U n)
  haveI : ((psu3U n).subgroupOf (psu3B n)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm
  have hcardB : Nat.card ↥(psu3B n) = Nat.card ↥(psu3U n) * Nat.card ↥(psu3T n) := by
    rw [psu3B_eq_sup_psu3T n]
    exact Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer _ _
      (psu3T_le_normalizer_psu3U n) (psu3U_inf_psu3T n)
  have hcardN : Nat.card ↥((psu3U n).subgroupOf (psu3B n)) = Nat.card ↥(psu3U n) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hindex : ((psu3U n).subgroupOf (psu3B n)).index = Nat.card ↥(psu3T n) := by
    have h := Subgroup.card_mul_index ((psu3U n).subgroupOf (psu3B n))
    rw [hcardN, hcardB] at h
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥(psu3U n))) h
  have hoddT : Odd (Nat.card ↥(psu3T n)) := by
    have hdiv : Nat.card ↥(psu3T n) ∣ Nat.card ↥(suTS n) := by
      have h := Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker (psu3Hom n)
        (psu3Hom_surjective n) (suTS n)
      exact ⟨Nat.card ↥(suTS n ⊓ (psu3Hom n).ker), h.symm⟩
    have hodd : Odd (Nat.card ↥(suTS n)) := by
      rw [suTS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suT_le_SU3 n)).toEquiv,
        card_suT n hn1]
      exact odd_two_pow_sub_one (2 * n) (by omega)
    exact hodd.of_dvd_nat hdiv
  obtain ⟨k, hk⟩ := hk
  have hx' : (⟨x, hxB⟩ : ↥(psu3B n)) ∈ (psu3U n).subgroupOf (psu3B n) :=
    mem_of_orderOf_eq_two_pow_of_odd_index _ (by rw [hindex]; exact hoddT) (k := k)
      ((Subgroup.orderOf_coe (⟨x, hxB⟩ : ↥(psu3B n))).symm.trans hk)
  exact psu3U_pow_four n (Subgroup.mem_subgroupOf.mp hx')

end Main

/-- **The lead's `BenderModelFacts2Prop` for `PSU(3, 2ⁿ)`** (`n ≥ 2`), with `Y = PSU3Model n`. Route: reduce to `H = B` with `Submission.PSU3.psu3StronglyEmbedded_eq_benderPair_borel`. (1°) `B = U ⋊ T` with `T = psu3T n` of odd order and `U = psu3U n` the Sylow 2-subgroup (of order `q³`, `q = 2^n`); a 2-element of `B` has trivial image in `B ⧸ U`, hence lies in `U`, and `u(b,c) ^ 2 = u(0, b^(q+1))` is an involution (`suUg_mul_self`, `suUg_sq_eq_one_iff`), so `x ^ 4 = 1`. (2°) is **vacuous**: prove `¬ IsZassenhaus H` for every strongly embedded `H`. It suffices to show `¬ IsZassenhaus B` for the Borel, plus invariance of `IsZassenhaus` under conjugation (use the group-theoretic form of the three-point condition: `∀ x y, x ∉ H → y ∉ H → x⁻¹ * y ∉ H → H ⊓ conj x H ⊓ conj y H = ⊥`; the pointwise stabiliser of `H, xH, yH` is exactly `H ⊓ xHx⁻¹ ⊓ yHy⁻¹`). Concretely, let `a ∈ (F n)ˣ` with `a ^ (q + 1) = 1`, `a ≠ 1` (exists for `n ≥ 2`); the torus element `t(a) = psu3Hom n (suTg n a)` is a nontrivial element of `B` with `t(a) ^ q = t(a)⁻¹`, hence the single eigenvalue `a` on the line `⟨e₀, e₂⟩`, so its fixed isotropic points include the three distinct points `[e₀]`, `[e₂]`, `[e₀ + e₂]` (`isIsoPt_mk`, the Hermitian form has matrix value `x^q y + y^q x` on `(x, 0, y)`); using transitivity on isotropic points (`suIsoPt_isPretransitive`) pick `u, v ∉ B` with `u • pE0' = [e₀+e₂]`, `v • pE0' = [e₂]`, then `t(a) ∈ B ⊓ uBu⁻¹ ⊓ vBv⁻¹`, a nontrivial three-point stabiliser. Useful files: `Work.Models.Port.PSU3.{Basic,Isotropic,Stabilizer,Torus,Sylow,Unipotent,Involutions,BNPairQuotient}`, `Work.Models.ModelData.psu3ModelData_data`. -/
theorem psu3_benderModelFacts2 (n : ℕ) (hn : 2 ≤ n) :
    ∀ H : Subgroup (LeanEval.GroupTheory.Defs.PSU3Model n),
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded H →
      (∀ x ∈ H, (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1) ∧
      (Submission.Blueprint.IsZassenhaus H →
        ∀ u ∈ Submission.Blueprint.involutions (H : Set (LeanEval.GroupTheory.Defs.PSU3Model n)),
        ∀ t : LeanEval.GroupTheory.Defs.PSU3Model n, orderOf t = 2 → t ∉ H →
        IsCyclic ↥(Subgroup.centralizer ({u * t} : Set (LeanEval.GroupTheory.Defs.PSU3Model n))) ∧
        (∀ y ∈ Subgroup.centralizer ({u * t} : Set (LeanEval.GroupTheory.Defs.PSU3Model n)),
          u * y * u⁻¹ = y⁻¹) ∧
        (127 ≤ (Submission.Blueprint.involutions
            (H : Set (LeanEval.GroupTheory.Defs.PSU3Model n))).ncard →
          6 ≤ Nat.card ↥(Subgroup.centralizer
            ({u * t} : Set (LeanEval.GroupTheory.Defs.PSU3Model n))))) := by
  intro H hH
  obtain ⟨g, hg⟩ := Submission.PSU3.psu3StronglyEmbedded_eq_benderPair_borel n hn H hH
  have hHmap : H = (psu3B n).map (MulAut.conj g).toMonoidHom := hg
  have hnotZ : ¬ Submission.Blueprint.IsZassenhaus H := by
    obtain ⟨x, y, w, hx, hy, hxy, hw, hwx, hwy, hw1⟩ := psu3B_triple n hn
    refine not_isZassenhaus_of_threePts H (x := g * x * g⁻¹) (y := g * y * g⁻¹)
      (w := g * w * g⁻¹) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hHmap, Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff,
        show g⁻¹ * (g * x * g⁻¹) * g = x from by group]
      exact hx
    · rw [hHmap, Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff,
        show g⁻¹ * (g * y * g⁻¹) * g = y from by group]
      exact hy
    · rw [hHmap, Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff,
        show g⁻¹ * ((g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)) * g = x⁻¹ * y from by group]
      exact hxy
    · rw [hHmap, Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff,
        show g⁻¹ * (g * w * g⁻¹) * g = w from by group]
      exact hw
    · rw [hHmap, Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff,
        show g⁻¹ * ((g * x * g⁻¹)⁻¹ * (g * w * g⁻¹) * (g * x * g⁻¹)) * g = x⁻¹ * w * x
          from by group]
      exact hwx
    · rw [hHmap, Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff,
        show g⁻¹ * ((g * y * g⁻¹)⁻¹ * (g * w * g⁻¹) * (g * y * g⁻¹)) * g = y⁻¹ * w * y
          from by group]
      exact hwy
    · intro h
      exact hw1 (by
        rw [show w = g⁻¹ * (g * w * g⁻¹) * g from by group, h]
        group)
  refine ⟨?_, fun hZ => absurd hZ hnotZ⟩
  intro x hx hk
  rw [hHmap] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  obtain ⟨k, hk⟩ := hk
  have hky : orderOf y = 2 ^ k := by
    rw [← (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y), hyx, hk]
  have hy4 := psu3B_twoElement n hn y hy ⟨k, hky⟩
  rw [show x = (MulAut.conj g).toMonoidHom y from hyx.symm, ← map_pow, hy4, map_one]

end Work.BSLit.BenderFacts2
