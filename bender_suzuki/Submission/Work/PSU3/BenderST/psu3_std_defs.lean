/-
# The `PSU(3,2ⁿ)` standard involution and its structure identity

This module defines the "standard involution" `u(0,1) ∈ PSU(3,2ⁿ)` (the image of the unipotent
matrix `!![1,0,1;0,1,0;0,0,1] ∈ SU(3,2ⁿ)`) and records the model facts about it that the
`PSU(3,2ⁿ)` clause of `BenderSTProp` needs for the standard split rank-one datum
`(B̄, Ū, w̄) = psu3BenderPair n hn`:

* `psu3_std_involution`: `u(0,1) ∈ Ū` and `orderOf (u(0,1)) = 2`;
* `psu3_std_struct`: the structure identity `w̄ u w̄⁻¹ = u w̄ u⁻¹` (equivalently
  `w u w = u w u`) and `orderOf (u w̄) = 3` — the matrix identity `s u s = u s u`, `(u s)³ = 1`
  in `SU(3,2ⁿ)` pushed through `psu3Hom`;
* `psu3_twoPoint_centralizes`: some `1 ≠ x ∈ twoPoint B̄ w̄ = T̄` centralises every involution
  of `B̄` — the `PSU(3,q)` clause of `BenderSTProp`.
-/
import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Port.PSU3.Centralizer
import Submission.Work.Models.ModelData.psu3ModelData_data
import Submission.Work.PSU3.Model.psu3_isSplitRankOne
import Submission.Work.Models.Abstract.involutions_subset_U

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.PSU3.BenderST

/-- The unipotent element `u(0,1) = !![1,0,1;0,1,0;0,0,1]` of `SU(3,2ⁿ)`. -/
noncomputable def psu3StdSU (n : ℕ) : ↥(Submission.PSU3.SU3 n) :=
  ⟨Submission.PSU3.suUg n 0 1,
    Submission.PSU3.suU_le_SU3 n (Submission.PSU3.suUg_zero_mem n 1 (by simp))⟩

/-- The standard involution `u(0,1) = psu3Hom (suUg 0 1) ∈ PSU(3,2ⁿ)`. -/
noncomputable def psu3Std (n : ℕ) : PSU3Model n := Submission.PSU3.psu3Hom n (psu3StdSU n)

@[simp] lemma psu3StdSU_coe (n : ℕ) :
    ((psu3StdSU n : ↥(Submission.PSU3.SU3 n)) : GL (Fin 3) (Submission.PSU3.F n)) =
      Submission.PSU3.suUg n 0 1 := rfl

@[simp] lemma psu3Std_val (n : ℕ) :
    psu3Std n = Submission.PSU3.psu3Hom n (psu3StdSU n) := rfl

lemma psu3StdSU_mem_suUS (n : ℕ) : psu3StdSU n ∈ Submission.PSU3.suUS n :=
  Subgroup.mem_subgroupOf.mpr (by
    show Submission.PSU3.suUg n 0 1 ∈ Submission.PSU3.suU n
    exact Submission.PSU3.suUg_zero_mem n 1 (by simp))

/-- The standard involution lies in the image of the unipotent radical. -/
lemma psu3Std_mem (n : ℕ) : psu3Std n ∈ Submission.PSU3.psu3U n := by
  rw [Submission.PSU3.psu3U]
  exact Subgroup.mem_map.mpr ⟨psu3StdSU n, psu3StdSU_mem_suUS n, rfl⟩

/-- The underlying element `u(0,1) ∈ SU(3,2ⁿ)` is an involution. -/
lemma psu3StdSU_sq (n : ℕ) : psu3StdSU n ^ 2 = 1 := by
  apply Subtype.ext
  show (Submission.PSU3.suUg n 0 1) ^ 2 = (1 : GL (Fin 3) (Submission.PSU3.F n))
  rw [pow_two, Submission.PSU3.suUg_mul_self, zero_pow (by positivity)]
  exact Submission.PSU3.suUg_zero n

lemma psu3StdSU_ne_one (n : ℕ) : psu3StdSU n ≠ 1 := by
  intro h
  have hsu : Submission.PSU3.suUg n 0 1 = (1 : GL (Fin 3) (Submission.PSU3.F n)) :=
    congrArg (fun z : ↥(Submission.PSU3.SU3 n) => (z : GL (Fin 3) (Submission.PSU3.F n))) h
  have hpair : ((0 : Submission.PSU3.F n), (1 : Submission.PSU3.F n)) =
      ((0 : Submission.PSU3.F n), (0 : Submission.PSU3.F n)) :=
    Submission.PSU3.suUg_injective n
      (show (fun p : Submission.PSU3.F n × Submission.PSU3.F n =>
          Submission.PSU3.suUg n p.1 p.2) (0, 1) =
        (fun p : Submission.PSU3.F n × Submission.PSU3.F n =>
          Submission.PSU3.suUg n p.1 p.2) (0, 0) from hsu.trans (Submission.PSU3.suUg_zero n).symm)
  exact one_ne_zero ((Prod.ext_iff.mp hpair).2)

/-- The image of `u(0,1)` in `PSU(3,2ⁿ)` is nontrivial: the kernel of the projection consists of
scalar matrices while `u(0,1)` is not scalar. -/
lemma psu3Std_ne_one (n : ℕ) : psu3Std n ≠ 1 := by
  intro h
  have hker : psu3StdSU n ∈ (Submission.PSU3.psu3Hom n).ker := MonoidHom.mem_ker.mpr h
  have hTS : psu3StdSU n ∈ Submission.PSU3.suTS n :=
    Submission.PSU3.psu3Hom_ker_le_suTS n hker
  have hmem : psu3StdSU n ∈ Submission.PSU3.suUS n ⊓ Submission.PSU3.suTS n :=
    ⟨psu3StdSU_mem_suUS n, hTS⟩
  rw [Submission.PSU3.suTS_inf_suUS n] at hmem
  exact psu3StdSU_ne_one n (Subgroup.mem_bot.mp hmem)

/-- The standard involution `u(0,1)` lies in `Ū` and has order two. -/
lemma psu3_std_involution (n : ℕ) :
    psu3Std n ∈ Submission.PSU3.psu3U n ∧ orderOf (psu3Std n) = 2 := by
  refine ⟨psu3Std_mem n, ?_⟩
  have h2 : (psu3Std n) ^ 2 = 1 := by
    have h := congrArg (Submission.PSU3.psu3Hom n) (psu3StdSU_sq n)
    simpa only [map_pow, map_one, psu3Std_val] using h
  exact (orderOf_eq_prime_iff (p := 2)).mpr ⟨h2, psu3Std_ne_one n⟩

/-- The structure identity for the standard involution in `PSU(3,2ⁿ)` together with the order of
`u(0,1) * w̄`: with `u = u(0,1)`, `s = J3` the Weyl matrix one has in characteristic two
`s u s = u s u` and `(u s)³ = 1`, `u s ≠ 1`; pushing through `psu3Hom` gives the two claims. -/
lemma psu3_std_struct (n : ℕ) :
    Submission.PSU3.psu3Weyl n * psu3Std n * (Submission.PSU3.psu3Weyl n)⁻¹ =
        psu3Std n * Submission.PSU3.psu3Weyl n * (psu3Std n)⁻¹ ∧
      orderOf (psu3Std n * Submission.PSU3.psu3Weyl n) = 3 := by
  have hGL1 : Submission.PSU3.suSg n * Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n =
      Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n * Submission.PSU3.suUg n 0 1 := by
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul, Submission.PSU3.suSg_coe,
      Submission.PSU3.suUg_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Submission.PSU3.suUmat, Submission.PSU3.J3, Matrix.mul_apply, Fin.sum_univ_three,
        CharTwo.add_self_eq_zero]
  have hstd_inv : (psu3StdSU n)⁻¹ = psu3StdSU n :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact psu3StdSU_sq n)
  have hSU1 : Submission.PSU3.suSgM n * psu3StdSU n * (Submission.PSU3.suSgM n)⁻¹ =
      psu3StdSU n * Submission.PSU3.suSgM n * (psu3StdSU n)⁻¹ := by
    rw [Submission.PSU3.suSgM_inv n, hstd_inv]
    exact Subtype.ext hGL1
  have hP1 : Submission.PSU3.psu3Weyl n * psu3Std n * (Submission.PSU3.psu3Weyl n)⁻¹ =
      psu3Std n * Submission.PSU3.psu3Weyl n * (psu3Std n)⁻¹ := by
    have h := congrArg (Submission.PSU3.psu3Hom n) hSU1
    simpa only [map_mul, map_inv, psu3Std_val, Submission.PSU3.psu3Weyl] using h
  have hGL3 : (Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n) ^ 3 = 1 := by
    rw [pow_three]
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul, Submission.PSU3.suSg_coe,
      Submission.PSU3.suUg_coe, Matrix.GeneralLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Submission.PSU3.suUmat, Submission.PSU3.J3, Matrix.mul_apply, Fin.sum_univ_three,
        CharTwo.add_self_eq_zero]
  have hSU3 : (psu3StdSU n * Submission.PSU3.suSgM n) ^ 3 = 1 :=
    Subtype.ext hGL3
  have hcube : (psu3Std n * Submission.PSU3.psu3Weyl n) ^ 3 = 1 := by
    have h := congrArg (Submission.PSU3.psu3Hom n) hSU3
    simpa only [map_pow, map_mul, map_one, psu3Std_val, Submission.PSU3.psu3Weyl] using h
  refine ⟨hP1, orderOf_eq_prime hcube ?_⟩
  intro h1
  refine Submission.PSU3.psu3W_notMem_psu3B n ?_
  have hmemB : psu3Std n ∈ Submission.PSU3.psu3B n :=
    Submission.PSU3.psu3U_le_psu3B n (psu3Std_mem n)
  have h2 : Submission.PSU3.psu3W n = (psu3Std n)⁻¹ := by
    rw [Submission.PSU3.psu3W_eq_weyl n]
    exact eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact (Submission.PSU3.psu3B n).inv_mem hmemB

/-- A unit `a ∈ GF(2^(2n))ˣ` with `a^(q+1) = 1` and `a³ ≠ 1` (`q = 2^n`, `n ≥ 2`): take
`a = gen n^(q-1)`, whose `(q+1)`-st power is `gen n^(q²-1) = 1` while `a³ = 1` would force
`q² - 1 ∣ 3(q-1)`, i.e. `q + 1 ∣ 3`, impossible since `q + 1 ≥ 5`. -/
lemma psu3_unit_exists (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : (Submission.PSU3.F n)ˣ, a ^ (2 ^ n + 1) = 1 ∧ a ^ 3 ≠ 1 := by
  refine ⟨Submission.PSU3.gen n ^ (2 ^ n - 1), ?_, ?_⟩
  · rw [← pow_mul, Submission.PSU3.two_pow_sub_one_mul_add_one n,
      ← Submission.PSU3.orderOf_gen n (by omega)]
    exact pow_orderOf_eq_one _
  · intro h
    have h1 : Submission.PSU3.gen n ^ ((2 ^ n - 1) * 3) = 1 := by
      simpa only [pow_mul] using h
    have hdvd : orderOf (Submission.PSU3.gen n) ∣ (2 ^ n - 1) * 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [Submission.PSU3.orderOf_gen n (by omega),
      ← Submission.PSU3.two_pow_sub_one_mul_add_one n] at hdvd
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    refine Nat.not_dvd_of_pos_of_lt (by omega) ?_ hdvd
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)

/-- The `PSU(3,2ⁿ)` "centraliser" clause: some `1 ≠ x ∈ twoPoint B̄ w̄ = T̄` centralises every
involution of `B̄`.  Take `x = psu3Hom (suTgSU n a)` for `a` from `psu3_unit_exists`; the
involutions of `B̄` lie in `Ū` and lift to involutions `u(b,c)` of `SU(3,2ⁿ)` with `b = 0`
(so `u = u(0,c)`), which `t(a)` centralises because `a^(q+1) = 1`. -/
lemma psu3_twoPoint_centralizes (n : ℕ) (hn : 2 ≤ n) :
    ∃ x ∈ Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n),
      x ≠ 1 ∧
      ∀ u ∈ Submission.Blueprint.involutions
        (Submission.PSU3.psu3B n : Set (PSU3Model n)),
        x * u = u * x := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨a, ha1, ha3⟩ := psu3_unit_exists n hn
  have ha1F : (a : Submission.PSU3.F n) ^ (2 ^ n + 1) = 1 := by
    have h := congrArg (fun z : (Submission.PSU3.F n)ˣ => (z : Submission.PSU3.F n)) ha1
    simpa using h
  refine ⟨Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a), ?_, ?_, ?_⟩
  · rw [Work.PSU3.Model.twoPoint_psu3B_psu3Weyl n]
    exact Subgroup.mem_map.mpr
      ⟨Submission.PSU3.suTgSU n a, Submission.PSU3.suTgSU_mem_suTS n a, rfl⟩
  · intro hx
    have hker : Submission.PSU3.suTgSU n a ∈ (Submission.PSU3.psu3Hom n).ker :=
      MonoidHom.mem_ker.mpr hx
    exact ha3 ((Work.Models.ModelData.suTgSU_mem_ker_iff n a).mp hker).2
  · intro u hu
    obtain ⟨huB, hu2⟩ := hu
    have huU : u ∈ Submission.PSU3.psu3U n :=
      Work.Models.Abstract.involutions_subset_U (Submission.PSU3.psu3BenderPair n hn)
        ⟨huB, hu2⟩
    have hu_sq : u * u = 1 := by
      have h := pow_orderOf_eq_one u
      rw [hu2] at h
      simpa [pow_two] using h
    rw [Submission.PSU3.psu3U] at huU
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp huU
    obtain ⟨b, c, _hc, hyb⟩ := Subgroup.mem_subgroupOf.mp hy
    have hy_sq : y * y = 1 := by
      have hker : y * y ∈ (Submission.PSU3.psu3Hom n).ker := by
        rw [MonoidHom.mem_ker, map_mul, hyu, hu_sq]
      have hTS : y * y ∈ Submission.PSU3.suTS n :=
        Submission.PSU3.psu3Hom_ker_le_suTS n hker
      have hmem : y * y ∈ Submission.PSU3.suUS n ⊓ Submission.PSU3.suTS n :=
        ⟨(Submission.PSU3.suUS n).mul_mem hy hy, hTS⟩
      rw [Submission.PSU3.suTS_inf_suUS n] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hb : b = 0 := by
      have hy2 : (Submission.PSU3.suUg n b c) ^ 2 = 1 := by
        have h : ((y : ↥(Submission.PSU3.SU3 n)) : GL (Fin 3) (Submission.PSU3.F n)) *
            ((y : ↥(Submission.PSU3.SU3 n)) : GL (Fin 3) (Submission.PSU3.F n)) = 1 := by
          have h' := congrArg (fun z : ↥(Submission.PSU3.SU3 n) =>
            (z : GL (Fin 3) (Submission.PSU3.F n))) hy_sq
          simpa using h'
        rw [hyb] at h
        rwa [← pow_two] at h
      exact (Submission.PSU3.suUg_sq_eq_one_iff n b c).mp hy2
    have hy_eq : ((y : ↥(Submission.PSU3.SU3 n)) : GL (Fin 3) (Submission.PSU3.F n)) =
        Submission.PSU3.suUg n 0 c := by rw [hyb, hb]
    have hcomm_gl : Submission.PSU3.suTg n a * Submission.PSU3.suUg n 0 c =
        Submission.PSU3.suUg n 0 c * Submission.PSU3.suTg n a := by
      rw [Submission.PSU3.suTg_mul_suUg, mul_zero, zero_mul]
      have hc' : (a : Submission.PSU3.F n) * c * (a : Submission.PSU3.F n) ^ (2 ^ n) = c := by
        rw [show (a : Submission.PSU3.F n) * c * (a : Submission.PSU3.F n) ^ (2 ^ n) =
            (a : Submission.PSU3.F n) ^ (2 ^ n + 1) * c by rw [pow_succ']; ring,
          ha1F, one_mul]
      rw [hc']
    have hcomm_su : Submission.PSU3.suTgSU n a * y = y * Submission.PSU3.suTgSU n a := by
      apply Subtype.ext
      show Submission.PSU3.suTg n a *
          ((y : ↥(Submission.PSU3.SU3 n)) : GL (Fin 3) (Submission.PSU3.F n)) =
        ((y : ↥(Submission.PSU3.SU3 n)) : GL (Fin 3) (Submission.PSU3.F n)) *
          Submission.PSU3.suTg n a
      rw [hy_eq]
      exact hcomm_gl
    calc Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a) * u
        = Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a) *
            Submission.PSU3.psu3Hom n y := by rw [hyu]
      _ = Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a * y) := by rw [map_mul]
      _ = Submission.PSU3.psu3Hom n (y * Submission.PSU3.suTgSU n a) := by rw [hcomm_su]
      _ = u * Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a) := by rw [map_mul, hyu]

end Work.PSU3.BenderST
