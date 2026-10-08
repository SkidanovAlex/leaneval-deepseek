import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.TwoGroup
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.PSL2Model
import Submission.Work.Models.Port.PSL2SylowConj
import Submission.Work.Models.Port.PSU3.Unipotent
import Submission.Work.Models.Port.PSU3.Simple
import Submission.Work.Models.Port.PSU3SylowConj
import Submission.Work.Models.Port.PSU3.Borel
import Submission.Work.Models.Port.PSU3.Main
import Submission.Work.Models.Port.SzSylowConj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.PSU3.StageA

/-- An odd natural number is not divisible by `2`. -/
lemma not_two_dvd_of_odd {n : ℕ} (h : Odd n) : ¬ 2 ∣ n := by
  intro hd
  rcases h with ⟨k, hk⟩
  obtain ⟨m, hm⟩ := hd
  omega

/-- The Suzuki 2-group `Sz(2^(2n+1))` is not abelian (`n ≥ 1`). -/
lemma szTwoGroupS_not_abelian (n : ℕ) (hn : 1 ≤ n) :
    ∃ x ∈ Submission.Sz.szTwoGroupS n, ∃ y ∈ Submission.Sz.szTwoGroupS n, x * y ≠ y * x := by
  obtain ⟨x, hx⟩ := Commons.FieldTheory.FiniteField.exists_pow_two_pow_ne_self n hn
  set A : SzModel n :=
    ⟨Submission.Sz.szUg n x 0, Submission.Sz.szUg_mem_szModel n x 0⟩ with hA
  set B : SzModel n :=
    ⟨Submission.Sz.szUg n 1 0, Submission.Sz.szUg_mem_szModel n 1 0⟩ with hB
  have hAmem : A ∈ Submission.Sz.szTwoGroupS n :=
    Subgroup.mem_subgroupOf.mpr ⟨x, 0, rfl⟩
  have hBmem : B ∈ Submission.Sz.szTwoGroupS n :=
    Subgroup.mem_subgroupOf.mpr ⟨1, 0, rfl⟩
  refine ⟨A, hAmem, B, hBmem, ?_⟩
  intro hcon
  have h2 : Submission.Sz.szUg n x 0 * Submission.Sz.szUg n 1 0 =
      Submission.Sz.szUg n 1 0 * Submission.Sz.szUg n x 0 :=
    congrArg Subtype.val hcon
  rw [Submission.Sz.szUg_mul, Submission.Sz.szUg_mul] at h2
  have h2' : Submission.Sz.szUg n (x + 1) x =
      Submission.Sz.szUg n (1 + x) (1 * x ^ 2 ^ (n + 1)) := by
    simpa only [zero_add, one_pow, mul_one] using h2
  have h3 : ((x + 1, x) : Submission.Sz.SzField n × Submission.Sz.SzField n) =
      (1 + x, 1 * x ^ 2 ^ (n + 1)) := by
    apply Submission.Sz.szUg_injective n
    exact h2'
  have h4 := (Prod.ext_iff.mp h3).2
  exact hx (by simpa using h4.symm)

/-- For `n ≥ 1`, `2 ^ (2 * n) - 1` does not divide `2 ^ n - 1`. -/
lemma not_dvd_two_pow_sub_one (n : ℕ) (hn : 1 ≤ n) : ¬ (2 ^ (2 * n) - 1) ∣ (2 ^ n - 1) := by
  intro hdvd
  have h2le : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpos : 0 < 2 ^ n - 1 := by omega
  have hle : 2 ^ (2 * n) - 1 ≤ 2 ^ n - 1 := Nat.le_of_dvd hpos hdvd
  have h2n : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [h2n] at hle
  have hle2 : (2 ^ n) ^ 2 ≤ 2 ^ n := by omega
  nlinarith [hle2, h2le]

/-- For `n ≥ 2`, `2 ^ (2 * n) - 1` does not divide `2 ^ n + 1`. -/
lemma not_dvd_two_pow_add_one (n : ℕ) (hn : 2 ≤ n) : ¬ (2 ^ (2 * n) - 1) ∣ (2 ^ n + 1) := by
  intro hdvd
  have h4le : 4 ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpos : 0 < 2 ^ n + 1 := by omega
  have hle : 2 ^ (2 * n) - 1 ≤ 2 ^ n + 1 := Nat.le_of_dvd hpos hdvd
  have h2n : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [h2n] at hle
  have hle2 : (2 ^ n) ^ 2 ≤ 2 ^ n + 2 := by omega
  nlinarith [hle2, h4le]

/-- Conjugation of `u(0,c)` by the torus element `t(gen n)`, at the level of `GL`. -/
lemma suTg_conj_gen_gl (n : ℕ) (c : Submission.PSU3.F n) :
    Submission.PSU3.suTg n (Submission.PSU3.gen n) * Submission.PSU3.suUg n 0 c *
        (Submission.PSU3.suTg n (Submission.PSU3.gen n))⁻¹ =
      Submission.PSU3.suUg n 0 (c * (Submission.PSU3.gen n : Submission.PSU3.F n) ^ 2 ^ n *
        (Submission.PSU3.gen n : Submission.PSU3.F n)) := by
  rw [Submission.PSU3.suTg_conj_suUg]
  congr 1
  all_goals ring

/-- The Sylow `2`-subgroup of `PSU(3,2^n)` is not abelian (`n ≥ 2`). -/
lemma psu3U_not_abelian (n : ℕ) (hn : 2 ≤ n) :
    ∃ x ∈ Submission.PSU3.psu3U n, ∃ y ∈ Submission.PSU3.psu3U n, x * y ≠ y * x := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  set a : Submission.PSU3.F n := (Submission.PSU3.gen n : Submission.PSU3.F n) with hadef
  have haq : a ^ 2 ^ n ≠ a := by
    intro hcon
    have h3 : (Submission.PSU3.gen n) ^ (2 ^ n) = Submission.PSU3.gen n := by
      apply Units.ext
      rw [← hadef]
      exact hcon
    have h4 : (Submission.PSU3.gen n) ^ (2 ^ n - 1) = 1 := by
      have h5 : (Submission.PSU3.gen n) ^ (2 ^ n - 1) * Submission.PSU3.gen n =
          Submission.PSU3.gen n := by
        rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, h3]
      exact mul_right_cancel (by rw [h5, one_mul])
    have hdvd : orderOf (Submission.PSU3.gen n) ∣ 2 ^ n - 1 :=
      orderOf_dvd_iff_pow_eq_one.mpr h4
    rw [Submission.PSU3.orderOf_gen n hn0] at hdvd
    exact not_dvd_two_pow_sub_one n hn1 hdvd
  have ha1 : (Submission.PSU3.gen n) ^ (2 ^ n + 1) ≠ 1 := by
    intro h1
    have hdvd : orderOf (Submission.PSU3.gen n) ∣ (2 ^ n + 1) :=
      orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [Submission.PSU3.orderOf_gen n hn0] at hdvd
    exact not_dvd_two_pow_add_one n hn hdvd
  have hc0 : a + a ^ 2 ^ n ≠ 0 := by
    intro hc
    exact haq (by
      have h := add_eq_zero_iff_eq_neg.mp hc
      simpa [CharTwo.neg_eq] using h.symm)
  have hc0fix : (a + a ^ 2 ^ n) ^ 2 ^ n = a + a ^ 2 ^ n := by
    rw [add_pow_char_pow, ← pow_mul, Submission.PSU3.sq_pow, hadef,
      Submission.PSU3.pow_card_eq_self n hn0]
    rw [add_comm]
  set c1 : Submission.PSU3.F n := Submission.PSU3.suCb n hn1 1 with hc1def
  have hc1 : c1 + c1 ^ 2 ^ n = (1 : Submission.PSU3.F n) ^ (2 ^ n + 1) :=
    Submission.PSU3.suCb_spec n hn1 1
  set c2 : Submission.PSU3.F n := Submission.PSU3.suCb n hn1 a with hc2def
  have hc2 : c2 + c2 ^ 2 ^ n = a ^ (2 ^ n + 1) := Submission.PSU3.suCb_spec n hn1 a
  set X : ↥(Submission.PSU3.SU3 n) :=
    ⟨Submission.PSU3.suUg n 1 c1, Submission.PSU3.suUg_isSU3 n 1 c1 hc1⟩ with hX
  set Y : ↥(Submission.PSU3.SU3 n) :=
    ⟨Submission.PSU3.suUg n a c2, Submission.PSU3.suUg_isSU3 n a c2 hc2⟩ with hY
  have hXU : X ∈ (Submission.PSU3.suU n).subgroupOf (Submission.PSU3.SU3 n) :=
    Subgroup.mem_subgroupOf.mpr ⟨1, c1, hc1, rfl⟩
  have hYU : Y ∈ (Submission.PSU3.suU n).subgroupOf (Submission.PSU3.SU3 n) :=
    Subgroup.mem_subgroupOf.mpr ⟨a, c2, hc2, rfl⟩
  refine ⟨Submission.PSU3.psu3Hom n X, Subgroup.mem_map.mpr ⟨X, hXU, rfl⟩,
    Submission.PSU3.psu3Hom n Y, Subgroup.mem_map.mpr ⟨Y, hYU, rfl⟩, ?_⟩
  intro hcon
  have hker : X * Y * (Y * X)⁻¹ ∈ (Submission.PSU3.psu3Hom n).ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [hcon, mul_inv_cancel]
  have hwmem : Submission.PSU3.suUg n 0 (a + a ^ 2 ^ n) ∈ Submission.PSU3.SU3 n :=
    Submission.PSU3.suUg_isSU3 n 0 _ (by
      rw [zero_pow (show 2 ^ n + 1 ≠ 0 by positivity), hc0fix, CharTwo.add_self_eq_zero])
  have hwval : X * Y * (Y * X)⁻¹ =
      (⟨Submission.PSU3.suUg n 0 (a + a ^ 2 ^ n), hwmem⟩ : ↥(Submission.PSU3.SU3 n)) := by
    apply Subtype.ext
    rw [hX, hY]
    show Submission.PSU3.suUg n 1 c1 * Submission.PSU3.suUg n a c2 *
        (Submission.PSU3.suUg n a c2 * Submission.PSU3.suUg n 1 c1)⁻¹ =
      Submission.PSU3.suUg n 0 (a + a ^ 2 ^ n)
    rw [Submission.PSU3.suUg_mul, Submission.PSU3.suUg_mul, ← Submission.PSU3.suUg_inv,
      Submission.PSU3.suUg_mul]
    congr 1
    · rw [add_assoc, ← add_assoc a a 1, CharTwo.add_self_eq_zero a, zero_add,
        CharTwo.add_self_eq_zero (1 : Submission.PSU3.F n)]
    · rw [show a + 1 = 1 + a from by rw [add_comm], pow_succ,
        mul_comm ((1 + a) ^ 2 ^ n) (1 + a)]
      rw [show (1 : Submission.PSU3.F n) * a ^ 2 ^ n = a ^ 2 ^ n from by rw [one_mul]]
      rw [show a * (1 : Submission.PSU3.F n) ^ 2 ^ n = a from by rw [one_pow, mul_one]]
      rw [show (c1 + c2 + a ^ 2 ^ n) +
            (c2 + c1 + a + (1 + a) * (1 + a) ^ 2 ^ n) +
            (1 + a) * (1 + a) ^ 2 ^ n =
          (c1 + c1) + (c2 + c2) + (a ^ 2 ^ n + a) +
            ((1 + a) * (1 + a) ^ 2 ^ n + (1 + a) * (1 + a) ^ 2 ^ n) from by abel]
      rw [CharTwo.add_self_eq_zero c1, CharTwo.add_self_eq_zero c2, zero_add, zero_add,
        CharTwo.add_self_eq_zero ((1 + a) * (1 + a) ^ 2 ^ n), add_zero, add_comm]
  have hwcent : X * Y * (Y * X)⁻¹ ∈ Subgroup.center ↥(Submission.PSU3.SU3 n) :=
    Submission.PSU3.psu3Hom_ker_le_center n hker
  set T : ↥(Submission.PSU3.SU3 n) :=
    ⟨Submission.PSU3.suTg n (Submission.PSU3.gen n),
      Submission.PSU3.suTg_isSU3 n (Submission.PSU3.gen n)⟩ with hT
  have hcen : T * (X * Y * (Y * X)⁻¹) = (X * Y * (Y * X)⁻¹) * T :=
    Subgroup.mem_center_iff.mp hwcent T
  have hwGL : ((X * Y * (Y * X)⁻¹ : ↥(Submission.PSU3.SU3 n)) :
      GL (Fin 3) (Submission.PSU3.F n)) = Submission.PSU3.suUg n 0 (a + a ^ 2 ^ n) := by
    rw [hwval]
  have hTGL : (T : GL (Fin 3) (Submission.PSU3.F n)) =
      Submission.PSU3.suTg n (Submission.PSU3.gen n) := by
    rw [hT]
  have hcomm' : (T : GL (Fin 3) (Submission.PSU3.F n)) *
      ((X * Y * (Y * X)⁻¹ : ↥(Submission.PSU3.SU3 n)) : GL (Fin 3) (Submission.PSU3.F n)) =
      ((X * Y * (Y * X)⁻¹ : ↥(Submission.PSU3.SU3 n)) : GL (Fin 3) (Submission.PSU3.F n)) *
      (T : GL (Fin 3) (Submission.PSU3.F n)) := congrArg Subtype.val hcen
  rw [hTGL, hwGL] at hcomm'
  have h2 : Submission.PSU3.suTg n (Submission.PSU3.gen n) *
      Submission.PSU3.suUg n 0 (a + a ^ 2 ^ n) *
      (Submission.PSU3.suTg n (Submission.PSU3.gen n))⁻¹ =
      Submission.PSU3.suUg n 0 (a + a ^ 2 ^ n) := by
    rw [hcomm', mul_assoc, mul_inv_cancel, mul_one]
  rw [suTg_conj_gen_gl] at h2
  have hpair : ((0 : Submission.PSU3.F n),
      (a + a ^ 2 ^ n) * (Submission.PSU3.gen n : Submission.PSU3.F n) ^ 2 ^ n *
        (Submission.PSU3.gen n : Submission.PSU3.F n)) =
      ((0 : Submission.PSU3.F n), a + a ^ 2 ^ n) := by
    apply Submission.PSU3.suUg_injective n
    exact h2
  have hcoord := (Prod.ext_iff.mp hpair).2
  have hfact : (a + a ^ 2 ^ n) * (a * a ^ 2 ^ n) = (a + a ^ 2 ^ n) * 1 := by
    rw [mul_one, mul_comm a (a ^ 2 ^ n)]
    simpa only [hadef, mul_assoc] using hcoord
  have hgen : a * a ^ 2 ^ n = 1 := mul_left_cancel₀ hc0 hfact
  have hgen' : a ^ (2 ^ n + 1) = 1 := by
    simpa only [pow_succ', mul_comm] using hgen
  refine ha1 (Units.ext ?_)
  rw [Units.val_pow_eq_pow_val, ← hadef, Units.val_one]
  exact hgen'

/-- The image of an odd-index `2`-subgroup `T ≤ Y` under an isomorphism `e : Y ≃* M` is
conjugate (in `M`) to any given Sylow `2`-subgroup `S` of `M`. -/
lemma map_eq_conj_sylow {Y M : Type} [Group Y] [Group M] [Finite Y] [Finite M]
    (e : Y ≃* M) {T : Subgroup Y} (hTp : IsPGroup 2 T) (hTodd : Odd T.index)
    (S : Sylow 2 M) :
    ∃ g : M, T.map (e : Y →* M) = (S : Subgroup M).map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap_p : IsPGroup 2 (T.map (e : Y →* M)) := hTp.map (e : Y →* M)
  have hmap_odd : Odd (T.map (e : Y →* M)).index := by
    rw [Subgroup.index_map_equiv T e]; exact hTodd
  let W : Sylow 2 M := hmap_p.toSylow (not_two_dvd_of_odd hmap_odd)
  have hWcoe : (W : Subgroup M) = T.map (e : Y →* M) :=
    IsPGroup.toSylow_coe hmap_p (not_two_dvd_of_odd hmap_odd)
  haveI : MulAction.IsPretransitive M (Sylow 2 M) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := M) S W
  refine ⟨g, ?_⟩
  have h1 : ((g • S : Sylow 2 M) : Subgroup M) = W :=
    congrArg (fun P : Sylow 2 M => (P : Subgroup M)) hg
  rw [Sylow.coe_subgroup_smul, hWcoe] at h1
  rw [← h1]
  rfl

/-- If `A = g B g⁻¹` and `B` is elementary abelian then so is `A`. -/
lemma sq_one_of_map_eq_conj {G : Type} [Group G] {A B : Subgroup G} {g : G}
    (h : A = B.map (MulAut.conj g).toMonoidHom) (hB : ∀ x ∈ B, x * x = 1) :
    ∀ x ∈ A, x * x = 1 := by
  intro x hx
  rw [h] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [← map_mul, hB y hy, map_one]

/-- A conjugate of a non-abelian subgroup is non-abelian. -/
lemma exists_nc_pair_of_map_eq_conj {G : Type} [Group G] {A B : Subgroup G} {g : G}
    (h : A = B.map (MulAut.conj g).toMonoidHom) (hB : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) :
    ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hB
  refine ⟨(MulAut.conj g) x, ?_, (MulAut.conj g) y, ?_, ?_⟩
  · rw [h]; exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  · rw [h]; exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  · intro hcon
    exact hxy ((MulAut.conj g).injective (by simpa only [map_mul] using hcon))

/-- **Model fact.** In a simple Bender group `Y` (i.e. `PSL(2,2ⁿ)`, `Sz(2^{2n+1})` or
`PSU(3,2ⁿ)`) an abelian `2`-subgroup `T` of odd index — equivalently, an abelian Sylow
`2`-subgroup — is elementary abelian.

The three model families give: the Sylow `2`-subgroup of `PSL(2,2ⁿ)` is elementary abelian
(of order `2ⁿ`), while those of `Sz(2^{2n+1})` (order `2^{4n+2}`) and `PSU(3,2ⁿ)` (order
`2^{3n}`) are non-abelian; all Sylow `2`-subgroups are conjugate. -/
theorem abelian_sylow_two_sq_one {Y : Type} [Group Y] [Finite Y]
    (hY : IsSimpleBenderGroup Y) {T : Subgroup Y} (hTp : IsPGroup 2 T) (hTodd : Odd T.index)
    (hab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) : ∀ x ∈ T, x * x = 1 := by
  classical
  cases hY with
  | isPSL2 n hn e =>
      obtain ⟨S, -, hSsq⟩ := Submission.PSL2Model_exists_sylow_two_elementaryAbelian n (by omega)
      have hSsq' : ∀ x ∈ (S : Subgroup (PSL2Model n)), x * x = 1 := by
        intro x hx
        have h := hSsq ⟨x, hx⟩
        have h2 : (x : PSL2Model n) ^ 2 = 1 :=
          congrArg (fun z : ↥(S : Subgroup (PSL2Model n)) => (z : PSL2Model n)) h
        simpa [pow_two] using h2
      obtain ⟨g, hconj⟩ := map_eq_conj_sylow e hTp hTodd S
      have hmap_sq : ∀ x ∈ T.map (e : Y →* PSL2Model n), x * x = 1 :=
        sq_one_of_map_eq_conj hconj hSsq'
      intro x hx
      refine e.injective ?_
      have h := hmap_sq (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      simpa using h
  | isSuzuki n hn e =>
      have hnc : ∃ x ∈ (Submission.Sz.szSylow n : Subgroup (SzModel n)),
          ∃ y ∈ (Submission.Sz.szSylow n : Subgroup (SzModel n)), x * y ≠ y * x := by
        simpa only [Submission.Sz.szSylow_coe_sub] using szTwoGroupS_not_abelian n hn
      obtain ⟨g, hconj⟩ := map_eq_conj_sylow e hTp hTodd (Submission.Sz.szSylow n)
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_nc_pair_of_map_eq_conj hconj hnc
      obtain ⟨x₀, hx₀, hx₀e⟩ := Subgroup.mem_map.mp hx
      obtain ⟨y₀, hy₀, hy₀e⟩ := Subgroup.mem_map.mp hy
      have hx₀' : e x₀ = x := hx₀e
      have hy₀' : e y₀ = y := hy₀e
      exfalso
      exact hxy (by
        calc x * y = e x₀ * e y₀ := by rw [hx₀', hy₀']
          _ = e (x₀ * y₀) := (map_mul (e : Y →* SzModel n) x₀ y₀).symm
          _ = e (y₀ * x₀) := by rw [hab x₀ hx₀ y₀ hy₀]
          _ = e y₀ * e x₀ := map_mul (e : Y →* SzModel n) y₀ x₀
          _ = y * x := by rw [hy₀', hx₀'])
  | isPSU3 n hn e =>
      have hn1 : 1 ≤ n := by omega
      have hU2 : IsPGroup 2 ↥(Submission.PSU3.psu3U n) := Submission.PSU3.isPGroup_psu3U n hn1
      have hUnd : ¬ 2 ∣ (Submission.PSU3.psu3U n).index :=
        Submission.PSU3.not_dvd_index_psu3U n hn
      let S₀ : Sylow 2 (PSU3Model n) := hU2.toSylow hUnd
      have hS₀coe : (S₀ : Subgroup (PSU3Model n)) = Submission.PSU3.psu3U n :=
        IsPGroup.toSylow_coe hU2 hUnd
      have hnc : ∃ x ∈ (S₀ : Subgroup (PSU3Model n)),
          ∃ y ∈ (S₀ : Subgroup (PSU3Model n)), x * y ≠ y * x := by
        simpa only [hS₀coe] using psu3U_not_abelian n hn
      obtain ⟨g, hconj⟩ := map_eq_conj_sylow e hTp hTodd S₀
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_nc_pair_of_map_eq_conj hconj hnc
      obtain ⟨x₀, hx₀, hx₀e⟩ := Subgroup.mem_map.mp hx
      obtain ⟨y₀, hy₀, hy₀e⟩ := Subgroup.mem_map.mp hy
      have hx₀' : e x₀ = x := hx₀e
      have hy₀' : e y₀ = y := hy₀e
      exfalso
      exact hxy (by
        calc x * y = e x₀ * e y₀ := by rw [hx₀', hy₀']
          _ = e (x₀ * y₀) := (map_mul (e : Y →* PSU3Model n) x₀ y₀).symm
          _ = e (y₀ * x₀) := by rw [hab x₀ hx₀ y₀ hy₀]
          _ = e y₀ * e x₀ := map_mul (e : Y →* PSU3Model n) y₀ x₀
          _ = y * x := by rw [hy₀', hx₀'])

end Work.PSU3.StageA
