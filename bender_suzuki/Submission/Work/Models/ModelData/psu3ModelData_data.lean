import Mathlib
import ChallengeDeps
import Submission.Work.Models.Abstract.ModelData
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Port.PSU3.Main
import Submission.Work.Models.Port.PSU3.Involutions
import Submission.Work.Models.Port.PSU3.Centralizer
import Submission.Work.Models.Port.PSU3.WeylQuotient
import Submission.Work.Models.Port.PSU3.Torus
import Submission.Work.Models.Abstract.ncard_involutions_B
import Submission.Work.Models.Port.Commons.GroupTheory.involutions_card_eq_of_surjective_centralOddKer
import Submission.Work.Models.Port.SuzukiSetup
import Submission.Work.Models.Port.Commons.FieldTheory.Finite.fixed_card_pow_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option autoImplicit false

open Matrix LeanEval.GroupTheory.Defs

namespace Work.Models.ModelData

open Submission.PSU3

/-! ## `μ_{q-1} = {a ∈ F^× | a^(q-1) = 1}` -/

noncomputable def suTm1 (n : ℕ) : Subgroup (F n)ˣ where
  carrier := {a | a ^ (2 ^ n - 1) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [inv_pow, ha, inv_one]

lemma card_suTm1 (n : ℕ) (hn : 1 ≤ n) : Nat.card ↥(suTm1 n) = 2 ^ n - 1 := by
  haveI : Fintype (F n) := Fintype.ofFinite _
  have h : Nat.card ↥(suTm1 n) = Nat.card {a : (F n)ˣ // a ^ (2 ^ n - 1) = 1} := rfl
  rw [h, Commons.FieldTheory.Finite.fixedPowTwo.card_units_pow_eq_one_gcd (K := F n) (2 ^ n - 1),
    Nat.card_units, GaloisField.card 2 (2 * n) (by omega)]
  exact Commons.FieldTheory.Finite.fixedPowTwo.gcd_two_pow_sub n

/-! ## `K₀` -/

noncomputable def psu3K (n : ℕ) : Subgroup (PSU3Model n) :=
  ((suTm1 n).map (suTgSU n)).map (psu3Hom n)

lemma psu3T_iff (n : ℕ) (x : PSU3Model n) :
    x ∈ psu3T n ↔ ∃ a : (F n)ˣ, psu3Hom n (suTgSU n a) = x := by
  rw [psu3T, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [suTS, Subgroup.mem_subgroupOf] at hy
    obtain ⟨a, ha⟩ := hy
    refine ⟨a, ?_⟩
    have hya : suTgSU n a = y := Subtype.ext ha.symm
    rw [hya, hyx]
  · rintro ⟨a, rfl⟩
    exact ⟨suTgSU n a, Subgroup.mem_subgroupOf.mpr ⟨a, rfl⟩, rfl⟩

lemma psu3Weyl_conj_suT (n : ℕ) (a : (F n)ˣ) :
    psu3Weyl n * psu3Hom n (suTgSU n a) * (psu3Weyl n)⁻¹
      = psu3Hom n (suTgSU n ((a ^ (2 ^ n))⁻¹)) := by
  show psu3Hom n (suSgM n) * psu3Hom n (suTgSU n a) * (psu3Hom n (suSgM n))⁻¹
      = psu3Hom n (suTgSU n ((a ^ (2 ^ n))⁻¹))
  rw [← map_inv, ← map_mul, ← map_mul, suSgM_conj_suTgSU]

/-! ## The kernel of `SU(3,2ⁿ) → PSU(3,2ⁿ)` intersected with the torus -/

/-- `suTgSU b` lies in the kernel of the projection iff `b^(q+1) = b^3 = 1`, i.e. iff the
diagonal matrix `diag(b, b^(q-1), b^(-q))` is a scalar matrix of `SU(3,2ⁿ)`. -/
lemma suTgSU_mem_ker_iff (n : ℕ) (b : (F n)ˣ) :
    suTgSU n b ∈ (psu3Hom n).ker ↔ b ^ (2 ^ n + 1) = 1 ∧ b ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hb
    have hc : ((suTgSU n b : ↥(SU3 n)) : GL (Fin 3) (F n)) ∈
        Subgroup.center (GL (Fin 3) (F n)) := by
      have h := hb
      rw [psu3Hom_ker_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h
      exact h.2
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨lam, hlam⟩ := MonoidHom.mem_range.mp hc
    have hmat : (Matrix.scalar (Fin 3) (lam : F n)) = suTmat n b := by
      have h := congrArg (fun z : GL (Fin 3) (F n) =>
        ((z : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n))) hlam
      simpa [Matrix.GeneralLinearGroup.coe_scalar, suTg_coe] using h
    have hlamu : lam = b := by
      have h00 := congrFun (congrFun hmat 0) 0
      refine Units.ext ?_
      simpa [Matrix.scalar_apply, suTmat, Matrix.diagonal_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons] using h00
    have hSU : IsSU3 (Matrix.GeneralLinearGroup.scalar (Fin 3) lam) := by
      rw [hlam]; exact (suTgSU n b).2
    obtain ⟨hq, h3⟩ := (isSU3_scalar_iff n lam).mp hSU
    rw [hlamu] at hq h3
    exact ⟨hq, h3⟩
  · rintro ⟨hq, h3⟩
    obtain ⟨hp, hqi⟩ := unit_pow_identities n b hq h3
    have hpF : (↑b : F n) ^ (2 ^ n - 1) = ↑b := by
      rw [← Units.val_pow_eq_pow_val, hp]
    have hqiF : (↑b : F n) ^ (2 ^ n) = (↑b)⁻¹ := by
      rw [← Units.val_pow_eq_pow_val, hqi, Units.val_inv_eq_inv_val]
    have hscalar : suTg n b = Matrix.GeneralLinearGroup.scalar (Fin 3) b := by
      apply Units.ext
      rw [suTg_coe, Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [suTmat, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
          hpF, hqiF]
    rw [psu3Hom_ker_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨(suTgSU n b).2, ?_⟩
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact MonoidHom.mem_range.mpr ⟨b, hscalar.symm⟩

/-! ## The two inclusions identifying `K₀` -/

lemma psu3K_subset_invertedBy (n : ℕ) :
    (psu3K n : Set (PSU3Model n)) ⊆
      Submission.Blueprint.invertedBy (psu3T n) (psu3Weyl n) := by
  intro x hx
  rw [SetLike.mem_coe] at hx
  rw [psu3K, Subgroup.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [Subgroup.mem_map] at hy
  obtain ⟨a, ha, hay⟩ := hy
  have ha' : a ^ (2 ^ n - 1) = 1 := ha
  have hpow : a ^ (2 ^ n) = a := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    calc a ^ (2 ^ n) = a ^ ((2 ^ n - 1) + 1) := by rw [Nat.sub_add_cancel h1]
      _ = a ^ (2 ^ n - 1) * a := by rw [pow_add, pow_one]
      _ = 1 * a := by rw [ha']
      _ = a := one_mul a
  have hxa : x = psu3Hom n (suTgSU n a) := by rw [← hyx, hay]
  refine ⟨?_, ?_⟩
  · rw [psu3T_iff]
    exact ⟨a, hxa.symm⟩
  · rw [hxa, psu3Weyl_conj_suT, show (a ^ (2 ^ n))⁻¹ = a⁻¹ by rw [hpow]]
    simp

lemma invertedBy_subset_psu3K (n : ℕ) (hn : 1 ≤ n) :
    Submission.Blueprint.invertedBy (psu3T n) (psu3Weyl n) ⊆
      (psu3K n : Set (PSU3Model n)) := by
  intro x hx
  obtain ⟨hxT, hconj⟩ := hx
  obtain ⟨a, ha⟩ := (psu3T_iff n x).mp hxT
  have h1 : psu3Hom n (suTgSU n ((a ^ 2 ^ n)⁻¹)) = psu3Hom n (suTgSU n a⁻¹) := by
    have h := hconj
    rw [← ha, psu3Weyl_conj_suT] at h
    rw [← map_inv (psu3Hom n), ← map_inv (suTgSU n)] at h
    exact h
  set u : (F n)ˣ := (a ^ 2 ^ n)⁻¹ * a with hu
  have hker : psu3Hom n (suTgSU n u) = 1 := by
    rw [hu]
    have e1 : psu3Hom n (suTgSU n ((a ^ 2 ^ n)⁻¹ * a))
        = psu3Hom n (suTgSU n ((a ^ 2 ^ n)⁻¹)) * psu3Hom n (suTgSU n a) := by
      rw [map_mul (suTgSU n), map_mul (psu3Hom n)]
    rw [e1, h1, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  obtain ⟨hq, h3⟩ := suTgSU_mem_ker_iff n u |>.mp (MonoidHom.mem_ker.mpr hker)
  have hu2 : u ^ (2 ^ n - 2) = 1 := by
    have hX : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hq' : u ^ (2 ^ n - 2) * u ^ 3 = u ^ (2 ^ n + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [h3, mul_one] at hq'
    exact hq'.trans hq
  have hca : (a * u) ^ (2 ^ n - 1) = 1 := by
    have h1u : a ^ (2 ^ n - 1) = u⁻¹ := by
      rw [hu, pow_sub a (Nat.one_le_two_pow : 1 ≤ 2 ^ n), _root_.mul_inv_rev, _root_.inv_inv,
        pow_one, mul_comm (a ^ (2 ^ n)) a⁻¹]
    have hle : 1 ≤ 2 ^ n - 1 := by
      have hX : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have h3u : u⁻¹ * u ^ (2 ^ n - 1) = 1 := by
      have hp : u ^ (2 ^ n - 2) = u ^ (2 ^ n - 1) * u⁻¹ := by
        have h := pow_sub u (m := 2 ^ n - 1) (n := 1) hle
        rw [pow_one] at h
        rw [Nat.sub_sub] at h
        exact h
      rw [mul_comm u⁻¹ (u ^ (2 ^ n - 1)), ← hp]
      exact hu2
    rw [mul_pow, h1u, h3u]
  refine Subgroup.mem_map.mpr ⟨suTgSU n (a * u), ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨a * u, hca, rfl⟩
  · have e1 : psu3Hom n (suTgSU n (a * u))
        = psu3Hom n (suTgSU n a) * psu3Hom n (suTgSU n u) := by
      rw [map_mul (suTgSU n), map_mul (psu3Hom n)]
    rw [e1, hker, mul_one, ← ha]

lemma coe_psu3K (n : ℕ) (hn : 1 ≤ n) :
    (psu3K n : Set (PSU3Model n)) =
      Submission.Blueprint.invertedBy (psu3T n) (psu3Weyl n) :=
  Set.Subset.antisymm (psu3K_subset_invertedBy n) (invertedBy_subset_psu3K n hn)

/-! ## `K₀` is cyclic of order `2ⁿ - 1` -/

lemma card_psu3K (n : ℕ) (hn : 1 ≤ n) : Nat.card ↥(psu3K n) = 2 ^ n - 1 := by
  have hbot : ((suTm1 n).map (suTgSU n)) ⊓ (psu3Hom n).ker = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    rw [Subgroup.mem_map] at hy1
    obtain ⟨a, ha, hay⟩ := hy1
    have ha' : a ^ (2 ^ n - 1) = 1 := ha
    have hyser : suTgSU n a ∈ (psu3Hom n).ker := by rw [hay]; exact hy2
    obtain ⟨hq, h3⟩ := (suTgSU_mem_ker_iff n a).mp hyser
    have ha2 : a ^ 2 = 1 := by
      have hX : (2 ^ n - 1) + 2 = 2 ^ n + 1 := by
        have h2 : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega
      have h : a ^ (2 ^ n - 1) * a ^ 2 = a ^ (2 ^ n + 1) := by rw [← pow_add, hX]
      rw [ha', one_mul, hq] at h
      exact h
    have hodd : Odd (2 ^ n - 1) := odd_two_pow_sub_one n hn
    obtain ⟨k, hk⟩ := hodd
    have ha1 : a = 1 := by
      have h : a ^ (2 ^ n - 1) = a := by
        rw [hk, pow_succ', pow_mul a 2 k, ha2]
        simp
      exact h.symm.trans ha'
    rw [← hay, ha1, map_one]
  have hcardA : Nat.card ↥((suTm1 n).map (suTgSU n)) = Nat.card ↥(suTm1 n) :=
    Subgroup.card_map_of_injective (suTgSU_injective n)
  have hmain := Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker (psu3Hom n)
    (psu3Hom_surjective n) ((suTm1 n).map (suTgSU n))
  rw [← psu3K, hbot, Subgroup.card_bot, mul_one, hcardA, card_suTm1 n hn] at hmain
  exact hmain

lemma isCyclic_psu3K (n : ℕ) : IsCyclic ↥(psu3K n) := by
  refine isCyclic_of_surjective
    ((((psu3Hom n).comp (suTgSU n)).comp (suTm1 n).subtype).codRestrict (psu3K n)
      (fun x => Subgroup.mem_map.mpr
        ⟨suTgSU n x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩, rfl⟩)) ?_
  intro y
  obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp y.2
  rw [Subgroup.mem_map] at hy'
  obtain ⟨a, ha, hay⟩ := hy'
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  show psu3Hom n (suTgSU n a) = (y : PSU3Model n)
  rw [hay, hyy]

/-! ## The torus is abelian and the Weyl element is an involution -/

lemma suTS_comm (n : ℕ) : ∀ x ∈ suTS n, ∀ y ∈ suTS n, x * y = y * x := by
  intro x hx y hy
  rw [suTS, Subgroup.mem_subgroupOf] at hx hy
  obtain ⟨α, hα⟩ := hx
  obtain ⟨β, hβ⟩ := hy
  apply Subtype.ext
  show ((x : ↥(SU3 n)) : GL (Fin 3) (F n)) * ((y : ↥(SU3 n)) : GL (Fin 3) (F n))
      = ((y : ↥(SU3 n)) : GL (Fin 3) (F n)) * ((x : ↥(SU3 n)) : GL (Fin 3) (F n))
  rw [hα, hβ, suTg_mul, suTg_mul, mul_comm α β]

lemma psu3T_comm (n : ℕ) : ∀ x ∈ psu3T n, ∀ y ∈ psu3T n, x * y = y * x := by
  intro x hx y hy
  rw [psu3T, Subgroup.mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [← map_mul, ← map_mul, suTS_comm n a ha b hb]

lemma psu3Weyl_mul_self (n : ℕ) : psu3Weyl n * psu3Weyl n = 1 := by
  show psu3Hom n (suSgM n) * psu3Hom n (suSgM n) = 1
  rw [← map_mul, suSgM_mul_self, map_one]

/-! ## Involutions of the unipotent radical are central -/

lemma suUg_zero_central (n : ℕ) (γ b' c' : F n) :
    suUg n 0 γ * suUg n b' c' = suUg n b' c' * suUg n 0 γ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, suUg_coe, suUg_coe,
    suUmat, suUmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

lemma suUS_involution_central (n : ℕ) {a : ↥(SU3 n)} (ha : a ∈ suUS n) (haa : a * a = 1) :
    ∀ b ∈ suUS n, a * b = b * a := by
  intro b hb
  obtain ⟨β, γ, -, hβγ⟩ := Subgroup.mem_subgroupOf.mp ha
  obtain ⟨β', γ', -, hβ'γ'⟩ := Subgroup.mem_subgroupOf.mp hb
  have haa' : (suUg n β γ) ^ 2 = 1 := by
    have h := congrArg (fun z : ↥(SU3 n) => (z : GL (Fin 3) (F n))) haa
    simp only [Subgroup.coe_mul, Subgroup.coe_one] at h
    rw [hβγ] at h
    simpa [pow_two] using h
  have hβ0 : β = 0 := (suUg_sq_eq_one_iff n β γ).mp haa'
  apply Subtype.ext
  show ((a : ↥(SU3 n)) : GL (Fin 3) (F n)) * ((b : ↥(SU3 n)) : GL (Fin 3) (F n))
      = ((b : ↥(SU3 n)) : GL (Fin 3) (F n)) * ((a : ↥(SU3 n)) : GL (Fin 3) (F n))
  rw [hβγ, hβ'γ', hβ0, suUg_zero_central n γ β' γ']

lemma psu3U_inv_central (n : ℕ) (hn : 1 ≤ n) :
    ∀ u ∈ psu3U n, u * u = 1 → ∀ v ∈ psu3U n, u * v = v * u := by
  intro u hu huu v hv
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hv
  have haa : a * a = 1 := by
    have hker : a * a ∈ (psu3Hom n).ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact huu
    have hmemU : a * a ∈ suUS n := (suUS n).mul_mem ha ha
    have hbot : (psu3Hom n).ker ⊓ suUS n = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      have : y ∈ suTS n ⊓ suUS n := ⟨psu3Hom_ker_le_suTS n hy1, hy2⟩
      rw [inf_comm, suTS_inf_suUS n, Subgroup.mem_bot] at this
      exact this
    have : a * a ∈ (psu3Hom n).ker ⊓ suUS n := ⟨hker, hmemU⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rw [← map_mul, ← map_mul, suUS_involution_central n ha haa b hb]

/-! ## Involutions of the Borel subgroup -/

lemma ncard_involutions_psu3B (n : ℕ) (hn : 2 ≤ n) :
    (Submission.Blueprint.involutions (psu3B n : Set (PSU3Model n))).ncard = 2 ^ n - 1 := by
  have hn1 : 1 ≤ n := by omega
  rw [show (Submission.Blueprint.involutions (psu3B n : Set (PSU3Model n))).ncard
      = Nat.card {t : ↥(psu3B n) // orderOf t = 2}
    from Work.Models.Abstract.ncard_involutions_eq_subtype (psu3BenderPair n hn)]
  let φ : ↥(suBS n) →* ↥(psu3B n) :=
    ((psu3Hom n).comp (suBS n).subtype).codRestrict (psu3B n)
      (fun x => Subgroup.mem_map.mpr ⟨(x : ↥(SU3 n)), x.2, rfl⟩)
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have hcent : (MonoidHom.ker φ) ≤ Subgroup.center ↥(suBS n) := by
    intro x hx
    have hx1 : (x : ↥(SU3 n)) ∈ (psu3Hom n).ker :=
      MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
    have hxc : (x : ↥(SU3 n)) ∈ Subgroup.center ↥(SU3 n) := psu3Hom_ker_le_center n hx1
    rw [Subgroup.mem_center_iff] at hxc ⊢
    intro y
    apply Subtype.ext
    exact hxc (y : ↥(SU3 n))
  have hodd : Odd (Nat.card (MonoidHom.ker φ)) := by
    have hker_eq : MonoidHom.ker φ = (psu3Hom n).ker.subgroupOf (suBS n) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (psu3Hom_ker_le_borel n)).toEquiv]
    exact odd_card_psu3Hom_ker n hn1
  rw [← Commons.GroupTheory.involutions_card_eq_of_surjective_centralOddKer φ hsurj hcent hodd]
  exact card_orderOf_eq_two_suBS n hn1

theorem psu3ModelData_data (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (Work.Models.ModelData (LeanEval.GroupTheory.Defs.PSU3Model n)) := by
  have hn1 : 1 ≤ n := by omega
  refine ⟨{ psu3BenderPair n hn with
    K0 := psu3K n
    hTab := psu3T_comm n
    hww := psu3Weyl_mul_self n
    hK0 := coe_psu3K n hn1
    hK0cyc := isCyclic_psu3K n
    hK0card := by
      rw [card_psu3K n hn1]
      exact (ncard_involutions_psu3B n hn).symm
    hK0two := by
      rw [card_psu3K n hn1]
      have h3 : 3 ≤ 2 ^ n := by
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    hUinv := psu3U_inv_central n hn1 }⟩

end Work.Models.ModelData
