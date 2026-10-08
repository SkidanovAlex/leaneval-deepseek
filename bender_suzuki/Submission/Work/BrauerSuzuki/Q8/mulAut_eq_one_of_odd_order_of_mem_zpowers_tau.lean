import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_mem_or
import Submission.Work.BrauerSuzuki.Q8.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Odd order automorphisms of `Q₈` preserving `⟨τ⟩` are trivial

Let `P` be a finite group with a generalized quaternion presentation
`d : GenQuaternionData P` in Dade's normal form (6.1) and `d.n = 2`; thus `P = ⟨τ, ρ⟩` with
`orderOf τ = 4`, `ρ τ ρ⁻¹ = τ⁻¹`, `ρ² = τ²`, i.e. `P ≅ Q₈`.

The automorphism group of `Q₈` is `S₄`, and the stabiliser of the cyclic subgroup `⟨τ⟩`
(a maximal cyclic subgroup) is a `2`-group.  Consequently every automorphism `σ` of `P` of
*odd* order with `σ τ ∈ ⟨τ⟩` is the identity.

The proof is broken into the four elementary computations below:

* `mulAut_fix_tau_of_odd_order` : `σ τ = τ` — `σ τ` has order `4` and lies in `⟨τ⟩`, so it is
  `τ` or `τ⁻¹`; the second alternative is impossible because it forces `σ ^ m τ = τ⁻¹` for the
  odd number `m = orderOf σ`, whereas `σ ^ m = 1`;
* `exists_rho_mul_tau_pow_of_fix_tau` : if `σ τ = τ` then `σ ρ = ρ τ ^ i` for some `i : ℕ` —
  `σ ρ ∉ ⟨τ⟩` (otherwise conjugating `ρ τ ρ⁻¹ = τ⁻¹` by `σ` gives `τ = τ⁻¹`) and every element
  of `P` is `τ ^ k` or `ρ τ ^ i`;
* `mulAut_pow_apply_of_fix` : iterating, `(σ ^ j) ρ = ρ τ ^ (i * j)`;
* `tau_pow_eq_one_of_odd_pow` : `(τ ^ i) ^ m = 1` with `m` odd forces `τ ^ i = 1`, because
  `orderOf (τ ^ i)` divides both `m` and `orderOf τ = 4`.

Combining: `ρ = (σ ^ m) ρ = ρ τ ^ (i m)` with `m = orderOf σ` odd, so `τ ^ i = 1` and
`σ ρ = ρ`; together with `σ τ = τ` (and `P = ⟨τ, ρ⟩`) this gives `σ = 1`.
-/

namespace Work.BrauerSuzuki.Q8

/-- In Dade's normal form with `n = 2`, `tau` has order `4`. -/
private theorem orderOf_tau_eq_four {P : Type*} [Group P] (d : GenQuaternionData P)
    (h2 : d.n = 2) : orderOf d.tau = 4 := by
  rw [d.tau_order, h2]
  norm_num

/-- With `n = 2` we have `orderOf tau = 4`, so `tau ≠ tau⁻¹`. -/
private theorem tau_ne_inv {P : Type*} [Group P] (d : GenQuaternionData P) (h2 : d.n = 2) :
    d.tau ≠ d.tau⁻¹ := by
  intro h
  have hsq : d.tau ^ 2 = 1 := by
    calc d.tau ^ 2 = d.tau * d.tau := by rw [pow_two]
      _ = d.tau * d.tau⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel d.tau
  have hdvd : orderOf d.tau ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
  rw [orderOf_tau_eq_four d h2] at hdvd
  have hle : 4 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- An odd natural number dividing `4` equals `1`. -/
private theorem eq_one_of_odd_of_dvd_four {n : ℕ} (hodd : Odd n) (h4 : n ∣ 4) : n = 1 := by
  have hpos : 0 < n := hodd.pos
  have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  interval_cases n
  · rfl
  · obtain ⟨j, hj⟩ := hodd; omega
  · obtain ⟨c, hc⟩ := h4; omega
  · obtain ⟨j, hj⟩ := hodd; omega

/-- **Step 1.**  An automorphism of odd order mapping `τ` into `⟨τ⟩` fixes `τ`.

`σ τ` has order `4` (`σ` preserves orders) and lies in the cyclic group `⟨τ⟩` of order `4`, so
`σ τ = τ` or `σ τ = τ⁻¹`.  In the second case `σ²` fixes `τ`, hence `σ ^ m τ = τ⁻¹` for the odd
number `m = orderOf σ` (`m = 2k+1`, so `σ ^ m = (σ²)^k σ`), contradicting `σ ^ m = 1`. -/
private theorem mulAut_fix_tau_of_odd_order {P : Type*} [Group P] [Finite P]
    (d : GenQuaternionData P) (h2 : d.n = 2) {σ : MulAut P}
    (hodd : Odd (orderOf σ)) (hfix : σ d.tau ∈ Subgroup.zpowers d.tau) :
    σ d.tau = d.tau := by
  have hτ4 : orderOf d.tau = 4 := orderOf_tau_eq_four d h2
  have hσ4 : orderOf (σ d.tau) = 4 := by
    rw [MulEquiv.orderOf_eq, hτ4]
  rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four hτ4 hfix hσ4 with h | h
  · exact h
  · exfalso
    -- `σ τ = τ⁻¹`, so `σ²` fixes `τ`
    have hσ2 : (σ ^ 2 : MulAut P) d.tau = d.tau := by
      calc (σ ^ 2 : MulAut P) d.tau = σ (σ d.tau) := rfl
        _ = σ d.tau⁻¹ := by rw [h]
        _ = (σ d.tau)⁻¹ := map_inv σ d.tau
        _ = (d.tau⁻¹)⁻¹ := by rw [h]
        _ = d.tau := inv_inv d.tau
    have hσ2pow : ∀ j : ℕ, ((σ ^ 2) ^ j : MulAut P) d.tau = d.tau := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
          rw [pow_succ']
          show (σ ^ 2 : MulAut P) (((σ ^ 2) ^ j : MulAut P) d.tau) = d.tau
          rw [ih, hσ2]
    -- write the odd order `m = orderOf σ` as `2 * k + 1`
    obtain ⟨k, hk⟩ := hodd
    have hstep : (σ ^ (2 * k + 1) : MulAut P) d.tau = d.tau⁻¹ := by
      rw [pow_succ, pow_mul]
      show ((σ ^ 2) ^ k : MulAut P) (σ d.tau) = d.tau⁻¹
      rw [h, map_inv, hσ2pow k]
    have hpow : (σ ^ orderOf σ : MulAut P) d.tau = d.tau := by
      calc (σ ^ orderOf σ : MulAut P) d.tau = (1 : MulAut P) d.tau := by
            rw [pow_orderOf_eq_one]
        _ = d.tau := MulAut.one_apply P d.tau
    have h1 : d.tau = (σ ^ (2 * k + 1) : MulAut P) d.tau := by
      calc d.tau = (σ ^ orderOf σ : MulAut P) d.tau := hpow.symm
        _ = (σ ^ (2 * k + 1) : MulAut P) d.tau := by rw [hk]
    exact tau_ne_inv d h2 (h1.trans hstep)

/-- **Step 2.**  If `σ` fixes `τ`, then `σ ρ = ρ τ ^ i` for some `i : ℕ`.

If `σ ρ` lay in `⟨τ⟩`, conjugating the relation `ρ τ ρ⁻¹ = τ⁻¹` by `σ` and using `σ τ = τ`
would give `σ ρ · τ · (σ ρ)⁻¹ = τ⁻¹` with `σ ρ ∈ ⟨τ⟩`, hence `τ = τ⁻¹`, contradicting
`orderOf τ = 4`.  So `σ ρ ∉ ⟨τ⟩`, and the normal form `genQuaternionData_mem_or` applies. -/
private theorem exists_rho_mul_tau_pow_of_fix_tau {P : Type*} [Group P] [Finite P]
    (d : GenQuaternionData P) (h2 : d.n = 2) {σ : MulAut P}
    (hτ : σ d.tau = d.tau) : ∃ i : ℕ, σ d.rho = d.rho * d.tau ^ i := by
  rcases Quaternion.genQuaternionData_mem_or P d (σ d.rho) with hmem | ⟨i, hi⟩
  · exfalso
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hconj : σ (d.rho * d.tau * d.rho⁻¹) = d.tau := by
      rw [map_mul, map_mul, map_inv, hτ, hk.symm]
      group
    have hinv : σ (d.rho * d.tau * d.rho⁻¹) = d.tau⁻¹ := by
      rw [d.rho_conj, map_inv, hτ]
    exact tau_ne_inv d h2 (hconj.symm.trans hinv)
  · exact ⟨i, hi⟩

/-- **Step 3.**  If `(τ ^ i) ^ m = 1` with `m` odd then `τ ^ i = 1`.

Indeed `orderOf (τ ^ i)` divides `orderOf τ = 4` and divides `m`; being odd it must be `1`. -/
private theorem tau_pow_eq_one_of_odd_pow {P : Type*} [Group P] [Finite P]
    (d : GenQuaternionData P) (h2 : d.n = 2) {i m : ℕ}
    (hm : Odd m) (hp : (d.tau ^ i) ^ m = 1) : d.tau ^ i = 1 := by
  have h4 : orderOf (d.tau ^ i) ∣ 4 := by
    rw [← orderOf_tau_eq_four d h2]
    exact orderOf_pow_dvd i
  have hodd : Odd (orderOf (d.tau ^ i)) :=
    Odd.of_dvd_nat hm (orderOf_dvd_iff_pow_eq_one.mpr hp)
  exact orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_four hodd h4)

/-- **Step 4.**  If `σ` fixes `τ` and `σ ρ = ρ τ ^ i`, then `(σ ^ j) ρ = ρ τ ^ (i * j)` for all
`j : ℕ` (induction on `j`; no commutation between `ρ` and `τ` is needed). -/
private theorem mulAut_pow_apply_of_fix {P : Type*} [Group P] (τ ρ : P) {σ : MulAut P}
    (hτ : σ τ = τ) {i : ℕ} (hρ : σ ρ = ρ * τ ^ i) :
    ∀ j : ℕ, (σ ^ j : MulAut P) ρ = ρ * τ ^ (i * j) := by
  intro j
  induction j with
  | zero =>
      calc ((σ ^ 0) : MulAut P) ρ = ρ := MulAut.one_apply P ρ
        _ = ρ * τ ^ (i * 0) := by rw [Nat.mul_zero, pow_zero, mul_one]
  | succ j ih =>
      rw [pow_succ']
      show σ (((σ ^ j) : MulAut P) ρ) = ρ * τ ^ (i * (j + 1))
      rw [ih, map_mul, map_pow, hρ, hτ]
      rw [mul_assoc, ← pow_add]
      have hexp : i + i * j = i * (j + 1) := by ring
      rw [hexp]

/-- **Odd order automorphisms of `Q₈` preserving `⟨τ⟩` are trivial.**

Writing `m = orderOf σ` (odd), the iterated action formula gives
`ρ = (σ ^ m) ρ = ρ τ ^ (i m)`, hence `(τ ^ i) ^ m = 1`, hence `τ ^ i = 1` (Step 3) and
`σ ρ = ρ τ ^ i = ρ`.  Thus `σ` fixes the generating set `{τ, ρ}` of `P = ⟨τ, ρ⟩`, so `σ = 1`. -/
theorem mulAut_eq_one_of_odd_order_of_mem_zpowers_tau {P : Type*} [Group P] [Finite P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) (h2 : d.n = 2) {σ : MulAut P}
    (hodd : Odd (orderOf σ)) (hfix : σ d.tau ∈ Subgroup.zpowers d.tau) : σ = 1 := by
  have hτ : σ d.tau = d.tau := mulAut_fix_tau_of_odd_order d h2 hodd hfix
  obtain ⟨i, hi⟩ := exists_rho_mul_tau_pow_of_fix_tau d h2 hτ
  have hform : ∀ j : ℕ, (σ ^ j : MulAut P) d.rho = d.rho * d.tau ^ (i * j) :=
    mulAut_pow_apply_of_fix d.tau d.rho hτ hi
  -- `ρ = (σ ^ orderOf σ) ρ = ρ τ ^ (i * orderOf σ)`, hence `(τ ^ i) ^ orderOf σ = 1`
  have hp : (d.tau ^ i) ^ orderOf σ = 1 := by
    have h4 : d.tau ^ (i * orderOf σ) = 1 := by
      have h1 : (σ ^ orderOf σ : MulAut P) d.rho = d.rho * d.tau ^ (i * orderOf σ) :=
        hform (orderOf σ)
      have h2' : (σ ^ orderOf σ : MulAut P) d.rho = d.rho := by
        calc (σ ^ orderOf σ : MulAut P) d.rho = (1 : MulAut P) d.rho := by
              rw [pow_orderOf_eq_one]
          _ = d.rho := MulAut.one_apply P d.rho
      have h3 : d.rho * d.tau ^ (i * orderOf σ) = d.rho := h1 ▸ h2'
      have h5 : d.rho * d.tau ^ (i * orderOf σ) = d.rho * 1 := by
        rw [mul_one]
        exact h3
      exact mul_left_cancel h5
    calc (d.tau ^ i) ^ orderOf σ = d.tau ^ (i * orderOf σ) :=
          (pow_mul d.tau i (orderOf σ)).symm
      _ = 1 := h4
  have hτi : d.tau ^ i = 1 := tau_pow_eq_one_of_odd_pow d h2 hodd hp
  have hρ : σ d.rho = d.rho := by rw [hi, hτi, mul_one]
  -- `σ` fixes both generators of `P`, hence is the identity
  refine MulEquiv.ext (fun x => ?_)
  show σ x = x
  let S : Subgroup P :=
    { carrier := {y : P | σ y = y}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by
        show σ 1 = 1
        exact map_one σ
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha] }
  have hle : Subgroup.closure ({d.tau, d.rho} : Set P) ≤ S := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · change σ d.tau = d.tau
      exact hτ
    · change σ d.rho = d.rho
      exact hρ
  have hxS : x ∈ S := by
    have hx : x ∈ Subgroup.closure ({d.tau, d.rho} : Set P) := by
      rw [d.closure_eq_top]
      exact Subgroup.mem_top x
    exact hle hx
  exact hxS

end Work.BrauerSuzuki.Q8
