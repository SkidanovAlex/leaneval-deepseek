import Mathlib
import Submission.Work.PGroup.Symplectic.exists_notMem_zpowers_pow_mem
import Submission.Work.PGroup.Symplectic.exists_mul_pow_eq_one_of_conj
import Submission.Work.PGroup.Symplectic.exists_pow_eq_one_add_mul_p
import Submission.Work.PGroup.Symplectic.p_pow_pred_dvd_sub_one_of_pow_dvd
import Submission.Work.PGroup.Symplectic.pow_eq_of_conj_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# An element of order `p` outside `⟨c⟩` acting trivially on `c ^ p`

Let `X` be a group, `p` an odd prime, `n ≥ 2`, `R ≤ X` a `p`-subgroup and `c ∈ R` of order
`p ^ n`, such that

* `R` normalizes `⟨c⟩` (`hnormal`),
* the centralizer in `R` of `c` is exactly `⟨c⟩` (`hCen`),
* `R ⊄ ⟨c⟩` (`hne`).

Then there is `y ∈ R ∖ ⟨c⟩` with `y ^ p = 1`, which centralizes `c ^ p` and conjugates `c` to
`c ^ (1 + m * p ^ (n - 1))`.

This is the group-theoretic input to P. Hall's classification of `p`-groups of symplectic type
(Feit–Thompson 3.5, Gorenstein §5.4): it exhibits the "symplectic transvection" `y` acting on the
`c`-coordinate.

The proof picks `x ∈ R ∖ ⟨c⟩` with `x ^ p ∈ ⟨c⟩` (`exists_notMem_zpowers_pow_mem`) and writes
`x⁻¹ * c * x = c ^ k`.  Since `x ^ p` centralizes `c`, `c ^ (k ^ p) = c`, so `p ^ n ∣ k ^ p - 1`;
lifting the exponent (`p_pow_pred_dvd_sub_one_of_pow_dvd`) gives `p ^ (n - 1) ∣ k - 1`, and then
`x` acts on `c` by an automorphism congruent to `1` modulo `p ^ (n - 1)`.  Finally
`exists_mul_pow_eq_one_of_conj` translates `x` to an element of order `p` by an element of `⟨c⟩`.
-/

namespace Work.PGroup.Symplectic

theorem exists_order_p_conj {X : Type*} [Group X] {p n : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hn : 2 ≤ n) {R : Subgroup X} (hR : IsPGroup p ↥R) {c : X} (hcR : c ∈ R)
    (hc : orderOf c = p ^ n)
    (hnormal : ∀ r ∈ R, r⁻¹ * c * r ∈ Subgroup.zpowers c)
    (hCen : ∀ r ∈ R, r⁻¹ * c * r = c → r ∈ Subgroup.zpowers c)
    (hne : ∃ r ∈ R, r ∉ Subgroup.zpowers c) :
    ∃ y ∈ R, y ∉ Subgroup.zpowers c ∧ y ^ p = 1 ∧ y⁻¹ * c ^ p * y = c ^ p ∧
      (∃ m : ℕ, y⁻¹ * c * y = c ^ (1 + m * p ^ (n - 1))) := by
  classical
  obtain ⟨x, hxR, hxK, hxp⟩ := exists_notMem_zpowers_pow_mem hp hR hne
  have hcn : c ^ (p ^ n) = 1 := by
    have h := pow_orderOf_eq_one c
    rwa [hc] at h
  have hfc : IsOfFinOrder c := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨p ^ n, pow_pos hp.pos n, hcn⟩
  -- write `x⁻¹ * c * x = c ^ k`
  obtain ⟨k, hk⟩ := exists_pow_eq_of_mem_zpowers hfc (hnormal x hxR)
  have hconjk : x⁻¹ * c * x = c ^ k := hk.symm
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hk
      have hc1 : c = 1 := by
        calc c = x * (x⁻¹ * c * x) * x⁻¹ := by group
          _ = x * 1 * x⁻¹ := by rw [hk]
          _ = 1 := by group
      have hpn : 1 < p ^ n := Nat.one_lt_pow (by omega) hp.one_lt
      rw [← hc, hc1, orderOf_one] at hpn
      exact absurd hpn (by norm_num)
    · exact hpos
  -- `x ^ p` centralizes `c`, so `c ^ (k ^ p) = c`
  have hxp_conj : (x ^ p)⁻¹ * c * x ^ p = c ^ (k ^ p) := by
    have hint : x⁻¹ * c * x = c ^ (k : ℤ) := by rw [zpow_natCast]; exact hconjk
    have h := conj_pow_eq hint p
    have hcast : (k : ℤ) ^ p = ((k ^ p : ℕ) : ℤ) := by push_cast; ring
    rw [h, hcast, zpow_natCast]
  have hxp_conj2 : (x ^ p)⁻¹ * c * x ^ p = c := by
    obtain ⟨t, ht⟩ := exists_pow_eq_of_mem_zpowers hfc hxp
    rw [← ht]
    group
  have hcpow : c ^ (k ^ p) = c := hxp_conj.symm.trans hxp_conj2
  -- `p ^ n ∣ k ^ p - 1`
  have hdiv : p ^ n ∣ k ^ p - 1 := by
    have hmod : k ^ p ≡ 1 [MOD p ^ n] := by
      have h := (pow_eq_pow_iff_modEq).mp
        (show c ^ (k ^ p) = c ^ 1 by rw [pow_one]; exact hcpow)
      rwa [hc] at h
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow p k (by omega))).mp hmod.symm
  -- lifting the exponent
  have hdiv2 : p ^ (n - 1) ∣ k - 1 := p_pow_pred_dvd_sub_one_of_pow_dvd hp hodd hn hdiv
  obtain ⟨m, hm⟩ := hdiv2
  have hk_eq : k = 1 + m * p ^ (n - 1) := by
    have hm' : k - 1 = m * p ^ (n - 1) := by rw [hm, mul_comm]
    omega
  have hconj : x⁻¹ * c * x = c ^ (1 + m * p ^ (n - 1)) := by
    rw [hconjk, hk_eq]
  -- `p ∤ m`, else `x` would centralize `c`
  have hm' : ¬ p ∣ m := by
    intro hpm
    obtain ⟨j, hj⟩ := hpm
    have hxcx_eq : x⁻¹ * c * x = c := by
      rw [hconjk, hk_eq, hj]
      have h1 : p * p ^ (n - 1) = p ^ n := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
      have hexp : 1 + (p * j) * p ^ (n - 1) = 1 + j * p ^ n := by
        rw [mul_assoc, mul_comm j (p ^ (n - 1)), ← mul_assoc, h1, mul_comm]
      rw [hexp, pow_add, pow_one, show j * p ^ n = p ^ n * j from mul_comm _ _, pow_mul,
        hcn, one_pow, mul_one]
    exact hxK (hCen x hxR hxcx_eq)
  obtain ⟨s, hs1, hs2⟩ := exists_mul_pow_eq_one_of_conj hp hodd hn hc hconj hm' hxp
  refine ⟨x * c ^ s, R.mul_mem hxR (R.pow_mem hcR s), ?_, hs1, ?_, m, hs2⟩
  · -- `x * c ^ s ∉ ⟨c⟩`
    intro hmem
    apply hxK
    have hcs : c ^ s ∈ Subgroup.zpowers c :=
      Subgroup.pow_mem (Subgroup.zpowers c) (Subgroup.mem_zpowers c) s
    have hxeq : x = (x * c ^ s) * (c ^ s)⁻¹ := by group
    rw [hxeq]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hcs)
  · -- `(x * c ^ s)⁻¹ * c ^ p * (x * c ^ s) = c ^ p`
    have h1 : (x * c ^ s)⁻¹ * c ^ p * (x * c ^ s)
        = ((x * c ^ s)⁻¹ * c * (x * c ^ s)) ^ p := by
      simpa using (conj_pow (i := p) (a := (x * c ^ s)⁻¹) (b := c)).symm
    rw [h1, hs2, ← pow_mul]
    have hexp : (1 + m * p ^ (n - 1)) * p = p + m * p ^ n := by
      rw [add_mul, one_mul, mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    rw [hexp, pow_add, show m * p ^ n = p ^ n * m from mul_comm _ _, pow_mul, hcn, one_pow,
      mul_one]

end Work.PGroup.Symplectic
