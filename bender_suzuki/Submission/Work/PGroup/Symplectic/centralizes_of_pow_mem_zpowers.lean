import Mathlib
import Submission.Work.PGroup.Symplectic.pow_eq_of_conj_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup.Symplectic

open scoped commutatorElement

theorem centralizes_of_pow_mem_zpowers {X : Type*} [Group X] {p n m : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (hn : 3 ≤ n) {c y z : X} (hc : orderOf c = p ^ n) (hy : y ^ p = 1)
    (hconj : y⁻¹ * c * y = c ^ (1 + m * p ^ (n - 1)))
    (hz : z ^ p ∈ Subgroup.zpowers (c ^ (p ^ (n - 1))))
    (hzc : ⁅z, c⁆ = 1) (hzy : ⁅z, y⁆ = 1)
    {i j : ℕ} (hpow : (z * (c ^ i * y ^ j)) ^ p = 1) :
    y * (z * (c ^ i * y ^ j)) = z * (c ^ i * y ^ j) * y := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  -- `z` commutes with both `c` and `y`
  have hzy' : Commute z y := commutatorElement_eq_one_iff_commute.mp hzy
  have hzc' : Commute z c := commutatorElement_eq_one_iff_commute.mp hzc
  have hzb : Commute z (c ^ i * y ^ j) :=
    (hzc'.pow_right i).mul_right (hzy'.pow_right j)
  -- the `p`-th power map on `⟨c, y⟩`
  have hbp : (c ^ i * y ^ j) ^ p = c ^ (i * p) := by
    have h1 := Work.PGroup.Symplectic.pow_eq_of_conj_eq hp hodd hn2 hc hconj i j
    have hyj : y ^ (j * p) = 1 := by rw [mul_comm, pow_mul, hy, one_pow]
    rw [h1, hyj, mul_one]
  -- hence `z ^ p * c ^ (i * p) = 1`
  have hstep : z ^ p * c ^ (i * p) = 1 := by
    have hh := hpow
    rw [hzb.mul_pow p, hbp] at hh
    exact hh
  -- so `c ^ (i * p) = (z ^ p)⁻¹` lies in `⟨c ^ (p ^ (n-1))⟩`
  have hmem : c ^ (i * p) ∈ Subgroup.zpowers (c ^ (p ^ (n - 1))) := by
    have hci : c ^ (i * p) = (z ^ p)⁻¹ := by
      calc c ^ (i * p) = (z ^ p)⁻¹ * (z ^ p * c ^ (i * p)) := by group
        _ = (z ^ p)⁻¹ * 1 := by rw [hstep]
        _ = (z ^ p)⁻¹ := by rw [mul_one]
    rw [hci]
    exact Subgroup.inv_mem _ hz
  -- the generator `c ^ (p ^ (n-1))` has `p`-th power `1`
  have hgpow : (c ^ (p ^ (n - 1))) ^ p = 1 := by
    rw [← pow_mul, show p ^ (n - 1) * p = p ^ n by rw [← pow_succ, Nat.sub_add_cancel hn1],
      ← hc, pow_orderOf_eq_one]
  -- hence every element of `⟨c ^ (p ^ (n-1))⟩` has `p`-th power `1`
  have hcip : (c ^ (i * p)) ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgpow, one_zpow]
  -- therefore `p ^ n ∣ i * p ^ 2`
  have hdvd : p ^ n ∣ i * p * p := by
    have h2 : c ^ (i * p * p) = 1 := by rw [pow_mul]; exact hcip
    have h3 := (orderOf_dvd_iff_pow_eq_one).mpr h2
    rwa [hc] at h3
  -- and `p ∣ i`
  have hp_dvd_i : p ∣ i := by
    have hpp : p ^ n = p ^ (n - 2) * p ^ 2 := by rw [← pow_add]; congr 1; omega
    have hd : p ^ (n - 2) * p ^ 2 ∣ i * p ^ 2 := by
      rw [← hpp]
      have hh : i * p * p = i * p ^ 2 := by ring
      rwa [hh] at hdvd
    have h4 := (Nat.mul_dvd_mul_iff_right (pow_pos hp.pos 2)).mp hd
    exact dvd_trans (dvd_pow_self p (by omega : n - 2 ≠ 0)) h4
  -- conjugation by `y` sends `c ^ i` to `c ^ i`, because `p ∣ i`
  have hconjpow : y⁻¹ * c ^ i * y = c ^ ((1 + m * p ^ (n - 1)) * i) := by
    have h1 : (y⁻¹ * c * y) ^ i = y⁻¹ * c ^ i * y := by
      simpa using (conj_pow (a := y⁻¹) (b := c) (i := i))
    rw [← h1, hconj, pow_mul]
  have hmain : y⁻¹ * c ^ i * y = c ^ i := by
    rw [hconjpow]
    have hexp : (1 + m * p ^ (n - 1)) * i = i + m * p ^ (n - 1) * i := by ring
    rw [hexp, pow_add]
    have hzero : c ^ (m * p ^ (n - 1) * i) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hc]
      obtain ⟨i', rfl⟩ := hp_dvd_i
      have hp1 : p ^ (n - 1) * p = p ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn1]
      rw [show m * p ^ (n - 1) * (p * i') = p ^ n * (m * i') by rw [← hp1]; ring]
      exact dvd_mul_right _ _
    rw [hzero, mul_one]
  -- so `y` commutes with `c ^ i`, and with `z`, hence with `z * (c ^ i * y ^ j)`
  have hyci : Commute y (c ^ i) := by
    have h : c ^ i * y = y * c ^ i := by
      calc c ^ i * y = y * (y⁻¹ * c ^ i * y) := by group
        _ = y * c ^ i := by rw [hmain]
    exact h.symm
  have hybz : Commute y (z * (c ^ i * y ^ j)) :=
    hzy'.symm.mul_right (hyci.mul_right ((Commute.refl y).pow_right j))
  exact hybz.eq

end Work.PGroup.Symplectic
