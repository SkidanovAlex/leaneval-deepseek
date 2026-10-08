import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Prove

open Finset

/-- Fermat's little theorem step: for a prime `p`, `p ∣ l ^ p - 1` forces `l ≡ 1 [ZMOD p]`. -/
lemma prime_dvd_sub_one_of_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) {l : ℤ}
    (h : (p : ℤ) ∣ l ^ p - 1) : (p : ℤ) ∣ l - 1 := by
  have h1 : ((l ^ p - 1 : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h
  have he : ((l : ZMod p)) ^ p = 1 := by
    have hh := h1
    push_cast at hh
    exact sub_eq_zero.mp hh
  have h2 : (l : ZMod p) = 1 := by
    have hp' := @ZMod.pow_card p ⟨hp⟩ (l : ZMod p)
    rw [he] at hp'
    exact hp'.symm
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  show ((l - 1 : ℤ) : ZMod p) = 0
  push_cast
  rw [h2]
  ring

/-- **A `p`-adic geometric-sum lemma.**

Let `p` be an odd prime and `l ≡ 1 [ZMOD p]`.  Put `S = ∑_{i < p} l ^ i`.  Then `v_p(S) = 1`:
explicitly `S = p * s` with `p ∤ s` (one has `S ≡ p [ZMOD p ^ 2]`).  Hence, if in addition
`p ^ m ∣ l ^ p - 1` (so that, by Fermat, `p ∣ l - 1`) and `p ^ m ∣ k * S`, then
`p ^ m ∣ k * (l - 1)`.  Indeed `p ^ m ∣ k * S` and `S = p * s`, `p ∤ s` give `p ^ (m-1) ∣ k`,
which together with `p ∣ l - 1` yields `p ^ m ∣ k * (l - 1)`. -/
theorem geomSumPadic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m)
    {l k : ℤ} (hl : (p : ℤ) ^ m ∣ l ^ p - 1)
    (hk : (p : ℤ) ^ m ∣ k * ∑ i ∈ Finset.range p, l ^ i) :
    (p : ℤ) ^ m ∣ k * (l - 1) := by
  have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hodd : Odd p := hp.odd_of_ne_two hp2
  -- From `p ^ m ∣ l ^ p - 1` deduce `p ∣ l - 1` (Fermat).
  have hl1 : (p : ℤ) ∣ l ^ p - 1 := by
    have : (p : ℤ) ^ 1 ∣ l ^ p - 1 := (pow_dvd_pow (p : ℤ) hm).trans hl
    simpa using this
  have hpl1 : (p : ℤ) ∣ l - 1 := prime_dvd_sub_one_of_dvd_pow_sub_one hp hl1
  have hlp : ¬ (p : ℤ) ∣ l := by
    intro h
    have hh : (p : ℤ) ∣ l - (l - 1) := dvd_sub h hpl1
    have h1 : (p : ℤ) ∣ (1 : ℤ) := by
      have : l - (l - 1) = (1 : ℤ) := by ring
      rwa [this] at hh
    exact hpint.not_isUnit (isUnit_iff_dvd_one.mpr h1)
  -- Lifting-the-exponent style fact: `v_p (∑ l ^ i) = 1`.
  have hS : emultiplicity (p : ℤ) (∑ i ∈ Finset.range p, l ^ i) = 1 := by
    have h := emultiplicity_geom_sum₂_eq_one (R := ℤ) hpint hodd hpl1 hlp
    simpa using h
  -- `p ^ m ∣ k * S` gives `m ≤ v_p k + 1 ≤ v_p k + v_p (l - 1) = v_p (k * (l - 1))`.
  have hk' : (↑m : ℕ∞) ≤ emultiplicity (p : ℤ) k + 1 := by
    have h0 := le_emultiplicity_of_pow_dvd hk
    rwa [emultiplicity_mul hpint, hS] at h0
  have hl1e : (↑(1 : ℕ) : ℕ∞) ≤ emultiplicity (p : ℤ) (l - 1) := by
    apply le_emultiplicity_of_pow_dvd
    rwa [pow_one]
  have hfin : (↑m : ℕ∞) ≤ emultiplicity (p : ℤ) (k * (l - 1)) := by
    rw [emultiplicity_mul hpint]
    calc (↑m : ℕ∞) ≤ emultiplicity (p : ℤ) k + 1 := hk'
      _ ≤ emultiplicity (p : ℤ) k + emultiplicity (p : ℤ) (l - 1) := add_le_add le_rfl hl1e
  exact pow_dvd_of_le_emultiplicity hfin

end Work.ThmF.Prove
