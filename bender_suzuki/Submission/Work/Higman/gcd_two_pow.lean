import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- If `m` is even then `x + 1` divides `x ^ m - 1`. -/
lemma add_one_dvd_pow_sub_one_of_even (x : ℕ) {m : ℕ} (hm : Even m) : x + 1 ∣ x ^ m - 1 := by
  obtain ⟨s, rfl⟩ := even_iff_two_dvd.mp hm
  have h1 : x + 1 ∣ x ^ 2 - 1 := ⟨x - 1, Nat.sq_sub_sq x 1⟩
  have h2 : x ^ 2 - 1 ∣ (x ^ 2) ^ s - 1 := Nat.sub_one_dvd_pow_sub_one (x ^ 2) s
  rw [pow_mul]
  exact h1.trans h2

/-- If `m` is odd and coprime to `k`, then `gcd m (2 * k) = 1`. -/
lemma gcd_odd_two_mul {m k : ℕ} (hm : Odd m) (h : m.Coprime k) : m.gcd (2 * k) = 1 := by
  have h2 : m.Coprime 2 := Nat.coprime_two_right.mpr hm
  have hmk : m.Coprime (2 * k) := by
    rw [mul_comm]; exact h.mul_right h2
  exact Nat.coprime_iff_gcd_eq_one.mp hmk

/-- `2 ^ n - 1` is odd for `n > 0`. -/
lemma odd_two_pow_sub_one {n : ℕ} (hn : 0 < n) : Odd (2 ^ n - 1) := by
  have he : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, hn.ne'⟩
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  exact Nat.Even.sub_odd (m := 2 ^ n) (n := 1) h1 he odd_one

/-- The transitivity criterion for `A(n,θ)`: with `θ = Frobenius ^ r` on `GF(2ⁿ)`, the
element `λ ^ (1 + 2 ^ r)` generates `F ^ ×` precisely when the order `n / gcd n r` of `θ`
is odd.  Equivalently `gcd (2 ^ n - 1) (2 ^ r + 1) = 1`. -/
theorem gcd_two_pow (n r : ℕ) (hn : 0 < n) :
    (2 ^ n - 1).gcd (2 ^ r + 1) = 1 ↔ Odd (n / n.gcd r) := by
  set d := n.gcd r with hd
  set m := n / d with hm
  set k := r / d with hk
  have hdpos : 0 < d := by rw [hd]; exact Nat.gcd_pos_of_pos_left r hn
  have hnm : d * m = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)
  have hrk : d * k = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)
  have hcop : m.Coprime k := Nat.coprime_div_gcd_div_gcd hdpos
  constructor
  · -- `¬ Odd m` implies the gcd is `≥ 2 ^ d + 1 > 1`.
    intro hg
    by_contra hno
    have hme : Even m := Nat.not_odd_iff_even.mp hno
    -- `k` is odd because `m` is even and coprime to `k`.
    have hkodd : Odd k := by
      rw [← Nat.not_even_iff_odd]
      intro hke
      have h2m : 2 ∣ m := even_iff_two_dvd.mp hme
      have h2k : 2 ∣ k := even_iff_two_dvd.mp hke
      have h2g : 2 ∣ m.gcd k := Nat.dvd_gcd h2m h2k
      rw [Nat.Coprime.gcd_eq_one hcop] at h2g
      exact absurd h2g (by norm_num)
    have hdiv1 : 2 ^ d + 1 ∣ 2 ^ r + 1 := by
      rw [← hrk, pow_mul]
      have := Odd.nat_add_dvd_pow_add_pow (2 ^ d) 1 hkodd
      simpa using this
    have hdiv2 : 2 ^ d + 1 ∣ 2 ^ n - 1 := by
      rw [← hnm, pow_mul]
      exact add_one_dvd_pow_sub_one_of_even (2 ^ d) hme
    have hgpos : 0 < (2 ^ n - 1).gcd (2 ^ r + 1) :=
      Nat.gcd_pos_of_pos_left _ (by
        have h := Nat.one_lt_pow (a := 2) hn.ne' (by norm_num); omega)
    have hle : 2 ^ d + 1 ≤ (2 ^ n - 1).gcd (2 ^ r + 1) :=
      Nat.le_of_dvd hgpos (Nat.dvd_gcd hdiv2 hdiv1)
    have hgt : 1 < 2 ^ d + 1 := by
      have : 1 ≤ 2 ^ d := Nat.one_le_two_pow; omega
    omega
  · -- `Odd m` implies the gcd is `1`.
    intro hom
    set g := (2 ^ n - 1).gcd (2 ^ r + 1) with hgdef
    have hgn : g ∣ 2 ^ n - 1 := by rw [hgdef]; exact Nat.gcd_dvd_left _ _
    have hgr : g ∣ 2 ^ r + 1 := by rw [hgdef]; exact Nat.gcd_dvd_right _ _
    -- `g` divides `2 ^ (2 * r) - 1`.
    have hgr2 : g ∣ 2 ^ (2 * r) - 1 := by
      have h1 : (2 ^ r + 1) ∣ 2 ^ (2 * r) - 1 := by
        refine ⟨2 ^ r - 1, ?_⟩
        have h22 : 2 ^ (2 * r) = (2 ^ r) ^ 2 := by
          rw [show 2 * r = r * 2 by ring, pow_mul]
        rw [h22]; exact Nat.sq_sub_sq (2 ^ r) 1
      exact hgr.trans h1
    -- hence `g ∣ 2 ^ (gcd n (2r)) - 1 = 2 ^ d - 1` (as `m` is odd).
    have hgcd : g ∣ (2 ^ n - 1).gcd (2 ^ (2 * r) - 1) := Nat.dvd_gcd hgn hgr2
    rw [Nat.pow_sub_one_gcd_pow_sub_one 2 n (2 * r)] at hgcd
    have hnd2r : n.gcd (2 * r) = d := by
      rw [← hnm, ← hrk]
      rw [show 2 * (d * k) = d * (2 * k) by ring]
      rw [Nat.gcd_mul_left, gcd_odd_two_mul hom hcop, mul_one]
    rw [hnd2r] at hgcd
    -- `d ∣ r`, so `g ∣ 2 ^ r - 1`; together with `g ∣ 2 ^ r + 1` this gives `g ∣ 2`.
    have hdr : d ∣ r := by rw [hd]; exact Nat.gcd_dvd_right n r
    have hgd : g ∣ 2 ^ r - 1 := hgcd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hdr)
    have hg2 : g ∣ 2 := by
      have hsub : g ∣ (2 ^ r + 1) - (2 ^ r - 1) := Nat.dvd_sub hgr hgd
      have heq : (2 ^ r + 1) - (2 ^ r - 1) = 2 := by
        have := Nat.one_le_two_pow (n := r); omega
      simpa [heq] using hsub
    -- `g ∣ 2` and `g ∣ 2 ^ n - 1` with `2 ^ n - 1` odd forces `g = 1`.
    have hodd : Odd (2 ^ n - 1) := odd_two_pow_sub_one hn
    have hg1 : g ∣ 1 := by
      have h : g ∣ (2 ^ n - 1).gcd 2 := Nat.dvd_gcd hgn hg2
      rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hodd)] at h
    exact Nat.dvd_one.mp hg1

end Work.Higman
