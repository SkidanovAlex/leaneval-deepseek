import Mathlib

/-!
# The sharp Mertens weight `h` for `Σ μ(δ)²/φ(δ)`

We introduce the multiplicative arithmetic function `h` with

`h(p) = 1/(p(p-1))`, `h(p²) = -1/(p(p-1))`, `h(p^j) = 0` for `j ≥ 3`,

realised as `hh n = cw n * μ(n / rad n)`.  This is the function appearing in the
convolution identity `n · μ(n)²/φ(n) = Σ_{e ∣ n} e · h(e)`, which turns the sharp
Mertens-type bound into a harmonic-sum estimate.
-/

open Finset BigOperators

namespace Work.LinnikAreas.Density4

noncomputable section

/-- The local weight `1/(p(p-1))`. -/
noncomputable def cc (p : ℕ) : ℝ := 1 / ((p : ℝ) * ((p : ℝ) - 1))

/-- The radical `∏_{p ∣ n} p`. -/
noncomputable def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The product over prime divisors of `cc`. -/
noncomputable def cw (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, cc p

/-- The multiplicative weight `h` with `h(p^1) = cc p`, `h(p^2) = -cc p`, `h(p^j)=0 (j≥3)`. -/
noncomputable def hh (n : ℕ) : ℝ := cw n * ((ArithmeticFunction.moebius (n / rad n) : ℤ) : ℝ)

lemma cw_nonneg (n : ℕ) : 0 ≤ cw n := by
  apply Finset.prod_nonneg
  intro p hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  simp only [cc]
  apply div_nonneg (by norm_num)
  nlinarith

lemma cw_one : cw 1 = 1 := by simp [cw]

lemma rad_one : rad 1 = 1 := by simp [rad]

lemma hh_zero : hh 0 = 0 := by
  simp [hh, cw, rad]

lemma hh_one : hh 1 = 1 := by
  simp [hh, cw, rad]

lemma hh_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    hh (a * b) = hh a * hh b := by
  have hrad : rad (a*b) = rad a * rad b := by
    rw [rad, rad, rad, Nat.primeFactors_mul ha hb,
      Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab)]
  have hcw : cw (a*b) = cw a * cw b := by
    rw [cw, cw, cw, Nat.primeFactors_mul ha hb,
      Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab)]
  have hda : rad a ∣ a := Nat.prod_primeFactors_dvd a
  have hdb : rad b ∣ b := Nat.prod_primeFactors_dvd b
  have hposa : 0 < rad a := Nat.pos_of_dvd_of_pos hda (Nat.pos_of_ne_zero ha)
  have hposb : 0 < rad b := Nat.pos_of_dvd_of_pos hdb (Nat.pos_of_ne_zero hb)
  have h1 : rad a * (a / rad a) = a := Nat.mul_div_cancel' hda
  have h2 : rad b * (b / rad b) = b := Nat.mul_div_cancel' hdb
  have hdiv : (a*b) / rad (a*b) = (a / rad a) * (b / rad b) := by
    rw [hrad]
    have heq : a * b = ((a / rad a) * (b / rad b)) * (rad a * rad b) := by
      conv_lhs => rw [← h1, ← h2]
      ring
    rw [heq, Nat.mul_div_left _ (Nat.mul_pos hposa hposb)]
  have hcop : Nat.Coprime (a / rad a) (b / rad b) :=
    (hab.coprime_dvd_left (Nat.div_dvd_of_dvd hda)).coprime_dvd_right (Nat.div_dvd_of_dvd hdb)
  rw [hh, hh, hh, hcw, hdiv]
  have hmu : ArithmeticFunction.moebius ((a / rad a) * (b / rad b))
      = ArithmeticFunction.moebius (a / rad a) * ArithmeticFunction.moebius (b / rad b) :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (Nat.coprime_iff_gcd_eq_one.mp hcop)
  rw [hmu]
  push_cast
  ring

lemma hh_prime (p : ℕ) (hp : Nat.Prime p) : hh p = cc p := by
  rw [hh, rad, hp.primeFactors, Finset.prod_singleton, Nat.div_self hp.pos, cw,
    hp.primeFactors, Finset.prod_singleton, ArithmeticFunction.moebius_apply_one]
  norm_num

lemma hh_prime_sq (p : ℕ) (hp : Nat.Prime p) : hh (p^2) = -cc p := by
  have h2 : (2:ℕ) ≠ 0 := by norm_num
  rw [hh, cw, Nat.primeFactors_pow p h2, hp.primeFactors, Finset.prod_singleton, rad,
    Nat.primeFactors_pow p h2, hp.primeFactors, Finset.prod_singleton]
  have hdiv : p^2 / p = p := by rw [pow_two]; exact Nat.mul_div_left p hp.pos
  rw [hdiv, ArithmeticFunction.moebius_apply_prime hp]
  ring

lemma hh_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 3 ≤ k) : hh (p^k) = 0 := by
  have hk0 : k ≠ 0 := by omega
  rw [hh, cw, Nat.primeFactors_pow p hk0, hp.primeFactors, Finset.prod_singleton, rad,
    Nat.primeFactors_pow p hk0, hp.primeFactors, Finset.prod_singleton]
  have hk1 : 1 ≤ k := by omega
  have hdiv : p^k / p = p^(k-1) := by
    simpa using Nat.pow_div (x := p) (m := k) (n := 1) hk1 hp.pos
  rw [hdiv]
  have hmu : ArithmeticFunction.moebius (p^(k-1)) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k - 1 ≠ 0)]
    simp [show k - 1 ≠ 1 by omega]
  rw [hmu]
  simp

/-- On the fibre `rad e = u` (`u` squarefree, `v ∣ u`), the weight factors as `cw u · μ v`. -/
lemma hh_sqfree_dvd (u v : ℕ) (hu : Squarefree u) (hv : v ∣ u) :
    hh (u*v) = cw u * ((ArithmeticFunction.moebius v : ℤ) : ℝ) := by
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := fun h => hu0 (Nat.eq_zero_of_zero_dvd (h ▸ hv))
  have hsub : v.primeFactors ⊆ u.primeFactors := Nat.primeFactors_mono hv hu0
  have hpf : (u*v).primeFactors = u.primeFactors := by
    rw [Nat.primeFactors_mul hu0 hv0, Finset.union_eq_left]
    exact hsub
  have hrad : rad (u*v) = u := by
    rw [rad, hpf]
    exact Nat.prod_primeFactors_of_squarefree hu
  have hcw' : cw (u*v) = cw u := by rw [cw, cw, hpf]
  have hdiv : (u*v)/u = v := Nat.mul_div_right v (Nat.pos_of_ne_zero hu0)
  rw [hh, hcw', hrad, hdiv]

/-- The absolute value bound `|h(n)| ≤ cw n`. -/
lemma abs_hh_le_cw (n : ℕ) : |hh n| ≤ cw n := by
  rw [hh, abs_mul]
  have h1 : |((ArithmeticFunction.moebius (n / rad n) : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    have : |ArithmeticFunction.moebius (n / rad n)| ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or (n / rad n) with h | h | h <;> rw [h] <;> norm_num
    exact_mod_cast this
  calc |cw n| * |((ArithmeticFunction.moebius (n / rad n) : ℤ) : ℝ)| ≤ |cw n| * 1 := by
        apply mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = cw n := by rw [mul_one, abs_of_nonneg (cw_nonneg n)]

end

end Work.LinnikAreas.Density4
