import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

namespace RamAux

noncomputable section

/-- `1 + i` is a prime of `ℤ[i]` (the ramified prime over `2`). -/
theorem prime_oneAddI : Prime (oneAddI : GaussianInt) := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime, irreducible_iff]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (oneAddI : GaussianInt).norm = 1 :=
      (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) _).2 h
    have h2 : (oneAddI : GaussianInt).norm = 2 := by
      rw [Zsqrtd.norm_def]; norm_num [oneAddI]
    omega
  · intro a b hab
    have h2 : (oneAddI : GaussianInt).norm = 2 := by
      rw [Zsqrtd.norm_def]; norm_num [oneAddI]
    have hna : 0 ≤ a.norm := Zsqrtd.norm_nonneg (d := -1) (by norm_num) a
    have hnb : 0 ≤ b.norm := Zsqrtd.norm_nonneg (d := -1) (by norm_num) b
    have hmul : a.norm * b.norm = 2 := by rw [← Zsqrtd.norm_mul, ← hab]; exact h2
    by_cases ha : a.norm = 1
    · exact Or.inl ((Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) a).1 ha)
    · refine Or.inr ((Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) b).1 ?_)
      have ha2 : 2 ≤ a.norm := by
        have ha0 : a.norm ≠ 0 := by intro h0; rw [h0, zero_mul] at hmul; omega
        omega
      have hb0 : b.norm ≠ 0 := by intro h0; rw [h0, mul_zero] at hmul; omega
      have hle : 2 * b.norm ≤ 2 := by
        have := mul_le_mul_of_nonneg_right ha2 hnb
        rwa [hmul] at this
      omega

/-- `z` is coprime to `(1+i)^k` (for `k ≥ 1`) exactly when `1+i` does not divide `z`,
i.e. when `z` is *odd*. -/
theorem isCoprime_oneAddI_pow_iff (z : GaussianInt) {k : ℕ} (hk : 1 ≤ k) :
    IsCoprime z (oneAddI ^ k) ↔ ¬ (oneAddI ∣ z) := by
  constructor
  · intro h
    have h1 : IsCoprime z oneAddI := h.of_isCoprime_of_dvd_right (pow_dvd_pow oneAddI hk)
    exact (Prime.coprime_iff_not_dvd prime_oneAddI).1 h1.symm
  · intro h
    exact ((Prime.coprime_iff_not_dvd prime_oneAddI).2 h).symm.pow_right

/-- `(2 : ℤ[i]) = (1+i)^2·(-i)`. -/
theorem two_eq : ((2 : ℕ) : GaussianInt) = oneAddI ^ 2 * (-(⟨0,1⟩ : GaussianInt)) := by decide

/-- `z` is coprime to the prime power `2^j` (`j ≥ 1`) exactly when `z` is odd. -/
theorem isCoprime_two_pow_iff (z : GaussianInt) {j : ℕ} (hj : 1 ≤ j) :
    IsCoprime z (((2 : ℕ) ^ j : ℕ) : GaussianInt) ↔ ¬ (oneAddI ∣ z) := by
  have h2j : (((2 : ℕ) ^ j : ℕ) : GaussianInt)
      = oneAddI ^ (2*j) * (-(⟨0,1⟩:GaussianInt))^j := by
    rw [Nat.cast_pow, two_eq, mul_pow, ← pow_mul]
  rw [h2j, IsCoprime.mul_right_iff]
  have hunit : IsUnit ((-(⟨0,1⟩ : GaussianInt))^j) := by
    have h1 : IsUnit ((⟨0,1⟩ : GaussianInt)) :=
      (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) _).1
        (by rw [Zsqrtd.norm_def]; norm_num)
    exact h1.neg.pow j
  constructor
  · rintro ⟨h1, _⟩
    exact (isCoprime_oneAddI_pow_iff z (by omega)).1 h1
  · intro h
    exact ⟨(isCoprime_oneAddI_pow_iff z (by omega)).2 h,
      IsCoprime.of_isCoprime_of_dvd_right isCoprime_one_right hunit.dvd⟩

/-- `z` is a unit modulo `4d` (in `ℤ[i]`) exactly when it is coprime to `4d`. -/
theorem isUnitMod4d_iff_isCoprime (d : ℕ) (z : GaussianInt) :
    IsUnitMod4d d z ↔ IsCoprime z (((4 * d : ℕ) : ℤ) : GaussianInt) := by
  constructor
  · rintro ⟨w, c, hc⟩
    exact ⟨w, -c, by linear_combination hc⟩
  · rintro ⟨a, b, hb⟩
    exact ⟨a, -b, by linear_combination hb⟩

/-- Being a unit modulo `4d` is a property of the residue class modulo `4d`. -/
theorem isUnitMod4d_add_dvd (d : ℕ) (z w : GaussianInt)
    (h : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ w) :
    IsUnitMod4d d (z + w) ↔ IsUnitMod4d d z := by
  rw [isUnitMod4d_iff_isCoprime, isUnitMod4d_iff_isCoprime]
  obtain ⟨c, hc⟩ := h
  rw [show z + w = z + (((4 * d : ℕ) : ℤ) : GaussianInt) * c from by rw [hc]]
  exact IsCoprime.add_mul_left_left_iff

/-- **Translation invariance of the units modulo `4d`.**  If `t` is divisible by the odd part
`m = d / 2^(v₂ d)` of `d` and by `1+i`, then the property "`z` is a unit modulo `4d`" is invariant
under translating `z` by `t`.  The proof splits `4d = 2^(k+2)·m` (`k = v₂ d`) and uses that
`z ↦ z` is a unit modulo `2^(k+2)` iff it is coprime to `1+i` (i.e. odd), while `m ∣ t` makes
the coprimality to `m` translation invariant. -/
theorem isUnitMod4d_add_iff (d : ℕ) (hd : 1 ≤ d) (z t : GaussianInt)
    (ht1 : oneAddI ∣ t) (ht2 : ((d / 2 ^ (d.factorization 2) : ℕ) : GaussianInt) ∣ t) :
    IsUnitMod4d d (z + t) ↔ IsUnitMod4d d z := by
  obtain ⟨c1, hc1⟩ := ht1
  obtain ⟨c2, hc2⟩ := ht2
  have hkey : ∀ z : GaussianInt, IsUnitMod4d d z ↔
      (¬ oneAddI ∣ z) ∧ IsCoprime z (((d / 2 ^ (d.factorization 2) : ℕ) : ℤ) : GaussianInt) := by
    intro z
    rw [isUnitMod4d_iff_isCoprime]
    have hdkm : 2 ^ (d.factorization 2) * (d / 2 ^ (d.factorization 2)) = d :=
      Nat.mul_div_cancel' (Nat.ordProj_dvd d 2)
    have hmul : (4*d : ℕ) = 2 ^ ((d.factorization 2)+2) * (d / 2 ^ (d.factorization 2)) := by
      conv_lhs => rw [← hdkm]
      rw [show 4 * (2 ^ (d.factorization 2) * (d / 2 ^ (d.factorization 2)))
          = 2 ^ ((d.factorization 2) + 2) * (d / 2 ^ (d.factorization 2)) from by
        rw [pow_add]; ring]
    have hcast : (((4*d : ℕ) : ℤ) : GaussianInt) =
        (((2 ^ ((d.factorization 2)+2) : ℕ) : ℤ) : GaussianInt) *
          (((d / 2 ^ (d.factorization 2) : ℕ) : ℤ) : GaussianInt) := by
      rw [show (4*d : ℕ) = 2 ^ ((d.factorization 2)+2) * (d / 2 ^ (d.factorization 2)) from hmul]
      simp only [Nat.cast_mul, Int.cast_mul]
    rw [hcast, IsCoprime.mul_right_iff]
    have h2 : (((2 ^ ((d.factorization 2)+2) : ℕ) : ℤ) : GaussianInt) =
        (((2:ℕ) ^ ((d.factorization 2)+2) : ℕ) : GaussianInt) := by simp
    rw [h2, isCoprime_two_pow_iff z (by omega)]
  rw [hkey (z+t), hkey z]
  have htdvd : oneAddI ∣ t := by rw [hc1]; exact dvd_mul_right _ _
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun hz => h1 (dvd_add hz htdvd), by
      rw [show z + t = z + ((d / 2 ^ (d.factorization 2) : ℕ) : GaussianInt) * c2 from by rw [hc2]] at h2
      exact IsCoprime.add_mul_left_left_iff.1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (by
        have : oneAddI ∣ (z + t) - t := dvd_sub h htdvd
        simpa using this),
      by rw [show z + t = z + ((d / 2 ^ (d.factorization 2) : ℕ) : GaussianInt) * c2 from by rw [hc2]]
         exact IsCoprime.add_mul_left_left_iff.2 h2⟩

/-- The Gaussian integer associated with a pair of natural numbers. -/
def zof (a : ℕ × ℕ) : GaussianInt := ⟨(a.1 : ℤ), (a.2 : ℤ)⟩

/-- Translation of a pair by a Gaussian integer `t`, reduced modulo `n`. -/
def shiftMod (n : ℕ) (t : GaussianInt) (a : ℕ × ℕ) : ℕ × ℕ :=
  (((a.1 : ZMod n) + (t.re : ZMod n)).val, ((a.2 : ZMod n) + (t.im : ZMod n)).val)

@[simp] theorem shiftMod_fst (n : ℕ) (t : GaussianInt) (a : ℕ × ℕ) :
    (shiftMod n t a).1 = ((a.1 : ZMod n) + (t.re : ZMod n)).val := rfl

@[simp] theorem shiftMod_snd (n : ℕ) (t : GaussianInt) (a : ℕ × ℕ) :
    (shiftMod n t a).2 = ((a.2 : ZMod n) + (t.im : ZMod n)).val := rfl

theorem shiftMod_mem (n : ℕ) [NeZero n] (t : GaussianInt) (a : ℕ × ℕ) :
    shiftMod n t a ∈ (Finset.range n).product (Finset.range n) := by
  rw [Finset.product_eq_sprod, Finset.mem_product]
  exact ⟨Finset.mem_range.mpr (ZMod.val_lt _), Finset.mem_range.mpr (ZMod.val_lt _)⟩

theorem shiftMod_shiftMod_neg (n : ℕ) [NeZero n] (t : GaussianInt) (a : ℕ × ℕ)
    (h1 : a.1 < n) (h2 : a.2 < n) : shiftMod n t (shiftMod n (-t) a) = a := by
  ext
  · show (shiftMod n t (shiftMod n (-t) a)).1 = a.1
    simp only [shiftMod_fst, ZMod.natCast_zmod_val]
    rw [show (((-t).re : ℤ) : ZMod n) = -(t.re : ZMod n) from by
      rw [Zsqrtd.re_neg]; push_cast; ring]
    have : (a.1 : ZMod n) + -(t.re : ZMod n) + (t.re : ZMod n) = (a.1 : ZMod n) := by ring
    rw [this, ZMod.val_natCast_of_lt h1]
  · show (shiftMod n t (shiftMod n (-t) a)).2 = a.2
    simp only [shiftMod_snd, ZMod.natCast_zmod_val]
    rw [show (((-t).im : ℤ) : ZMod n) = -(t.im : ZMod n) from by
      rw [Zsqrtd.im_neg]; push_cast; ring]
    have : (a.2 : ZMod n) + -(t.im : ZMod n) + (t.im : ZMod n) = (a.2 : ZMod n) := by ring
    rw [this, ZMod.val_natCast_of_lt h2]

theorem dvd_val_add_sub (n : ℕ) [NeZero n] (x : ℕ) (y : ℤ) :
    (n : ℤ) ∣ ((((x : ZMod n) + (y : ZMod n)).val : ℤ)) - ((x : ℤ) + y) := by
  have h : (((((x : ZMod n) + (y : ZMod n)).val : ℤ)) : ZMod n) = (((x : ℤ) + y : ℤ) : ZMod n) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).1 h
  refine ⟨-c, ?_⟩
  rw [show (↑n : ℤ) * (-c) = -((↑n : ℤ) * c) from by ring, ← hc]
  ring

theorem dvd_shiftMod_sub (n : ℕ) [NeZero n] (t : GaussianInt) (a : ℕ × ℕ) :
    ((n : ℤ) : GaussianInt) ∣ zof (shiftMod n t a) - (zof a + t) := by
  rw [Zsqrtd.intCast_dvd]
  constructor
  · show (n : ℤ) ∣ (zof (shiftMod n t a)).re - (zof a + t).re
    rw [show (zof (shiftMod n t a)).re = ((((a.1 : ZMod n) + (t.re : ZMod n)).val : ℤ)) from rfl,
        show (zof a + t).re = ((a.1 : ℤ)) + t.re from rfl]
    exact dvd_val_add_sub n a.1 t.re
  · show (n : ℤ) ∣ (zof (shiftMod n t a)).im - (zof a + t).im
    rw [show (zof (shiftMod n t a)).im = ((((a.2 : ZMod n) + (t.im : ZMod n)).val : ℤ)) from rfl,
        show (zof a + t).im = ((a.2 : ℤ)) + t.im from rfl]
    exact dvd_val_add_sub n a.2 t.im

theorem re_mul_I (z : GaussianInt) : (z * (⟨0,1⟩ : GaussianInt)).re = -z.im := by
  rw [Zsqrtd.re_mul]; ring

/-- The character `z ↦ exp(2πi·Re(z·δ)/(4d))`. -/
def chi (d : ℕ) (δ : GaussianInt) : GaussianInt → ℂ :=
  fun z => Complex.exp (2 * Real.pi * Complex.I * ((((z * δ).re : ℤ) : ℂ) / ((4 * d : ℕ) : ℂ)))

theorem chi_add (d : ℕ) (δ x y : GaussianInt) :
    chi d δ (x + y) = chi d δ x * chi d δ y := by
  unfold chi
  have hre : ((x + y) * δ).re = (x * δ).re + (y * δ).re := by rw [add_mul, Zsqrtd.re_add]
  rw [hre, Int.cast_add]
  rw [show 2 * ↑Real.pi * Complex.I * ((↑(x * δ).re + ↑(y * δ).re) / ↑(4 * d))
      = 2 * ↑Real.pi * Complex.I * (↑(x * δ).re / ↑(4 * d))
        + 2 * ↑Real.pi * Complex.I * (↑(y * δ).re / ↑(4 * d)) from by ring]
  rw [Complex.exp_add]

theorem exp_int_two_pi_I (n : ℤ) : Complex.exp (↑n * (2 * ↑Real.pi * Complex.I)) = 1 := by
  rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I]
  simp

theorem chi_add_nat (d : ℕ) (hd : 1 ≤ d) (δ z w : GaussianInt) :
    chi d δ (z + ((4 * d : ℕ) : GaussianInt) * w) = chi d δ z := by
  unfold chi
  have hre : ((z + ((4 * d : ℕ) : GaussianInt) * w) * δ).re
      = (z * δ).re + (4 * d : ℕ) * (w * δ).re := by
    rw [add_mul, Zsqrtd.re_add]
    congr 1
    rw [mul_assoc, Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]
    ring
  rw [hre]
  have hd' : (↑d : ℂ) ≠ 0 := by simp only [Nat.cast_ne_zero]; omega
  have h1 : Complex.exp (2 * ↑Real.pi * Complex.I * (↑((z * δ).re + (4 * d : ℕ) * (w * δ).re) / ↑(4 * d)))
      = Complex.exp (2 * ↑Real.pi * Complex.I * (↑((z * δ).re) / ↑(4 * d))) *
        Complex.exp (↑((w * δ).re) * (2 * ↑Real.pi * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  rw [h1, exp_int_two_pi_I, mul_one]

/-- `chi` only depends on `z` modulo `4d`. -/
theorem chi_congr (d : ℕ) (hd : 1 ≤ d) (δ : GaussianInt) {z z' : GaussianInt}
    (h : ((4 * d : ℕ) : GaussianInt) ∣ z - z') : chi d δ z = chi d δ z' := by
  obtain ⟨w, hw⟩ := h
  have : z = z' + ((4 * d : ℕ) : GaussianInt) * w := by rw [← hw]; ring
  rw [this, chi_add_nat d hd δ z' w]

theorem exp_two_pi_I_mul_eq_one_iff (x : ℂ) :
    Complex.exp (2 * ↑Real.pi * Complex.I * x) = 1 ↔ ∃ n : ℤ, x = n := by
  rw [Complex.exp_eq_one_iff]
  have h2pi : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 := by
    simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, mul_left_cancel₀ h2pi (by rw [hn]; ring)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

theorem chi_eq_one_iff (d : ℕ) (hd : 1 ≤ d) (δ z : GaussianInt) :
    chi d δ z = 1 ↔ ((4 * d : ℕ) : ℤ) ∣ (z * δ).re := by
  rw [chi, exp_two_pi_I_mul_eq_one_iff]
  have hN : (↑(4 * d : ℕ) : ℂ) ≠ 0 := by
    simp only [Nat.cast_ne_zero]; omega
  constructor
  · rintro ⟨n, hn⟩
    rw [div_eq_iff hN] at hn
    refine ⟨n, ?_⟩
    have h' : (z * δ).re = n * ((4 * d : ℕ) : ℤ) := by exact_mod_cast hn
    rw [h', mul_comm]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn, Int.cast_mul]
    have hc : ((↑((4 * d : ℕ) : ℤ) : ℂ)) = ((4 * d : ℕ) : ℂ) := by simp
    rw [hc, mul_div_cancel_left₀ _ hN]

end

end RamAux

open RamAux

end Work.FIArea5.S16Hecke
