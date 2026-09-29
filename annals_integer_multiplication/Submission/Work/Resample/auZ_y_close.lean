import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Fx.expStepErr

/-!
# Closeness of the fixed-point exponent `auZ` to `π N/(α²t²)`

`auZ p α t N = ⌊2^{auPrec p}·π·N / (α²t²)⌋` is the fixed-point representative of the exponent
`π N/(α²t²)` of the Gaussian weight.  Its guard `hg` (`auZ ≤ (p+10)·2^{auPrec p}`) says that the
exponent is below `p+10`; this module deduces (i) that the exact exponent `π N/(α²t²)` is at most
`p+12` and (ii) that the fixed-point value is within `(p+13)/2^{auPrec p}` of the exact exponent.

The proof is pure real arithmetic on the two error sources: the truncating division (error `< 1`
at scale `2^{auPrec p}`) and the π-approximation `hpi` (error `≤ 1` at the same scale).
-/

set_option autoImplicit false

namespace Work.Resample

/-- Growth of the working precision: `p + 16 ≤ 2·2^{auPrec p}`. -/
theorem pow_two_auPrec_ge (p : ℕ) (hp : 100 ≤ p) : (p : ℝ) + 16 ≤ 2 * (2 : ℝ) ^ (auPrec p) := by
  have hN : p + 16 ≤ 2 * 2 ^ (auPrec p) := by
    rw [two_mul]
    have h1 : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self (n := p))
    have h2 : 16 ≤ 2 ^ p := by
      have h4 : 4 ≤ p := by omega
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h4
    have h3 : 2 ^ p ≤ 2 ^ (auPrec p) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [auPrec]; omega)
    omega
  exact_mod_cast hN

/-- Abstract ratio bound.  If `Z` bounds from below the truncated quantity `(2^P π - 1) Q - 1`
and from above the guard `(p+10)·2^P`, then `π Q ≤ p + 12`. -/
theorem ratio_le_of_guard (p : ℕ) (Q Z : ℝ)
    (hT : (p : ℝ) + 16 ≤ 2 * (2 : ℝ) ^ (auPrec p)) (hQ : 0 ≤ Q)
    (hZ : Z ≤ ((p : ℝ) + 10) * (2 : ℝ) ^ (auPrec p))
    (hZlow : (2 : ℝ) ^ (auPrec p) * Real.pi * Q - Q - 1 ≤ Z) :
    Real.pi * Q ≤ (p : ℝ) + 12 := by
  have hTpos : (0 : ℝ) < (2 : ℝ) ^ (auPrec p) := by nlinarith only [hT]
  have hTpi : (0 : ℝ) < (2 : ℝ) ^ (auPrec p) * Real.pi - 1 := by
    nlinarith only [hT, Real.pi_gt_three]
  have h1 : ((2 : ℝ) ^ (auPrec p) * Real.pi - 1) * Q
      ≤ ((p : ℝ) + 10) * (2 : ℝ) ^ (auPrec p) + 1 := by
    nlinarith only [hZlow, hZ]
  have h2 : Real.pi * (((p : ℝ) + 10) * (2 : ℝ) ^ (auPrec p) + 1)
      ≤ ((2 : ℝ) ^ (auPrec p) * Real.pi - 1) * ((p : ℝ) + 12) := by
    nlinarith only [hT, Real.pi_gt_three, Real.pi_lt_four]
  have h4 : Real.pi * (((2 : ℝ) ^ (auPrec p) * Real.pi - 1) * Q)
      ≤ Real.pi * (((p : ℝ) + 10) * (2 : ℝ) ^ (auPrec p) + 1) :=
    mul_le_mul_of_nonneg_left h1 (by linarith only [Real.pi_gt_three])
  have h3 : ((2 : ℝ) ^ (auPrec p) * Real.pi - 1) * (Real.pi * Q)
      ≤ ((2 : ℝ) ^ (auPrec p) * Real.pi - 1) * ((p : ℝ) + 12) := by
    nlinarith only [h4, h2]
  exact le_of_mul_le_mul_left h3 hTpi

/-- Abstract error bound: two errors of modulus at most `1`, rescaled by `1/T` and by `Q/T`
with `Q ≤ p+12`, accumulate to at most `(p+13)/T`. -/
theorem err_le_of_bounds (p : ℕ) (T e1 e2 Q : ℝ) (hT : 0 < T) (hQ : 0 ≤ Q)
    (hQb : Q ≤ (p : ℝ) + 12) (he1 : |e1| ≤ 1) (he2 : |e2| ≤ 1) :
    |(e1 + e2 * Q) / T| ≤ ((p : ℝ) + 13) / T := by
  rw [abs_div, abs_of_pos hT, div_le_div_iff_of_pos_right hT]
  have h1 : |e1 + e2 * Q| ≤ |e1| + |e2| * Q := by
    calc |e1 + e2 * Q| ≤ |e1| + |e2 * Q| := abs_add_le _ _
      _ = |e1| + |e2| * Q := by rw [abs_mul, abs_of_nonneg hQ]
  nlinarith only [h1, he1, he2, hQb, hQ]

theorem auZ_y_close (p α t : ℕ) (N : ℕ) (hp : 100 ≤ p) (hα : 2 ≤ α) (ht : 1 ≤ t)
    (hpi : |(auPi p : ℝ) - (2:ℝ)^(auPrec p) * Real.pi| ≤ 1)
    (hg : auZ p α t (N:ℤ) ≤ ((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p)) :
    |(auZ p α t (N:ℤ) : ℝ) / (2:ℝ)^(auPrec p) - Real.pi * (N:ℝ) / ((α:ℝ)^2 * (t:ℝ)^2)|
        ≤ ((p:ℝ)+13)/(2:ℝ)^(auPrec p)
      ∧ Real.pi * (N:ℝ) / ((α:ℝ)^2 * (t:ℝ)^2) ≤ (p:ℝ) + 12 := by
  have hTbig : (p : ℝ) + 16 ≤ 2 * (2 : ℝ) ^ (auPrec p) := pow_two_auPrec_ge p hp
  set T : ℝ := (2 : ℝ) ^ (auPrec p) with hTdef
  set D : ℝ := (α : ℝ) ^ 2 * (t : ℝ) ^ 2 with hDdef
  set Q : ℝ := (N : ℝ) / D with hQdef
  have hTpos : (0 : ℝ) < T := by rw [hTdef]; positivity
  have hDpos : (0 : ℝ) < D := by
    rw [hDdef]
    have h1 : (0 : ℝ) < (α : ℝ) := by
      have : (2 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
      linarith
    have h2 : (0 : ℝ) < (t : ℝ) := by
      have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      linarith
    exact mul_pos (pow_pos h1 2) (pow_pos h2 2)
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    exact div_nonneg (by positivity) (le_of_lt hDpos)
  have hguess : (auZ p α t (N:ℤ) : ℝ) ≤ ((p : ℝ) + 10) * T := by
    have h' : ((auZ p α t (N:ℤ) : ℤ) : ℝ)
        ≤ ((((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p) : ℤ) : ℝ) := by exact_mod_cast hg
    push_cast at h'
    linarith only [h', hTdef]
  have hDposZ : (0 : ℤ) < ((α:ℤ)^2 * (t:ℤ)^2) := by
    have h1 : (2 : ℤ) ≤ (α : ℤ) := by exact_mod_cast hα
    have h2 : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
    have h3 : (4 : ℤ) ≤ (α : ℤ) ^ 2 := by nlinarith only [h1]
    have h4 : (1 : ℤ) ≤ (t : ℤ) ^ 2 := by nlinarith only [h2]
    nlinarith only [h3, h4]
  have htdiv : |(auZ p α t (N:ℤ) : ℝ) - (auPi p : ℝ) * (N:ℝ) / D| ≤ 1 := by
    have h := Work.Fx.tdiv_abs_le_one (auPi p * (N:ℤ)) ((α:ℤ)^2 * (t:ℤ)^2) hDposZ
    have e1 : (((auPi p * (N:ℤ) : ℤ)) : ℝ) = (auPi p : ℝ) * (N:ℝ) := by push_cast; ring
    have e2 : ((((α:ℤ)^2 * (t:ℤ)^2 : ℤ)) : ℝ) = D := by rw [hDdef]; push_cast; ring
    simpa [auZ, e1, e2] using h
  have htdivQ : |(auZ p α t (N:ℤ) : ℝ) - (auPi p : ℝ) * Q| ≤ 1 := by
    rw [hQdef]
    rw [mul_div_assoc] at htdiv
    exact htdiv
  have hzlow : T * Real.pi * Q - Q - 1 ≤ (auZ p α t (N:ℤ) : ℝ) := by
    have hA : (auPi p : ℝ) * Q - 1 ≤ (auZ p α t (N:ℤ) : ℝ) := by
      have hh := htdivQ
      rw [abs_le] at hh
      linarith only [hh.1]
    have hB : T * Real.pi * Q - Q ≤ (auPi p : ℝ) * Q := by
      have h3 : (-1 : ℝ) ≤ (auPi p : ℝ) - T * Real.pi := by
        have hh := hpi
        rw [abs_le] at hh
        linarith only [hh.1]
      nlinarith only [mul_le_mul_of_nonneg_right h3 hQnn]
    linarith only [hA, hB]
  have hratio : Real.pi * Q ≤ (p : ℝ) + 12 :=
    ratio_le_of_guard p Q (auZ p α t (N:ℤ) : ℝ) hTbig hQnn hguess hzlow
  have hQb : Q ≤ (p : ℝ) + 12 := by
    nlinarith only [hratio, hQnn, Real.pi_gt_three]
  have herr := err_le_of_bounds p T ((auZ p α t (N:ℤ) : ℝ) - (auPi p : ℝ) * Q)
    ((auPi p : ℝ) - T * Real.pi) Q hTpos hQnn hQb htdivQ hpi
  constructor
  · rw [mul_div_assoc, ← hQdef]
    have hid : (auZ p α t (N:ℤ) : ℝ) / T - Real.pi * Q
        = (((auZ p α t (N:ℤ) : ℝ) - (auPi p : ℝ) * Q)
            + ((auPi p : ℝ) - T * Real.pi) * Q) / T := by
      field_simp
      ring
    rw [hid]
    exact herr
  · rw [mul_div_assoc, ← hQdef]
    exact hratio

end Work.Resample
