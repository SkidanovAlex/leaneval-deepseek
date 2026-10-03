import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea2

open Work.FIPlan

/-- **The residue (6.6) is `≡ 1 (mod 8)` when `z₁ ≡ z₂ (mod 8)`**: if `|z₁|²` is odd (e.g. `z₁` primary), `z₂ − z₁ = 8m`, `8 ∣ |Δ|` and `a` is a residue of `z₂/z₁` modulo `|Δ|` (i.e. `a·|z₁|² ≡ Re(z̄₁z₂) (mod |Δ|)`), then `a ≡ 1 (mod 8)`.  This is the input `a ≡ 1 (mod 8)` of (8.11), hence of the corrected (8.16) `Nsol_eq_two_sum_jacobi`; it is the paper's remark "`z₂/z₁ ≡ 1 (mod 8)` due to (5.7)".  (The oddness hypothesis is necessary: at `z₁ = 2`, `z₂ = 10`, `a = 5` the other hypotheses hold and the conclusion fails.)

Sketch: `z̄₁z₂ = |z₁|² + 8z̄₁m ≡ |z₁|² (mod 8)`, so `Re(z̄₁z₂) ≡ |z₁|² (mod 8)`; reduce `a·|z₁|² ≡ Re(z̄₁z₂)` modulo `8` (legitimate because `8 ∣ |Δ|`) and cancel the unit `|z₁|²` modulo `8`. -/
theorem a_mod_eight {z1 z2 m : GaussianInt} {a : ℤ}
    (hodd : Odd (Work.FIPlan.gnorm z1))
    (hm : z2 - z1 = 8 * m) (h8 : 8 ∣ Work.FIPlan.absDelta z1 z2)
    (ha : a * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)]) :
    a ≡ 1 [ZMOD 8] := by
  -- `z₂ = z₁ + 8m`, hence `z̄₁z₂ = |z₁|² + 8·(z̄₁m)`.
  have hz2 : z2 = z1 + 8 * m := by linear_combination hm
  have hc : star z1 * z1 = ((gnorm z1 : ℕ) : GaussianInt) := by
    rw [mul_comm, ← Zsqrtd.norm_eq_mul_conj]
    congr 1
    exact (GaussianInt.abs_natCast_norm z1).symm
  have hkey : star z1 * z2
      = ((gnorm z1 : ℕ) : GaussianInt) + ((8 : ℤ) : GaussianInt) * (star z1 * m) := by
    rw [hz2, mul_add, hc]
    ring
  have hre : (star z1 * z2).re = (gnorm z1 : ℤ) + 8 * (star z1 * m).re := by
    rw [hkey, Zsqrtd.re_add, Zsqrtd.re_smul, Zsqrtd.re_natCast]
  -- So `Re(z̄₁z₂) ≡ |z₁|² (mod 8)`.
  have hmod_re : (star z1 * z2).re ≡ (gnorm z1 : ℤ) [ZMOD 8] := by
    rw [hre, Int.modEq_iff_dvd]
    exact ⟨-(star z1 * m).re, by ring⟩
  -- Reduce `a·|z₁|² ≡ Re(z̄₁z₂)` modulo `8` (legitimate since `8 ∣ |Δ|`).
  have h8dvd : (8 : ℤ) ∣ (absDelta z1 z2 : ℤ) := by exact_mod_cast h8
  have ha8 : a * (gnorm z1 : ℤ) ≡ (star z1 * z2).re [ZMOD 8] := Int.ModEq.of_dvd h8dvd ha
  have h : a * (gnorm z1 : ℤ) ≡ (gnorm z1 : ℤ) [ZMOD 8] := ha8.trans hmod_re
  -- Cancel the unit `|z₁|²` modulo `8` (it is odd, hence coprime to `8`).
  have hdvd : (8 : ℤ) ∣ (1 - a) * (gnorm z1 : ℤ) := by
    convert h.dvd using 1
    ring
  have hcop : Int.gcd (8 : ℤ) (gnorm z1 : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    have h2 : Nat.Coprime (gnorm z1) 2 := Nat.coprime_two_right.mpr hodd
    have h3 : Nat.Coprime (gnorm z1) (2 ^ 3) := h2.pow_right 3
    norm_num at h3
    exact Nat.coprime_comm.mp h3
  have hunit : (8 : ℤ) ∣ 1 - a := Int.dvd_of_dvd_mul_left_of_gcd_one hdvd hcop
  exact Int.modEq_iff_dvd.mpr hunit

end Work.FIArea2
