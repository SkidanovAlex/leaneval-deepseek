/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Area BSW: arithmetic engines for Bender §3.3/3.4 (`Work.BSW.BSWS34ArithProp`)

Pure integer/natural-number arithmetic used in the proof of
`Submission/Work/BSW/S3/s34Arith.lean` (`Work.BSW.BSWS34ArithProp`).

Setting (Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235, §3.3/3.4):
`k = |K| > 4` is even, `ε = ±1`, `I = |G:H| = (2k+ε)(k+ε)`, `f = |F|` odd, `n = |K ⊓ M|` even with
`n ∣ k` and `n ∣ f-1`, `m = |G:M|`, `a = 2k/n`, and `f n m = 2 k I`.  Bender's counting inequalities
are

* `1 + f (a-1) ≤ m`,  `f ∣ m - (1 + f(a-1))`,
* `f (k+1) ≤ I`,  `I - f(k+1) ≤ m - (1 + f(a-1))`.

Writing `I = f j` (`j = I/f ≥ k+1`) and `m = a j`, the last inequality becomes the single integer
inequality

`f (j - k - 1) ≤ a (j - f) + f - 1`,

and the two ε-cases are separated by the resulting arithmetic:
* ε = +1: `a ≤ k`, `f ≥ k+2` force `j = k+1`, whence `f = 2k+1` and (from `1 + f(a-1) ≤ m`) `a = 2`,
  i.e. `n = k`;
* ε = −1: `a ≤ k`, `f ≥ k-1` force `f = k-1`, and then `n ∣ k`, `n ∣ k-2` force `n = 2`.

This file contains the three reusable pieces: the two integer engines and the ℕ → ℤ transport of the
counting inequality.
-/

import Mathlib

namespace Work.BSW.S3

/-- **Integer engine, case `ε = +1`.**  With `2 ≤ A ≤ K` (so `A` is the integer `2k/n` above),
`K ≥ 5` and `F ≥ K+2`, the counting inequality `F (J-K-1) ≤ A (J-F) + F - 1` together with
`J ≥ K+1` forces `J = K+1`. -/
lemma s34PosEng (K F J A : ℤ) (hK : 5 ≤ K) (hA2 : 2 ≤ A) (hAK : A ≤ K)
    (hF1 : 1 ≤ F) (hJ : K + 1 ≤ J)
    (hkey : F * (J - K - 1) ≤ A * (J - F) + F - 1) (hFge : K + 2 ≤ F) :
    J = K + 1 := by
  by_contra hne
  have hJ2 : K + 2 ≤ J := by omega
  have hFA : 0 ≤ F - A := by omega
  have h1 : (K + 2) * (F - A) ≤ J * (F - A) := mul_le_mul_of_nonneg_right hJ2 hFA
  nlinarith [hkey, h1, hFge, hAK, hA2]

/-- **Integer engine, case `ε = −1`.**  With `2 ≤ A ≤ K`, `K ≥ 6`, `J ≥ K+1` and `K-1 ≤ F`,
the counting inequality `F (J-K-1) ≤ A (J-F) + F - 1` together with `F J = (2K-1)(K-1)` forces
`F = K-1`. -/
lemma s34NegEng (K F J A : ℤ) (hK : 6 ≤ K) (hA2 : 2 ≤ A) (hAK : A ≤ K)
    (hF1 : 1 ≤ F) (hJ : K + 1 ≤ J)
    (hkey : F * (J - K - 1) ≤ A * (J - F) + F - 1)
    (hFJ : F * J = (2 * K - 1) * (K - 1)) (hFge : K - 1 ≤ F) :
    F = K - 1 := by
  by_contra hne
  have hFge' : K ≤ F := by omega
  have hJne : J ≠ K + 1 := by
    intro hJ1
    have hdvd : (K + 1) ∣ (2 * K - 1) * (K - 1) := ⟨F, by rw [← hFJ, hJ1]; ring⟩
    have hdvd6 : (K + 1) ∣ 6 := by
      have h2 : (K + 1) ∣ (2 * K - 1) * (K - 1) - (K + 1) * (2 * K - 5) :=
        dvd_sub hdvd (dvd_mul_right (K + 1) (2 * K - 5))
      have he : (2 * K - 1) * (K - 1) - (K + 1) * (2 * K - 5) = 6 := by ring
      rwa [he] at h2
    have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 6) hdvd6
    omega
  have hJ2 : K + 2 ≤ J := by omega
  have hFJle : F ≤ J := by
    by_contra hlt
    have hlt' : J < F := by omega
    have hAJ : A * (J - F) ≤ 0 := by nlinarith
    have hkk : (1 : ℤ) ≤ J - K - 1 := by omega
    have hFF : F ≤ F * (J - K - 1) := by nlinarith
    have hstep : F * (J - K - 1) ≤ F - 1 := by linarith [hkey, hAJ]
    linarith [hFF, hstep]
  have hkey2 : J * (F - K) ≤ 2 * F - 1 := by
    have hAJ : A * (J - F) ≤ K * (J - F) := mul_le_mul_of_nonneg_right hAK (by linarith)
    nlinarith [hkey, hAJ]
  have hFK : F ≤ K + 1 := by
    have h1 : (K + 2) * (F - K) ≤ J * (F - K) :=
      mul_le_mul_of_nonneg_right hJ2 (by linarith : 0 ≤ F - K)
    by_contra hc
    have hc' : K + 2 ≤ F := by omega
    nlinarith [hkey2, h1, hc', hK]
  have hcases : F = K ∨ F = K + 1 := by omega
  rcases hcases with hFK1 | hFK1
  · have hdvd : K ∣ 1 := by
      have hd : K ∣ (2 * K - 1) * (K - 1) := ⟨J, by rw [← hFJ, hFK1]⟩
      have h2 : K ∣ (2 * K - 1) * (K - 1) - K * (2 * K - 3) :=
        dvd_sub hd (dvd_mul_right K (2 * K - 3))
      have he : (2 * K - 1) * (K - 1) - K * (2 * K - 3) = 1 := by ring
      rwa [he] at h2
    have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) hdvd
    omega
  · have hdvd : (K + 1) ∣ 6 := by
      have hd : (K + 1) ∣ (2 * K - 1) * (K - 1) := ⟨J, by rw [← hFJ, hFK1]⟩
      have h2 : (K + 1) ∣ (2 * K - 1) * (K - 1) - (K + 1) * (2 * K - 5) :=
        dvd_sub hd (dvd_mul_right (K + 1) (2 * K - 5))
      have he : (2 * K - 1) * (K - 1) - (K + 1) * (2 * K - 5) = 6 := by ring
      rwa [he] at h2
    have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 6) hdvd
    omega

/-- **Transport of Bender's counting inequality to `ℤ`.**  If `I = f j`, `m = (2k/n) j`,
`1 + f(2k/n - 1) ≤ m` and `f(k+1) ≤ I` (so that both natural subtractions are exact), then the
natural inequality `I - f(k+1) ≤ m - (1 + f(2k/n - 1))` is equivalent to
`f (j - k - 1) ≤ (2k/n) (j - f) + f - 1`, the form consumed by `s34PosEng` / `s34NegEng`. -/
lemma s34KeyOfNat (k f n m I j : ℕ) (hI : I = f * j) (hm : m = (2 * k / n) * j)
    (h1 : 1 + f * (2 * k / n - 1) ≤ m) (h3 : f * (k + 1) ≤ I)
    (h4 : I - f * (k + 1) ≤ m - (1 + f * (2 * k / n - 1))) :
    (f : ℤ) * ((j : ℤ) - (k : ℤ) - 1) ≤
      ((2 * k / n : ℕ) : ℤ) * ((j : ℤ) - (f : ℤ)) + (f : ℤ) - 1 := by
  have hA1 : 1 ≤ 2 * k / n := by
    by_contra hc
    have hc0 : 2 * k / n = 0 := Nat.eq_zero_of_not_pos (by omega)
    rw [hc0] at h1 hm
    simp only [Nat.zero_sub, Nat.mul_zero, Nat.add_zero, Nat.zero_mul] at h1 hm
    omega
  have h4Z : (((I - f * (k + 1) : ℕ)) : ℤ) ≤ (((m - (1 + f * (2 * k / n - 1)) : ℕ)) : ℤ) := by
    exact_mod_cast h4
  have hcast1 : (((I - f * (k + 1) : ℕ)) : ℤ) = (f : ℤ) * ((j : ℤ) - (k : ℤ) - 1) := by
    rw [Nat.cast_sub h3, hI]
    push_cast
    ring
  have hcast2 : (((m - (1 + f * (2 * k / n - 1)) : ℕ)) : ℤ) =
      ((2 * k / n : ℕ) : ℤ) * ((j : ℤ) - (f : ℤ)) + (f : ℤ) - 1 := by
    have hb : (((1 + f * (2 * k / n - 1)) : ℕ) : ℤ) =
        1 + (f : ℤ) * (((2 * k / n : ℕ) : ℤ) - 1) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hA1]
      push_cast
      ring
    rw [Nat.cast_sub h1, hm, hb]
    push_cast
    ring
  rw [hcast1, hcast2] at h4Z
  exact h4Z

end Work.BSW.S3
