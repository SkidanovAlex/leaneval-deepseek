import Mathlib
import Submission.Work.C17.logP_defs

/-!
# `Work.C17.Kfun_bound`

Bound on the remainder coefficients
`K n = (r_b + r_ab·η_a)·uₙ(a)·dₙ(b) + r_ab·dₙ(a)·dₙ(b)`
of the unlikely series `P = logP a b r_a r_b r_ab r0` (see
`Submission.Work.C17.logP_defs`), where `uₙ = Submission.CDT.beukersUR`,
`dₙ = Submission.CDT.beukersD`.

Given the exponential-type bounds `|dₙ(a)| ≤ C (n+1)²/Aⁿ`, `|dₙ(b)| ≤ C (n+1)²/Bⁿ`
(`A = a+√(a²−1)`, `B = b+√(b²−1)`) and `uₙ(a) ≤ Aⁿ`, one has

`|K n| ≤ C₂ (n+1)⁴ (xs a b)ⁿ`,  `xs a b = A·(b−√(b²−1)) = A/B`,

which is the "polynomial-times-`xsⁿ`" growth of the remainder term of `P`.

The proof is elementary: `(A/B)ⁿ = xsⁿ`, and `1/(A·B) ≤ A/B` because `A ≥ 1`.
-/

namespace Work.C17

set_option maxHeartbeats 1000000 in
theorem Kfun_bound (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (ra rb rab : ℤ) (C : ℝ) (hC : 0 < C)
    (hdahi : ∀ n : ℕ, |Submission.CDT.beukersD (a : ℝ) n|
        ≤ C * ((n : ℝ) + 1) ^ 2 / ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n)
    (hdbhi : ∀ n : ℕ, |Submission.CDT.beukersD (b : ℝ) n|
        ≤ C * ((n : ℝ) + 1) ^ 2 / ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ n)
    (huahi : ∀ n : ℕ, Submission.CDT.beukersUR (a : ℝ) n
        ≤ ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ n : ℕ,
        |Kfun a b ra rb rab n| ≤ C₂ * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n := by
  set A : ℝ := (a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1) with hA
  set B : ℝ := (b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1) with hB
  have ha3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hb3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hsqA : Real.sqrt ((a : ℝ) ^ 2 - 1) ^ 2 = (a : ℝ) ^ 2 - 1 :=
    Real.sq_sqrt (by nlinarith)
  have hsqB : Real.sqrt ((b : ℝ) ^ 2 - 1) ^ 2 = (b : ℝ) ^ 2 - 1 :=
    Real.sq_sqrt (by nlinarith)
  have hApos : 0 < A := by rw [hA]; exact add_pos_of_pos_of_nonneg ha0 (Real.sqrt_nonneg _)
  have hBpos : 0 < B := by rw [hB]; exact add_pos_of_pos_of_nonneg hb0 (Real.sqrt_nonneg _)
  have hA1 : 1 ≤ A := by rw [hA]; have := Real.sqrt_nonneg ((a:ℝ)^2 - 1); linarith
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hbminus : (b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1) = 1 / B := by
    rw [eq_div_iff hBne, hB]
    nlinarith [hsqB]
  have hxs : xs a b = A / B := by
    rw [xs, ← hA, hbminus, mul_one_div]
  have hxspos : 0 < xs a b := by rw [hxs]; positivity
  have hdahi' : ∀ n : ℕ, |Submission.CDT.beukersD (a : ℝ) n| ≤ C * ((n : ℝ) + 1) ^ 2 / A ^ n :=
    fun n => by simpa only [hA] using hdahi n
  have hdbhi' : ∀ n : ℕ, |Submission.CDT.beukersD (b : ℝ) n| ≤ C * ((n : ℝ) + 1) ^ 2 / B ^ n :=
    fun n => by simpa only [hB] using hdbhi n
  have huahi' : ∀ n : ℕ, Submission.CDT.beukersUR (a : ℝ) n ≤ A ^ n :=
    fun n => by simpa only [hA] using huahi n
  set K1 : ℝ := (rb : ℝ) + (rab : ℝ) * Submission.CDT.beukersEta (a : ℝ) with hK1
  set K2 : ℝ := (rab : ℝ) with hK2
  refine ⟨|K1| * C + |K2| * C ^ 2 + 1, ?_, ?_⟩
  · have h1 : 0 ≤ |K1| * C := mul_nonneg (abs_nonneg _) hC.le
    have h2 : 0 ≤ |K2| * C ^ 2 := mul_nonneg (abs_nonneg _) (sq_nonneg C)
    linarith
  · intro n
    have hp0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hp1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have h : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have hp2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [hp1]
    have hp24 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 4 := by
      calc ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ 2 * 1 := (mul_one _).symm
        _ ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 :=
              mul_le_mul_of_nonneg_left hp2 (by positivity)
        _ = ((n : ℝ) + 1) ^ 4 := by ring
    have hu : Submission.CDT.beukersUR (a : ℝ) n ≤ A ^ n := huahi' n
    have hupos : 0 < Submission.CDT.beukersUR (a : ℝ) n :=
      Submission.CDT.beukersUR_pos _ (by linarith) n
    have hda := hdahi' n
    have hdb := hdbhi' n
    -- the `F`-term: `uₙ(a)·|dₙ(b)|`, of cusp growth `(A/B)ⁿ = xsⁿ`
    have hstep1 : Submission.CDT.beukersUR (a : ℝ) n * |Submission.CDT.beukersD (b : ℝ) n|
        ≤ C * ((n : ℝ) + 1) ^ 2 * (A / B) ^ n := by
      have h1 : Submission.CDT.beukersUR (a : ℝ) n * |Submission.CDT.beukersD (b : ℝ) n|
          ≤ A ^ n * (C * ((n : ℝ) + 1) ^ 2 / B ^ n) :=
        mul_le_mul hu hdb (abs_nonneg _) (pow_nonneg hApos.le n)
      have h2 : A ^ n * (C * ((n : ℝ) + 1) ^ 2 / B ^ n)
          = C * ((n : ℝ) + 1) ^ 2 * (A / B) ^ n := by
        rw [div_pow]; ring_nf
      linarith [h1, h2]
    have hterm1 : |K1 * (Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)|
        ≤ |K1| * C * ((n : ℝ) + 1) ^ 2 * xs a b ^ n := by
      rw [abs_mul, abs_mul, abs_of_pos hupos]
      calc |K1| * (Submission.CDT.beukersUR (a : ℝ) n * |Submission.CDT.beukersD (b : ℝ) n|)
          ≤ |K1| * (C * ((n : ℝ) + 1) ^ 2 * (A / B) ^ n) :=
              mul_le_mul_of_nonneg_left hstep1 (abs_nonneg _)
        _ = |K1| * C * ((n : ℝ) + 1) ^ 2 * xs a b ^ n := by rw [← hxs]; ring
    -- `1/(A·B) ≤ A/B = xs` since `A ≥ 1`
    have hle : 1 / (A * B) ≤ xs a b := by
      rw [hxs]
      have hAle : 1 / A ≤ A := by rw [div_le_iff₀ hApos]; nlinarith [hA1]
      have h1B : 0 ≤ 1 / B := by positivity
      have hAB : 1 / (A * B) = 1 / A * (1 / B) := by rw [one_div, one_div, one_div, mul_inv]
      rw [hAB]
      calc 1 / A * (1 / B) ≤ A * (1 / B) := mul_le_mul_of_nonneg_right hAle h1B
        _ = A / B := mul_one_div A B
    -- the `K`-term: `|dₙ(a)·dₙ(b)|`
    have hstep2 : |Submission.CDT.beukersD (a : ℝ) n| * |Submission.CDT.beukersD (b : ℝ) n|
        ≤ C ^ 2 * ((n : ℝ) + 1) ^ 4 * xs a b ^ n := by
      have h1 : |Submission.CDT.beukersD (a : ℝ) n| * |Submission.CDT.beukersD (b : ℝ) n|
          ≤ (C * ((n:ℝ)+1)^2 / A^n) * (C * ((n:ℝ)+1)^2 / B^n) :=
        mul_le_mul hda hdb (abs_nonneg _)
          (div_nonneg (mul_nonneg hC.le (sq_nonneg ((n:ℝ)+1))) (pow_nonneg hApos.le n))
      have h2 : (C * ((n:ℝ)+1)^2 / A^n) * (C * ((n:ℝ)+1)^2 / B^n)
          = C^2 * ((n:ℝ)+1)^4 / (A^n * B^n) := by
        rw [div_mul_div_comm]; ring
      have h3 : C^2 * ((n:ℝ)+1)^4 / (A^n * B^n)
          = C^2 * ((n:ℝ)+1)^4 * (1/(A*B))^n := by
        rw [div_pow, one_pow, mul_pow, mul_one_div]
      have h4 : (1/(A*B))^n ≤ xs a b ^ n := pow_le_pow_left₀ (by positivity) hle n
      have h5 : C^2 * ((n:ℝ)+1)^4 * (1/(A*B))^n ≤ C^2 * ((n:ℝ)+1)^4 * xs a b^n :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      linarith [h1, h2, h3, h5]
    have hterm2 : |K2 * (Submission.CDT.beukersD (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)|
        ≤ |K2| * C ^ 2 * ((n : ℝ) + 1) ^ 4 * xs a b ^ n := by
      rw [abs_mul, abs_mul]
      calc |K2| * (|Submission.CDT.beukersD (a : ℝ) n| * |Submission.CDT.beukersD (b : ℝ) n|)
          ≤ |K2| * (C ^ 2 * ((n : ℝ) + 1) ^ 4 * xs a b ^ n) :=
              mul_le_mul_of_nonneg_left hstep2 (abs_nonneg _)
        _ = |K2| * C ^ 2 * ((n : ℝ) + 1) ^ 4 * xs a b ^ n := by ring
    rw [Kfun, ← hK1, ← hK2]
    calc |K1 * (Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)
            + K2 * (Submission.CDT.beukersD (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)|
        ≤ |K1 * (Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)|
            + |K2 * (Submission.CDT.beukersD (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)| :=
              abs_add_le _ _
      _ ≤ |K1| * C * ((n : ℝ) + 1) ^ 2 * xs a b ^ n
            + |K2| * C ^ 2 * ((n : ℝ) + 1) ^ 4 * xs a b ^ n := add_le_add hterm1 hterm2
      _ ≤ (|K1| * C + |K2| * C ^ 2 + 1) * ((n : ℝ) + 1) ^ 4 * xs a b ^ n := by
            have hxnn : 0 ≤ xs a b ^ n := pow_nonneg hxspos.le n
            have h1' : |K1| * C * ((n : ℝ) + 1) ^ 2 * xs a b ^ n
                ≤ |K1| * C * ((n : ℝ) + 1) ^ 4 * xs a b ^ n := by
              have hX : 0 ≤ |K1| * C * xs a b ^ n :=
                mul_nonneg (mul_nonneg (abs_nonneg K1) hC.le) hxnn
              have hh := mul_le_mul_of_nonneg_right hp24 hX
              nlinarith [hh]
            have hp4nn : 0 ≤ ((n : ℝ) + 1) ^ 4 * xs a b ^ n :=
              mul_nonneg (pow_nonneg hp0.le 4) hxnn
            nlinarith [h1', hp4nn]

end Work.C17
