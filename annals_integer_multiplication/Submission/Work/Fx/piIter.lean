import Mathlib
import Submission.Work.Fx.piDefs

/-!
# Error and size bounds for the π fixed-point iteration

`Work.Fx.piIter` is the numerical core of the fixed-point evaluation of `π` from
`REFS/nlogn.txt` §2.8.  The integer iterate `aval p k` approximates
`2^(2·qq p) · Aseq k` with a uniform error `4 · 2^(qq p)` (independent of `k`),
and every intermediate value has size `isz ≤ SZ p`.

The proof is a discrete contraction argument.  Writing `Q = 2^(2·qq p)`,
`r = 2^(qq p)` (so `Q = r^2`), the real map governing one step is

  `h t = √(2 Q² + Q t)`,

which has `h t = r · √(2Q + t)`, is `(2√2)⁻¹`-Lipschitz on `t ≥ 0`, and has fixed
point `2Q`.  The real iterate `w k = Q · Aseq k` satisfies `w (k+1) = h (w k)`
exactly, while the integer iterate `y k = aval p k` satisfies
`y (k+1) = r · ⌊√(2Q + y k)⌋`, so `y (k+1)` differs from `h (y k)` by at most
`r`; the resulting recursion `|y k - w k| ≤ r + (2√2)⁻¹ |y (k-1) - w (k-1)|`
is bounded by `2r ≤ 4r`.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- `Nat.sqrt` agrees with `Real.sqrt` up to `1`; both are nonnegative so this is
the statement that `Nat.sqrt n ≤ Real.sqrt n < Nat.sqrt n + 1`. -/
theorem natSqrt_abs_sub_le_one (n : ℕ) : |((Nat.sqrt n : ℝ)) - Real.sqrt n| ≤ 1 := by
  have h1 : ((Nat.sqrt n : ℝ)) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast Nat.sqrt_le' n
  have h2 : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact_mod_cast Nat.lt_succ_sqrt' n
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem piIter (p : ℕ) :
    (∀ k : ℕ, |(2 : ℝ) ^ (2 * Work.Fx.qq p) * Work.Fx.Aseq k - (Work.Fx.aval p k : ℝ)|
        ≤ 4 * (2 : ℝ) ^ Work.Fx.qq p) ∧
    (∀ k : ℕ, HvdH.isz (Work.Fx.aval p k) ≤ Work.Fx.SZ p) := by
  set Q : ℝ := (2:ℝ)^(2 * qq p) with hQdef
  set r : ℝ := (2:ℝ)^(qq p) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hrnn : 0 ≤ r := le_of_lt hrpos
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  have hQnn : 0 ≤ Q := le_of_lt hQpos
  have hQr : Q = r^2 := by rw [hQdef, hrdef, mul_comm 2 (qq p), ← pow_mul]
  have hsqrtQ : Real.sqrt Q = r := by rw [hQr, Real.sqrt_sq hrnn]
  have hC : ((C0c p : ℤ) : ℝ) = 2*Q := by
    rw [C0c, hQdef]; push_cast; rw [pow_succ]; ring
  set h : ℝ → ℝ := fun t => Real.sqrt (2*Q^2 + Q*t) with hhdef
  -- `h` is `(2√2)⁻¹`-Lipschitz on the nonnegative half-line.
  have h_lip : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      |h a - h b| ≤ |a - b| / (2*Real.sqrt 2) := by
    intro a b ha hb
    have hA2 : (h a)^2 = 2*Q^2 + Q*a := by
      rw [hhdef]; exact Real.sq_sqrt (by nlinarith [hQpos, ha])
    have hB2 : (h b)^2 = 2*Q^2 + Q*b := by
      rw [hhdef]; exact Real.sq_sqrt (by nlinarith [hQpos, hb])
    have h2Q2 : Real.sqrt (2*Q^2) = Real.sqrt 2 * Q := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq hQnn]
    have hAlow : Real.sqrt 2 * Q ≤ h a := by
      rw [hhdef, ← h2Q2]
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg hQnn ha]
    have hBlow : Real.sqrt 2 * Q ≤ h b := by
      rw [hhdef, ← h2Q2]
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg hQnn hb]
    have hABpos : 0 < h a + h b := by
      have : 0 < Real.sqrt 2 * Q := by positivity
      linarith
    have habsmul : |h a - h b| * (h a + h b) = Q * |a - b| := by
      have e1 : |h a - h b| * (h a + h b) = |(h a - h b) * (h a + h b)| := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hABpos)]
      have e2 : (h a - h b)*(h a + h b) = (h a)^2 - (h b)^2 := by ring
      have e3 : (h a)^2 - (h b)^2 = Q*(a-b) := by rw [hA2, hB2]; ring
      rw [e1, e2, e3, abs_mul, abs_of_nonneg hQnn]
    have hAplus : 2*Real.sqrt 2 * Q ≤ h a + h b := by linarith
    have hkey : |h a - h b| * (2*Real.sqrt 2) * Q ≤ |a - b| * Q := by
      rw [show |h a - h b| * (2*Real.sqrt 2) * Q = |h a - h b| * (2*Real.sqrt 2 * Q) by ring,
          show |a - b| * Q = Q * |a - b| by ring, ← habsmul]
      exact mul_le_mul_of_nonneg_left hAplus (abs_nonneg _)
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.sqrt 2)]
    exact (mul_le_mul_iff_of_pos_right hQpos).1 hkey
  -- The strong invariant `|aval p k - Q · Aseq k| ≤ 2r`.
  have strong : ∀ k, |Q * Aseq k - (aval p k : ℝ)| ≤ 2*r := by
    intro k
    induction k with
    | zero =>
      rw [Aseq_zero, aval_zero]
      simp only [mul_zero, Int.cast_zero, sub_self, abs_zero]
      positivity
    | succ k ih =>
      have hAseq_nn : 0 ≤ Aseq k := Real.sqrtTwoAddSeries_zero_nonneg k
      have hy_k_nn : 0 ≤ (aval p k : ℝ) := by exact_mod_cast sq_nonneg' p k
      have hw_nn : 0 ≤ Q * Aseq k := mul_nonneg hQnn hAseq_nn
      -- the integer step, as a real
      have hy_succ : (aval p (k+1) : ℝ)
          = r * (Nat.sqrt ((C0c p + aval p k).toNat) : ℝ) := by
        rw [aval_succ, astep]
        push_cast
        rw [← hrdef]
      -- the model step, as `h` applied to the previous model value
      have hw_succ : Q * Aseq (k+1) = h (Q * Aseq k) := by
        rw [Aseq_succ,
          show h (Q * Aseq k) = Real.sqrt (2*Q^2 + Q*(Q*Aseq k)) from rfl]
        have harg : 2*Q^2 + Q*(Q*Aseq k) = Q^2 * (2 + Aseq k) := by ring
        rw [harg, Real.sqrt_mul (sq_nonneg Q), Real.sqrt_sq hQnn]
      have hMcast : (((C0c p + aval p k).toNat : ℕ) : ℝ) = 2*Q + (aval p k : ℝ) := by
        have hsum : 0 ≤ C0c p + aval p k := by
          have : 0 ≤ C0c p := by rw [C0c]; positivity
          linarith [sq_nonneg' p k]
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hsum]
        push_cast
        rw [hC]
      have hAy : h ((aval p k : ℝ))
          = r * Real.sqrt (((C0c p + aval p k).toNat : ℕ) : ℝ) := by
        rw [show h ((aval p k : ℝ)) = Real.sqrt (2*Q^2 + Q*(aval p k : ℝ)) from rfl,
          hMcast]
        rw [show 2*Q^2 + Q*(aval p k : ℝ) = Q*(2*Q + (aval p k : ℝ)) by ring,
          Real.sqrt_mul hQnn, hsqrtQ]
      have hstep1 : |h (Q * Aseq k) - h ((aval p k : ℝ))| ≤ r := by
        have h1 := h_lip (Q * Aseq k) ((aval p k : ℝ)) hw_nn hy_k_nn
        have hs2 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num : (1:ℝ) ≤ 2)
        have hdiv : |Q * Aseq k - (aval p k : ℝ)| / (2*Real.sqrt 2) ≤ r := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.sqrt 2)]
          nlinarith [ih, hrnn, hs2, Real.sqrt_nonneg 2]
        linarith
      have hstep2 : |h ((aval p k : ℝ))
          - r * (Nat.sqrt ((C0c p + aval p k).toNat) : ℝ)| ≤ r := by
        rw [hAy]
        rw [show r * Real.sqrt (((C0c p + aval p k).toNat : ℕ) : ℝ)
              - r * (Nat.sqrt ((C0c p + aval p k).toNat) : ℝ)
            = r * (Real.sqrt (((C0c p + aval p k).toNat : ℕ) : ℝ)
              - (Nat.sqrt ((C0c p + aval p k).toNat) : ℝ)) by ring]
        rw [abs_mul, abs_of_nonneg hrnn]
        have hle := natSqrt_abs_sub_le_one ((C0c p + aval p k).toNat)
        have hswap : |Real.sqrt (((C0c p + aval p k).toNat : ℕ) : ℝ)
              - (Nat.sqrt ((C0c p + aval p k).toNat) : ℝ)| ≤ 1 := by
          rw [abs_sub_comm]; exact hle
        nlinarith [hrpos]
      rw [hy_succ, hw_succ]
      have htri := abs_sub_le (h (Q * Aseq k)) (h ((aval p k : ℝ)))
        (r * (Nat.sqrt ((C0c p + aval p k).toNat) : ℝ))
      linarith
  constructor
  · intro k
    have := strong k
    linarith
  · intro k
    have h1 : (aval p k : ℝ) ≤ Q * Aseq k + 2*r := by
      have := (abs_le.mp (strong k)).1
      linarith
    have hAseq_lt : Aseq k < 2 := Real.sqrtTwoAddSeries_lt_two k
    have hrQ : r ≤ Q := by
      rw [hrdef, hQdef]
      apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
      omega
    have hbound : (aval p k : ℝ) < (2:ℝ)^(8*p+6) := by
      have h2 : Q * Aseq k < Q * 2 := mul_lt_mul_of_pos_left hAseq_lt hQpos
      have hthis : (aval p k : ℝ) < 4*Q := by linarith
      have hQval : Q = (2:ℝ)^(8*p) := by
        rw [hQdef, qq]; congr 1; ring
      have h4 : (4:ℝ) * Q < (2:ℝ)^(8*p+6) := by
        rw [hQval, show (4:ℝ) = 2^2 by norm_num, ← pow_add]
        exact pow_lt_pow_right₀ (by norm_num) (by omega)
      linarith
    have hcast : (((aval p k).natAbs : ℕ) : ℝ) = (aval p k : ℝ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (sq_nonneg' p k)]
    have hreal : (((aval p k).natAbs : ℕ) : ℝ) < (2:ℝ)^(8*p+6) := by
      rw [hcast]; exact hbound
    have hnat : (aval p k).natAbs < 2^(8*p+6) := by
      exact_mod_cast hreal
    have hs : (aval p k).natAbs.size ≤ 8*p+6 := Nat.size_le.mpr hnat
    simp only [isz, SZ]
    omega

end Work.Fx
