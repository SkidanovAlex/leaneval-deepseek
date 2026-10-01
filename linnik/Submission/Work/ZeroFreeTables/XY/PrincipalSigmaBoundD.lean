/-
# `Work.ZeroFreeTables.XY.PrincipalSigmaBoundD`

The principal-character `P₃` bound of Heath-Brown §9, with an *arbitrary* error `ε` and an
arbitrary bound `M` on the shift `λ₁`:

for every `M ≥ 0` and `ε > 0` there is `q₀` such that for every modulus `q ≥ q₀`, every test point
`s` with `Re s = 1 + (17/5)/log q` and `|Im s| ≤ 4`, and every `λ₁ ∈ [0, M]`,

`Σ(s, χ₀) ≤ Re P₃((17/5+λ₁)/((s-1)log q)) + (17/5+λ₁)·ε`,

where `Σ = SigmaP3L` is HB's smoothing functional (8.4) for the principal character mod `q` and
`P₃(X) = X + X² + (2/3)X³` is the third polynomial of (4.12).

## Proof

`P9.SigmaP3L_eq_logDeriv_derivs` writes `Σ` in terms of the first two derivatives of
`logDeriv L(·,χ₀)`, and `XY.PrincipalSigma.LogDerivPrincipalDecomp` splits that log-derivative into
the zeta contribution and the Euler factors of the primes `p ∣ q`:

`Σ = -c·Re(L'/L)(s) + c²·Re((L'/L)'(s)) - (1/3)c³·Re((L'/L)''(s))`,  `c = (17/5+λ₁)/log q`.

Splitting off the pole at `s = 1` (the three `Re((s-1)^{-k})` terms, whose combination is exactly
`Re P₃(c/(s-1)) = W`) leaves an error of the form

`c·M₀ + c²·M₀ + (1/3)c³·M₀ + c·(2S₁) + c²·(4S₂) + (1/3)c³·(16S₃)`,

where `M₀` is the bound `XY.PrincipalSigma.ZetaPoleBounded` for the pole-subtracted
`ζ'-derivatives` on `{1 < Re s ≤ 4, |Im s| ≤ 5}`, and `S_j = ∑_{p ∣ q}(log p)^j/p`.  The Euler
factor bounds `XY.PrincipalSigma.EulerFactorBounds` give the three `‖·‖ ≤ 2S₁, 4S₂, 16S₃`, and
`P9.primeFactors_logPow_div_le` bounds `S_j` by `C·(log log q)^{j+1}`.  Since `c = α/L` with
`α ≤ A := 17/5+M` and `L = log q`, the bracket is at most
`α·(M₀(1+A/L+A²/(3L²))/L + 2C(log L+2)²/L + 4AC(log L+2)³/L² + (16/3)A²C(log L+2)⁴/L³)`, and
`Table4.principalArith` produces `L₀` beyond which the bracket is `≤ ε`.  This is the
"`P₃`-method" content of HB §9 at the archimedean point.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs
import Submission.Work.ZeroFreeTables.XY.PrincipalSigma.ZetaPoleBounded
import Submission.Work.ZeroFreeTables.XY.PrincipalSigma.LogDerivPrincipalDecomp
import Submission.Work.ZeroFreeTables.XY.PrincipalSigma.EulerFactorBounds
import Submission.Work.ZeroFreeTables.Table4.principalArith

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 2000000

namespace Work.ZeroFreeTables.XY

noncomputable section

open Work.ZeroFreeTables.XY.PrincipalSigma

/-- The error bracket of the principal-character `P₃` bound is `≤ α ε` once `L` is large enough.

With `c = α/L`, `α ≤ A`, `α ≥ 0` and the prime sums bounded by `C (log L + 2)^j`, the six terms
`c M₀ + c² M₀ + (1/3)c³ M₀ + c·2S₁ + c²·4S₂ + (1/3)c³·16S₃` are each at most `α` times a term of
the bracket `M₀(1+A/L+A²/(3L²))/L + 2C(log L+2)²/L + 4AC(log L+2)³/L² + (16/3)A²C(log L+2)⁴/L³`,
which is `≤ ε` by hypothesis. -/
lemma errorBracket_le {M₀ C A ε α L S₁ S₂ S₃ : ℝ}
    (hL : 1 ≤ L) (hα0 : 0 ≤ α) (hαA : α ≤ A) (hA0 : 0 ≤ A)
    (hM₀ : 0 ≤ M₀) (hC : 0 ≤ C)
    (hS₁ : S₁ ≤ C * (Real.log L + 2) ^ 2)
    (hS₂ : S₂ ≤ C * (Real.log L + 2) ^ 3)
    (hS₃ : S₃ ≤ C * (Real.log L + 2) ^ 4)
    (hS₁0 : 0 ≤ S₁) (hS₂0 : 0 ≤ S₂) (hS₃0 : 0 ≤ S₃)
    (ht : M₀ * (1 + A / L + A ^ 2 / (3 * L ^ 2)) / L + 2 * C * (Real.log L + 2) ^ 2 / L
        + 4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2
        + (16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3 ≤ ε) :
    (α / L) * M₀ + (α / L) ^ 2 * M₀ + (1 / 3) * (α / L) ^ 3 * M₀
      + (α / L) * (2 * S₁) + (α / L) ^ 2 * (4 * S₂) + (1 / 3) * (α / L) ^ 3 * (16 * S₃)
        ≤ α * ε := by
  have hLpos : 0 < L := by linarith
  have hlog2 : 0 ≤ Real.log L + 2 := by
    have := Real.log_nonneg hL
    linarith
  have hM0 : 0 ≤ M₀ := hM₀
  have t1 : (α / L) * M₀ ≤ α * (M₀ / L) := le_of_eq (by ring)
  have t2 : (α / L) ^ 2 * M₀ ≤ α * (A * M₀ / L ^ 2) := by
    have e : (α / L) ^ 2 * M₀ = α * ((α / L ^ 2) * M₀) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hα0
    calc (α / L ^ 2) * M₀ ≤ (A / L ^ 2) * M₀ :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαA (by positivity)) hM0
      _ = A * M₀ / L ^ 2 := by ring
  have t3 : (1 / 3) * (α / L) ^ 3 * M₀ ≤ α * ((1 / 3) * A ^ 2 * M₀ / L ^ 3) := by
    have e : (1 / 3) * (α / L) ^ 3 * M₀ = α * ((1 / 3) * (α ^ 2 / L ^ 3) * M₀) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hα0
    have h : α ^ 2 / L ^ 3 ≤ A ^ 2 / L ^ 3 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hα0 hαA 2) (by positivity)
    calc (1 / 3) * (α ^ 2 / L ^ 3) * M₀ ≤ (1 / 3) * (A ^ 2 / L ^ 3) * M₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num)) hM0
      _ = (1 / 3) * A ^ 2 * M₀ / L ^ 3 := by ring
  have t4 : (α / L) * (2 * S₁) ≤ α * (2 * C * (Real.log L + 2) ^ 2 / L) := by
    have e : (α / L) * (2 * S₁) = α * ((2 * S₁) / L) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hα0
    calc (2 * S₁) / L ≤ (2 * (C * (Real.log L + 2) ^ 2)) / L :=
          div_le_div_of_nonneg_right (by linarith [hS₁]) (le_of_lt hLpos)
      _ = 2 * C * (Real.log L + 2) ^ 2 / L := by ring
  have t5 : (α / L) ^ 2 * (4 * S₂) ≤ α * (4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2) := by
    have e : (α / L) ^ 2 * (4 * S₂) = α * ((4 * α * S₂) / L ^ 2) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hα0
    have hn : 4 * α * S₂ ≤ 4 * (A * (C * (Real.log L + 2) ^ 3)) := by
      have h1 : α * S₂ ≤ A * (C * (Real.log L + 2) ^ 3) :=
        mul_le_mul hαA hS₂ hS₂0 (le_trans hα0 hαA)
      linarith [h1]
    calc (4 * α * S₂) / L ^ 2 ≤ (4 * (A * (C * (Real.log L + 2) ^ 3))) / L ^ 2 :=
          div_le_div_of_nonneg_right hn (by positivity)
      _ = 4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2 := by ring
  have t6 : (1 / 3) * (α / L) ^ 3 * (16 * S₃) ≤
      α * ((16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3) := by
    have e : (1 / 3) * (α / L) ^ 3 * (16 * S₃) = α * ((16 / 3) * (α ^ 2 * S₃) / L ^ 3) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hα0
    have hn : α ^ 2 * S₃ ≤ A ^ 2 * (C * (Real.log L + 2) ^ 4) := by
      have h1 : α ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hα0 hαA 2
      exact mul_le_mul h1 hS₃ hS₃0 (by positivity)
    calc (16 / 3) * (α ^ 2 * S₃) / L ^ 3 ≤ (16 / 3) * (A ^ 2 * (C * (Real.log L + 2) ^ 4)) / L ^ 3 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (by positivity)
      _ = (16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3 := by ring
  have hsum : (α / L) * M₀ + (α / L) ^ 2 * M₀ + (1 / 3) * (α / L) ^ 3 * M₀
      + (α / L) * (2 * S₁) + (α / L) ^ 2 * (4 * S₂) + (1 / 3) * (α / L) ^ 3 * (16 * S₃)
      ≤ α * (M₀ / L) + α * (A * M₀ / L ^ 2) + α * ((1 / 3) * A ^ 2 * M₀ / L ^ 3)
        + α * (2 * C * (Real.log L + 2) ^ 2 / L)
        + α * (4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2)
        + α * ((16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3) := by
    linarith [t1, t2, t3, t4, t5, t6]
  have hBeq : α * (M₀ / L) + α * (A * M₀ / L ^ 2) + α * ((1 / 3) * A ^ 2 * M₀ / L ^ 3)
        + α * (2 * C * (Real.log L + 2) ^ 2 / L)
        + α * (4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2)
        + α * ((16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3)
      = α * (M₀ * (1 + A / L + A ^ 2 / (3 * L ^ 2)) / L + 2 * C * (Real.log L + 2) ^ 2 / L
        + 4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2
        + (16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3) := by ring
  have hfin := mul_le_mul_of_nonneg_left ht hα0
  linarith [hsum, hBeq, hfin]



/-- **The pole-extraction reduction for the principal character.**  Writing the first two
derivatives of `logDeriv L(·,χ₀)` as `logDeriv ζ + (Euler sum)` (`hd0`–`hd2`), and using the
three bounds `hG0`–`hG2` for the pole-subtracted zeta derivatives and `hF0`–`hF2` for the Euler
sum, the smoothing functional `Σ` is at most the pole term `Re P₃(α/((s-1)L))` plus the six
elementary error terms. -/
theorem principalSigmaMasterD {q : ℕ} [NeZero q] {s : ℂ} {a lam₁ L M S1 S2 S3 W : ℝ}
    (hW : W = (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re)
    (hL : 0 < L) (hs : 1 < s.re) (ha : 0 ≤ a) (hlam0 : 0 ≤ lam₁)
    (hG0 : |(logDeriv riemannZeta s + 1 / (s - 1)).re| ≤ M)
    (hG1 : |(iteratedDeriv 1 (logDeriv riemannZeta) s - 1 / (s - 1) ^ 2).re| ≤ M)
    (hG2 : |(iteratedDeriv 2 (logDeriv riemannZeta) s + 2 / (s - 1) ^ 3).re| ≤ M)
    (hF0 : ‖(∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1))‖ ≤ 2 * S1)
    (hF1 : ‖iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
            (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖ ≤ 4 * S2)
    (hF2 : ‖iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
            (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖ ≤ 16 * S3)
    (hd0 : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
            = logDeriv riemannZeta s
              + ∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1))
    (hd1 : iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s
            = iteratedDeriv 1 (logDeriv riemannZeta) s
              + iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
                  (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s)
    (hd2 : iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s
            = iteratedDeriv 2 (logDeriv riemannZeta) s
              + iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
                  (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s) :
    Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      ≤ W
        + (((a + lam₁) / L) * M + ((a + lam₁) / L) ^ 2 * M
           + (1 / 3) * ((a + lam₁) / L) ^ 3 * M
           + ((a + lam₁) / L) * (2 * S1) + ((a + lam₁) / L) ^ 2 * (4 * S2)
           + (1 / 3) * ((a + lam₁) / L) ^ 3 * (16 * S3)) := by
  rw [hW]
  have hsig := Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs
      (1 : DirichletCharacter ℂ q) hs a lam₁ L
  rw [hsig, hd0, hd1, hd2]
  rw [Complex.add_re (logDeriv riemannZeta s)
        (∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1)),
      Complex.add_re (iteratedDeriv 1 (logDeriv riemannZeta) s)
        (iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
          (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s),
      Complex.add_re (iteratedDeriv 2 (logDeriv riemannZeta) s)
        (iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
          (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s)]
  rw [Work.ZeroFreeTables.P9.P3_arg_eq a lam₁ L s 1, Work.ZeroFreeTables.P9.P3_re_mul_inv]
  set c : ℝ := (a + lam₁) / L with hc
  set A0 : ℝ := (logDeriv riemannZeta s).re with hA0
  set A1 : ℝ := (iteratedDeriv 1 (logDeriv riemannZeta) s).re with hA1
  set A2 : ℝ := (iteratedDeriv 2 (logDeriv riemannZeta) s).re with hA2
  set Br : ℝ := (((1 / (s - 1)) : ℂ)).re with hBr
  set B2 : ℝ := ((((1 / (s - 1)) : ℂ) ^ 2)).re with hB2
  set B3 : ℝ := ((((1 / (s - 1)) : ℂ) ^ 3)).re with hB3
  set F0 : ℝ := ((∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1))).re with hF0'
  set F1 : ℝ := (iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s).re with hF1'
  set F2 : ℝ := (iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s).re with hF2'
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hG0
  have hS10 : 0 ≤ S1 := by
    have h := norm_nonneg (∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1))
    linarith
  have hS20 : 0 ≤ S2 := by
    have h := norm_nonneg (iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s)
    linarith
  have hS30 : 0 ≤ S3 := by
    have h := norm_nonneg (iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s)
    linarith
  have hsq : ((1 / (s - 1)) : ℂ) ^ 2 = 1 / (s - 1) ^ 2 := by rw [div_pow, one_pow]
  have hcu : ((1 / (s - 1)) : ℂ) ^ 3 = 1 / (s - 1) ^ 3 := by rw [div_pow, one_pow]
  have hG1' : |(iteratedDeriv 1 (logDeriv riemannZeta) s
      - ((1 / (s - 1)) : ℂ) ^ 2).re| ≤ M := by
    rw [hsq]; exact hG1
  have hG2' : |(iteratedDeriv 2 (logDeriv riemannZeta) s
      + 2 * ((1 / (s - 1)) : ℂ) ^ 3).re| ≤ M := by
    have e : (2 : ℂ) * ((1 / (s - 1)) : ℂ) ^ 3 = 2 / (s - 1) ^ 3 := by rw [hcu]; ring
    rw [e]; exact hG2
  have hg0 : |A0 + Br| ≤ M := by
    rw [Complex.add_re, ← hA0, ← hBr] at hG0; exact hG0
  have hg1 : |A1 - B2| ≤ M := by
    rw [Complex.sub_re, ← hA1, ← hB2] at hG1'; exact hG1'
  have hg2 : |A2 + 2 * B3| ≤ M := by
    have e : (iteratedDeriv 2 (logDeriv riemannZeta) s
        + (2 : ℂ) * ((1 / (s - 1)) : ℂ) ^ 3).re = A2 + 2 * B3 := by
      rw [Complex.add_re, Complex.mul_re, ← hA2, ← hB3]
      norm_num
    rw [e] at hG2'
    exact hG2'
  have hFr0 : |F0| ≤ ‖(∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1))‖ := by
    rw [hF0']; exact Complex.abs_re_le_norm _
  have hFr1 : |F1| ≤ ‖iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖ := by
    rw [hF1']; exact Complex.abs_re_le_norm _
  have hFr2 : |F2| ≤ ‖iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖ := by
    rw [hF2']; exact Complex.abs_re_le_norm _
  have h3c : (0 : ℝ) ≤ (1 / 3) * c ^ 3 := by positivity
  have e1 : -c * (A0 + Br) ≤ c * M := by
    have h : -(A0 + Br) ≤ M := le_trans (neg_le_abs (A0 + Br)) hg0
    have h2 := mul_le_mul_of_nonneg_left h hc0
    linarith [h2]
  have e2 : c ^ 2 * (A1 - B2) ≤ c ^ 2 * M := by
    have h : A1 - B2 ≤ M := le_trans (le_abs_self (A1 - B2)) hg1
    have h2 := mul_le_mul_of_nonneg_left h (sq_nonneg c)
    linarith [h2]
  have e3 : -(1 / 3) * c ^ 3 * (A2 + 2 * B3) ≤ (1 / 3) * c ^ 3 * M := by
    have h : -(A2 + 2 * B3) ≤ M := le_trans (neg_le_abs (A2 + 2 * B3)) hg2
    have h2 := mul_le_mul_of_nonneg_left h h3c
    linarith [h2]
  have e4 : -c * F0 ≤ c * (2 * S1) := by
    have h : -F0 ≤ 2 * S1 := le_trans (neg_le_abs F0) (le_trans hFr0 hF0)
    have h2 := mul_le_mul_of_nonneg_left h hc0
    linarith [h2]
  have e5 : c ^ 2 * F1 ≤ c ^ 2 * (4 * S2) := by
    have h : F1 ≤ 4 * S2 := le_trans (le_abs_self F1) (le_trans hFr1 hF1)
    have h2 := mul_le_mul_of_nonneg_left h (sq_nonneg c)
    linarith [h2]
  have e6 : -(1 / 3) * c ^ 3 * F2 ≤ (1 / 3) * c ^ 3 * (16 * S3) := by
    have h : -F2 ≤ 16 * S3 := le_trans (neg_le_abs F2) (le_trans hFr2 hF2)
    have h2 := mul_le_mul_of_nonneg_left h h3c
    linarith [h2]
  have hkey : -(c) * (A0 + F0) + c ^ 2 * (A1 + F1) - (1 / 3) * c ^ 3 * (A2 + F2)
      = (c * Br + c ^ 2 * B2 + (2 / 3) * c ^ 3 * B3)
        + (-c * (A0 + Br) + c ^ 2 * (A1 - B2) - (1 / 3) * c ^ 3 * (A2 + 2 * B3))
        + (-c * F0 + c ^ 2 * F1 - (1 / 3) * c ^ 3 * F2) := by ring
  rw [hkey]
  have hP3W : c * Br + c ^ 2 * B2 + (2 / 3) * c ^ 3 * B3
      = (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re := by
    rw [Work.ZeroFreeTables.P9.P3_arg_eq a lam₁ L s 1, Work.ZeroFreeTables.P9.P3_re_mul_inv]
  rw [hP3W]
  have hG : -c * (A0 + Br) + c ^ 2 * (A1 - B2) - (1 / 3) * c ^ 3 * (A2 + 2 * B3)
      ≤ c * M + c ^ 2 * M + (1 / 3) * c ^ 3 * M := by linarith [e1, e2, e3]
  have hF : -c * F0 + c ^ 2 * F1 - (1 / 3) * c ^ 3 * F2
      ≤ c * (2 * S1) + c ^ 2 * (4 * S2) + (1 / 3) * c ^ 3 * (16 * S3) := by
    linarith [e4, e5, e6]
  linarith [hG, hF]

theorem PrincipalSigmaBoundD {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (lam₁ : ℝ) (s : ℂ),
      0 ≤ lam₁ → lam₁ ≤ M → s.re = 1 + (17 / 5) / Real.log q → |s.im| ≤ 4 →
      Work.ZeroFreeTables.SigmaP3L q (Real.log q) (1 : DirichletCharacter ℂ q) s (17 / 5) lam₁
        ≤ (Work.ZeroFreeTables.P3 (((((17 : ℝ) / 5) + lam₁) : ℂ)
              / ((s - 1) * ((Real.log q : ℝ) : ℂ)))).re + (17 / 5 + lam₁) * ε := by
  obtain ⟨M₀, hM₀pos, hzB⟩ := PrincipalSigma.ZetaPoleBounded
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨C₃, hC₃pos, hC₃⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 3 (by norm_num)
  set C : ℝ := max C₁ (max C₂ C₃) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le hC₁pos (le_max_left _ _)
  have hC₁le : C₁ ≤ C := le_max_left _ _
  have hC₂le : C₂ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC₃le : C₃ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hA0 : (0 : ℝ) ≤ 17 / 5 + M := by linarith
  obtain ⟨L₀, hL₀1, hL₀bd⟩ :=
    Work.ZeroFreeTables.Table4.principalArith M₀ C (17 / 5 + M) ε hM₀pos hCpos hA0 hε
  refine ⟨max 3 (⌈Real.exp (max L₀ 2)⌉₊ + 1), fun q hq hNe lam₁ s hlam0 hlamM hre him => ?_⟩
  have hq3 : 3 ≤ q := le_trans (le_max_left _ _) hq
  have hqexp : ⌈Real.exp (max L₀ 2)⌉₊ + 1 ≤ q := le_trans (le_max_right _ _) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hexp_le : Real.exp (max L₀ 2) ≤ (q : ℝ) := by
    have h2 : Real.exp (max L₀ 2) ≤ ((⌈Real.exp (max L₀ 2)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : (((⌈Real.exp (max L₀ 2)⌉₊ + 1 : ℕ)) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqexp
    push_cast at h3
    linarith
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hLge' : max L₀ 2 ≤ L := by
    rw [hLdef]
    have h := Real.log_le_log (Real.exp_pos (max L₀ 2)) hexp_le
    rwa [Real.log_exp] at h
  have hLge : L₀ ≤ L := le_trans (le_max_left _ _) hLge'
  have hL2 : (2 : ℝ) ≤ L := le_trans (le_max_right _ _) hLge'
  have hL1 : 1 ≤ L := le_trans hL₀1 hLge
  have hLpos : 0 < L := by linarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hsre1 : 1 < s.re := by
    rw [hre]
    have h : 0 < (17 : ℝ) / 5 / L := div_pos (by norm_num) hLpos
    linarith
  have hsre4 : s.re ≤ 4 := by
    rw [hre]
    have h : (17 : ℝ) / 5 / L ≤ 3 := by
      rw [div_le_iff₀ hLpos]
      linarith
    linarith
  have him5 : |s.im| ≤ 5 := by linarith [him]
  obtain ⟨hz0, hz1, hz2⟩ := hzB s hsre1 hsre4 him5
  obtain ⟨hE0, hE1, hE2⟩ := PrincipalSigma.EulerFactorBounds q (le_of_lt hsre1)
  have hd0 := PrincipalSigma.LogDerivPrincipalDecomp q 0 (by norm_num) hsre1
  have hd1 := PrincipalSigma.LogDerivPrincipalDecomp q 1 (by norm_num) hsre1
  have hd2 := PrincipalSigma.LogDerivPrincipalDecomp q 2 (by norm_num) hsre1
  have hd0' : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
      = logDeriv riemannZeta s
        + ∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1) := by
    simpa only [iteratedDeriv_zero] using hd0
  set S₁ : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) with hS₁def
  set S₂ : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) with hS₂def
  set S₃ : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) with hS₃def
  have hS₁bd : S₁ ≤ C * (Real.log L + 2) ^ 2 := by
    have h := hC₁ q hq3
    have h' : S₁ ≤ C₁ * (Real.log L) ^ 2 := by
      rw [hS₁def]
      simpa only [pow_one, ← hLdef] using h
    refine le_trans h' ?_
    have h1 : (Real.log L) ^ 2 ≤ (Real.log L + 2) ^ 2 :=
      pow_le_pow_left₀ hlogL0 (by linarith) 2
    have h2 : C₁ * (Real.log L) ^ 2 ≤ C₁ * (Real.log L + 2) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hC₁pos)
    have h3 : C₁ * (Real.log L + 2) ^ 2 ≤ C * (Real.log L + 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hC₁le (by positivity)
    linarith [h2, h3]
  have hS₂bd : S₂ ≤ C * (Real.log L + 2) ^ 3 := by
    have h := hC₂ q hq3
    have h' : S₂ ≤ C₂ * (Real.log L) ^ 3 := by
      rw [hS₂def]
      simpa only [← hLdef] using h
    refine le_trans h' ?_
    have h1 : (Real.log L) ^ 3 ≤ (Real.log L + 2) ^ 3 :=
      pow_le_pow_left₀ hlogL0 (by linarith) 3
    have h2 : C₂ * (Real.log L) ^ 3 ≤ C₂ * (Real.log L + 2) ^ 3 :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hC₂pos)
    have h3 : C₂ * (Real.log L + 2) ^ 3 ≤ C * (Real.log L + 2) ^ 3 :=
      mul_le_mul_of_nonneg_right hC₂le (by positivity)
    linarith [h2, h3]
  have hS₃bd : S₃ ≤ C * (Real.log L + 2) ^ 4 := by
    have h := hC₃ q hq3
    have h' : S₃ ≤ C₃ * (Real.log L) ^ 4 := by
      rw [hS₃def]
      simpa only [← hLdef] using h
    refine le_trans h' ?_
    have h1 : (Real.log L) ^ 4 ≤ (Real.log L + 2) ^ 4 :=
      pow_le_pow_left₀ hlogL0 (by linarith) 4
    have h2 : C₃ * (Real.log L) ^ 4 ≤ C₃ * (Real.log L + 2) ^ 4 :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hC₃pos)
    have h3 : C₃ * (Real.log L + 2) ^ 4 ≤ C * (Real.log L + 2) ^ 4 :=
      mul_le_mul_of_nonneg_right hC₃le (by positivity)
    linarith [h2, h3]
  have hS₁0 : 0 ≤ S₁ := by
    rw [hS₁def]
    refine Finset.sum_nonneg fun p hp => div_nonneg ?_ (Nat.cast_nonneg p)
    exact Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)))
  have hS₂0 : 0 ≤ S₂ := by
    rw [hS₂def]
    exact Finset.sum_nonneg fun p hp => div_nonneg (by positivity) (Nat.cast_nonneg p)
  have hS₃0 : 0 ≤ S₃ := by
    rw [hS₃def]
    exact Finset.sum_nonneg fun p hp => div_nonneg (by positivity) (Nat.cast_nonneg p)
  have hF0 : ‖(∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1))‖ ≤ 2 * S₁ := by
    have hsum : (∑ p ∈ q.primeFactors, 2 * Real.log (p : ℝ) / (p : ℝ)) = 2 * S₁ := by
      rw [hS₁def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [← hsum]
    exact hE0
  have hF1 : ‖iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖ ≤ 4 * S₂ := by
    have hsum : (∑ p ∈ q.primeFactors, 4 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) = 4 * S₂ := by
      rw [hS₂def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [← hsum]
    exact hE1
  have hF2 : ‖iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖ ≤ 16 * S₃ := by
    have hsum : (∑ p ∈ q.primeFactors, 16 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) = 16 * S₃ := by
      rw [hS₃def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [← hsum]
    exact hE2
  have hm := principalSigmaMasterD (q := q) (s := s) (a := 17 / 5) (lam₁ := lam₁)
    (L := L) (M := M₀) (S1 := S₁) (S2 := S₂) (S3 := S₃)
    (W := (Work.ZeroFreeTables.P3 (((((17 : ℝ) / 5) + lam₁) : ℂ)
            / ((s - 1) * ((L : ℝ) : ℂ)))).re)
    (by push_cast; ring)
    hLpos hsre1 (by norm_num) hlam0 hz0 hz1 hz2 hF0 hF1 hF2 hd0' hd1 hd2
  have hbr : ((17 : ℝ) / 5 + lam₁) / L * M₀ + (((17 : ℝ) / 5 + lam₁) / L) ^ 2 * M₀
      + (1 / 3) * (((17 : ℝ) / 5 + lam₁) / L) ^ 3 * M₀
      + ((17 : ℝ) / 5 + lam₁) / L * (2 * S₁) + (((17 : ℝ) / 5 + lam₁) / L) ^ 2 * (4 * S₂)
      + (1 / 3) * (((17 : ℝ) / 5 + lam₁) / L) ^ 3 * (16 * S₃) ≤ ((17 : ℝ) / 5 + lam₁) * ε :=
    errorBracket_le (M₀ := M₀) (C := C) (A := 17 / 5 + M) (ε := ε) (α := (17 : ℝ) / 5 + lam₁)
      (S₁ := S₁) (S₂ := S₂) (S₃ := S₃) hL1 (by linarith) (by linarith) hA0 (le_of_lt hM₀pos)
      (le_of_lt hCpos) hS₁bd hS₂bd hS₃bd hS₁0 hS₂0 hS₃0 (hL₀bd L hLge)
  have hfin : Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s (17 / 5) lam₁
      ≤ (Work.ZeroFreeTables.P3 (((((17 : ℝ) / 5) + lam₁) : ℂ)
            / ((s - 1) * ((L : ℝ) : ℂ)))).re + (17 / 5 + lam₁) * ε := by
    refine le_trans hm ?_
    linarith [hbr]
  simpa only [hLdef] using hfin


end

end Work.ZeroFreeTables.XY
