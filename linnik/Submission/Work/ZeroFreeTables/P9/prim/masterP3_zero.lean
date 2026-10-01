/-
# ZeroFreeTables/P9/prim/masterP3_zero

The zero-sum substitution of `masterP3`: starting from the explicit-formula shape
`SigmaP3L_eq_explicit_zeros`, the two zero sums `Z₂, Z₃` are replaced by their near/far bounds
`quadNearFar`/`cubicNearFar`, and the near pieces are reassembled with `nearP3sum_split`.

The parity (trivial) sums `T₂, T₃` are deliberately left symbolic: this lemma is exactly the
part of the assembly that depends on the zeros, and the parity terms are bounded separately.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.prim.masterP3
import Submission.Work.ZeroFreeTables.P9.prim.quadNearFar_selfContained
import Submission.Work.ZeroFreeTables.P9.prim.cubicNearFar
import Submission.Work.ZeroFreeTables.P9.prim.nearP3sum_split

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.P9.prim

/-- **Zero-sum substitution.**  For a non-principal primitive character, `1 < Re s`,
`Re s ≤ 1 + δ/2`, `α = a + λ₁ ≥ 0` and `L > 0`,

`Σ(s,χ) ≤ -nearP3sum + (α/L)·(Re(-L'/L)(s) + nearInvSum)`
`            + (α/L)²·((1+4/δ²)·invSqSum - Re T₂)`
`            + (2/3)(α/L)³·((2/δ)(1+4/δ²)·invSqSum - Re T₃)`.

The `-nearP3sum` packages the near parts of the two zero sums; the `invSqSum` terms are the far
parts; the parity sums `T₂, T₃` are untouched. -/
theorem SigmaP3L_le_nearP3sum_add {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {a lam₁ δ L : ℝ} (hα : 0 ≤ a + lam₁) (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) {s : ℂ} (hs : 1 < s.re) (hsδ : s.re ≤ 1 + δ / 2)
    (par : ℕ) (hpar0 : χ.Even → par = 0) (hpar1 : χ.Odd → par = 1)
    (hsum2 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2))
    (hsum3 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3)) :
    SigmaP3L N L χ s a lam₁
      ≤ -nearP3sum N L χ s a lam₁ δ
        + ((a + lam₁) / L) * ((-logDeriv (DirichletCharacter.LFunction χ) s).re
            + nearInvSum N χ s δ)
        + ((a + lam₁) / L) ^ 2 *
            ((1 + 4 / δ ^ 2) * invSqSum N χ s
              - (∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2).re)
        + (2 / 3) * ((a + lam₁) / L) ^ 3 *
            ((2 / δ) * (1 + 4 / δ ^ 2) * invSqSum N χ s
              - (∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3).re) := by
  have hquad := quadNearFar_selfContained χ hχ hprim hδ hδ1 hs hsδ hsum2
  have hcub := cubicNearFar χ hχ hprim hδ hδ1 hs hsδ hsum3
  have hsplit := nearP3sum_split (a := a) (lam₁ := lam₁) (L := L) χ hχ hprim hδ hδ1 hs hsδ hsum2 hsum3
  have hA2 : 0 ≤ ((a + lam₁) / L) ^ 2 := sq_nonneg _
  have hA3 : 0 ≤ (2 / 3) * ((a + lam₁) / L) ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg (div_nonneg hα (le_of_lt hL)) 3)
  have hq2 := mul_le_mul_of_nonneg_left hquad hA2
  have hc2 := mul_le_mul_of_nonneg_left hcub hA3
  -- rearrange the two multiplied near/far bounds into "bracket ≥ 0" form
  have hq2' : 0 ≤ ((a + lam₁) / L) ^ 2 *
      ((1 + 4 / δ ^ 2) * invSqSum N χ s
        - (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u
            * ((1 / (s - u)) ^ 2).re)
        + (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2).re) := by
    have := hq2
    nlinarith [this]
  have hc2' : 0 ≤ (2 / 3) * ((a + lam₁) / L) ^ 3 *
      ((2 / δ) * (1 + 4 / δ ^ 2) * invSqSum N χ s
        - (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u
            * ((1 / (s - u)) ^ 3).re)
        + (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3).re) := by
    have := hc2
    nlinarith [this]
  rw [SigmaP3L_eq_explicit_zeros χ hχ hprim par hpar0 hpar1 hs a lam₁ L]
  rw [Complex.add_re, Complex.add_re, hsplit, Complex.neg_re]
  nlinarith [hq2', hc2']

end Work.ZeroFreeTables.P9.prim
