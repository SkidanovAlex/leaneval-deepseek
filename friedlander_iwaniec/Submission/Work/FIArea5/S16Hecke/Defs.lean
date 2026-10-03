/-
# `Submission.Work.FIArea5.S16Hecke.Defs`

Vocabulary of the Hecke `L`-function chapter of `ℚ(i)` used in *FI* §16.

* `psi chi k z = χ(z)·(z/|z|)^k` — the value of the Größencharacter (16.16) at a Gaussian integer
  `z` (for primary `z` this is the value at the ideal `(z)`).
* `heckeLam chi k n = ∑_{z primary, |z|² = n} ψ(z)` — the Hecke eigenvalue (16.30).  The sum runs
  over primary `z` only, so that ideals of norm `n` and primary generators correspond bijectively
  (`Commons.NumberTheory.GaussianInt.primary_associate_exists_unique`).
* `heckeLSeries chi k s = ∑' n, λ(n)n^{-s}` — the Dirichlet series (16.17).

The elementary algebraic facts (`psi_mul`, `psi_one`, `norm_psi_le_one`, `heckeLam_even`) are
recorded here; everything else about these objects is delegated.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- **(16.16)**: the Größencharacter `ψ(z) = χ(z)·(z/|z|)^k`.  For `z = 0` the inner factor is
`0/0 = 0`, so that `ψ(0) = 0` (because `χ(0) = 0` as soon as the modulus is nonzero). -/
def psi (chi : GaussianInt → ℂ) (k : ℤ) (z : GaussianInt) : ℂ :=
  chi z * (z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ)) ^ k

/-- **(16.30)**: the Hecke eigenvalue `λ(n) = ∑_{|z|² = n} ψ(z)`, the sum running over the
*primary* Gaussian integers of norm `n` (equivalently, over the ideals of norm `n`). -/
def heckeLam (chi : GaussianInt → ℂ) (k : ℤ) (n : ℕ) : ℂ := by
  classical
  exact ∑ z ∈ (gBox (n : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = n), psi chi k z

/-- **(16.17)**: the Dirichlet series `L(s,ψ) = ∑_n λ(n)n^{-s}` attached to the eigenvalue
sequence. -/
def heckeLSeries (chi : GaussianInt → ℂ) (k : ℤ) (s : ℂ) : ℂ :=
  LSeries (heckeLam chi k) s

/-- The **spherical** theta series (16.16): `Θ(u) = Σ_{z primary} ψ(z) e^{-πu|z|²}`.  Its Mellin
transform is `π^{-s}Γ(s)L(s,ψ)` — i.e. `∫_0^∞Θ(u)u^{s-1}du = Γ(s)π^{-s}·L(s,ψ)` with
`L(s,ψ) = heckeLSeries chi k s` — which is why its functional equation (Hecke) gives the
functional equation of the Hecke `L`-function.  The `if IsPrimary z then … else 0` makes the sum
a `tsum` over all of `ℤ[i]`. -/
def thetaSph (chi : GaussianInt → ℂ) (k : ℤ) (u : ℝ) : ℂ := by
  classical
  exact ∑' z : GaussianInt,
    (if IsPrimary z then psi chi k z * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0)

/-- The **holomorphic** theta series of weight `m ≥ 0` attached to `χ`:
`H(u) = Σ_{z primary} χ(z) z^m e^{-πu|z|²}`.  It is the Poisson-friendly form (`(z/|z|)^m = z^m|z|^{-m}`
is replaced by the harmonic polynomial `z^m`), and its Mellin transform is
`∫_0^∞H(u)u^{σ-1}du = Γ(σ)π^{-σ}L(σ - m/2, ψ)`; the Mellin/Beta convolution
`Θ(u) = (πu)^{m/2}Γ(m/2)^{-1}∫_0^∞t^{m/2-1}H(u(1+t))dt` recovers the spherical theta. -/
def thetaHol (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) : ℂ := by
  classical
  exact ∑' z : GaussianInt,
    (if IsPrimary z then chi z * (z.toComplex) ^ m * Complex.exp (-Real.pi * u * (gnorm z : ℝ))
     else 0)

/-- `‖z‖ = √|z|²` for a Gaussian integer. -/
lemma norm_toComplex (z : GaussianInt) : ‖z.toComplex‖ = Real.sqrt (gnorm z : ℝ) := by
  have hsq : ‖z.toComplex‖ ^ 2 = (gnorm z : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : (z.toComplex).re = (z.re : ℝ) := by simp
    have h2 : (z.toComplex).im = (z.im : ℝ) := by simp
    rw [h1, h2, gnorm, Zsqrtd.norm_def]
    have h3 : z.re * z.re - -1 * z.im * z.im = z.re ^ 2 + z.im ^ 2 := by ring
    rw [h3]
    have h : ((z.re ^ 2 + z.im ^ 2).natAbs : ℤ) = z.re ^ 2 + z.im ^ 2 :=
      Int.natAbs_of_nonneg (by positivity)
    rw [← Int.cast_natCast, h]
    push_cast
    ring
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- `ψ(1) = χ(1)`. -/
lemma psi_one (chi : GaussianInt → ℂ) (k : ℤ) : psi chi k 1 = chi 1 := by
  rw [psi]
  have h : (1 : GaussianInt).toComplex / ((Real.sqrt (gnorm (1 : GaussianInt) : ℝ)) : ℂ) = 1 := by
    rw [GaussianInt.toComplex_one, gnorm_one, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one,
      div_one]
  rw [h, one_zpow, mul_one]

/-- **(16.16), multiplicativity**: `ψ` is multiplicative as soon as `χ` is. -/
lemma psi_mul (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (z w : GaussianInt) :
    psi chi k (z * w) = psi chi k z * psi chi k w := by
  have hbase : (z * w).toComplex / ((Real.sqrt (gnorm (z * w) : ℝ)) : ℂ)
      = (z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ))
        * (w.toComplex / ((Real.sqrt (gnorm w : ℝ)) : ℂ)) := by
    rw [GaussianInt.toComplex_mul, gnorm_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
      Complex.ofReal_mul, ← div_mul_div_comm]
  rw [psi, psi, psi, hbase, hchi z w, mul_zpow]
  ring

/-- The unit complex number `z/|z|` raised to an integer power has modulus at most one. -/
lemma norm_div_sqrt_zpow_le_one (z : GaussianInt) (k : ℤ) :
    ‖(z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ)) ^ k‖ ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [GaussianInt.toComplex_zero, gnorm, Zsqrtd.norm_def]
    norm_num
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · rw [zero_zpow k hk]; norm_num
  · have hne : z.toComplex ≠ 0 :=
      fun h => hz (GaussianInt.toComplex_injective (h.trans GaussianInt.toComplex_zero.symm))
    have h1 : ‖z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ)‖ = 1 := by
      rw [norm_div, norm_toComplex]
      have h2 : ‖((Real.sqrt (gnorm z : ℝ) : ℝ) : ℂ)‖ = Real.sqrt (gnorm z : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [h2, div_self]
      rw [← norm_toComplex, norm_ne_zero_iff]
      exact hne
    rw [norm_zpow, h1, one_zpow]

/-- **Size bound** `‖ψ(z)‖ ≤ 1` for a character with `‖χ‖ ≤ 1`. -/
lemma norm_psi_le_one (chi : GaussianInt → ℂ) (k : ℤ) (hchi : ∀ z, ‖chi z‖ ≤ 1) (z : GaussianInt) :
    ‖psi chi k z‖ ≤ 1 := by
  rw [psi, norm_mul]
  calc ‖chi z‖ * ‖(z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ)) ^ k‖ ≤ 1 * 1 :=
        mul_le_mul (hchi z) (norm_div_sqrt_zpow_le_one z k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Primary Gaussian integers have odd norm, so `λ(n) = 0` for even `n`. -/
lemma heckeLam_even (chi : GaussianInt → ℂ) (k : ℤ) {n : ℕ} (hn : Even n) :
    heckeLam chi k n = 0 := by
  classical
  unfold heckeLam
  refine Finset.sum_eq_zero ?_
  intro z hz
  rw [Finset.mem_filter] at hz
  obtain ⟨-, hprim, hgn⟩ := hz
  have hodd : Odd n := hgn ▸ isPrimary_odd_gnorm hprim
  exact absurd hn (Nat.not_even_iff_odd.mpr hodd)

end

end Work.FIArea5.S16Hecke
