/-
# `Submission.Work.FIArea6Road.PhifacIdent` — the Euler-product identity `Φ = M·L`

*FI* (16.31) continues `M(s) = ∏_p (1 - λ(p)p^{-s})` past `re s = 1` by writing it as a quotient of
the absolutely convergent Euler product

  `Φ(s) = ∏_p (1 - λ(p)p^{-s}) / localL_p(s)`,   `localL_p(s) = 1 - λ(p)p^{-s} + (λ(p)²-λ(p²))p^{-2s}`,

by the Hecke `L`-series `L(s,ψ) = Σ_n λ(n)n^{-s}`: indeed `Φ = M·L`.  This module proves that
identity, i.e. it factors the infinite product defining `Phifac` into the infinite product `Mfac`
and the Euler product of the Hecke `L`-series.

The proof has three ingredients:

* `MultipliableLocF` — the product `M(s) = ∏_p (1 - λ(p)p^{-s})` converges unconditionally for
  `re s > 1` (the local deviations `λ(p)p^{-s}` are summable since `‖λ(p)‖ ≤ 2` and `Σ_p p^{-σ}`
  converges);
* `LocalLInvTprod` — the inverse local factors form a convergent product with value `L(s,ψ)`
  (`localL_p(s)⁻¹ = Σ_ν λ(p^ν)p^{-νs}`, from the local recursion, and Mathlib's Euler product);
* the infinite product of a pointwise product factors, `Multipliable.tprod_mul`.
-/
import Mathlib
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd
import Submission.Work.FIArea5.S16Hecke.heckeLam_localInverse
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four

namespace Work.FIArea6Road

open scoped BigOperators

set_option maxHeartbeats 1600000

noncomputable section

/-- The local Hecke eigenvalue at a rational prime is bounded by `2`: `‖λ(p)‖ ≤ 2`. -/
lemma heckeLam_prime_norm_le_two' (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (p : Nat.Primes) :
    ‖Work.FIArea5.S16Hecke.heckeLam chi m (p : ℕ)‖ ≤ 2 := by
  have hp : Nat.Prime (p : ℕ) := p.2
  by_cases h4 : (p : ℕ) % 4 = 1
  · exact Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two hp h4 hchibd
  · rw [Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four hp h4]; norm_num

/-- **The Euler product `M(s) = ∏_p (1 - λ(p)p^{-s})` converges** for `re s > 1`.

The local deviations `u_p = λ(p)p^{-s}` satisfy `‖u_p‖ ≤ 2 p^{-σ}` with `σ = re s > 1`, so
`Σ_p ‖u_p‖ < ∞`; Mathlib's `multipliable_one_add_of_summable` then gives the unconditional
convergence of `∏_p (1 + (-u_p))`. -/
theorem MultipliableLocF (chi : GaussianInt → ℂ) (m : ℤ) {s : ℂ} (hs : 1 < s.re)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    Multipliable (fun p : Nat.Primes =>
      1 - Work.FIArea5.S16Hecke.heckeLam chi m (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) := by
  have hsum : Summable (fun p : Nat.Primes =>
      ‖-(Work.FIArea5.S16Hecke.heckeLam chi m (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))‖) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hprimes : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s.re)) :=
      hbase.subtype (fun n : ℕ => n.Prime)
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) (hprimes.mul_left 2)
    have hp : Nat.Prime (p : ℕ) := p.2
    rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos (-s), Complex.neg_re]
    have hlam := heckeLam_prime_norm_le_two' chi m hchibd p
    exact mul_le_mul_of_nonneg_right hlam (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact multipliable_one_add_of_summable
    (f := fun p : Nat.Primes =>
      -(Work.FIArea5.S16Hecke.heckeLam chi m (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))) hsum

/-- **The local Euler factor inversion** at a rational prime: for `re s > 1`,
`localL_p(s)⁻¹ = Σ_ν λ(p^ν) p^{-νs}`.

With `z = p^{-s}` (`‖z‖ < 1`), the local recursion `heckeLam_localInverse` gives
`(Σ_ν λ(p^ν)z^ν)·localL_p(s) = 1`, whence `localL_p(s)⁻¹ = Σ_ν λ(p^ν)z^ν`; rewriting
`z^ν = p^{-νs}` finishes. -/
lemma localL_inv_eq_localFactor (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    (Work.FIArea6.TauPieces.localL chi m (p : ℕ) s)⁻¹
      = ∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam chi m ((p : ℕ) ^ e)
          / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)) := by
  have hp : Nat.Prime (p : ℕ) := p.2
  have hz : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos (-s), Complex.neg_re]
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp.two_le
    have h1 : (((p : ℕ) : ℝ)) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    have h2 : (2 : ℝ) ^ (-s.re) < 1 := by
      have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
        (show -s.re < 0 by linarith)
      rwa [Real.rpow_zero] at h
    linarith
  have hkey := Work.FIArea5.S16Hecke.heckeLam_localInverse (k := m) hp hchimul hchi1 hchibd hz
  have hkey2 : (∑' e : ℕ,
        Work.FIArea5.S16Hecke.heckeLam chi m ((p : ℕ) ^ e) * (((p : ℕ) : ℂ) ^ (-s)) ^ e)
      * Work.FIArea6.TauPieces.localL chi m (p : ℕ) s = 1 := by
    rw [Work.FIArea6.TauPieces.localL]
    exact hkey
  have hS : (∑' e : ℕ,
        Work.FIArea5.S16Hecke.heckeLam chi m ((p : ℕ) ^ e) * (((p : ℕ) : ℂ) ^ (-s)) ^ e)
      = ∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam chi m ((p : ℕ) ^ e)
          / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)) := by
    refine tsum_congr fun e => ?_
    rw [div_eq_mul_inv, ← Complex.cpow_nat_mul]
    congr 1
    rw [show (e : ℂ) * (-s) = -((e : ℂ) * s) by ring, Complex.cpow_neg]
  rw [← hS]
  exact inv_eq_of_mul_eq_one_left hkey2

/-- **The Euler product of `L(s,ψ)` in terms of the local factors `localL`**: for `re s > 1`,
`∏_p localL_p(s)⁻¹ = L(s,ψ)`, and the product converges unconditionally.

The pointwise inversion `localL_inv_eq_localFactor` converts this into Mathlib's Euler product
(`heckeLSeries_eulerProduct_hasProd`). -/
theorem LocalLInvTprod (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (Work.FIArea6.TauPieces.localL chi m (p : ℕ) s)⁻¹)
        = Work.FIArea5.S16Hecke.heckeLSeries chi m s
      ∧ Multipliable (fun p : Nat.Primes =>
          (Work.FIArea6.TauPieces.localL chi m (p : ℕ) s)⁻¹) := by
  have hB : ∀ p : Nat.Primes,
      (Work.FIArea6.TauPieces.localL chi m (p : ℕ) s)⁻¹
        = ∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam chi m ((p : ℕ) ^ e)
            / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)) :=
    fun p => localL_inv_eq_localFactor chi m hchi1 hchimul hchibd hs p
  have hMulti : Multipliable (fun p : Nat.Primes =>
      ∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam chi m ((p : ℕ) ^ e)
        / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s))) :=
    ⟨Work.FIArea5.S16Hecke.heckeLSeries chi m s,
      Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd chi m hchi1 hchimul hchibd hs⟩
  refine ⟨?_, ?_⟩
  · rw [tprod_congr hB]
    exact Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct chi m hchi1 hchimul hchibd hs
  · simpa only [hB] using hMulti

theorem PhifacIdent (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea6.TauPieces.Phifac chi m s
      = Work.FIArea6.TauPieces.Mfac chi m s * Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
  obtain ⟨hLinvEq, hMlinv⟩ := LocalLInvTprod chi m hchi1 hchimul hchibd hs
  have hMlocF := MultipliableLocF chi m hs hchibd
  have hPhifac : Work.FIArea6.TauPieces.Phifac chi m s
      = ∏' p : Nat.Primes,
          (1 - Work.FIArea5.S16Hecke.heckeLam chi m (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))
            / Work.FIArea6.TauPieces.localL chi m (p : ℕ) s := rfl
  rw [hPhifac]
  have hsplit : ∀ p : Nat.Primes,
      (1 - Work.FIArea5.S16Hecke.heckeLam chi m (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))
          / Work.FIArea6.TauPieces.localL chi m (p : ℕ) s
        = (1 - Work.FIArea5.S16Hecke.heckeLam chi m (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))
          * (Work.FIArea6.TauPieces.localL chi m (p : ℕ) s)⁻¹ := fun p => div_eq_mul_inv _ _
  rw [tprod_congr hsplit, Multipliable.tprod_mul hMlocF hMlinv, hLinvEq]
  rfl

end

end Work.FIArea6Road
