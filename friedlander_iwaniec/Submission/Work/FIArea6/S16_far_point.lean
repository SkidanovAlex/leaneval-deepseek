/-
# `Submission.Work.FIArea6.S16_far_point` — the pointwise truncation error of §16

The three reusable ingredients of the far-pair estimate of *FI* (16.9)/(16.15), kept in a module
of their own so that the §16 mass modules can import them without importing
`Submission.Work.FIArea6.S16_error_bound` itself (the mass modules are consumed by that file, so
importing it back would be circular):

* `theta_le_one_of_params` — `Pa.θ ≤ 1`;
* `gnorm_le_two_N` — `|z|² ≤ 2N` on the support of a round-6 coefficient (from (5.14));
* `error_le_far` — for a pair off the diagonal with both members on the support,
  `‖logFac6 z₁z₂ − logFac6Series z₁z₂ (Kcut X)‖ ≤ 8N/(X³·|Δ(z₁,z₂)|)`.

`Kcut X = X³` is the frequency cutoff of (16.9) and `8 = 4·2` is `4M` with `M ≥ |zᵢ|²`
(`abs_logFac6_sub_series_le` gives `4M/(K|Δ|)`; on the support `M = 2N`).
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea7.UniMollify6

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `θ ≤ 1` for the §16 parameters. -/
lemma theta_le_one_of_params (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
  · have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have h3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    linarith [Real.log_le_log (by norm_num) hx3]
  · have h : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    linarith

/-- On the support of a round-6 coefficient, `|z|² ≤ 2N`. -/
lemma gnorm_le_two_N {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hz : β z ≠ 0) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * Pa.N := by
  obtain ⟨-, -, hle, -⟩ := Work.FITop4.IsBetaCoeff6.support hβ hz
  have hθ1 := theta_le_one_of_params Pa
  have hN1 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  nlinarith [hle, hθ1, hN1]

/-- **The far-pair pointwise error** (*FI* (16.9) sharpened): off the diagonal, the truncated
Fourier series of `logFac6` differs from `logFac6` by at most `8N/(X³|Δ(z₁,z₂)|)`. -/
lemma error_le_far {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (X : ℕ) (hX : 1 ≤ X)
    {z1 z2 : GaussianInt} (hz1 : β z1 ≠ 0) (hz2 : β z2 ≠ 0)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) :
    ‖(Work.FITop4.logFac6 z1 z2 : ℂ) - Work.FIArea7.logFac6Series z1 z2 (Kcut X)‖
      ≤ 8 * Pa.N / ((Kcut X : ℝ) * (Work.FIPlan.absDelta z1 z2 : ℝ)) := by
  have hK : 1 ≤ Kcut X := by rw [Kcut]; exact one_le_pow₀ hX
  have hM : (0 : ℝ) ≤ 2 * Pa.N := by linarith [Pa.hN1]
  refine le_trans (Work.FIArea7.abs_logFac6_sub_series_le z1 z2 (Kcut X) hK hM
    (gnorm_le_two_N hβ hz1) (gnorm_le_two_N hβ hz2) hΔ) (le_of_eq ?_)
  ring

/-- On the support of a round-6 coefficient, `|z|²` is coprime to `4d` whenever `4d ≤ Pz`: every
prime divisor of `4d` is `≤ 4d ≤ Pz`, and (5.8) forbids such primes from dividing `|z|²`. -/
lemma coprime_gnorm_four_mul {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) {d : ℕ} (hd : 1 ≤ d) (hPz : 4 * d ≤ Pa.Pz) :
    Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) := by
  have h4d : 0 < 4 * d := by omega
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : p ∣ Work.FIPlan.gnorm z := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ 4 * d := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  have hpPz : p ≤ Pa.Pz := le_trans (Nat.le_of_dvd h4d h2) hPz
  exact (Work.FITop4.IsBetaCoeff6.noSmallPrimes hβ hz) p hp hpPz h1

/-- `unitInd (4d) z = 1` on the support of a round-6 coefficient, for `4d ≤ Pz`. -/
lemma unitInd_eq_one_of_mem_supp {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) {d : ℕ} (hd : 1 ≤ d) (hPz : 4 * d ≤ Pa.Pz) :
    Work.FIArea7.unitInd (4 * d) z = 1 := by
  simp only [Work.FIArea7.unitInd,
    if_pos (coprime_gnorm_four_mul hβ hz hd hPz)]

end

end Work.FIArea6
