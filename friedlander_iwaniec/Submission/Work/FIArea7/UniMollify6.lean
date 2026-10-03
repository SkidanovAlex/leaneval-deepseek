/-
# `Submission.Work.FIArea7.UniMollify6` — the mollification of `logFac6` ((16.7)–(16.9))

The (17.10) step needs the *pair* factor `logFac6 z₁ z₂` of `WUniOmega6Pull6` to be a **product**
`c(z₁)·conj(c(z₂))`, because that is the hypothesis of the §16 character expansion
`Work.FIArea7.section16_omegaDetect_expansion`.  `Work.FIArea7.logFac6_eq_sum_freq` (proved) gives
exactly that:

  `logFac6 z₁z₂ = (2log2 + log4) + Σ_{0<|k|≤2K, k even} (1/|k|)·c_k(z₁)·conj(c_k(z₂)) + O(1/(K|sin t|))`,

with `c_k(z) = (z/|z|)^k` and `t = arg z₂ − arg z₁`.  This file records

* `uniPow`, `evenFreq`, `logFac6Series` — the frequency factors and the truncated series, in the
  product form;
* `abs_logFac6_sub_series_le` — the pointwise error in the *sharp* form
  `≤ 4·M/(K·|Δ|)` for `|z_i|² ≤ M` and `Δ ≠ 0`, obtained from `|sin t| = |Δ|/(|z₁||z₂|)`
  (`Work.FIArea7.absDelta_eq_norm_mul_abs_sin`), which is what the pair estimate of (17.10) needs
  (the paper's `O(K⁻¹H²)` per-pair error comes from first *cutting* `log(2|sin|)` at the
  diagonal, (16.5)–(16.9); the sharp form above has no `H²`);
* `WUniOmega6Pull6Moll` — the pull-out sum with the logarithmic factor replaced by
  `logFac6Series`, i.e. the main term of (17.10).

**Caveat (the diagonal).**  For `Δ = 0` the pair contributes `0` to `WUniOmega6Pull6`
(`logFac6 = 0`) but `logFac6Series` is **not** small there (its partial sums grow like
`log K`).  Any summed error estimate must therefore treat the `Δ = 0` pairs separately; this is
the discrete counterpart of the paper's near-diagonal cut (`O(H⁻¹N²)`,
`Work.FIArea7.diagonal_cutoff_le`).
-/
import Mathlib
import Submission.Work.FIArea7.UniChain6
import Submission.Work.FIArea7.logFac6_eq_sum_freq
import Submission.Work.FIArea7.LogFacArg
import Submission.Work.FIArea7.Section16Expansion
import Submission.Work.FIArea4.absDelta_le_sector

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The frequency factors and the truncated series -/

/-- The unit-angle power `(z/|z|)^k` — the frequency factor of the expansion (16.9)/(17.10). -/
def uniPow (z : GaussianInt) (k : ℤ) : ℂ :=
  (z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ)) ^ k

/-- The even, non-zero frequencies `0 < |k| ≤ 2K` (the index set of `logFac6_eq_sum_freq`). -/
def evenFreq (K : ℕ) : Finset ℤ :=
  (Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter (fun k => k ≠ 0 ∧ Even k)

/-- **The truncated Fourier series of `logFac6`**, in the product form `c_k(z₁)·conj(c_k(z₂))`
that the §16 expansion (16.11) consumes. -/
def logFac6Series (z1 z2 : GaussianInt) (K : ℕ) : ℂ :=
  ((2 * Real.log 2 + Real.log 4 : ℝ) : ℂ)
    + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * (uniPow z1 k * star (uniPow z2 k))

/-- `logFac6` vanishes on the diagonal `Δ = 0` (Lean's `x / 0 = 0`, `Real.log 0 = 0`). -/
lemma logFac6_eq_zero_of_absDelta_eq_zero {z1 z2 : GaussianInt}
    (h : Work.FIPlan.absDelta z1 z2 = 0) : Work.FITop4.logFac6 z1 z2 = 0 := by
  rw [Work.FITop4.logFac6, h]
  simp

/-! ## 2. The pointwise mollification error -/

/-- **The pointwise error of the truncated Fourier series of `logFac6`.**  For `z₁, z₂` with
`|z_i|² ≤ M` and `Δ ≠ 0`,

  `‖logFac6 z₁z₂ − logFac6Series z₁z₂ K‖ ≤ 4·M / (K·|Δ|)`,

i.e. the sharp form of (16.9): `|sin t| = |Δ|/(|z₁||z₂|)` turns the `1/(K|sin t|)` error of
`Work.FIArea7.logFac6_eq_sum_freq` into `|z₁z₂|/(K|Δ|) ≤ M/(K|Δ|)`. -/
theorem abs_logFac6_sub_series_le (z1 z2 : GaussianInt) (K : ℕ) (hK : 1 ≤ K) {M : ℝ}
    (hM : 0 ≤ M) (hz1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ M)
    (hz2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ M) (hD : Work.FIPlan.Delta z1 z2 ≠ 0) :
    ‖((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K‖
      ≤ 4 * M / ((K : ℝ) * (Work.FIPlan.absDelta z1 z2 : ℝ)) := by
  have h0 := Work.FIArea7.logFac6_eq_sum_freq z1 z2 K hK hD
  have hsub : ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K
      = ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - ((2 * Real.log 2 + Real.log 4 : ℝ) : ℂ)
        - ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * (uniPow z1 k * star (uniPow z2 k)) := by
    rw [logFac6Series]
    ring
  rw [hsub]
  refine le_trans h0 ?_
  -- `|sin t| = |Δ|/(‖z₁‖‖z₂‖)`
  have hΔcast : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := by
    rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]
  -- the two norms are positive
  have hz1ne : z1 ≠ 0 := by
    intro h0
    rw [h0, Work.FIPlan.Delta] at hD
    simp at hD
  have hz2ne : z2 ≠ 0 := by
    intro h0
    rw [h0, Work.FIPlan.Delta] at hD
    simp at hD
  have hZ1 : (z1 : ℂ) ≠ 0 :=
    Work.FIArea7.LogFacArg.toComplex_ne_zero_of_gnorm_pos
      (Work.FIArea7.LogFacArg.gnorm_pos_of_ne_zero hz1ne)
  have hZ2 : (z2 : ℂ) ≠ 0 :=
    Work.FIArea7.LogFacArg.toComplex_ne_zero_of_gnorm_pos
      (Work.FIArea7.LogFacArg.gnorm_pos_of_ne_zero hz2ne)
  have hp0 : 0 < ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ :=
    mul_pos (norm_pos_iff.mpr hZ1) (norm_pos_iff.mpr hZ2)
  have hsin : |Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg)|
      = ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) / (‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖) := by
    rw [Work.FIArea7.LogFacArg.sin_arg_sub hD, abs_div, hΔcast,
      abs_of_pos hp0]
  rw [hsin]
  have had0 : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    rw [hΔcast]
    exact abs_pos.mpr (Int.cast_ne_zero.mpr hD)
  have hK0 : 0 < (K : ℝ) := by exact_mod_cast hK
  -- `4 / (K·(|Δ|/‖z₁z₂‖)) = 4‖z₁z₂‖ / (K·|Δ|)`
  rw [show (4 : ℝ) / ((K : ℝ) * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
        / (‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖)))
      = 4 * (‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖)
        / ((K : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) by
    rw [← mul_div_assoc, div_div_eq_mul_div]]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hprod : ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ ≤ M := by
    have h1 : ‖(z1 : ℂ)‖ ≤ Real.sqrt M := by
      rw [← Work.FIArea4.sqrt_gnorm z1]; exact Real.sqrt_le_sqrt hz1
    have h2 : ‖(z2 : ℂ)‖ ≤ Real.sqrt M := by
      rw [← Work.FIArea4.sqrt_gnorm z2]; exact Real.sqrt_le_sqrt hz2
    calc ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ ≤ Real.sqrt M * Real.sqrt M :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg M)
      _ = M := Real.mul_self_sqrt hM
  have hstep : (4 : ℝ) * (‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖)
        * ((K : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
      ≤ 4 * M * ((K : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith [hprod]) (by positivity)
  exact hstep

/-! ## 3. The mollified pull-out sum -/

/-- **The main term of (17.10)**: the pull-out sum with the logarithmic factor replaced by its
truncated Fourier series `logFac6Series`. -/
def WUniOmega6Pull6Moll (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (K : ℕ) : ℂ :=
  2 * ∑ b ∈ Finset.Icc 1 (uniB Pa),
        ∑ e ∈ Finset.Icc 1 X,
          (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
            * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  (if Work.FIPlan.GaussCoprime z1 z2
                      ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
                    (Work.FIArea7.reflSign z1 z2 : ℂ)
                      * omegaDetect (4 * b * e) e z1 z2
                      * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
                      * (betaPrime β z1 * star (betaPrime β z2))
                      * logFac6Series z1 z2 K
                   else 0)

/-- The §17 coefficient of the `k`-th Fourier mode: `c_k(z) = ε(z)·β'(z)·(z/|z|)^k`.  The sign
factor `ε` is `1` or `sgn(z.re)` according to which branch of `Work.FIArea7.reflSign_separable`
holds on the box; it enters the character sums of (17.10)/(17.12) inside the coefficient, where
both choices produce the same bound (Proposition 17.2 is uniform in the character and in `k`). -/
def uniCoeff (ε : GaussianInt → ℤ) (β : GaussianInt → ℂ) (k : ℤ) (z : GaussianInt) : ℂ :=
  (ε z : ℂ) * betaPrime β z * uniPow z k

/-- **The pair sum of one Fourier mode** (`k`), with the guards of the pull-out (`(z₁,z₂) = 1` and
`4be ∣ |Δ|`) and all the §17 factors (`reflSign`, `omegaDetect`, the Kubota power) but *without*
the logarithmic factor.  `Work.FIArea7.WUniOmega6Pull6Moll` is the `(b,e)`-sum of these, weighted
by `(2log2+log4)` for `k = 0` and `1/|k|` for `k ∈ evenFreq K`
(`Work.FIArea7.WUniOmega6Pull6Moll_eq_modes`). -/
def uniModePair (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ) (k : ℤ) : ℂ :=
  ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
    ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
        (Work.FIArea7.reflSign z1 z2 : ℂ) * omegaDetect (4 * b * e) e z1 z2
          * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
          * (betaPrime β z1 * star (betaPrime β z2))
          * (uniPow z1 k * star (uniPow z2 k))
       else 0)

/-- **The `unitInd`/`ω`-sum form of a Fourier mode** — exactly the left-hand side of the §16
identity `Work.FIArea7.section16_omegaDetect_expansion` at the modulus `Q = 4be` and the
coefficient `c = Work.FIArea7.uniCoeff ε β k`: the pair criterion is the congruence (encoded by
`omegaDetect`, which unfolds to the explicit `ω`-sum `Σ_ω [z₁ ≡ ωz₂] (ω|e)` by
`Work.FIArea7.omegaDetect_unfold6` when `4be ≠ 0`) and the coprimality guard is still present.
`Work.FIArea7.uniModePair_eq_uniModeChar` identifies the two. -/
def uniModeChar (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ) (k : ℤ)
    (ε : GaussianInt → ℤ) : ℂ :=
  ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
    ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      (if Work.FIPlan.GaussCoprime z1 z2 then
        unitInd (4 * b * e) z1 * unitInd (4 * b * e) z2
          * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
          * omegaDetect (4 * b * e) e z1 z2
       else 0)

/-- **The off-diagonal cut of the mollified main term.**  As `WUniOmega6Pull6Moll`, but with the
pair criterion strengthened by `M ≤ |Δ(z₁,z₂)|` — the pairs on which the truncated series of
`logFac6` approximates it with the *uniform* error `4(1+θ)N/(K·M)`
(`Work.FIArea7.abs_logFac6_sub_series_le`, i.e. the `|Δ|`-cut form of *FI* (16.9); the same cut is
`Work.FIArea7.logFac_expansion_offdiag`, whose uniform error is `16(2Rz+1)²/(K·M)`).  The pairs
with `|Δ| < M` are the near-diagonal ones; they are estimated by
`Work.FIArea7.card_pairs_gBox_absDelta_lt`. -/
def WUniOmega6Pull6Cut (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ)
    (K M : ℕ) : ℂ :=
  2 * ∑ b ∈ Finset.Icc 1 (uniB Pa),
        ∑ e ∈ Finset.Icc 1 X,
          (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
            * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  (if Work.FIPlan.GaussCoprime z1 z2
                      ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2
                      ∧ M ≤ Work.FIPlan.absDelta z1 z2 then
                    (Work.FIArea7.reflSign z1 z2 : ℂ)
                      * omegaDetect (4 * b * e) e z1 z2
                      * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
                      * (betaPrime β z1 * star (betaPrime β z2))
                      * logFac6Series z1 z2 K
                   else 0)

end

end Work.FIArea7
