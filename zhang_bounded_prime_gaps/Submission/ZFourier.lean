import Mathlib
import Submission.SieveExpansion
import Submission.FinalCompetitor

open scoped BigOperators
open scoped FourierTransform RealInnerProductSpace SchwartzMap Topology
open MeasureTheory

/-!
# P8 Lemma 4.1 campaign: the per-coordinate multiplicative sum `Z(F,G)`

The remaining analytic input for the sieve main term (see the boundary marker
in `SieveExpansion.lean`) is P8 Lemma 4.1: for smooth compactly supported
`F, G : ℝ → ℝ` and scale `R`,

    Z(F,G) := Σ_{d,d′ ≥ 1, ([d,d′],WN) = 1} μ(d)μ(d′)F(log_R d)G(log_R d′)/[d,d′]

    = (1 + o(1)) · B⁻¹ · N/φ(N) · ∫₀^∞ F′(t)G′(t) dt ,   B := φ(W)/W · log R.

This file hosts the campaign.  Its internal decomposition:

  1. *Fourier representation* (P8 (37)): with `H(u) := eᵘF(u)` extended to a
     smooth compactly supported function on ℝ, `F(log_R d)` is recovered from
     the Fourier transform of `H`:
     `F(log_R d) = ∫_ℝ Ĥ(ξ)·exp(−(1+iξ)·log d / log R) dξ`.
     Mathlib provides the Fourier calculus
     (`Mathlib.Analysis.Fourier.FourierTransform`, `.Inversion`,
     `.SchwartzSpace.Fourier`, `Mathlib.Analysis.Distribution.FourierSchwartz`);
     the plan is to use the Schwartz-space inversion for the smooth compactly
     supported `H`.
  2. *Modified-zeta Euler product and simple pole*: the ξ-dependent sum over
     `d,d′` (once `μμ/[d,d′]` is summed with the exponential weights) factors
     through `ζ_{WN}(s) := ∏_{p ∤ WN} (1 − p⁻ˢ)⁻¹` near `s = 1`.
  3. *Truncation estimates*: the ξ-integrals away from `ξ = 0` are negligible
     (rapid decay of `Ĥ`), leaving the pole contribution `∫F′G′`.

Everything below is the *algebraic shell* of the campaign: the per-coordinate
object `Zpair` in the finite formal setting (sums over `Fin (D+1)`, matching
the ranges used throughout), and its Möbius sign / squarefree form.

Status of the three analytic sub-goals of 4.1:
  (i) *Fourier representation* (P8 (37)) — DONE in this file: `divisorForm`
      (inversion at a point), `divisorForm_phase` (the phase pulled inside the
      integral), and `divisorForm_smoothComp` (hypothesis-free corollary for
      smooth compactly supported `F`, via the Schwartz representative
      `expCutoffSchwartz` and the integrability lemmas `expCutoff_integrable`,
      `fourier_expCutoff_integrable`).
  (ii) *Modified-zeta Euler product and simple pole* (`ζ_{WN}(s)` at `s = 1`),
       and
  (iii) *truncation estimates* (ξ-integrals away from 0 are negligible),
  remain future work.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- Base-`R` logarithm on divisor values, `log_R d := log d / log R`. -/
noncomputable def logR (d R : ℕ) : ℝ := Real.log (d : ℝ) / Real.log (R : ℝ)

/-- The per-coordinate multiplicative summand `μ(a)μ(b)F(log_R a)G(log_R b)`
divided by `[a,b]` (in the finite formal range `a, b < D+1`). -/
noncomputable def Zpair {D : ℕ} (F G : ℝ → ℝ) (R : ℕ) : ℝ :=
  ∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
    moebiusReal (a : ℕ) * moebiusReal (b : ℕ) *
      F (logR (a : ℕ) R) * G (logR (b : ℕ) R) /
        ((Nat.lcm (a : ℕ) (b : ℕ) : ℕ) : ℝ)

/-- A single coordinate of the sieve is not squarefree if the corresponding
value is 0, and μ(0)=0; here we record that only squarefree values contribute.
-/
lemma Zpair_pointwise_eq_sqInd {D : ℕ} {F G : ℝ → ℝ} (R : ℕ)
    {a b : Fin (D + 1)} :
    moebiusReal (a : ℕ) * moebiusReal (b : ℕ) *
        F (logR (a : ℕ) R) * G (logR (b : ℕ) R) /
          ((Nat.lcm (a : ℕ) (b : ℕ) : ℕ) : ℝ) =
      (if Squarefree (a : ℕ) ∧ Squarefree (b : ℕ) then (1 : ℝ) else 0) *
        (moebiusReal (a : ℕ) * moebiusReal (b : ℕ) *
          F (logR (a : ℕ) R) * G (logR (b : ℕ) R) /
            ((Nat.lcm (a : ℕ) (b : ℕ) : ℕ) : ℝ)) := by
  classical
  by_cases hs : Squarefree (a : ℕ) ∧ Squarefree (b : ℕ)
  · simp [hs]
  · have hzero : moebiusReal (a : ℕ) * moebiusReal (b : ℕ) = 0 := by
      by_cases hna : Squarefree (a : ℕ)
      · have hnb : ¬ Squarefree (b : ℕ) := by
          intro hb
          exact hs ⟨hna, hb⟩
        have hμ : (ArithmeticFunction.moebius (b : ℕ) : ℝ) = 0 := by
          have hz : ArithmeticFunction.moebius (b : ℕ) = 0 :=
            ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnb
          simp [hz]
        simp [moebiusReal, hμ]
      · have hμ : (ArithmeticFunction.moebius (a : ℕ) : ℝ) = 0 := by
          have hz : ArithmeticFunction.moebius (a : ℕ) = 0 :=
            ArithmeticFunction.moebius_eq_zero_of_not_squarefree hna
          simp [hz]
        simp [moebiusReal, hμ]
    simp [hs, hzero]


/-- The per-coordinate multiplicative sum, restricted to squarefree values
(sum-level: non-squarefree pairs contribute zero). -/
theorem Zpair_sqfree_restricted {D : ℕ} {F G : ℝ → ℝ} (R : ℕ) :
    Zpair (D := D) F G R =
      ∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
        (if Squarefree (a : ℕ) ∧ Squarefree (b : ℕ) then (1 : ℝ) else 0) *
          (moebiusReal (a : ℕ) * moebiusReal (b : ℕ) *
            F (logR (a : ℕ) R) * G (logR (b : ℕ) R) /
              ((Nat.lcm (a : ℕ) (b : ℕ) : ℕ) : ℝ)) := by
  classical
  dsimp [Zpair]
  refine Finset.sum_congr rfl ?_
  intro a ha
  refine Finset.sum_congr rfl ?_
  intro b hb
  exact Zpair_pointwise_eq_sqInd R

/-! ## Anchor for 4.1(i): Fourier inversion in Mathlib

The inversion theorem available in Mathlib is
`MeasureTheory.Integrable.fourierInv_fourier_eq`
(`Analysis/Fourier/Inversion.lean`): if `f : V → E` (V a finite-dimensional
real inner product space, E complete) is integrable and its Fourier transform
`𝓕 f` is integrable, then `𝓕⁻ (𝓕 f) v = f v` at every continuity point `v`.

For 4.1(i) the plan is: take `H(u) := eᵘ·F(u)` (complex-valued, smooth
compactly supported, hence integrable with integrable Schwartz-class Fourier
transform), obtain `H(log_R d) = (𝓕⁻ (𝓕 H)) (log_R d)` by
`fourierInv_fourier_eq`, unfold the inverse transform to
`∫_ℝ exp(character (log_R d · ξ))·(𝓕 H)(ξ) dξ`, and change variables to write
`F(log_R d) = ∫_ℝ Ĥ(ξ)·exp(−(1+iξ)·log d/log R) dξ` (P8 (37)), matching the
per-coordinate sums.  The remaining steps of the campaign (interchange the
finite `d,d′`-sums with the resulting double integral, factor the inner sum
through `ζ_{WN}`, estimate the tails) are future work; this file holds the
algebraic shell (`Zpair`, squarefree restriction) and the exact API anchor
above. -/


/-- The `eᵘF(u)` rescaling of a smooth cutoff, as a complex-valued function
(this is the `H` of P8 (37), smooth compactly supported when `F` is). -/
noncomputable def expCutoff (F : ℝ → ℝ) : ℝ → ℂ := fun u => ((Real.exp u * F u : ℝ) : ℂ)

/-- **4.1(i), inversion step.**  For `H := expCutoff F`, Mathlib's Fourier
inversion (`fourierInv_fourier_eq` at the point `u`) gives
`H(u) = ∫_ξ 𝐞(u·ξ)·(𝓕H)(ξ) dξ`, where `𝐞(x) = exp(2πix)` — i.e. `H` is the
inverse Fourier transform of `𝓕 H` (Mathlib's normalization, no prefactor). -/
theorem fourierInversion_expCutoff (F : ℝ → ℝ) (u : ℝ)
    (hcont : ContinuousAt (expCutoff F) u)
    (hint : Integrable (expCutoff F))
    (hint' : Integrable (𝓕 (expCutoff F))) :
    expCutoff F u = ∫ ξ : ℝ, (𝐞 (u * ξ) * 𝓕 (expCutoff F) ξ) := by
  have h := (hint.fourierInv_fourier_eq (E := ℂ) hint' hcont)
  rw [← h]
  rw [Real.fourierInv_eq (f := 𝓕 (expCutoff F)) (w := u)]
  apply integral_congr_ae
  filter_upwards with v
  congr 1


/-- P8 (37) algebraic step: `e^{-u}·(eᵘF(u)) = F(u)`. -/
lemma F_eq_exp_neg_expCutoff (F : ℝ → ℝ) (u : ℝ) :
    (F u : ℂ) = Complex.exp (-(u : ℂ)) * expCutoff F u := by
  have h : Complex.exp (-(u : ℂ)) * expCutoff F u = (F u : ℂ) := by
    calc
      Complex.exp (-(u : ℂ)) * expCutoff F u
          = Complex.exp (-(u : ℂ)) * ((Real.exp u : ℂ) * (F u : ℂ)) := by
              dsimp [expCutoff]
              rw [Complex.ofReal_mul]
      _ = Complex.exp (-(u : ℂ)) * (Complex.exp (u : ℂ) * (F u : ℂ)) := by
              rw [Complex.ofReal_exp]
      _ = (Complex.exp (u : ℂ))⁻¹ * (Complex.exp (u : ℂ) * (F u : ℂ)) := by
              rw [Complex.exp_neg]
      _ = (F u : ℂ) := by
              rw [← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero (u : ℂ)), one_mul]
  exact h.symm

/-- P8 (37) phase: `e^{-u}·𝐞(u·ξ) = e^{-u + 2πi·u·ξ}`, where
`𝐞(x) = exp(2πix)` (Mathlib's real Fourier character). -/
lemma phase_char_mul (u ξ : ℝ) :
    Complex.exp (-(u : ℂ)) * (𝐞 (u * ξ) : ℂ) =
      Complex.exp (-(u : ℂ) + ((2 * Real.pi * (u * ξ) : ℝ) : ℂ) * Complex.I) := by
  rw [Real.fourierChar_apply]
  rw [← Complex.exp_add]

/-- P8 (37) at the divisor point `u = log_R d`: combining the inversion step
(`fourierInversion_expCutoff`) with `F = e^{-u}·H` gives `F(log_R d)` as
`e^{-log_R d}` times the integral of `𝐞(log_R d · ξ)·(𝓕(expCutoff F))(ξ)` —
the divisor form whose integrand, after the phase rewrite
(`phase_char_mul`) and interchanging with the `d,d′`-sums, feeds the
modified-zeta factor. -/
theorem divisorForm (F : ℝ → ℝ) (R d : ℕ)
    (hcont : ContinuousAt (expCutoff F) (logR d R))
    (hint : Integrable (expCutoff F))
    (hint' : Integrable (𝓕 (expCutoff F))) :
    (F (logR d R) : ℂ) =
      Complex.exp (-(logR d R : ℂ)) *
        ∫ ξ : ℝ, (𝐞 (logR d R * ξ) * 𝓕 (expCutoff F) ξ) := by
  calc
    (F (logR d R) : ℂ) = Complex.exp (-(logR d R : ℂ)) * expCutoff F (logR d R) := by
        exact F_eq_exp_neg_expCutoff F (logR d R)
    _ = Complex.exp (-(logR d R : ℂ)) *
          ∫ ξ : ℝ, (𝐞 (logR d R * ξ) * 𝓕 (expCutoff F) ξ) := by
        rw [fourierInversion_expCutoff F (logR d R) hcont hint hint']


/-! ## Smooth compactly supported cutoffs are Schwartz

For `F : ℝ → ℝ` smooth with compact support, the rescaled cutoff
`H(u) := eᵘ·F(u)` is again smooth with compact support, hence a Schwartz
function (`HasCompactSupport.toSchwartzMap`).  This gives, with no further
hypotheses, the integrability of `H` and of its Fourier transform that the
pointwise lemmas above (`divisorForm`, `divisorForm_phase`) require.
-/

/-- `H = expCutoff F` is smooth when `F` is. -/
lemma expCutoff_contDiff (F : ℝ → ℝ) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (expCutoff F) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun u : ℝ => Real.exp u * F u) := Real.contDiff_exp.mul hsm
  have hcomp : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun u : ℝ => (Complex.ofRealCLM (Real.exp u * F u) : ℂ)) := by
    simpa [Function.comp_def] using (Complex.ofRealCLM.contDiff.comp h1)
  convert hcomp using 1
  ext u
  rfl

/-- `H = expCutoff F` has compact support when `F` does. -/
lemma expCutoff_hasCompactSupport (F : ℝ → ℝ) (hcs : HasCompactSupport F) :
    HasCompactSupport (expCutoff F) := by
  refine hcs.mono ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro hF
  apply hu
  dsimp [expCutoff]
  rw [hF, mul_zero]
  norm_num

/-- The Schwartz representative of the rescaled cutoff `H(u) = eᵘ·F(u)`,
for smooth compactly supported real `F`. -/
noncomputable def expCutoffSchwartz (F : ℝ → ℝ) (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    𝓢(ℝ, ℂ) :=
  (expCutoff_hasCompactSupport F hcs).toSchwartzMap
    (expCutoff_contDiff F hsm)

/-- The Schwartz representative agrees pointwise with `expCutoff F`. -/
lemma expCutoffSchwartz_coe (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    ⇑(expCutoffSchwartz F hcs hsm) = expCutoff F := by
  funext u
  rw [expCutoffSchwartz]
  exact HasCompactSupport.toSchwartzMap_toFun _ _ u

/-- For smooth compactly supported `F`, `H = expCutoff F` is integrable. -/
lemma expCutoff_integrable (F : ℝ → ℝ) (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    Integrable (expCutoff F) := by
  have hI : Integrable ⇑(expCutoffSchwartz F hcs hsm) := (expCutoffSchwartz F hcs hsm).integrable
  rwa [expCutoffSchwartz_coe] at hI

/-- For smooth compactly supported `F`, the Fourier transform of
`H = expCutoff F` is integrable (it is again a Schwartz function). -/
lemma fourier_expCutoff_integrable (F : ℝ → ℝ) (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    Integrable (𝓕 (expCutoff F)) := by
  have hI : Integrable ⇑((𝓕 : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)) (expCutoffSchwartz F hcs hsm)) := by
    exact ((𝓕 : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)) (expCutoffSchwartz F hcs hsm)).integrable
  have heq : ⇑((𝓕 : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)) (expCutoffSchwartz F hcs hsm)) = 𝓕 (expCutoff F) := by
    rw [SchwartzMap.fourier_coe, expCutoffSchwartz_coe]
  rwa [heq] at hI

/-- Multiplication by the unit-modulus character `𝐞(u·ξ)` preserves
integrability (pointwise norm bound `‖𝐞(u·ξ) · g ξ‖ = ‖g ξ‖`). -/
lemma integrable_char_mul (u : ℝ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun ξ : ℝ => (𝐞 (u * ξ) : ℂ) * g ξ) := by
  have hchar : AEStronglyMeasurable (fun ξ : ℝ => (𝐞 (u * ξ) : ℂ)) := by
    apply Continuous.aestronglyMeasurable
    rw [show (fun ξ : ℝ => (𝐞 (u * ξ) : ℂ))
          = fun ξ : ℝ => Complex.exp (((2 * Real.pi * (u * ξ) : ℝ) : ℂ) * Complex.I) by
          funext ξ
          exact Real.fourierChar_apply (u * ξ)]
    fun_prop
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ => (𝐞 (u * ξ) : ℂ) * g ξ) :=
    hchar.mul hg.aestronglyMeasurable
  refine hg.congr' hmeas ?_
  filter_upwards with ξ
  rw [norm_mul, Circle.norm_coe, one_mul]

/-! ## 4.1(i) continued: the divisor form with the full phase

`divisorForm` writes `F(log_R d)` with the constant `e^{-log_R d}` in front of
the integral; here it is pulled inside and merged with the character into the
single exponential `exp(-log_R d + 2πi·log_R d·ξ)` (P8 (37), phase form).  The
smooth-compact-support corollary `divisorForm_smoothComp` then has no analytic
hypotheses at all.
-/

/-- **4.1(i), phase form.**  `F(log_R d) = ∫_ξ exp(-log_R d + 2πi·log_R d·ξ) ·
(𝓕(expCutoff F))(ξ) dξ`, i.e. P8 (37) with the phase written out. -/
theorem divisorForm_phase (F : ℝ → ℝ) (R d : ℕ)
    (hcont : ContinuousAt (expCutoff F) (logR d R))
    (hint : Integrable (expCutoff F))
    (hint' : Integrable (𝓕 (expCutoff F))) :
    (F (logR d R) : ℂ) =
      ∫ ξ : ℝ,
        (Complex.exp (-(logR d R : ℂ) +
            (((2 * Real.pi * (logR d R * ξ) : ℝ) : ℂ) * Complex.I)) *
          𝓕 (expCutoff F) ξ) := by
  calc
    (F (logR d R) : ℂ)
        = Complex.exp (-(logR d R : ℂ)) *
            ∫ ξ : ℝ, (𝐞 (logR d R * ξ) * 𝓕 (expCutoff F) ξ) :=
            divisorForm F R d hcont hint hint'
    _ = ∫ ξ : ℝ, Complex.exp (-(logR d R : ℂ)) *
            (𝐞 (logR d R * ξ) * 𝓕 (expCutoff F) ξ) := by
        rw [integral_const_mul]
    _ = ∫ ξ : ℝ, (Complex.exp (-(logR d R : ℂ)) * (𝐞 (logR d R * ξ) : ℂ)) *
            𝓕 (expCutoff F) ξ := by
        congr 1
        ext ξ
        rw [mul_assoc]
    _ = ∫ ξ : ℝ,
          Complex.exp (-(logR d R : ℂ) +
            (((2 * Real.pi * (logR d R * ξ) : ℝ) : ℂ) * Complex.I)) *
            𝓕 (expCutoff F) ξ := by
        congr 1
        ext ξ
        exact congrArg (fun z : ℂ => z * 𝓕 (expCutoff F) ξ) (phase_char_mul (logR d R) ξ)

/-- **4.1(i), hypothesis-free corollary.**  For smooth compactly supported
`F : ℝ → ℝ`, P8 (37) holds at every divisor point `log_R d` with no further
assumptions. -/
theorem divisorForm_smoothComp (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (R d : ℕ) :
    (F (logR d R) : ℂ) =
      ∫ ξ : ℝ,
        (Complex.exp (-(logR d R : ℂ) +
            (((2 * Real.pi * (logR d R * ξ) : ℝ) : ℂ) * Complex.I)) *
          𝓕 (expCutoff F) ξ) := by
  apply divisorForm_phase F R d
  · rw [← expCutoffSchwartz_coe F hcs hsm]
    exact (expCutoffSchwartz F hcs hsm).continuous.continuousAt
  · exact expCutoff_integrable F hcs hsm
  · exact fourier_expCutoff_integrable F hcs hsm

end Commons.NumberTheory.MaynardSieve
