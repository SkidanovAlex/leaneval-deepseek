import Mathlib
import Submission.ZFourier

open scoped BigOperators
open scoped FourierTransform RealInnerProductSpace SchwartzMap Topology
open MeasureTheory Filter

noncomputable section

/-!
# P8 Lemma 4.1: interchanging the divisor sums with the Fourier integrals

`Submission/ZFourier.lean` (part (i) of the campaign) proved the *pointwise*
divisor representation of a smooth compactly supported cutoff `F`:

    F(log_R d) = ∫_ξ exp(−log_R d + 2πi·log_R d·ξ)·(𝓕(expCutoff F))(ξ) dξ

(`divisorForm_smoothComp`, P8 (37)).  This file performs the first summation
step of the proof of Lemma 4.1: because the divisor sums of the sieve are
*finite* (divisors are truncated at a fixed bound, `Fin (D+1)` throughout
`Submission/SieveExpansion.lean`), substituting the representation into a sum
`Σ_d w(d)·F(log_R d)` and interchanging with the ξ-integral needs only the
Fubini-free `integral_finset_sum`, with integrability of each summand coming
from the Schwartz representative of the Fourier transform.  The result is the
finite analogue of Polymath8a's equation (38).
-/

namespace Commons.NumberTheory.MaynardSieve

/-- For smooth compactly supported `F`, each summand of the substituted
divisor sum is integrable in `ξ`: the phase (unit modulus character) times
the Schwartz-class Fourier transform of `expCutoff F`. -/
lemma integrable_phase_mul_fourier (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (R b : ℕ) :
    Integrable (fun ξ : ℝ =>
      Complex.exp (-(logR b R : ℂ) +
          (((2 * Real.pi * (logR b R * ξ) : ℝ) : ℂ) * Complex.I)) *
        𝓕 (expCutoff F) ξ) := by
  -- exp(a + c·i) = exp a · exp(c·i); with c = 2π·logR b·ξ the second factor is
  -- the Fourier character 𝐞(logR b · ξ) (unit modulus).
  have hmain : (fun ξ : ℝ =>
      Complex.exp (-(logR b R : ℂ) +
          (((2 * Real.pi * (logR b R * ξ) : ℝ) : ℂ) * Complex.I)) *
        𝓕 (expCutoff F) ξ) = fun ξ : ℝ =>
      (Complex.exp (-(logR b R : ℂ)) * (𝐞 (logR b R * ξ) : ℂ)) *
        𝓕 (expCutoff F) ξ := by
    funext ξ
    rw [Real.fourierChar_apply (logR b R * ξ)]
    rw [← Complex.exp_add]
  rw [hmain]
  -- integrability: exp(-logR b) constant · (char · 𝓕), char·𝓕 integrable by
  -- `integrable_char_mul` applied to `fourier_expCutoff_integrable`.
  have hint : Integrable (fun ξ : ℝ => (𝐞 (logR b R * ξ) : ℂ) * 𝓕 (expCutoff F) ξ) :=
    integrable_char_mul (logR b R) (fourier_expCutoff_integrable F hcs hsm)
  have hc : Integrable (fun ξ : ℝ =>
      Complex.exp (-(logR b R : ℂ)) * ((𝐞 (logR b R * ξ) : ℂ) * 𝓕 (expCutoff F) ξ)) := by
    simpa [mul_assoc] using hint.const_mul (Complex.exp (-(logR b R : ℂ)))
  simpa [mul_assoc] using hc

/-- Substituting the divisor representation (P8 (37)) into a finite `b`-sum
of weighted cutoff values, and interchanging with the ξ-integral:

    Σ_b w(b)·F(log_R b) = ∫_ξ Σ_b w(b)·exp(−log_R b + 2πi·log_R b·ξ)·Ĥ(ξ) dξ

with `H(u) := eᵘF(u)`; the finite analogue of P8 (38) for a single divisor
coordinate. -/
theorem sum_mul_divisorForm_smoothComp (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (R : ℕ) {D : ℕ} (w : Fin (D + 1) → ℂ) :
    (∑ b : Fin (D + 1), w b * (F (logR (b : ℕ) R) : ℂ)) =
      ∫ ξ : ℝ, ∑ b : Fin (D + 1),
        w b * (Complex.exp (-(logR (b : ℕ) R : ℂ) +
            (((2 * Real.pi * (logR (b : ℕ) R * ξ) : ℝ) : ℂ) * Complex.I)) *
          𝓕 (expCutoff F) ξ) := by
  calc
    (∑ b : Fin (D + 1), w b * (F (logR (b : ℕ) R) : ℂ))
        = ∑ b : Fin (D + 1),
            w b * (∫ ξ : ℝ,
              Complex.exp (-(logR (b : ℕ) R : ℂ) +
                (((2 * Real.pi * (logR (b : ℕ) R * ξ) : ℝ) : ℂ) * Complex.I)) *
                𝓕 (expCutoff F) ξ) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            rw [divisorForm_smoothComp F hcs hsm R (b : ℕ)]
    _ = ∑ b : Fin (D + 1),
            ∫ ξ : ℝ, w b *
              (Complex.exp (-(logR (b : ℕ) R : ℂ) +
                (((2 * Real.pi * (logR (b : ℕ) R * ξ) : ℝ) : ℂ) * Complex.I)) *
                𝓕 (expCutoff F) ξ) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            rw [← integral_const_mul]
    _ = ∫ ξ : ℝ, ∑ b : Fin (D + 1),
            w b * (Complex.exp (-(logR (b : ℕ) R : ℂ) +
              (((2 * Real.pi * (logR (b : ℕ) R * ξ) : ℝ) : ℂ) * Complex.I)) *
              𝓕 (expCutoff F) ξ) := by
            rw [integral_finsetSum]
            intro b hb
            exact (integrable_phase_mul_fourier F hcs hsm R (b : ℕ)).const_mul (w b)


/-! ## Two-coordinate (double) substitution

For a pair of smooth compactly supported cutoffs `F, G` and arbitrary
coefficients `w : (Fin (D+1))² → ℂ` (the Möbius/lcm weights of `Zpair` are to
be folded into `w`), both divisor representations are substituted and both
finite sums interchanged with the two ξ-integrals — the finite analogue of
Polymath8a (38) for a single coordinate pair `(F_j, G_j)`.  The natural
derivation order (substitute `G` over the `b`-sum first, then `F` over the
`a`-sum) puts the `ξ'`-integral outermost.
-/

/-- The Fourier transform of the rescaled cutoff (abbreviation). -/
noncomputable abbrev fourierCut (F : ℝ → ℝ) : ℝ → ℂ :=
  (𝓕 : (ℝ → ℂ) → (ℝ → ℂ)) (expCutoff F)

/-- The divisor phase `exp(−log_R b + 2πi·log_R b·ξ)` (abbreviation). -/
noncomputable abbrev divisorPhase (R b : ℕ) (ξ : ℝ) : ℂ :=
  Complex.exp (-(logR b R : ℂ) +
    (((2 * Real.pi * (logR b R * ξ) : ℝ) : ℂ) * Complex.I))

/-- **Two-coordinate divisor substitution** (P8 (38), finite form):
`Σ_{a,b} w(a,b)·F(log_R a)·G(log_R b)` equals the double ξ-integral of the
separated phases times `(𝓕 e^uF(u))(ξ)·(𝓕 e^uG(u))(ξ')`. -/
theorem doubleSum_mul_divisorForm_smoothComp (F G : ℝ → ℝ) (hcsF : HasCompactSupport F)
    (hsmF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (hcsG : HasCompactSupport G) (hsmG : ContDiff ℝ (↑(⊤ : ℕ∞)) G)
    (R : ℕ) {D : ℕ} (w : Fin (D + 1) → Fin (D + 1) → ℂ) :
    (∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
        w a b * (F (logR (a : ℕ) R) : ℂ) * (G (logR (b : ℕ) R) : ℂ)) =
      ∫ ξ' : ℝ, ∫ ξ : ℝ, ∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
        w a b * divisorPhase R (b : ℕ) ξ' * divisorPhase R (a : ℕ) ξ *
          (fourierCut G ξ' * fourierCut F ξ) := by
  classical
  -- Step 1: substitute G in each inner b-sum (coefficients carry the F-value).
  have hGsub : ∀ a : Fin (D + 1),
      (∑ b : Fin (D + 1), w a b * (F (logR (a : ℕ) R) : ℂ) * (G (logR (b : ℕ) R) : ℂ)) =
        ∫ ξ' : ℝ, ∑ b : Fin (D + 1),
          (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ' := by
    intro a
    have h := sum_mul_divisorForm_smoothComp G hcsG hsmG R
      (w := fun b : Fin (D + 1) => w a b * (F (logR (a : ℕ) R) : ℂ))
    simpa [divisorPhase, fourierCut, mul_assoc, mul_left_comm, mul_comm] using h
  have h2 : (∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
        w a b * (F (logR (a : ℕ) R) : ℂ) * (G (logR (b : ℕ) R) : ℂ)) =
      ∑ a : Fin (D + 1), ∫ ξ' : ℝ, ∑ b : Fin (D + 1),
          (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ' := by
    exact Finset.sum_congr rfl (fun a ha => hGsub a)
  -- Step 2: swap the finite a-sum with the ξ'-integral.
  have hSlice : ∀ a : Fin (D + 1), Integrable (fun ξ' : ℝ =>
      ∑ b : Fin (D + 1),
        (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ') := by
    intro a
    refine integrable_finsetSum (Finset.univ) ?_
    intro b hb
    have hint : Integrable (fun ξ' : ℝ => divisorPhase R (b : ℕ) ξ' * fourierCut G ξ') := by
      simpa [divisorPhase, fourierCut] using integrable_phase_mul_fourier G hcsG hsmG R (b : ℕ)
    simpa [mul_assoc] using hint.const_mul (w a b * (F (logR (a : ℕ) R) : ℂ))
  have h3 : (∑ a : Fin (D + 1), ∫ ξ' : ℝ, ∑ b : Fin (D + 1),
        (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ') =
      ∫ ξ' : ℝ, ∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
        (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ' := by
    rw [integral_finsetSum]
    intro i hi
    exact hSlice i
  -- Step 3: substitute F over the a-sum, for each fixed ξ'.
  have hFsub : ∀ ξ' : ℝ,
      (∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
          (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ') =
        ∫ ξ : ℝ, ∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
          w a b * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ' *
            divisorPhase R (a : ℕ) ξ * fourierCut F ξ := by
    intro ξ'
    -- hα: pull F(log_R a) out of the b-sum
    have hα : (∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
          (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ') =
        ∑ a : Fin (D + 1),
          (∑ b : Fin (D + 1), w a b * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ') *
            (F (logR (a : ℕ) R) : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      -- inner: ∑ b ((w a b * Fv a) * phG b ξ' * ĤG ξ') = (∑ b w a b * phG b ξ' * ĤG ξ') * Fv a
      calc
        (∑ b : Fin (D + 1),
            (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ')
            = (F (logR (a : ℕ) R) : ℂ) * (∑ b : Fin (D + 1),
                w a b * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ') := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro b hb
                ring
        _ = (∑ b : Fin (D + 1), w a b * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ') *
              (F (logR (a : ℕ) R) : ℂ) := by
                rw [mul_comm]
    have hsingle := sum_mul_divisorForm_smoothComp F hcsF hsmF R
      (w := fun a : Fin (D + 1) =>
        ∑ b : Fin (D + 1), w a b * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ')
    -- hsingle : (∑ a, α a * (F a : ℂ)) = ∫ ξ, ∑ a, α a * phF a ξ * ĤF ξ
    calc
      (∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
          (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ')
          = ∑ a : Fin (D + 1),
              (∑ b : Fin (D + 1), w a b * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ') *
                (F (logR (a : ℕ) R) : ℂ) := hα
      _ = ∫ ξ : ℝ, ∑ a : Fin (D + 1),
              (∑ b : Fin (D + 1), w a b * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ') *
                divisorPhase R (a : ℕ) ξ * fourierCut F ξ := by
              simpa [divisorPhase, fourierCut, mul_assoc] using hsingle
      _ = ∫ ξ : ℝ, ∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
              w a b * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ' *
                divisorPhase R (a : ℕ) ξ * fourierCut F ξ := by
              apply congrArg (fun h : ℝ → ℂ => ∫ x : ℝ, h x)
              apply funext
              intro ξ
              simp_rw [Finset.sum_mul]
  -- assemble
  calc
    (∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
        w a b * (F (logR (a : ℕ) R) : ℂ) * (G (logR (b : ℕ) R) : ℂ))
        = ∑ a : Fin (D + 1), ∫ ξ' : ℝ, ∑ b : Fin (D + 1),
            (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ' := h2
    _ = ∫ ξ' : ℝ, ∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
          (w a b * (F (logR (a : ℕ) R) : ℂ)) * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ' := h3
    _ = ∫ ξ' : ℝ, (∫ ξ : ℝ, ∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
          w a b * divisorPhase R (b : ℕ) ξ' * fourierCut G ξ' *
            divisorPhase R (a : ℕ) ξ * fourierCut F ξ) := by
          congr 1
          ext ξ'
          exact hFsub ξ'
    _ = ∫ ξ' : ℝ, ∫ ξ : ℝ, ∑ a : Fin (D + 1), ∑ b : Fin (D + 1),
          w a b * divisorPhase R (b : ℕ) ξ' * divisorPhase R (a : ℕ) ξ *
            (fourierCut G ξ' * fourierCut F ξ) := by
          apply congrArg (fun h : ℝ → ℂ => ∫ ξ' : ℝ, h ξ')
          apply funext
          intro ξ'
          apply congrArg (fun h : ℝ → ℂ => ∫ ξ : ℝ, h ξ)
          apply funext
          intro ξ
          refine Finset.sum_congr rfl ?_
          intro a ha
          refine Finset.sum_congr rfl ?_
          intro b hb
          ring


end Commons.NumberTheory.MaynardSieve
