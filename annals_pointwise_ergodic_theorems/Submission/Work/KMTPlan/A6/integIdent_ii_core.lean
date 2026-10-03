/-
# `integ-ident`(ii) of Krause--Mirek--Tao §6

The paper's second integration-by-parts identity is (with `Φ(t) = e(ξ₁Nt + ξ₂P(Nt))` and `P'`,
`P''` the derivatives of `P` evaluated at `Nt`)

  `∫_{1/2}^1 Φ(t) dt = [Φ(t)/(2πi ξ₂ N P'(Nt))]_{1/2}^1 - (ξ₁/ξ₂) ∫_{1/2}^1 Φ/P' dt
      + (1/(2πiξ₂)) ∫_{1/2}^1 Φ · P''(Nt)/P'(Nt)² dt`,

obtained from the fundamental theorem of calculus for the primitive
`t ↦ Φ(t)/(2πi ξ₂ N P'(Nt))`, which is differentiable on `[1/2,1]` as soon as `P'(Nt) ≠ 0` there
(this is the form used for the `s₂`-decay of §6--§8 in the low case `CaseRest`).  This module
proves that identity as `integIdent_ii_corrected` below.

## The statement that was requested is FALSE — it is mis-parenthesized

The requested declaration was

```
theorem integIdent_ii_core (P : Polynomial ℤ) {N ξ₁ ξ₂ : ℝ} (hN : N ≠ 0) (hξ₂ : ξ₂ ≠ 0)
    (hP' : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, PderivR P (N * t) ≠ 0) :
    ∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t
      = Phi P N ξ₁ ξ₂ 1 / cnorm₂ P N ξ₂ 1
        - Phi P N ξ₁ ξ₂ (1 / 2) / cnorm₂ P N ξ₂ (1 / 2)
        - ((ξ₁ / ξ₂ : ℝ) : ℂ) * ∫ t in (1 / 2 : ℝ)..1,
            Phi P N ξ₁ ξ₂ t / ((PderivR P (N * t) : ℝ) : ℂ)
        + (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ))) * ∫ t in (1 / 2 : ℝ)..1,
            Phi P N ξ₁ ξ₂ t
              * (((Pderiv2R P (N * t) / (PderivR P (N * t)) ^ 2 : ℝ)) : ℂ)
```

Because the body of `∫ t in a..b, ...` extends over `+`, the trailing `+ (1/(2πiξ₂)) * ∫ ..`
is parsed **inside the body of the preceding integral**.  Elaborating the statement verbatim
produces the goal

  `∫ Φ = A - B - ↑(ξ₁/ξ₂) * ∫ t in 1/2..1, ( Φ t / ↑P' + 1/(2πiξ₂) * ∫ t in 1/2..1, Φ t * ↑(P''/P'²) )`

(with `A = Φ 1/cnorm₂ 1`, `B = Φ (1/2)/cnorm₂ (1/2)`); and the test
`example (h : <requested>) : <same with explicit parentheses around the two integrals> := h`
**fails** — the two are not definitionally equal.  So the requested statement is *not* a
reformulation of the paper's identity, and it is false.

Writing `C = ξ₁/ξ₂`, `D = 1/(2πiξ₂)` and `K = ∫_{1/2}^1 Φ·P''/P'²`, the parsed right-hand side is
`A - B - C·(∫Φ/P' + D·K/2)`, while the true theorem gives `A - B - C·∫Φ/P' + D·K`; the difference
is `-D·K·(C/2 + 1)`.

### Counterexample (`C = 0`)

Take `P = X²`, `N = 1`, `ξ₁ = 0`, `ξ₂ = 1`; then `P'(Nt) = 2t ≠ 0` on `[1/2,1]`, so all three
hypotheses hold, `Φ(t) = exp(2πi t²)`, and the parsed statement reads
`∫_{1/2}^1 e(t²)dt = 1/(4πi) - 1/(2π)` (the coefficient `↑(ξ₁/ξ₂) = 0` kills the whole mis-placed
integral term).  Numerically (midpoint rule, `10^6` points):

  `∫_{1/2}^1 e(t²)dt    = -0.14581999715081 - 0.04742173451346 i`
  `1/(4πi) - 1/(2π)     = -0.15915494309190 - 0.07957747154595 i`
  residual `(A-B) - ∫Φ  = +0.0133349459411  + 0.0321557370325 i`

and the predicted error term `D·K = (1/(2πi)) ∫_{1/2}^1 e(t²)/(2t²) dt` is
`0.0133349459411 + 0.0321557370326 i` — the residual matches it to `5·10^{-13}`, while the
*corrected* identity `∫Φ = A - B + D·K` is satisfied by the same quadrature to `4·10^{-13}`.
So the mis-placed parentheses are precisely the obstruction.

### The fix

Parenthesize the two integrals:

  `... - ((ξ₁/ξ₂ : ℝ) : ℂ) * (∫ t in (1/2)..1, Phi P N ξ₁ ξ₂ t / ((PderivR P (N*t) : ℝ) : ℂ))`
  `  + (1/(2*π*I*ξ₂)) * (∫ t in (1/2)..1, Phi P N ξ₁ ξ₂ t * (((Pderiv2R P (N*t) / (PderivR P (N*t))^2 : ℝ)) : ℂ))`

That statement is true and is proved here as `Work.KMTPlan.A6.integIdent_ii_corrected`.

The requested name `integIdent_ii_core` is deliberately **not** declared in this file: it was
reported FALSE, so the path is free for the corrected statement.

## The proof of the corrected identity

`HasDerivAt.div` applied to `t ↦ Φ(t)` and `t ↦ 2πi ξ₂ N P'(Nt)` gives, after clearing
denominators (`field_simp`), the derivative of `t ↦ Φ(t)/cnorm₂(t)` as `Efac` below.  The
functions `Ffac = Φ/P'` and `Gfac = Φ·(P''/P'²)` are continuous on `uIcc (1/2) 1` because
`P'(Nt) ≠ 0` there, `Efac` is their combination, and the fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) plus linearity of the interval integral
(`integral_add`, `integral_sub`, `integral_const_mul`) finish the job.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.IntegIdent

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

/-! ## The three integrands of the identity -/

/-- The integrand `Φ(t)/P'(Nt)` of the second term. -/
noncomputable def Ffac (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ) : ℝ → ℂ :=
  fun t => Phi P N ξ₁ ξ₂ t / ((PderivR P (N * t) : ℝ) : ℂ)

/-- The integrand `Φ(t)·P''(Nt)/P'(Nt)²` of the third term. -/
noncomputable def Gfac (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ) : ℝ → ℂ :=
  fun t => Phi P N ξ₁ ξ₂ t * (((Pderiv2R P (N * t) / (PderivR P (N * t)) ^ 2 : ℝ)) : ℂ)

/-- The derivative of the primitive `t ↦ Φ(t)/cnorm₂(t)`, i.e.
`Φ + (ξ₁/ξ₂)·Φ/P' - (1/(2πiξ₂))·Φ·P''/P'²`, integrated on `[1/2,1]`. -/
noncomputable def Efac (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ) : ℝ → ℂ :=
  fun t => Phi P N ξ₁ ξ₂ t + ((ξ₁ / ξ₂ : ℝ) : ℂ) * Ffac P N ξ₁ ξ₂ t
    - (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ))) * Gfac P N ξ₁ ξ₂ t

theorem Ffac_apply (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ) (t : ℝ) :
    Ffac P N ξ₁ ξ₂ t = Phi P N ξ₁ ξ₂ t / ((PderivR P (N * t) : ℝ) : ℂ) := rfl

theorem Gfac_apply (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ) (t : ℝ) :
    Gfac P N ξ₁ ξ₂ t
      = Phi P N ξ₁ ξ₂ t * (((Pderiv2R P (N * t) / (PderivR P (N * t)) ^ 2 : ℝ)) : ℂ) := rfl

theorem Efac_apply (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ) (t : ℝ) :
    Efac P N ξ₁ ξ₂ t = Phi P N ξ₁ ξ₂ t + ((ξ₁ / ξ₂ : ℝ) : ℂ) * Ffac P N ξ₁ ξ₂ t
      - (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ))) * Gfac P N ξ₁ ξ₂ t := rfl

/-! ## Continuity on `[1/2,1]` -/

theorem continuousOn_Ffac (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ)
    (hP : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, PderivR P (N * t) ≠ 0) :
    ContinuousOn (Ffac P N ξ₁ ξ₂) (Set.uIcc (1 / 2 : ℝ) 1) := by
  refine ContinuousOn.div ((continuous_Phi P N ξ₁ ξ₂).continuousOn)
    ((Complex.continuous_ofReal.comp (continuous_PderivR_comp P N)).continuousOn) ?_
  intro t ht
  exact_mod_cast hP t ht

theorem continuousOn_Gfac (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ)
    (hP : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, PderivR P (N * t) ≠ 0) :
    ContinuousOn (Gfac P N ξ₁ ξ₂) (Set.uIcc (1 / 2 : ℝ) 1) := by
  have h1 : ContinuousOn (fun t : ℝ => Phi P N ξ₁ ξ₂ t * ((Pderiv2R P (N * t) : ℝ) : ℂ))
      (Set.uIcc (1 / 2 : ℝ) 1) :=
    ((continuous_Phi P N ξ₁ ξ₂).continuousOn).mul
      ((Complex.continuous_ofReal.comp (continuous_PderivR_comp P.derivative N)).continuousOn)
  have h2 : ContinuousOn (fun t : ℝ => (((PderivR P (N * t) : ℝ) : ℂ)) ^ 2)
      (Set.uIcc (1 / 2 : ℝ) 1) :=
    ((Complex.continuous_ofReal.comp (continuous_PderivR_comp P N)).continuousOn).pow 2
  refine (ContinuousOn.div h1 h2 ?_).congr ?_
  · intro t ht
    exact pow_ne_zero 2 (by exact_mod_cast hP t ht)
  · intro t ht
    simp only [Pi.div_apply, Gfac]
    push_cast
    ring

theorem continuousOn_Efac (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ)
    (hP : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, PderivR P (N * t) ≠ 0) :
    ContinuousOn (Efac P N ξ₁ ξ₂) (Set.uIcc (1 / 2 : ℝ) 1) := by
  have h := ((continuous_Phi P N ξ₁ ξ₂).continuousOn.add
    ((continuousOn_Ffac P N ξ₁ ξ₂ hP).const_mul ((ξ₁ / ξ₂ : ℝ) : ℂ))).sub
      ((continuousOn_Gfac P N ξ₁ ξ₂ hP).const_mul
        (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ))))
  refine h.congr ?_
  intro t ht
  simp only [Efac, Pi.add_apply, Pi.sub_apply]

/-! ## The derivative of the primitive -/

/-- The derivative of `t ↦ Φ(t)/cnorm₂(t)` at `t`, computed by the quotient rule and cleared of
denominators.  This is exactly `Efac P N ξ₁ ξ₂ t`. -/
theorem hasDerivAt_Phi_div_cnorm₂ (P : ℤ[X]) (N ξ₁ ξ₂ t : ℝ) (hξ₂ : ξ₂ ≠ 0) (hN : N ≠ 0)
    (hP : PderivR P (N * t) ≠ 0) :
    HasDerivAt (fun s : ℝ => Phi P N ξ₁ ξ₂ s / cnorm₂ P N ξ₂ s) (Efac P N ξ₁ ξ₂ t) t := by
  have hΦ := hasDerivAt_Phi P N ξ₁ ξ₂ t
  have hD := hasDerivAt_cnorm₂ P N ξ₂ t
  have hDne : cnorm₂ P N ξ₂ t ≠ 0 := cnorm₂_ne_zero hξ₂ hN hP
  have hq := hΦ.div hD hDne
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hξ₂c : (ξ₂ : ℂ) ≠ 0 := by exact_mod_cast hξ₂
  have hP'c : (((PderivR P (N * t)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP
  have key : (Phi P N ξ₁ ξ₂ t *
            (2 * ↑Real.pi * Complex.I *
              ↑(ξ₁ * N + ξ₂ * (PderivR P (N * t) * N))) *
          cnorm₂ P N ξ₂ t -
        Phi P N ξ₁ ξ₂ t *
          (2 * ↑Real.pi * Complex.I * ↑ξ₂ * ↑N *
            ↑(Pderiv2R P (N * t) * N))) /
      cnorm₂ P N ξ₂ t ^ 2
      = Efac P N ξ₁ ξ₂ t := by
    simp only [Efac, Ffac, Gfac]
    rw [cnorm₂_apply]
    push_cast
    field_simp
    ring_nf
  rw [key] at hq
  exact hq

/-! ## The corrected identity -/

/-- **`integ-ident`(ii)** of Krause--Mirek--Tao §6, correctly parenthesized: integrating
`e(ξ₂ P(Nt))` by parts along `[1/2,1]`, where `P'(Nt) ≠ 0` on that interval.  This is the
statement that should replace the (mis-parsed, false) requested `integIdent_ii_core`; the
parentheses around the last two integrals are essential. -/
theorem integIdent_ii_corrected (P : ℤ[X]) {N ξ₁ ξ₂ : ℝ} (hN : N ≠ 0) (hξ₂ : ξ₂ ≠ 0)
    (hP' : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, PderivR P (N * t) ≠ 0) :
    ∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t
      = Phi P N ξ₁ ξ₂ 1 / cnorm₂ P N ξ₂ 1
        - Phi P N ξ₁ ξ₂ (1 / 2) / cnorm₂ P N ξ₂ (1 / 2)
        - ((ξ₁ / ξ₂ : ℝ) : ℂ) * (∫ t in (1 / 2 : ℝ)..1,
            Phi P N ξ₁ ξ₂ t / ((PderivR P (N * t) : ℝ) : ℂ))
        + (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ))) * (∫ t in (1 / 2 : ℝ)..1,
            Phi P N ξ₁ ξ₂ t
              * (((Pderiv2R P (N * t) / (PderivR P (N * t)) ^ 2 : ℝ)) : ℂ)) := by
  change (∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t)
      = Phi P N ξ₁ ξ₂ 1 / cnorm₂ P N ξ₂ 1 - Phi P N ξ₁ ξ₂ (1 / 2) / cnorm₂ P N ξ₂ (1 / 2)
        - ((ξ₁ / ξ₂ : ℝ) : ℂ) * (∫ t in (1 / 2 : ℝ)..1, Ffac P N ξ₁ ξ₂ t)
        + (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)))
            * (∫ t in (1 / 2 : ℝ)..1, Gfac P N ξ₁ ξ₂ t)
  have hIΦ : IntervalIntegrable (fun t : ℝ => Phi P N ξ₁ ξ₂ t) volume ((1 / 2 : ℝ)) 1 :=
    (continuous_Phi P N ξ₁ ξ₂).intervalIntegrable _ _
  have hIf : IntervalIntegrable (Ffac P N ξ₁ ξ₂) volume ((1 / 2 : ℝ)) 1 :=
    (continuousOn_Ffac P N ξ₁ ξ₂ hP').intervalIntegrable
  have hIg : IntervalIntegrable (Gfac P N ξ₁ ξ₂) volume ((1 / 2 : ℝ)) 1 :=
    (continuousOn_Gfac P N ξ₁ ξ₂ hP').intervalIntegrable
  have hIe : IntervalIntegrable (Efac P N ξ₁ ξ₂) volume ((1 / 2 : ℝ)) 1 :=
    (continuousOn_Efac P N ξ₁ ξ₂ hP').intervalIntegrable
  have hFTC : ∫ t in (1 / 2 : ℝ)..1, Efac P N ξ₁ ξ₂ t
      = Phi P N ξ₁ ξ₂ 1 / cnorm₂ P N ξ₂ 1
        - Phi P N ξ₁ ξ₂ (1 / 2) / cnorm₂ P N ξ₂ (1 / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_Phi_div_cnorm₂ P N ξ₁ ξ₂ t hξ₂ hN (hP' t ht)) hIe
  have hsplit : ∫ t in (1 / 2 : ℝ)..1, Efac P N ξ₁ ξ₂ t
      = (∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t)
        + ((ξ₁ / ξ₂ : ℝ) : ℂ) * (∫ t in (1 / 2 : ℝ)..1, Ffac P N ξ₁ ξ₂ t)
        - (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)))
            * (∫ t in (1 / 2 : ℝ)..1, Gfac P N ξ₁ ξ₂ t) := by
    have e1 : ∫ t in (1 / 2 : ℝ)..1, Efac P N ξ₁ ξ₂ t
        = (∫ t in (1 / 2 : ℝ)..1,
              Phi P N ξ₁ ξ₂ t + ((ξ₁ / ξ₂ : ℝ) : ℂ) * Ffac P N ξ₁ ξ₂ t)
          - (∫ t in (1 / 2 : ℝ)..1,
              (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ))) * Gfac P N ξ₁ ξ₂ t) :=
      intervalIntegral.integral_sub (hIΦ.add (hIf.const_mul _)) (hIg.const_mul _)
    have e2 : ∫ t in (1 / 2 : ℝ)..1,
          Phi P N ξ₁ ξ₂ t + ((ξ₁ / ξ₂ : ℝ) : ℂ) * Ffac P N ξ₁ ξ₂ t
        = (∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t)
          + ((ξ₁ / ξ₂ : ℝ) : ℂ) * ∫ t in (1 / 2 : ℝ)..1, Ffac P N ξ₁ ξ₂ t := by
      rw [intervalIntegral.integral_add hIΦ (hIf.const_mul _),
        intervalIntegral.integral_const_mul]
    have e3 : ∫ t in (1 / 2 : ℝ)..1,
          (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ))) * Gfac P N ξ₁ ξ₂ t
        = (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)))
            * ∫ t in (1 / 2 : ℝ)..1, Gfac P N ξ₁ ξ₂ t :=
      intervalIntegral.integral_const_mul _ _
    rw [e1, e2, e3]
  have key : (∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t)
        + ((ξ₁ / ξ₂ : ℝ) : ℂ) * (∫ t in (1 / 2 : ℝ)..1, Ffac P N ξ₁ ξ₂ t)
        - (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)))
            * (∫ t in (1 / 2 : ℝ)..1, Gfac P N ξ₁ ξ₂ t)
      = Phi P N ξ₁ ξ₂ 1 / cnorm₂ P N ξ₂ 1
        - Phi P N ξ₁ ξ₂ (1 / 2) / cnorm₂ P N ξ₂ (1 / 2) := by
    rw [← hsplit]; exact hFTC
  calc ∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t
      = (∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t)
            + ((ξ₁ / ξ₂ : ℝ) : ℂ) * (∫ t in (1 / 2 : ℝ)..1, Ffac P N ξ₁ ξ₂ t)
            - (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)))
                * (∫ t in (1 / 2 : ℝ)..1, Gfac P N ξ₁ ξ₂ t)
            - ((ξ₁ / ξ₂ : ℝ) : ℂ) * (∫ t in (1 / 2 : ℝ)..1, Ffac P N ξ₁ ξ₂ t)
            + (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)))
                * (∫ t in (1 / 2 : ℝ)..1, Gfac P N ξ₁ ξ₂ t) := by ring
    _ = Phi P N ξ₁ ξ₂ 1 / cnorm₂ P N ξ₂ 1
          - Phi P N ξ₁ ξ₂ (1 / 2) / cnorm₂ P N ξ₂ (1 / 2)
            - ((ξ₁ / ξ₂ : ℝ) : ℂ) * (∫ t in (1 / 2 : ℝ)..1, Ffac P N ξ₁ ξ₂ t)
            + (1 / (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)))
                * (∫ t in (1 / 2 : ℝ)..1, Gfac P N ξ₁ ξ₂ t) := by
        rw [key]

end

end Work.KMTPlan.A6
