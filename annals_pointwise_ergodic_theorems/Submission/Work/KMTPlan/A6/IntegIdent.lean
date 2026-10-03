/-
# The integration-by-parts identities `integ-ident` of Krause--Mirek--Tao §6

This module formalises Lemma `integ-ident` of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022 (arXiv:2008.00857),

the elementary integration-by-parts identity which produces the *exponential decay in the
continuous frequency parameters* `s₁, s₂` of the model estimates of §6--§8.  It is used exactly in
the case `p₁ = p₂ = 2` of Theorem `varp` when `max(s₁,s₂) > l`, i.e. (in the vocabulary of
`Work.KMTPlan.A6.LowDefs`) in the **low case** `CaseRest`, with one of `k₁, k₂ = 0` and the other
parameter exceeding `max(l₁,l₂)`.

The continuous part of the halved average at the scale `N` is the oscillatory integral
`Φ(t) = e(ξ₁ N t + ξ₂ P(N t))`, `e(x) = exp(2πi x)`, and the two identities are

* (i) integrating `e(ξ₁ N t)` by parts,
  `∫_{1/2}^1 Φ dt = [Φ/(2πi N ξ₁)]_{1/2}^1 - (ξ₂/ξ₁) ∫_{1/2}^1 Φ (P'(Nt)) dt`;
* (ii) integrating `e(ξ₂ P(N t))` by parts (for `P'(Nt) ≠ 0` on `[1/2,1]`, which holds for
  `N ≥ C₃` since `P'` is a non-zero polynomial),
  `∫_{1/2}^1 Φ dt = [Φ/(2πi N ξ₂ P'(Nt))]_{1/2}^1 - (ξ₁/ξ₂)∫_{1/2}^1 Φ/P'(Nt) dt
      + (1/(2πi ξ₂))∫_{1/2}^1 Φ P''(Nt)/P'(Nt)² dt`.

The identity (i) is proved here for the *core* oscillatory integral, as the fundamental theorem of
calculus applied to the primitive `t ↦ Φ(t)/(2πi N ξ₁)`; the companion identity (ii) (with the
primitive `t ↦ Φ(t)/(2πi N ξ₂ P'(Nt))`) is proved in `Submission.Work.KMTPlan.A6.integIdent_ii_core`
as `Work.KMTPlan.A6.integIdent_ii_corrected` — **note** that in the `(ii)` identity
the parentheses around the two integrals on the right-hand side are essential: the body of
`∫ t in a..b, ...` extends over `+`, so writing the last term unparenthesized parses it *inside* the
previous integral's body and yields a false proposition.
Beware also that the corresponding statements elsewhere should use them; the same parse trap.
The identity (i) is stated with the trailing integral last, where the parse is unambiguous.
The identity (i) is stated here as follows: (ii) is the analogue with the primitive
`t ↦ Φ(t)/(2πi N ξ₂ P'(Nt))`.  The modified bumps `φ_{N,t,j}(ξ) = (2^{-s}Nξ)^j φ_{N,t}(ξ)` cancel
exactly the singular factors `1/ξ` produced by the integration by parts, which is why the paper
excludes the pairs `(s,j) = (-u,-1)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

/-! ## The derivatives of `P` at real points -/

/-- `P'` evaluated at a real point. -/
noncomputable def PderivR (P : ℤ[X]) (x : ℝ) : ℝ :=
  (P.derivative.map (Int.castRingHom ℝ)).eval x

/-- `P''` evaluated at a real point. -/
noncomputable def Pderiv2R (P : ℤ[X]) (x : ℝ) : ℝ :=
  (P.derivative.derivative.map (Int.castRingHom ℝ)).eval x

theorem PderivR_apply (P : ℤ[X]) (x : ℝ) :
    PderivR P x = (P.derivative.map (Int.castRingHom ℝ)).eval x := rfl

theorem hasDerivAt_PevalR (P : ℤ[X]) (x : ℝ) :
    HasDerivAt (PevalR P) (PderivR P x) x := by
  have h : HasDerivAt (fun y : ℝ => (P.map (Int.castRingHom ℝ)).eval y)
      ((P.derivative.map (Int.castRingHom ℝ)).eval x) x := by
    simpa only [Polynomial.derivative_map] using
      (Polynomial.hasDerivAt (P.map (Int.castRingHom ℝ)) x)
  exact h

theorem hasDerivAt_PevalR_comp (P : ℤ[X]) (N t : ℝ) :
    HasDerivAt (fun s : ℝ => PevalR P (N * s)) (PderivR P (N * t) * N) t := by
  have h := (hasDerivAt_PevalR P (N * t)).comp t (hasDerivAt_const_mul (𝕜 := ℝ) N)
  simpa [Function.comp_def] using h

theorem continuous_PevalR_comp (P : ℤ[X]) (N : ℝ) :
    Continuous fun s : ℝ => PevalR P (N * s) := by
  have h : Continuous fun y : ℝ => (P.map (Int.castRingHom ℝ)).eval y :=
    (P.map (Int.castRingHom ℝ)).continuous
  simpa [PevalR, Function.comp_def] using h.comp (continuous_const.mul continuous_id)

theorem continuous_PderivR_comp (P : ℤ[X]) (N : ℝ) :
    Continuous fun s : ℝ => PderivR P (N * s) :=
  continuous_PevalR_comp P.derivative N

theorem hasDerivAt_PderivR_comp (P : ℤ[X]) (N t : ℝ) :
    HasDerivAt (fun s : ℝ => PderivR P (N * s)) (Pderiv2R P (N * t) * N) t :=
  hasDerivAt_PevalR_comp P.derivative N t

/-! ## The character `e(x) = exp(2πi x)` and the phase -/

/-- The character `e(x) = exp(2πi x)`, with the coercions made explicit. -/
noncomputable def chi (x : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))

theorem chi_apply (x : ℝ) :
    chi x = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) := rfl

theorem chi_add (a b : ℝ) : chi (a + b) = chi a * chi b := by
  rw [chi_apply, chi_apply, chi_apply]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((a + b : ℝ) : ℂ)
      = 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) by
        push_cast; ring,
    Complex.exp_add]

theorem continuous_chi : Continuous chi := by
  have h : Continuous fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) :=
    Complex.continuous_exp.comp (continuous_const.mul continuous_id)
  have h2 : Continuous fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) :=
    h.comp Complex.continuous_ofReal
  rw [show chi = fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) from rfl]
  exact h2

theorem hasDerivAt_chi (z : ℝ) :
    HasDerivAt chi (chi z * (2 * (Real.pi : ℂ) * Complex.I)) z := by
  have hw : HasDerivAt (fun s : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * (s : ℂ))
      (2 * (Real.pi : ℂ) * Complex.I) z := by
    have h1 : HasDerivAt (fun w : ℂ => (2 * (Real.pi : ℂ) * Complex.I) * w)
        (2 * (Real.pi : ℂ) * Complex.I) (z : ℂ) := hasDerivAt_const_mul (𝕜 := ℂ) _
    simpa [Function.comp_def] using h1.comp z (hasDerivAt_id z).ofReal_comp
  have h := hw.cexp
  have hfun : (fun s : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (s : ℂ))) = chi := by
    funext s
    rw [chi_apply]
  rw [hfun] at h
  rw [show Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (z : ℂ)) = chi z from
    (by rw [chi_apply])] at h
  exact h

/-- The phase `t ↦ ξ₁ N t + ξ₂ P(N t)`. -/
noncomputable def phase (P : ℤ[X]) (N ξ₁ ξ₂ t : ℝ) : ℝ :=
  ξ₁ * N * t + PevalR P (N * t) * ξ₂

theorem phase_apply (P : ℤ[X]) (N ξ₁ ξ₂ t : ℝ) :
    phase P N ξ₁ ξ₂ t = ξ₁ * N * t + PevalR P (N * t) * ξ₂ := rfl

/-- The continuous part of the halved average: `Φ(t) = e(ξ₁ N t + ξ₂ P(N t))`. -/
noncomputable def Phi (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ) : ℝ → ℂ :=
  fun t => chi (phase P N ξ₁ ξ₂ t)

theorem Phi_apply (P : ℤ[X]) (N ξ₁ ξ₂ t : ℝ) :
    Phi P N ξ₁ ξ₂ t = chi (phase P N ξ₁ ξ₂ t) := rfl

theorem continuous_Phi (P : ℤ[X]) (N ξ₁ ξ₂ : ℝ) : Continuous (Phi P N ξ₁ ξ₂) := by
  have h : Continuous fun t : ℝ => ξ₁ * N * t + PevalR P (N * t) * ξ₂ :=
    (continuous_const.mul continuous_id).add
      ((continuous_PevalR_comp P N).mul continuous_const)
  rw [show Phi P N ξ₁ ξ₂
      = fun t : ℝ => chi (ξ₁ * N * t + PevalR P (N * t) * ξ₂) from rfl]
  exact continuous_chi.comp h

theorem hasDerivAt_phase (P : ℤ[X]) (N ξ₁ ξ₂ t : ℝ) :
    HasDerivAt (fun s : ℝ => phase P N ξ₁ ξ₂ s)
      (ξ₁ * N + ξ₂ * (PderivR P (N * t) * N)) t := by
  have h : HasDerivAt (fun s : ℝ => ξ₁ * N * s + PevalR P (N * s) * ξ₂)
      (ξ₁ * N + (PderivR P (N * t) * N) * ξ₂) t := by
    have h₁ : HasDerivAt (fun s : ℝ => ξ₁ * N * s) (ξ₁ * N) t := by
      simpa using (hasDerivAt_const_mul (𝕜 := ℝ) (ξ₁ * N))
    have h₂ : HasDerivAt (fun s : ℝ => PevalR P (N * s) * ξ₂)
        ((PderivR P (N * t) * N) * ξ₂) t :=
      (hasDerivAt_PevalR_comp P N t).mul_const ξ₂
    exact h₁.add h₂
  rw [show (fun s : ℝ => phase P N ξ₁ ξ₂ s)
      = fun s : ℝ => ξ₁ * N * s + PevalR P (N * s) * ξ₂ from rfl]
  convert h using 1
  ring

theorem hasDerivAt_Phi (P : ℤ[X]) (N ξ₁ ξ₂ t : ℝ) :
    HasDerivAt (Phi P N ξ₁ ξ₂)
      (Phi P N ξ₁ ξ₂ t
        * ((2 * (Real.pi : ℂ) * Complex.I)
          * (((ξ₁ * N + ξ₂ * (PderivR P (N * t) * N) : ℝ)) : ℂ))) t := by
  have hphase : HasDerivAt (fun s : ℝ => ((phase P N ξ₁ ξ₂ s : ℝ) : ℂ))
      (((ξ₁ * N + ξ₂ * (PderivR P (N * t) * N) : ℝ)) : ℂ) t :=
    (hasDerivAt_phase P N ξ₁ ξ₂ t).ofReal_comp
  have hg : HasDerivAt
      (fun s : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * ((phase P N ξ₁ ξ₂ s : ℝ) : ℂ))
      ((2 * (Real.pi : ℂ) * Complex.I)
        * (((ξ₁ * N + ξ₂ * (PderivR P (N * t) * N) : ℝ)) : ℂ)) t :=
    hphase.const_mul _
  have h := hg.cexp
  rw [show (fun s : ℝ => Complex.exp
        ((2 * (Real.pi : ℂ) * Complex.I) * ((phase P N ξ₁ ξ₂ s : ℝ) : ℂ)))
      = Phi P N ξ₁ ξ₂ from (by
        funext s
        rw [Phi_apply, chi_apply])] at h
  rw [show Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((phase P N ξ₁ ξ₂ t : ℝ) : ℂ))
      = Phi P N ξ₁ ξ₂ t from (by rw [Phi_apply, chi_apply])] at h
  exact h

/-! ## The normalising factors -/

/-- The normalising factor `2πi ξ₁ N` of the identity (i). -/
noncomputable def cnorm₁ (ξ₁ N : ℝ) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (ξ₁ : ℂ) * (N : ℂ)

theorem cnorm₁_apply (ξ₁ N : ℝ) :
    cnorm₁ ξ₁ N = 2 * (Real.pi : ℂ) * Complex.I * (ξ₁ : ℂ) * (N : ℂ) := rfl

theorem cnorm₁_ne_zero {ξ₁ N : ℝ} (hξ₁ : ξ₁ ≠ 0) (hN : N ≠ 0) : cnorm₁ ξ₁ N ≠ 0 := by
  have h1 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  rw [cnorm₁_apply]
  exact mul_ne_zero (mul_ne_zero h1 (by exact_mod_cast hξ₁)) (by exact_mod_cast hN)

/-- The normalising factor `2πi ξ₂ N P'(Nt)` of the identity (ii). -/
noncomputable def cnorm₂ (P : ℤ[X]) (N ξ₂ t : ℝ) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ) * (N : ℂ) * ((PderivR P (N * t) : ℝ) : ℂ)

theorem cnorm₂_apply (P : ℤ[X]) (N ξ₂ t : ℝ) :
    cnorm₂ P N ξ₂ t
      = 2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ) * (N : ℂ) * ((PderivR P (N * t) : ℝ) : ℂ)
      := rfl

theorem cnorm₂_eq (P : ℤ[X]) (N ξ₂ t : ℝ) :
    cnorm₂ P N ξ₂ t
      = (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ) * (N : ℂ))
        * ((PderivR P (N * t) : ℝ) : ℂ) := rfl

theorem hasDerivAt_cnorm₂ (P : ℤ[X]) (N ξ₂ t : ℝ) :
    HasDerivAt (fun s : ℝ => cnorm₂ P N ξ₂ s)
      ((2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ) * (N : ℂ))
        * (((Pderiv2R P (N * t) * N : ℝ)) : ℂ)) t := by
  have h : HasDerivAt (fun s : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ) * (N : ℂ))
        * ((PderivR P (N * s) : ℝ) : ℂ))
      ((2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ) * (N : ℂ))
        * (((Pderiv2R P (N * t) * N : ℝ)) : ℂ)) t :=
    ((hasDerivAt_PderivR_comp P N t).ofReal_comp).const_mul _
  rw [show (fun s : ℝ => cnorm₂ P N ξ₂ s)
      = fun s : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ) * (N : ℂ))
        * ((PderivR P (N * s) : ℝ) : ℂ) from rfl]
  exact h

theorem cnorm₂_ne_zero {P : ℤ[X]} {N ξ₂ t : ℝ} (hξ₂ : ξ₂ ≠ 0) (hN : N ≠ 0)
    (hP : PderivR P (N * t) ≠ 0) : cnorm₂ P N ξ₂ t ≠ 0 := by
  have h1 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have h4 : ((PderivR P (N * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP
  rw [cnorm₂_eq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 (by exact_mod_cast hξ₂))
    (by exact_mod_cast hN)) h4

/-! ## The identity (i) -/

/-- **`integ-ident`(i)**: integrating `e(ξ₁ N t)` by parts. -/
theorem integIdent_i_core (P : ℤ[X]) {N ξ₁ ξ₂ : ℝ} (hN : N ≠ 0) (hξ₁ : ξ₁ ≠ 0) :
    ∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t
      = Phi P N ξ₁ ξ₂ 1 / cnorm₁ ξ₁ N
        - Phi P N ξ₁ ξ₂ (1 / 2) / cnorm₁ ξ₁ N
        - ((ξ₂ / ξ₁ : ℝ) : ℂ) * ∫ t in (1 / 2 : ℝ)..1,
            Phi P N ξ₁ ξ₂ t * ((PderivR P (N * t) : ℝ) : ℂ) := by
  have hpt : ∀ t : ℝ,
      (cnorm₁ ξ₁ N)⁻¹ * (Phi P N ξ₁ ξ₂ t
          * ((2 * (Real.pi : ℂ) * Complex.I)
            * (((ξ₁ * N + ξ₂ * (PderivR P (N * t) * N) : ℝ)) : ℂ)))
        = Phi P N ξ₁ ξ₂ t
          + ((ξ₂ / ξ₁ : ℝ) : ℂ)
              * (Phi P N ξ₁ ξ₂ t * ((PderivR P (N * t) : ℝ) : ℂ)) := by
    intro t
    have h1c : ((ξ₁ : ℂ)) ≠ 0 := by exact_mod_cast hξ₁
    have h2c : ((N : ℂ)) ≠ 0 := by exact_mod_cast hN
    have hπ : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    rw [cnorm₁_apply]
    push_cast
    field_simp
  have hderiv : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (cnorm₁ ξ₁ N)⁻¹ * Phi P N ξ₁ ξ₂ s)
        ((cnorm₁ ξ₁ N)⁻¹ * (Phi P N ξ₁ ξ₂ t
          * ((2 * (Real.pi : ℂ) * Complex.I)
            * (((ξ₁ * N + ξ₂ * (PderivR P (N * t) * N) : ℝ)) : ℂ)))) t :=
    fun t _ => (hasDerivAt_Phi P N ξ₁ ξ₂ t).const_mul _
  have hcont : Continuous fun t : ℝ =>
      (cnorm₁ ξ₁ N)⁻¹ * (Phi P N ξ₁ ξ₂ t
        * ((2 * (Real.pi : ℂ) * Complex.I)
          * (((ξ₁ * N + ξ₂ * (PderivR P (N * t) * N) : ℝ)) : ℂ))) :=
    continuous_const.mul ((continuous_Phi P N ξ₁ ξ₂).mul (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.add (continuous_const.mul
        ((continuous_PderivR_comp P N).mul continuous_const))))))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable _ _)
  have hsplit : ∫ t in (1 / 2 : ℝ)..1, (Phi P N ξ₁ ξ₂ t
        + ((ξ₂ / ξ₁ : ℝ) : ℂ)
            * (Phi P N ξ₁ ξ₂ t * ((PderivR P (N * t) : ℝ) : ℂ)))
      = (∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t)
        + ((ξ₂ / ξ₁ : ℝ) : ℂ)
            * ∫ t in (1 / 2 : ℝ)..1,
                Phi P N ξ₁ ξ₂ t * ((PderivR P (N * t) : ℝ) : ℂ) := by
    have hInt1 : IntervalIntegrable (fun t : ℝ => Phi P N ξ₁ ξ₂ t) volume (1 / 2) 1 :=
      (continuous_Phi P N ξ₁ ξ₂).intervalIntegrable _ _
    have hInt2 : IntervalIntegrable (fun t : ℝ => ((ξ₂ / ξ₁ : ℝ) : ℂ)
        * (Phi P N ξ₁ ξ₂ t * ((PderivR P (N * t) : ℝ) : ℂ))) volume (1 / 2) 1 :=
      (continuous_const.mul ((continuous_Phi P N ξ₁ ξ₂).mul
        (Complex.continuous_ofReal.comp (continuous_PderivR_comp P N)))).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (f := fun t : ℝ => Phi P N ξ₁ ξ₂ t)
      (g := fun t : ℝ => ((ξ₂ / ξ₁ : ℝ) : ℂ)
        * (Phi P N ξ₁ ξ₂ t * ((PderivR P (N * t) : ℝ) : ℂ))) hInt1 hInt2,
      intervalIntegral.integral_const_mul]
  have hcongr : ∫ t in (1 / 2 : ℝ)..1,
        (cnorm₁ ξ₁ N)⁻¹ * (Phi P N ξ₁ ξ₂ t
          * ((2 * (Real.pi : ℂ) * Complex.I)
            * (((ξ₁ * N + ξ₂ * (PderivR P (N * t) * N) : ℝ)) : ℂ)))
      = ∫ t in (1 / 2 : ℝ)..1, (Phi P N ξ₁ ξ₂ t
        + ((ξ₂ / ξ₁ : ℝ) : ℂ)
            * (Phi P N ξ₁ ξ₂ t * ((PderivR P (N * t) : ℝ) : ℂ))) :=
    intervalIntegral.integral_congr (fun t _ => hpt t)
  have key : (∫ t in (1 / 2 : ℝ)..1, Phi P N ξ₁ ξ₂ t)
        + ((ξ₂ / ξ₁ : ℝ) : ℂ)
            * ∫ t in (1 / 2 : ℝ)..1,
                Phi P N ξ₁ ξ₂ t * ((PderivR P (N * t) : ℝ) : ℂ)
      = (cnorm₁ ξ₁ N)⁻¹ * Phi P N ξ₁ ξ₂ 1
        - (cnorm₁ ξ₁ N)⁻¹ * Phi P N ξ₁ ξ₂ (1 / 2) := by
    rw [← hsplit, ← hcongr]
    exact hFTC
  rw [inv_mul_eq_div, inv_mul_eq_div] at key
  exact (eq_sub_iff_add_eq).mpr key


end

end Work.KMTPlan.A6
