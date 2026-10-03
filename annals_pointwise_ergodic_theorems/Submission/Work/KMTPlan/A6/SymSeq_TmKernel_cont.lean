/-
# The symbol of the exact-height IW kernel, with a *continuous* periodisation

`SymSeq_TmKernel` (the target of `Work.KMTPlan.A6.SymSeq_TmKernel`) states, for an integrable and
continuous `φ : ℝ → ℂ` with `∑_p ‖cw φ p‖ < ∞` and every `x : ℝ`,

  `symSeq (TmKernel ρ l φ) x = ∑_{γ ∈ diffFreqs ρ l} (periodize φ) ((x : ℝ/ℤ) - γ)`.

**That statement is false as it stands.**  `periodize φ` is the *pointwise* (unconditional) sum
`(periodize φ) ξ = ∑'_k φ (x_ξ + k)`, while `hsum` only controls the `L¹`-class of `periodize φ`
(its Fourier coefficients are `cw φ p`); the pointwise values of the periodisation can differ from
the sum of the (absolutely convergent) Fourier series `∑_p cw φ p · e (p x)` at the points where
the family `k ↦ φ (x + k)` is not summable.  A concrete counterexample is

  `h x = (1 + 1 / (1 + max 0 x)) * exp (-|x|^3 * dist (x, ℤ)^2)`,   `φ = h - (h ∘ (· + 1))`:

`h` is continuous and integrable, `φ` is continuous and integrable, and for every `p : ℤ`

  `cw φ p = ∫ x, (h x - h (x + 1)) * e (-p x) = (1 - e (p)) * ∫ x, h x * e (-p x) = 0`

because `e (p) = exp (2 π i p) = 1`; hence `hsum` holds and the left-hand side at `x = 0` is
`∑_p cw φ p = 0`.  On the other hand `(periodize φ) 0 = ∑'_k φ k = ∑'_k (h k - h (k + 1))`, and
`h k = 1 + 1/(1+k)` for `k ≥ 0` while `h k = 2` for `k < 0`, so that the symmetric partial sums are
`h (-N) - h (N+1) → 2 - 1 = 1 ≠ 0`.  For `l = 0` one has `diffFreqs ρ 0 = {0}`, so the right-hand
side of the statement is exactly `(periodize φ) 0`, and the statement asserts `0 = 1`.

The missing hypothesis is the *continuity of the periodisation*: with it, the pointwise Fourier
inversion theorem on the circle applies and the identity is proved.  That is the statement proved
below (in the definitionally equal form with `TmKernel` unfolded).  It covers all symbols actually
used in §6: for the `η_{≤k}`-type bumps the periodisation is a locally finite sum of continuous
functions, hence continuous.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymSeq
import Submission.Work.KMTAreas.A7.ModelOps
import Submission.Work.KMTPlan.A6.IwKernelArithChar
import Submission.Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- The Fourier coefficient of the periodisation of an integrable `φ` is `cw φ p`
(the `A = {0}` case of `IwKernelArithChar`). -/
theorem fourierCoeff_periodize_eq_cw {φ : ℝ → ℂ} (hφ : MeasureTheory.Integrable φ) (p : ℤ) :
    fourierCoeff (Work.Analysis.IonescuWainger.periodize φ) p
      = Work.KMTAreas.A7.cw φ p := by
  have h := IwKernelArithChar (A := ({(0 : Circ)} : Finset Circ)) hφ p
  have hsym : Work.Analysis.IonescuWainger.iwSymbolSet ({(0 : Circ)} : Finset Circ)
      (Work.Analysis.IonescuWainger.periodize φ)
      = Work.Analysis.IonescuWainger.periodize φ := by
    funext ξ
    simp [Work.Analysis.IonescuWainger.iwSymbolSet]
  have hone : (∑ α ∈ ({(0 : Circ)} : Finset Circ), fourier (T := 1) (-p) α) = 1 := by
    simp
  rw [hsym, hone, one_mul] at h
  simpa [Work.Analysis.IWMultiplier.iwKernel] using h

/-- `fourier p (x : ℝ/ℤ) = e (p x)`. -/
theorem fourier_coe_one' (p : ℤ) (x : ℝ) :
    fourier (T := 1) p ((x : ℝ) : Circ) = eeC ((p : ℝ) * x) := by
  rw [fourier_coe_apply]
  norm_num [eeC]
  ring_nf

/-- `fourier` is multiplicative in its base point. -/
theorem fourier_add_point (n : ℤ) (ξ η : Circ) :
    fourier (T := 1) n (ξ + η) = fourier (T := 1) n ξ * fourier (T := 1) n η := by
  simp only [fourier_apply]
  rw [smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- `fourier n (-ξ)` is the conjugate of `fourier n ξ`. -/
theorem fourier_neg_point (n : ℤ) (ξ : Circ) :
    fourier (T := 1) n (-ξ) = starRingEnd ℂ (fourier (T := 1) n ξ) := by
  simp only [fourier_apply]
  rw [smul_neg]
  exact fourier_neg'

/-- The character identity behind the splice:
`fourier (-p) γ * fourier p (x : ℝ/ℤ) = fourier p ((x : ℝ/ℤ) - γ)`. -/
theorem fourier_splice (p : ℤ) (γ : Circ) (x : ℝ) :
    fourier (T := 1) (-p) γ * fourier (T := 1) p ((x : ℝ) : Circ)
      = fourier (T := 1) p (((x : ℝ) : Circ) - γ) := by
  rw [sub_eq_add_neg, fourier_add_point, fourier_neg_point, fourier_neg]
  ring

/-- The splice, with the constant `c` in front. -/
theorem splice_mul (p : ℤ) (γ : Circ) (x : ℝ) (c : ℂ) :
    fourier (T := 1) (-p) γ * (c * fourier (T := 1) p ((x : ℝ) : Circ))
      = c * fourier (T := 1) p (((x : ℝ) : Circ) - γ) := by
  rw [mul_left_comm, fourier_splice p γ x]

/-- The unit modulus of the characters. -/
theorem norm_fourier_one (p : ℤ) (ξ : Circ) : ‖fourier (T := 1) p ξ‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- **The symbol of the exact-height IW kernel**, with the periodisation assumed continuous.

`Work.KMTPlan.A6.TmKernel ρ l φ` is *defined* as
`fun j => Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize φ)) j`,
so this is the statement of `SymSeq_TmKernel` with the additional hypothesis
`Continuous (periodize φ)`. -/
theorem SymSeq_iwKernel_cont (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hper : Continuous (Work.Analysis.IonescuWainger.periodize φ))
    (hsum : Summable fun p : ℤ => ‖Work.KMTAreas.A7.cw φ p‖) (x : ℝ) :
    Work.KMTPlan.A6.symSeq
        (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize φ)) j) x
      = ∑ γ ∈ Work.KMTAreas.A7.diffFreqs ρ l,
          Work.Analysis.IonescuWainger.periodize φ
            ((x : Work.Analysis.IonescuWainger.Circle) - γ) := by
  set A : Finset Circ := Work.KMTAreas.A7.diffFreqs ρ l with hA
  have hcoeff : ∀ p : ℤ,
      fourierCoeff (Work.Analysis.IonescuWainger.periodize φ) p
        = Work.KMTAreas.A7.cw φ p := fun p => fourierCoeff_periodize_eq_cw hφ p
  have hsum_cw : Summable (fun p : ℤ => Work.KMTAreas.A7.cw φ p) := hsum.of_norm
  have hsum_F : Summable (fun p : ℤ =>
      fourierCoeff (Work.Analysis.IonescuWainger.periodize φ) p) := by
    refine hsum_cw.congr (fun p => ?_)
    exact (hcoeff p).symm
  have hinv : ∀ ξ : Circ, HasSum (fun p : ℤ =>
      Work.KMTAreas.A7.cw φ p * fourier (T := 1) p ξ)
      (Work.Analysis.IonescuWainger.periodize φ ξ) := by
    intro ξ
    have h := has_pointwise_sum_fourier_series_of_summable
      (f := (⟨Work.Analysis.IonescuWainger.periodize φ, hper⟩ : C(Circ, ℂ))) hsum_F ξ
    simpa [hcoeff, smul_eq_mul] using h
  have hTm : ∀ p : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize φ)) p
      = (∑ γ ∈ A, fourier (T := 1) (-p) γ) * Work.KMTAreas.A7.cw φ p := by
    intro p
    have h := IwKernelArithChar (A := A) hφ p
    simpa using h
  have hsumm : ∀ γ ∈ A, Summable (fun p : ℤ =>
      Work.KMTAreas.A7.cw φ p * fourier (T := 1) p (((x : ℝ) : Circ) - γ)) := by
    intro γ _
    refine Summable.of_norm_bounded hsum (fun p => ?_)
    rw [norm_mul, norm_fourier_one, mul_one]
  have hL : symSeq (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize φ)) j) x
      = ∑' p : ℤ, ∑ γ ∈ A,
          Work.KMTAreas.A7.cw φ p * fourier (T := 1) p (((x : ℝ) : Circ) - γ) := by
    rw [symSeq]
    refine tsum_congr (fun p => ?_)
    have hstep : Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize φ)) p
        = (∑ γ ∈ A, fourier (T := 1) (-p) γ) * Work.KMTAreas.A7.cw φ p := by
      rw [← hA]; exact hTm p
    show Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize φ)) p * eeC ((p : ℝ) * x)
      = ∑ γ ∈ A, Work.KMTAreas.A7.cw φ p * fourier (T := 1) p (((x : ℝ) : Circ) - γ)
    rw [hstep, ← fourier_coe_one' p x, mul_assoc, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    exact splice_mul p γ x (Work.KMTAreas.A7.cw φ p)
  rw [hL, Summable.tsum_finsetSum (fun γ hγ => hsumm γ hγ)]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  exact (hinv (((x : ℝ) : Circ) - γ)).tsum_eq

/-- **The form in which §6 uses the identity.**  For a continuous symbol with compact support (in
particular for every `η_{≤k}`-type bump of the paper), the hypothesis `Continuous (periodize φ)` of
`SymSeq_iwKernel_cont` is automatic, so the symbol identity holds with the *original* hypotheses
`hφ`, `hcont`, `hsum` of the requested statement. -/
theorem SymSeq_iwKernel_cont_of_hasCompactSupport (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ)
    (hφ : MeasureTheory.Integrable φ) (hcont : Continuous φ) (hsupp : HasCompactSupport φ)
    (hsum : Summable fun p : ℤ => ‖Work.KMTAreas.A7.cw φ p‖) (x : ℝ) :
    Work.KMTPlan.A6.symSeq
        (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize φ)) j) x
      = ∑ γ ∈ Work.KMTAreas.A7.diffFreqs ρ l,
          Work.Analysis.IonescuWainger.periodize φ
            ((x : Work.Analysis.IonescuWainger.Circle) - γ) :=
  SymSeq_iwKernel_cont ρ l φ hφ
    (continuous_periodize_of_hasCompactSupport φ hcont hsupp) hsum x

end

end Work.KMTPlan.A6
