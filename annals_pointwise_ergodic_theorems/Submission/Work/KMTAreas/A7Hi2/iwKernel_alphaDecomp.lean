import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory

namespace Work.KMTAreas.A7Hi2

variable {A : Finset Work.Analysis.IonescuWainger.Circle}
variable {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
variable {j : ℤ}

/-- Integrability on the (compact, finite-measure) circle of a continuous function. -/
private lemma integrable_of_continuous_circle
    (f : Work.Analysis.IonescuWainger.Circle → ℂ) (hf : Continuous f) :
    Integrable f (AddCircle.haarAddCircle (T := 1)) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The character identity in the *argument*: `fourier n (y + α) = fourier n y * fourier n α`. -/
private lemma fourier_add_arg (n : ℤ) (α y : Work.Analysis.IonescuWainger.Circle) :
    (fourier n) (y + α) = (fourier n) y * (fourier n) α := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add]
  norm_cast

/-- **Linearity of the Fourier coefficient in an `A`-indexed finite sum.** -/
private lemma fourierCoeff_finset_sum (g : Work.Analysis.IonescuWainger.Circle →
    Work.Analysis.IonescuWainger.Circle → ℂ) (hg : ∀ α, Continuous (g α)) (j : ℤ) :
    fourierCoeff (fun ξ : Work.Analysis.IonescuWainger.Circle => ∑ α ∈ A, g α ξ) j
      = ∑ α ∈ A, fourierCoeff (g α) j := by
  have hint : ∀ α ∈ A, Integrable (fun t : Work.Analysis.IonescuWainger.Circle =>
      (fourier (-j)) t • g α t) (AddCircle.haarAddCircle (T := 1)) :=
    fun α _ => integrable_of_continuous_circle _ (((fourier (-j)).continuous).smul (hg α))
  simp only [fourierCoeff]
  rw [show (fun t : Work.Analysis.IonescuWainger.Circle =>
        (fourier (-j)) t • ∑ α ∈ A, g α t)
      = (fun t : Work.Analysis.IonescuWainger.Circle =>
        ∑ α ∈ A, (fourier (-j)) t • g α t) from by
        funext t
        rw [Finset.smul_sum]]
  rw [MeasureTheory.integral_finsetSum (s := A) (f := fun α t =>
    (fourier (-j)) t • g α t) hint]

/-- **The kernel of a translated symbol**: the Fourier coefficient of `Φ(· - α)` at `j` is
`fourier (-j) α` times that of `Φ`. -/
private lemma fourierCoeff_comp_sub (hΦ : Continuous Φ) (j : ℤ)
    (α : Work.Analysis.IonescuWainger.Circle) :
    fourierCoeff (fun ξ : Work.Analysis.IonescuWainger.Circle => Φ (ξ - α)) j
      = (fourier (-j) α) • fourierCoeff Φ j := by
  have hint : Integrable (fun y : Work.Analysis.IonescuWainger.Circle =>
      (fourier (-j)) (y + α) • Φ y) (AddCircle.haarAddCircle (T := 1)) :=
    integrable_of_continuous_circle _
      (((fourier (-j)).continuous.comp (continuous_id.add continuous_const)).smul hΦ)
  simp only [fourierCoeff]
  -- substitute `t = y + α` using the translation invariance of the Haar measure
  rw [show (fun t : Work.Analysis.IonescuWainger.Circle => (fourier (-j)) t • Φ (t - α))
      = (fun t : Work.Analysis.IonescuWainger.Circle =>
          (fun y : Work.Analysis.IonescuWainger.Circle => (fourier (-j)) (y + α) • Φ y)
            (t + (-α))) from by
        funext t
        show (fourier (-j)) t • Φ (t - α) = (fourier (-j)) (t + (-α) + α) • Φ (t + (-α))
        rw [show t + (-α) + α = t from by abel]
        rw [show t - α = t + (-α) from sub_eq_add_neg t α]]
  rw [MeasureTheory.integral_add_right_eq_self
    (f := fun y : Work.Analysis.IonescuWainger.Circle => (fourier (-j)) (y + α) • Φ y) (-α)]
  -- extract the character factor
  rw [show (fun y : Work.Analysis.IonescuWainger.Circle => (fourier (-j)) (y + α) • Φ y)
      = (fun y : Work.Analysis.IonescuWainger.Circle =>
          (fourier (-j)) α • ((fourier (-j)) y • Φ y)) from by
        funext y
        rw [fourier_add_arg, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        ring]
  rw [MeasureTheory.integral_smul]

/-- **The `α`-decomposition of the Ionescu--Wainger symbol at the level of the kernel.**

For a *continuous* symbol `Φ` on the circle and every `j : ℤ`,

`iwKernel (∑_{α ∈ A} Φ(· - α)) j = (∑_{α∈A} star (fourier j α)) * iwKernel Φ j`.

This is what turns the arithmetic operator `iwConv A Φ` (a convolution by the comb kernel
`j ↦ W_A(j)·(kernel of Φ)(j)`) into the sum of the `#A` *modulated* copies `M_α (Φ-convolution) M_{-α}`
of the scalar convolution, i.e. the form to which the arithmetic-free lacunary variational estimate
`Work.KMTAreas.A7Hi.DilVar` applies.  (The hypothesis `Continuous Φ` is used only for the
integrability of the summands; it holds in the applications, where `Φ = periodize (etaCut kmtEta k)`
is smooth and compactly supported.) -/
theorem iwKernel_alphaDecomp (Φ : Work.Analysis.IonescuWainger.Circle → ℂ)
    (hΦ : Continuous Φ) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j
      = (∑ α ∈ A, star (fourier j α)) * Work.Analysis.IWMultiplier.iwKernel Φ j := by
  have hsym : Work.Analysis.IonescuWainger.iwSymbolSet A Φ
      = fun ξ => ∑ α ∈ A, Φ (ξ - α) := by
    funext ξ
    exact Work.Analysis.IonescuWainger.iwSymbolSet_apply A Φ ξ
  rw [Work.Analysis.IWMultiplier.iwKernel, hsym,
    fourierCoeff_finset_sum (A := A) (fun α ξ => Φ (ξ - α))
      (fun α => hΦ.comp (continuous_id.sub continuous_const)) j]
  rw [Finset.sum_congr rfl fun α _ => fourierCoeff_comp_sub hΦ j α]
  rw [← Finset.sum_smul]
  rw [show (∑ α ∈ A, (fourier (-j)) α) = ∑ α ∈ A, star (fourier j α) from
        Finset.sum_congr rfl fun α _ => fourier_neg (n := j) (x := α)]
  simp only [Work.Analysis.IWMultiplier.iwKernel, smul_eq_mul]

end Work.KMTAreas.A7Hi2
