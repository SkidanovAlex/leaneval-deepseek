import Mathlib
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

/-!
# The Fourier transform on `ℤ` as a pointwise exponential series

For a sequence `ψ : ℤ → ℂ` which is both absolutely summable and in `ℓ²(ℤ)`, the Fourier
transform `𝓕_ℤ ψ ∈ L²(ℝ/ℤ)` (Mathlib's `fourierBasis` expansion, `fourierZ`) agrees almost
everywhere with the pointwise exponential series

`ξ ↦ ∑' x : ℤ, ψ x * e(-x ξ)`.

This is the bridge between the abstract `L²`-form of the Ionescu–Wainger Fourier transform
(used to define the Fourier multipliers `T_m`) and its punctual description as a series of
characters; it is used whenever a symbol/operator identity has to be read off pointwise on a
conull set of frequencies.

The proof is the expansion `fourierZ ψ = ∑' n, ψ n • fourierLp 2 n` (Mathlib's Hilbert-basis
expansion `fourierZ_hasSum`), together with `Lp.coeFn_tsum`, which computes the values of an
`L²`-convergent series pointwise almost everywhere, and the a.e. identification
`fourierLp 2 n =ᵐ fourier n` of the `n`-th Fourier monomial (`coeFn_fourierLp`).
-/

open MeasureTheory

open scoped BigOperators

namespace Work.KMTAreas.A4

/-- The Fourier monomial on the circle is invariant under negating both the frequency index
and the point: `e(-n · (-ξ)) = e(n ξ)`. -/
theorem fourier_neg_neg_apply (n : ℤ) (ξ : Work.Analysis.IonescuWainger.Circle) :
    (fourier (-n) (-ξ) : ℂ) = fourier n ξ := by
  have h : (fourier n (-ξ) : ℂ) = starRingEnd ℂ (fourier n ξ) := by
    rw [fourier_apply, fourier_apply, smul_neg]
    exact fourier_neg' (T := 1) (n := n) (x := ξ)
  rw [fourier_neg, h]
  simp

theorem fourierZCoeFnEqTsum {ψ : ℤ → ℂ} (hψ : Summable fun x : ℤ => ‖ψ x‖)
    (hm : Memℓp ψ 2) :
    ⇑(Work.Analysis.IonescuWainger.fourierZ (⟨ψ, hm⟩ : Work.Analysis.IonescuWainger.L2Z))
      =ᵐ[Work.Analysis.IonescuWainger.circleMeasure]
      fun ξ => ∑' x : ℤ, ψ x * (fourier (-x) (-ξ) : ℂ) := by
  classical
  set F : Work.Analysis.IonescuWainger.L2Z := ⟨ψ, hm⟩ with hF
  have hFn : ∀ n : ℤ, ((F : ∀ _ : ℤ, ℂ) n) = ψ n := fun n => rfl
  -- the expansion converges absolutely in `ℓ²(ℤ)`-norm
  have hsum : Summable (fun n : ℤ => ‖((F : ∀ _ : ℤ, ℂ) n) • fourierLp (T := 1) 2 n‖) := by
    refine Summable.of_norm_bounded (g := fun n : ℤ => ‖ψ n‖) hψ (fun n => ?_)
    rw [norm_smul, hFn n, (orthonormal_fourier (T := 1)).norm_eq_one n, mul_one]
    simp
  have hnorm : ∑' n : ℤ, ‖((F : ∀ _ : ℤ, ℂ) n) • fourierLp (T := 1) 2 n‖ₑ ≠ ⊤ := by
    have h1 : ∑' n : ℤ, ‖((F : ∀ _ : ℤ, ℂ) n) • fourierLp (T := 1) 2 n‖ₑ
        = ENNReal.ofReal
            (∑' n : ℤ, ‖((F : ∀ _ : ℤ, ℂ) n) • fourierLp (T := 1) 2 n‖) := by
      simp only [← ofReal_norm]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hsum).symm
    rw [h1]
    exact ENNReal.ofReal_ne_top
  -- `Lp.coeFn_tsum`: the values of the `L²`-series are the pointwise series
  have hcoe : ⇑(Work.Analysis.IonescuWainger.fourierZ F) =ᵐ[
      Work.Analysis.IonescuWainger.circleMeasure]
      fun ξ => ∑' n : ℤ, (((F : ∀ _ : ℤ, ℂ) n) • fourierLp (T := 1) 2 n) ξ := by
    have h := Lp.coeFn_tsum (μ := Work.Analysis.IonescuWainger.circleMeasure) (p := 2)
      (f := fun n : ℤ => ((F : ∀ _ : ℤ, ℂ) n) • fourierLp (T := 1) 2 n) hnorm
    rw [(Work.Analysis.IonescuWainger.fourierZ_hasSum F).tsum_eq] at h
    exact h
  -- each summand is the corresponding exponential, almost everywhere
  have hterm : ∀ᵐ ξ ∂Work.Analysis.IonescuWainger.circleMeasure, ∀ n : ℤ,
      (((F : ∀ _ : ℤ, ℂ) n) • fourierLp (T := 1) 2 n) ξ = ψ n * (fourier n ξ : ℂ) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul ((F : ∀ _ : ℤ, ℂ) n) (fourierLp (T := 1) 2 n),
      coeFn_fourierLp (T := 1) 2 n] with ξ h1 h2
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul, h2, hFn n]
  filter_upwards [hcoe, hterm] with ξ h1 h2
  rw [h1]
  refine tsum_congr fun n => ?_
  rw [h2 n, ← fourier_neg_neg_apply n ξ]

end Work.KMTAreas.A4
