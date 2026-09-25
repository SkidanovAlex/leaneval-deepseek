import Mathlib
import Submission.PolynomialKernel
import Submission.Work.BourgainPlan.Maximal.khatDefs
import Submission.Work.BourgainPlan.Maximal.minor_arc_lp
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.OpMulLinear

/-!
# The `L²(𝕋)`-multiplier vocabulary of the polynomial density average

The density average `A_N g (m) = N⁻¹ Σ_{i<N} g (m + P (i))` (`discAvgZC`) is the convolution with
the density kernel `k_N (j) = N⁻¹ #{i < N : P (i) = j}`, hence the Fourier multiplier on `ℓ²(ℤ)`
with symbol `Σ_j k_N (j) · e^{-2πi j ξ} = conj (khat P N ξ)`.

This file sets up that symbol in the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary of
`IonescuWainger/FourierL2Defs.lean`:

* `khatCircle P N` — the symbol `khat P N` of `khatDefs.lean` read as a function on the circle
  `𝕋 = AddCircle 1`, i.e. the trigonometric polynomial `Σ_j k_N(j) · e_j` (agreement with the
  `ℝ`-valued `khat` is `khatCircle_coe`);
* `khatMult P N` — the same symbol as an element of `L^∞(𝕋)`, the multiplier of the density
  average: `khatMult P N = Σ_j k_N(j) • \bar e_j`.

The point of the `L^∞`-form is that `opMul (khatMult P N) g hg` is then the operator whose symbol
is `conj ∘ khat`, and the multiplier identity `ftLp (discAvgZC P N g) = khatMult P N • ftLp g`
(proved in the companion file) turns the `ℓ²` bound for `A_N ∘ (1 - Π)` into the pointwise bound
`sup ‖khat · (1 - σ)‖`.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-! ## The symbol of the density average on the circle -/

/-- The symbol `khat P N` of the density average, read as a function on the circle `𝕋 = AddCircle 1`:
the trigonometric polynomial `Σ_j k_N(j) · e_j` with `e_j (ξ) = e^{2πi j ξ}`. -/
noncomputable def khatCircle (P : Polynomial ℤ) (N : ℕ) :
    Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  fun ξ => ∑ j ∈ Finset.range (Submission.polySupport P N),
    (Submission.polyKernel P N j : ℂ) * fourier (j : ℤ) ξ

/-- On the real representatives `θ : ℝ` the circle symbol `khatCircle` is the `khat` of
`khatDefs.lean`. -/
theorem khatCircle_coe (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) :
    khatCircle P N ((θ : ℝ) : Work.BourgainPlan.IonescuWainger.Circle) = khat P N θ := by
  unfold khatCircle khat
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem continuous_khatCircle (P : Polynomial ℤ) (N : ℕ) : Continuous (khatCircle P N) := by
  unfold khatCircle
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul (map_continuous (fourier (j : ℤ)))

/-- The symbol of the density average as an `L^∞(𝕋)`-class: `Σ_j k_N(j) • \bar e_j`, i.e. the
class of `conj ∘ khat` (`khatMult_coeFn`). -/
noncomputable def khatMult (P : Polynomial ℤ) (N : ℕ) :
    Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)) :=
  ∑ j ∈ Finset.range (Submission.polySupport P N),
    (Submission.polyKernel P N j : ℂ) • fourierLp (T := 1) (p := ⊤) (-(j : ℤ))

/-- The class of `khatMult P N` is `conj ∘ khatCircle P N`. -/
theorem khatMult_coeFn (P : Polynomial ℤ) (N : ℕ) :
    (khatMult P N : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] fun ξ => star (khatCircle P N ξ) := by
  classical
  rw [khatMult]
  refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
  have hterm : ∀ j ∈ Finset.range (Submission.polySupport P N),
      (((Submission.polyKernel P N j : ℂ) • fourierLp (T := 1) (p := ⊤) (-(j : ℤ)) :
          Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) :
          Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        =ᵐ[AddCircle.haarAddCircle (T := 1)]
        fun ξ => star ((Submission.polyKernel P N j : ℂ) * fourier (j : ℤ) ξ) := by
    intro j _
    refine (Lp.coeFn_smul _ _).trans ?_
    refine (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ _)
      (coeFn_fourierLp (T := 1) (⊤ : ℝ≥0∞) (-(j : ℤ)))).trans ?_
    filter_upwards with ξ
    show (Submission.polyKernel P N j : ℂ) * fourier (-(j : ℤ)) ξ
      = star ((Submission.polyKernel P N j : ℂ) * fourier (j : ℤ) ξ)
    rw [fourier_neg, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  have hev : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ∀ j ∈ Finset.range (Submission.polySupport P N),
        (((Submission.polyKernel P N j : ℂ) • fourierLp (T := 1) (p := ⊤) (-(j : ℤ)) :
            Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) :
            Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
          = star ((Submission.polyKernel P N j : ℂ) * fourier (j : ℤ) ξ) :=
    (Finset.eventually_all (Finset.range (Submission.polySupport P N))).mpr fun j hj =>
      hterm j hj
  filter_upwards [hev] with ξ hξ
  rw [Finset.sum_congr rfl (fun j hj => hξ j hj), ← star_sum]
  congr 1

/-! ## Elementary multiplier identities in the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary -/

/-- The symbol of the density average multiplies the characters as `\bar e_j`. -/
theorem opMul_fourierLp_neg (j : ℤ) (g : ℤ → ℂ) (hg : Memℓp g 2) :
    opMul (fourierLp (T := 1) (p := ⊤) (-j)) g hg = fun m => g (m + j) := by
  funext m
  rw [opMul_apply, opMulLp, show g (m + j)
      = inner ℂ (fourierBasis (T := 1) (m + j)) (ftLp g hg) from (ftLp_coeff hg (m + j)).symm]
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  have h1 : ((fourierBasis (T := 1) m : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
      Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] ⇑(fourier m) := by
    simpa using coeFn_fourierLp (T := 1) (2 : ℝ≥0∞) (n := m)
  have h2 : ((fourierLp (T := 1) (p := ⊤) (-j) • ftLp g hg :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
      Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
        fun ξ => fourier (-j) ξ * (ftLp g hg : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ := by
    refine (Lp.coeFn_lpSMul _ _).trans ?_
    exact Filter.EventuallyEq.mul (coeFn_fourierLp (T := 1) (⊤ : ℝ≥0∞) (-j))
      (Filter.EventuallyEq.refl _ _)
  have h3 : ((fourierBasis (T := 1) (m + j) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
      Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] ⇑(fourier (m + j)) := by
    simpa using coeFn_fourierLp (T := 1) (2 : ℝ≥0∞) (n := m + j)
  filter_upwards [h1, h2, h3] with ξ h1ξ h2ξ h3ξ
  rw [h1ξ, h2ξ, h3ξ, RCLike.inner_apply', RCLike.inner_apply', fourier_neg, fourier_add]
  rw [map_mul]
  ring

end

end Work.BourgainPlan.Maximal
