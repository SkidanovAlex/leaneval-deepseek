import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.norm_opMul_le_of_kernel
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.fourierCoeff_arcTranslate

open MeasureTheory
open scoped lp BigOperators ENNReal

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The Fourier coefficients of the arc symbol `Σ_{β ∈ E} φ(· - β)`: they are the coefficients of
`φ` modulated by the characters of the arc points,
`∫ (Σ_{β∈E} φ(·-β)) · star e_m = (Σ_{β∈E} star e_m(β)) · ∫ φ · star e_m`.

The sum is exchanged with the integral (`integral_finsetSum`, all terms being bounded hence
integrable on the probability space `𝕋`), and each term is evaluated by translation invariance of
the Haar measure (`fourierCoeff_arcTranslate`). -/
theorem integral_arcSymbol_mul_fourier (φ : Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ}
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    (E : Finset Circle) (m : ℤ) :
    ∫ ξ : Circle, arcSymbol φ E ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = (∑ β ∈ E, star (fourier m β)) * K m := by
  have hpoint : (fun ξ : Circle => arcSymbol φ E ξ * star (fourier m ξ))
      = fun ξ : Circle => ∑ β ∈ E, arcTranslate β φ ξ * star (fourier m ξ) := by
    funext ξ
    simp only [arcSymbol_apply, arcTranslate_apply, Finset.sum_mul]
  rw [hpoint]
  rw [integral_finsetSum E (fun β _ => ?_)]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [fourierCoeff_arcTranslate φ hφ β m, hK m]
  · have hchar : MemLp (fun ξ : Circle => star (fourier m ξ)) ⊤
        (AddCircle.haarAddCircle (T := 1)) :=
      memLp_top_of_bound ((continuous_star.comp (map_continuous (fourier m))).aestronglyMeasurable) 1
        (Filter.Eventually.of_forall fun ξ => by rw [norm_star, norm_fourier_apply'])
    have hβ := memLp_arcTranslate hφ β
    have haesm : AEStronglyMeasurable (fun ξ : Circle => arcTranslate β φ ξ * star (fourier m ξ))
        (AddCircle.haarAddCircle (T := 1)) :=
      (hβ.aestronglyMeasurable).mul (hchar.aestronglyMeasurable)
    have hle : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
        ‖arcTranslate β φ ξ * star (fourier m ξ)‖ ≤ ‖arcTranslate β φ ξ‖ :=
      Filter.Eventually.of_forall fun ξ => by rw [norm_mul, norm_star, norm_fourier_apply', mul_one]
    exact (hβ.of_le haesm hle).integrable le_top

/-- The Fourier coefficients of the `L^∞`-class `arcSymbolLp φ hφ E` of the arc symbol.  The class
is a.e. equal to the symbol (`arcSymbolLp_coeFn`), so the integrals agree. -/
theorem integral_arcSymbolLp_mul_fourier (φ : Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ}
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    (E : Finset Circle) (m : ℤ) :
    ∫ ξ : Circle, (arcSymbolLp φ hφ E : Circle → ℂ) ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = (∑ β ∈ E, star (fourier m β)) * K m := by
  have hcoef : ∫ ξ : Circle, (arcSymbolLp φ hφ E : Circle → ℂ) ξ * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1))
      = ∫ ξ : Circle, arcSymbol φ E ξ * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1)) := by
    refine integral_congr_ae ?_
    filter_upwards [arcSymbolLp_coeFn φ hφ E] with ξ hξ
    rw [hξ]
  rw [hcoef]
  exact integral_arcSymbol_mul_fourier φ hφ hK E m

/-- **The convolution identity for the arc multiplier `opArc φ hφ E`**: the multiplier whose
symbol is `Σ_{β ∈ E} φ(· - β)` acts as the convolution with its kernel

`K'(j) := (∑_{β ∈ E} star (fourier j β)) * K j`,  where  `K j := ∫ ξ, φ ξ * star (fourier j ξ)`.

This is the ℓᵖ *realisation* of `opArc`: `opArc` is defined through the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary
(`opMul` and `fourierBasis.repr`), so its action on sequences which are not in `ℓ²` is only visible
through this formula.  It is what allows the kernel-language estimates of this directory
(`kernel_arcSymbol_torsion`, `norm_opMul_le_of_kernel`, `msw_torsion_kernel`, ...) to be applied to
`opArc`, and it exhibits the operator on the dense class of finitely supported sequences.

Route: instantiate the landed `opMul_eq_tsum_kernel` with the symbol `arcSymbolLp φ hφ E` and the
kernel `K'` above.  Its kernel hypothesis is
`∫ ξ, (arcSymbolLp φ hφ E : Circle → ℂ) ξ * star (fourier m ξ) ∂haar = K' m`; reduce the left side to
`∫ ξ, Σ_{β ∈ E} φ (ξ - β) * star (fourier m ξ) ∂haar` with `arcSymbolLp_coeFn`, exchange the finite
sum with the integral, and evaluate each term by the translation invariance of the Haar measure
(`integral_add_right_eq_self`) together with the character identity
`fourier m (η + β) = fourier m η * fourier m β`.  The per-`β` step is already landed as
`fourierCoeff_arcTranslate`. -/
theorem opArc_eq_tsum_kernel (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ}
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    (E : Finset Work.BourgainPlan.IonescuWainger.Circle) (f : ℤ → ℂ) (hf : Memℓp f 2) (n : ℤ) :
    Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n
      = ∑' k : ℤ, f k * ((∑ β ∈ E, star (fourier (n - k) β)) * K (n - k)) := by
  simpa [opArc] using
    opMul_eq_tsum_kernel (arcSymbolLp φ hφ E) f hf
      (integral_arcSymbolLp_mul_fourier φ hφ hK E) n

end

end Work.BourgainPlan.IonescuWainger
