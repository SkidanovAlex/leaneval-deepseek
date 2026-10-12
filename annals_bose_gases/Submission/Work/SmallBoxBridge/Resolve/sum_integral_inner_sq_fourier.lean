import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inner-product-square sum against the Fourier transform

For a Schwartz function `f : ℝ³ → ℂ` and the standard coordinate basis `e_k = kcStdBasis k`,

    Σ_k ∫_ξ ⟨ξ,e_k⟩² ‖𝓕f(ξ)‖² = ∫_ξ ‖ξ‖² ‖𝓕f(ξ)‖² .

The two ingredients are elementary:

* the pointwise orthonormal-basis identity `Σ_k ⟨ξ,e_k⟩² = ‖ξ‖²` (Parseval for the
  coordinate basis, proved directly from `EuclideanSpace.inner_single_right`);
* the exchange of the finite sum `Σ_k` with the `ξ`-integral, which needs the integrability
  of each summand `ξ ↦ ⟨ξ,e_k⟩² ‖𝓕f(ξ)‖²`.

For the integrability, note `‖𝓕f‖` is a Schwartz function and the multiplier `ξ ↦ ⟨ξ,e_k⟩`
has temperate growth, so `ξ ↦ ⟨ξ,e_k⟩ • 𝓕f(ξ)` is again a Schwartz function `G_k`; then
`‖G_k ξ‖² = ⟨ξ,e_k⟩² ‖𝓕f(ξ)‖²` is integrable because `G_k ∈ L²` and
`MemLp.… ↔ Integrable (‖·‖²)`.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.SmallBoxBridge.Resolve

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Parseval for the standard coordinate basis**: `Σ_k ⟨ξ, e_k⟩² = ‖ξ‖²`. -/
lemma sum_inner_kcStdBasis_sq_local (ξ : ℝ³) :
    (∑ k : Fin 3, (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2) = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Submission.BoseGases.kcStdBasis, EuclideanSpace.inner_single_right]
  simp [Real.norm_eq_abs, sq_abs]

/-- The pointwise form used in the assembly: `Σ_k ⟨ξ,e_k⟩² c = ‖ξ‖² c`. -/
lemma sum_inner_sq_mul_local (ξ : ℝ³) (c : ℝ) :
    (∑ k : Fin 3, (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2 * c)
      = ‖ξ‖ ^ 2 * c := by
  rw [← Finset.sum_mul, sum_inner_kcStdBasis_sq_local]

/-- **Integrability of `ξ ↦ ⟨ξ,m⟩² ‖g ξ‖²`** for a Schwartz function `g`.

The multiplier `ξ ↦ ⟨ξ,m⟩` has temperate growth, so `G : ξ ↦ (⟨ξ,m⟩ : ℂ) * g ξ` is again a
Schwartz function (`SchwartzMap.smulLeftCLM`); moreover
`‖G ξ‖² = ⟨ξ,m⟩² ‖g ξ‖²`, and `G ∈ L²` gives the integrability of `‖G‖²`. -/
lemma integrable_inner_sq_mul_norm_sq (g : SchwartzMap ℝ³ ℂ) (m : ℝ³) :
    Integrable (fun ξ : ℝ³ => (inner ℝ ξ m) ^ 2 * ‖g ξ‖ ^ 2) := by
  have htg : Function.HasTemperateGrowth (fun ξ : ℝ³ => ((inner ℝ ξ m : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp ((innerSL ℝ).flip m)).hasTemperateGrowth
  let G : SchwartzMap ℝ³ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ³ => ((inner ℝ ξ m : ℝ) : ℂ)) g
  have hcoe : ⇑G = fun ξ : ℝ³ => ((inner ℝ ξ m : ℝ) : ℂ) * g ξ := by
    rw [SchwartzMap.smulLeftCLM_apply htg]
    funext ξ
    rfl
  have hmem : MemLp (⇑G) 2 (volume : Measure ℝ³) := G.memLp 2 (volume : Measure ℝ³)
  have hint : Integrable (fun ξ : ℝ³ => ‖G ξ‖ ^ 2) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  refine hint.congr ?_
  filter_upwards with ξ
  rw [hcoe]
  simp only []
  rw [norm_mul, mul_pow]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  ring

theorem sum_integral_inner_sq_fourier (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    (∑ k : Fin 3, ∫ ξ : EuclideanSpace ℝ (Fin 3),
        (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
          * ‖(FourierTransform.fourier f) ξ‖ ^ 2)
      = ∫ ξ : EuclideanSpace ℝ (Fin 3),
          ‖ξ‖ ^ 2 * ‖(FourierTransform.fourier f) ξ‖ ^ 2 := by
  have hint : ∀ k ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun ξ : ℝ³ =>
      (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
        * ‖(FourierTransform.fourier f) ξ‖ ^ 2) :=
    fun k _ => integrable_inner_sq_mul_norm_sq (FourierTransform.fourier f)
      (Submission.BoseGases.kcStdBasis k)
  have hswap : (∑ k : Fin 3, ∫ ξ : ℝ³,
      (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
        * ‖(FourierTransform.fourier f) ξ‖ ^ 2)
      = ∫ ξ : ℝ³, ∑ k : Fin 3,
      (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
        * ‖(FourierTransform.fourier f) ξ‖ ^ 2 :=
    (MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun k ξ => (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
        * ‖(FourierTransform.fourier f) ξ‖ ^ 2) hint).symm
  rw [hswap]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  exact sum_inner_sq_mul_local ξ _

end Work.SmallBoxBridge.Resolve
