import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace Commons.Analysis.Measure

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

/-- The measurable equivalence `(ℝ^d × ℝ^d) ≃ᵐ ℂ^d` sending `(x, y)` to `x + i y`. -/
def stripEquiv (d : ℕ) : ((Fin d → ℝ) × (Fin d → ℝ)) ≃ᵐ (Fin d → ℂ) :=
  (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)).symm.trans
    (MeasurableEquiv.piCongrRight (fun _ : Fin d => Complex.measurableEquivRealProd)).symm

theorem stripEquiv_apply (d : ℕ) (x y : Fin d → ℝ) :
    stripEquiv d (x, y) = fun i => (x i : ℂ) + (y i : ℂ) * Complex.I := by
  have h1 : (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)).symm (x, y)
      = (fun i => (x i, y i)) := by
    funext i
    exact Equiv.arrowProdEquivProdArrow_symm_apply (Fin d) (fun _ => ℝ) (fun _ => ℝ) (x, y) i
  funext i
  rw [stripEquiv, MeasurableEquiv.coe_trans, Function.comp_apply, h1]
  show Complex.measurableEquivRealProd.symm (x i, y i) = _
  rw [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]

theorem stripEquiv_measurePreserving (d : ℕ) : MeasurePreserving (stripEquiv d) := by
  have h1 : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)).symm :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin d)).symm
  have h2' : MeasurePreserving
      (fun (p : Fin d → ℝ × ℝ) i => Complex.measurableEquivRealProd.symm (p i)) :=
    measurePreserving_pi (fun _ : Fin d => (volume : Measure (ℝ × ℝ)))
      (fun _ : Fin d => (volume : Measure ℂ))
      (fun _ => Complex.volume_preserving_equiv_real_prod.symm)
  have h2 : MeasurePreserving
      (MeasurableEquiv.piCongrRight (fun _ : Fin d => Complex.measurableEquivRealProd)).symm :=
    h2'
  have h12 := h1.trans h2
  simpa only [stripEquiv] using h12

/-- The integral over the horizontal strip `{|Im z_i| ≤ Q}` in `ℂ^d` equals the iterated
integral over real part `x ∈ ℝ^d` and imaginary part `y ∈ [-Q,Q]^d`. -/
theorem integral_strip_eq_iterated {d : ℕ} (f : (Fin d → ℂ) → ℝ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hf : IntegrableOn f {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ Q} volume) :
    ∫ z in {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ Q}, f z
      = ∫ y in Set.pi Set.univ (fun _ : Fin d => Set.Icc (-Q) Q),
          ∫ x : Fin d → ℝ, f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) := by
  classical
  have hQ0 : (0 : ℝ) ≤ Q := hQ
  set B : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ : Fin d => Set.Icc (-Q) Q) with hB
  set S : Set (Fin d → ℂ) := {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ Q} with hS
  have hmp : MeasurePreserving (stripEquiv d) := stripEquiv_measurePreserving d
  have hpre : (stripEquiv d) ⁻¹' S = Set.univ ×ˢ B := by
    ext p
    simp only [Set.mem_preimage, hS, hB, Set.mem_prod, Set.mem_pi, Set.mem_Icc,
      Set.mem_ofPred_eq, Set.mem_univ, true_implies, true_and]
    have him : ∀ i, ((stripEquiv d) p i).im = p.2 i := by
      intro i
      rw [stripEquiv_apply d p.1 p.2]
      simp
    constructor
    · intro h i
      have := abs_le.mp (h i)
      rwa [him i] at this
    · intro h i
      have := abs_le.mpr (h i)
      simpa [him i] using this
  have hg : IntegrableOn (fun p : (Fin d → ℝ) × (Fin d → ℝ) => f (stripEquiv d p))
      (Set.univ ×ˢ B) volume := by
    have h := (hmp.integrableOn_comp_preimage (stripEquiv d).measurableEmbedding
      (f := f) (s := S)).mpr hf
    rwa [hpre] at h
  have hswap : IntegrableOn (fun q : (Fin d → ℝ) × (Fin d → ℝ) => f (stripEquiv d q.swap))
      (B ×ˢ Set.univ) volume := hg.swap
  have step1 : ∫ z in S, f z
      = ∫ p : (Fin d → ℝ) × (Fin d → ℝ),
          f (stripEquiv d p) ∂(volume.restrict ((stripEquiv d) ⁻¹' S)) := by
    have hmap : (volume : Measure (Fin d → ℂ)).restrict S
        = Measure.map (stripEquiv d)
            ((volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))).restrict ((stripEquiv d) ⁻¹' S)) := by
      calc (volume : Measure (Fin d → ℂ)).restrict S
          = (Measure.map (stripEquiv d) (volume : Measure ((Fin d → ℝ) × (Fin d → ℝ)))).restrict S := by
            rw [hmp.map_eq]
        _ = _ := MeasurableEquiv.restrict_map (stripEquiv d) volume S
    rw [hmap]
    exact integral_map_equiv (stripEquiv d) f
  have step2 : ∫ p : (Fin d → ℝ) × (Fin d → ℝ),
        f (stripEquiv d p) ∂(volume.restrict ((stripEquiv d) ⁻¹' S))
      = ∫ p in Set.univ ×ˢ B, f (stripEquiv d p) ∂volume := by
    rw [hpre]
  have step3 : ∫ p in Set.univ ×ˢ B, f (stripEquiv d p) ∂volume
      = ∫ q in B ×ˢ Set.univ, f (stripEquiv d q.swap) ∂volume :=
    (setIntegral_prod_swap (μ := (volume : Measure (Fin d → ℝ)))
      (ν := (volume : Measure (Fin d → ℝ))) Set.univ B (fun p => f (stripEquiv d p))).symm
  have step4 : ∫ q in B ×ˢ Set.univ, f (stripEquiv d q.swap) ∂volume
      = ∫ y in B, ∫ x in Set.univ, f (stripEquiv d (x, y)) ∂volume ∂volume :=
    setIntegral_prod (fun q : (Fin d → ℝ) × (Fin d → ℝ) => f (stripEquiv d q.swap)) hswap
  have step5 : ∫ y in B, ∫ x in Set.univ, f (stripEquiv d (x, y)) ∂volume ∂volume
      = ∫ y in B, ∫ x : Fin d → ℝ,
          f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [Measure.restrict_univ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [stripEquiv_apply])
  rw [step1, step2, step3, step4, step5]

end

end Commons.Analysis.Measure