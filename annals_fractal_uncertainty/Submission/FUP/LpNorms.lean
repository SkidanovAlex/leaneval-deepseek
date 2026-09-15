import Submission.FUP.HormanderBound
import Submission.FUP.Dbar2Calc
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Identifying the `formPair`/`dbarNormSq`/`adjNormSq` quantities with `L²(μ_φ)` norms

The Kohn--Morrey estimate `norm_formPair_sq_le` is stated in terms of the explicit integrals
`formPair`, `dbarNormSq`, `adjNormSq` of `Submission.FUP.HormanderBound`.  To feed it into the
abstract existence theorem of Demailly (via `Commons.…exists_solution_of_bound`) those integrals
have to be identified with the inner products and norms of the Hilbert spaces
`L²(μ_φ)`, `L²(ℂᵈ, FormSpace d, μ_φ)`, `L²(ℂᵈ, FormSpace2 d, μ_φ)`:

* `‖MemLp.toLp f h‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂μ_φ` (`norm_sq_toLp`);
* `‖liftForm2 Ψ z‖ ^ 2 = ∑ i, ‖Ψ z i‖ ^ 2` (`norm_sq_liftForm2`);
* `dbarNormSq u φ = (1/2) * ‖toLp (liftForm2 (dbarFormFun2 u))‖ ^ 2` (`dbarNormSq_eq`);
* `adjNormSq u φ = ‖toLp (dbarAdjoint φ u)‖ ^ 2` (`adjNormSq_eq`);
* `formPair η u φ = ⟪toLp (liftForm u), toLp (liftForm η)⟫` (`formPair_eq_inner`).
-/

namespace Submission.FUP

variable {d : ℕ}

section NormSq

/-- The `L²(μ_φ)`-norm of the class of a function is the weighted integral of `‖f‖^2`. -/
lemma norm_sq_toLp {φ : FormDu d → ℝ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (f : FormDu d → E)
    (hf : MemLp f 2 (wtMeasure φ)) :
    ‖hf.toLp f‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂(wtMeasure φ) := by
  have hint : Integrable (fun z => inner ℂ ((hf.toLp f) z) ((hf.toLp f) z)) (wtMeasure φ) :=
    MeasureTheory.L2.integrable_inner (hf.toLp f) (hf.toLp f)
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (hf.toLp f), MeasureTheory.L2.inner_def,
    ← integral_re hint]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf] with z hz
  rw [hz, inner_self_eq_norm_sq]

end NormSq

section Pointwise

@[simp] lemma dbarFormFun2_eq {x : FormDu d → (Fin d → ℂ)} (z : FormDu d) (j k : Fin d) :
    dbarFormFun2 x z (j, k) = dbComp x k j z - dbComp x j k z := rfl

/-- The `ℓ²`-norm squared of `liftForm2 Ψ z` is the sum of the squares of its components. -/
lemma norm_sq_liftForm2 {Ψ : FormDu d → (Fin d × Fin d → ℂ)} (z : FormDu d) :
    ‖liftForm2 Ψ z‖ ^ 2 = ∑ i : Fin d × Fin d, ‖Ψ z i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin d × Fin d => ℂ)]
  simp only [liftForm2_apply]

/-- The `ℓ²`-norm squared of `liftForm u z` is the sum of the squares of its components. -/
lemma norm_sq_liftForm {u : FormDu d → (Fin d → ℂ)} (z : FormDu d) :
    ‖liftForm u z‖ ^ 2 = ∑ j : Fin d, ‖u z j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin d => ℂ)]
  simp only [liftForm_apply]

/-- The double sum over `Fin d × Fin d` of the pointwise `∂̄₂` of a `(0,1)`-form. -/
lemma sum_norm_sq_dbarFormFun2 (x : FormDu d → (Fin d → ℂ)) (z : FormDu d) :
    (∑ i : Fin d × Fin d, ‖dbarFormFun2 x z i‖ ^ 2)
      = ∑ j : Fin d, ∑ k : Fin d, ‖dbComp x k j z - dbComp x j k z‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [dbarFormFun2_eq]

end Pointwise

section DbarNorm

/-- `dbarNormSq u φ` is half the squared `L²(μ_φ)`-norm of the pointwise `∂̄₂u`. -/
theorem dbarNormSq_eq {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) {u : FormDu d → (Fin d → ℂ)}
    (hmem : MemLp (liftForm2 (dbarFormFun2 u)) 2 (wtMeasure φ)) :
    dbarNormSq u φ = (1 / 2) * ‖hmem.toLp (liftForm2 (dbarFormFun2 u))‖ ^ 2 := by
  have hφc : Continuous φ := hφ.continuous
  rw [dbarNormSq, norm_sq_toLp _ hmem, integral_wtMeasure hφc,
    ← integral_const_mul (1/2 : ℝ)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [norm_sq_liftForm2, sum_norm_sq_dbarFormFun2, smul_eq_mul]
  ring

end DbarNorm

section AdjNorm

/-- `adjNormSq u φ` is the squared `L²(μ_φ)`-norm of `ϑ_φ u = -dbarAdjoint φ u`. -/
theorem adjNormSq_eq {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) {u : FormDu d → (Fin d → ℂ)}
    (hmem : MemLp (dbarAdjoint φ u) 2 (wtMeasure φ)) :
    adjNormSq u φ = ‖hmem.toLp (dbarAdjoint φ u)‖ ^ 2 := by
  have hφc : Continuous φ := hφ.continuous
  rw [adjNormSq, norm_sq_toLp _ hmem, integral_wtMeasure hφc]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  have h1 : dbarAdjoint φ u z = -∑ j : Fin d, covComp u φ j z := rfl
  rw [h1, norm_neg, smul_eq_mul]
  ring

end AdjNorm

section FormPair

/-- The pointwise `L²` pairing of two `(0,1)`-forms is `formDot`. -/
lemma inner_liftForm_eq_formDot (u η : FormDu d → (Fin d → ℂ)) (z : FormDu d) :
    inner ℂ (liftForm u z) (liftForm η z) = formDot η u z := by
  rw [PiLp.inner_apply, formDot]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.inner_apply]
  simp only [liftForm_apply, starRingEnd_apply]

/-- `formPair η u φ` is the `L²(μ_φ)` inner product of the classes of `u` and `η`. -/
theorem formPair_eq_inner {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {η u : FormDu d → (Fin d → ℂ)}
    (hu : MemLp (liftForm u) 2 (wtMeasure φ))
    (hη : MemLp (liftForm η) 2 (wtMeasure φ)) :
    formPair η u φ = inner ℂ (hu.toLp (liftForm u)) (hη.toLp (liftForm η)) := by
  rw [formPair, MeasureTheory.L2.inner_def]
  have hR : (∫ z, inner ℂ ((hu.toLp (liftForm u)) z) ((hη.toLp (liftForm η)) z) ∂(wtMeasure φ))
      = ∫ z, formDot η u z ∂(wtMeasure φ) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hu, MemLp.coeFn_toLp hη] with z hz1 hz2
    rw [hz1, hz2, inner_liftForm_eq_formDot]
  rw [hR, integral_wtMeasure hφ.continuous]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [Complex.real_smul]
  ring

end FormPair

end Submission.FUP
