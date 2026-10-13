/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of a weighted mixed derivative on the product measure

This is the bookkeeping lemma which identifies the `L²`-norm of a weighted mixed
derivative `D_z^j D_θ^i g · W` (for `1 ≤ i`, `i + j ≤ 4`) with its value as an integral
against the product measure `(volume|Iz).prod (volume|Iθ)`.

The proof has three ingredients:

* `aesm_mixed_Wt_sq_prod` (proved in `Submission/Work/Spaces/aesm_mixed_Wt_sq_prod.lean`):
  the integrand is a.e. strongly measurable on the product, because it is *continuous*
  on the open quadrant `(0,∞) × (0,π/2)`, whose complement inside `Iz × Iθ` is null;
* pointwise domination by the `H⁴`-integrand of `g`: the mixed term
  `(D_z^j D_θ^i g · W)²` is one of the summands of `HkIntegrand α 4 g`, so that both the
  angular slices and the iterated integral are dominated by the `HkMem α 4 g` data;
* `integrable_prod_of_iterated` (proved in
  `Submission/Work/Spaces/integrable_prod_of_iterated.lean`): Fubini–Tonelli for a
  nonnegative jointly measurable function whose slices and iterated integral are
  integrable, which turns the iterated integral into the Bochner integral on the
  product measure.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Angular slices are integrable, by domination by `HkIntegrand α 4 g` -/

private theorem slice_integrable_aux (α : ℝ) (g : ℝ → ℝ → ℝ) (hmem : HkMem α 4 g)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (mixed j i g p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ))) :
    ∀ᵐ z ∂(volume.restrict Iz),
      Integrable (fun θ => (mixed j i g z θ * Wt α z θ) ^ 2) (volume.restrict Iθ) := by
  -- The slice is a.e. strongly measurable because the joint function is, and for
  -- `z ∈ Iz` it is dominated by the (integrable) slice of the `H⁴`-integrand.
  filter_upwards [hAE.prodMk_left, ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)]
    with z hz_meas hz
  refine Integrable.mono' (hmem.1 z hz) hz_meas ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij

/-! ## The iterated integral is integrable, by domination by `hmem.2` -/

private theorem outer_integrable_aux (α : ℝ) (g : ℝ → ℝ → ℝ) (hmem : HkMem α 4 g)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (mixed j i g p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ))) :
    Integrable (fun z => ∫ θ, (mixed j i g z θ * Wt α z θ) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz) := by
  -- `z ↦ ∫_θ (…)²` is a.e. strongly measurable (partial integral of the joint function)
  -- and pointwise bounded by the integrable function `z ↦ ∫_θ HkIntegrand α 4 g`.
  refine Integrable.mono' hmem.2 hAE.integral_prod_right' ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
  exact integral_mono_of_nonneg
    (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
      (fun θ _ => sq_nonneg _))
    (hmem.1 z hz)
    (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
      (fun θ _ => sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij))

/-! ## Assembly -/

theorem bt_prod_integrable (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α 4 g)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.integral
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ (mixed j i g z θ * Wt α z θ) ^ 2 := fun z θ => sq_nonneg _
  have hAE := aesm_mixed_Wt_sq_prod α g hsm j i
  have hslice := slice_integrable_aux α g hmem j i hi hij hAE
  have houter := outer_integrable_aux α g hmem j i hi hij hAE
  obtain ⟨hint, hval⟩ := integrable_prod_of_iterated hnn hAE hslice houter
  refine ⟨hint, ?_⟩
  rw [hval]
  simp only [L2Sq]

end Work.Spaces
