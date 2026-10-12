import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsFS.coulomb_pair_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.coulomb_iterated_lintegral_ne_top`

The finiteness of the position-space iterated Coulomb `∫⁻` for an even, nonnegative, `L¹` kernel
`V` whose momentum-space Coulomb energy `∫ |V̂(q)|²/(2‖q‖²)` is finite.

The pair kernel `(x,y) ↦ V x · V y / ‖x − y‖` is `L¹` on the product measure by
`Work.BoseRowsFS.coulomb_pair_integrable` (the forward direction of the classical
Newtonian-energy identity, itself derived from
`Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq`).  Reading that integrability through
`hasFiniteIntegral_iff_ofReal` and Tonelli (`lintegral_prod`) gives exactly the finiteness of the
iterated `∫⁻`, hence `≠ ⊤`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixR.LatGreen

/-- **Finiteness of the position-space iterated Coulomb `∫⁻`.**

For an even, pointwise nonnegative, integrable kernel `V` on `ℝ³` whose Fourier transform
(`Work.BoseFixR.chat`, the `p`-convention `V̂(k) = ∫ e^{-i⟨k,y⟩}V(y) dy`) has finite Coulomb energy
in momentum space, the iterated `∫⁻ x, ∫⁻ y, ofReal (V x · V y / ‖x − y‖)` is finite.

This is the `Ineq`-side half of the Fourier–Coulomb identity: the momentum-space finiteness
hypothesis `hint` makes the pair kernel `(x,y) ↦ V x · V y/‖x − y‖` integrable on
`volume × volume` (`Work.BoseRowsFS.coulomb_pair_integrable`), and Tonelli converts that into the
finiteness of the iterated `∫⁻`. -/
theorem coulomb_iterated_lintegral_ne_top {V : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hV1 : MeasureTheory.Integrable V)
    (hVnn : ∀ x, 0 ≤ V x) (hVev : ∀ x, V (-x) = V x)
    (hint : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.chat V q) ^ 2 / (2 * ‖q‖ ^ 2))) :
    (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (V x * V y / ‖x - y‖)) ≠ ⊤ := by
  -- ## 1. the pair kernel is `L¹` on the product measure
  have hI : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        V z.1 * V z.2 / ‖z.1 - z.2‖) (MeasureTheory.volume.prod MeasureTheory.volume) :=
    Work.BoseRowsFS.coulomb_pair_integrable hV1
      (Filter.Eventually.of_forall hVnn) hVev hint
  -- ## 2. integrability = finiteness of the product-measure `∫⁻`
  have hnnz : ∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
      0 ≤ V z.1 * V z.2 / ‖z.1 - z.2‖ := fun z =>
    div_nonneg (mul_nonneg (hVnn z.1) (hVnn z.2)) (norm_nonneg _)
  have hprod_lt : (∫⁻ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (V z.1 * V z.2 / ‖z.1 - z.2‖)
        ∂(MeasureTheory.volume.prod MeasureTheory.volume)) < ⊤ :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal (μ := MeasureTheory.volume.prod MeasureTheory.volume)
      (Filter.Eventually.of_forall hnnz)).mp hI.2
  -- ## 3. Tonelli: the product `∫⁻` is the iterated `∫⁻`
  have hVam : AEMeasurable V MeasureTheory.volume := hV1.1.aemeasurable
  have hAEM : AEMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal (V z.1 * V z.2 / ‖z.1 - z.2‖))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (((hVam.comp_fst).mul (hVam.comp_snd)).div
      (((measurable_fst.sub measurable_snd).norm).aemeasurable)).ennreal_ofReal
  rw [MeasureTheory.lintegral_prod _ hAEM] at hprod_lt
  exact ne_of_lt hprod_lt

end Work.BoseFixR.LatGreen
