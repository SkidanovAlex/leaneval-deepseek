import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.Geom
import Submission.Work.SmallBoxSliding.farSet_chiSmallB_zero
import Submission.Work.SmallBoxSliding.integrable_chiSmallB_mass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

open MeasureTheory
open scoped Real ENNReal BigOperators

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma compl_mass_le {M : ℕ} (hM : 1 ≤ M) {ℓ d μ a C₁ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hμ : 0 < μ) (ha : 0 ≤ a) (hC₁ : 0 ≤ C₁)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ))
    (hEst : (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2
        ≤ C₁ * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3) :
    (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
        ∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2)
      ≤ 12 * (1 + d) ^ 2 * (Submission.BoseGases.chiSmallBandDecay M d) * C₁
          * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3 := by
  set F : ℝ³ → ℝ := fun u => ∫ x : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2 with hFdef
  have hFint : Integrable F := by
    rw [hFdef]; exact integrable_chiSmallB_mass hM hℓ hd
  have hF0 : ∀ u, 0 ≤ F u := by
    intro u; rw [hFdef]; exact integral_nonneg_of_ae (ae_of_all _ (fun x => sq_nonneg _))
  have hsub : (goodSet ℓ d μ)ᶜ ⊆ bandSet ℓ d μ ∪ farSet ℓ d μ := goodSet_compl_subset hμ
  have hunion : (∫ u in bandSet ℓ d μ ∪ farSet ℓ d μ, F u)
      = (∫ u in bandSet ℓ d μ, F u) + (∫ u in farSet ℓ d μ, F u) :=
    setIntegral_union (disjoint_bandSet_farSet ℓ d μ) (measurableSet_farSet ℓ d μ)
      hFint.integrableOn hFint.integrableOn
  have hfar : (∫ u in farSet ℓ d μ, F u) = 0 := by
    have hpt : ∀ u ∈ farSet ℓ d μ, F u = 0 := by
      intro u hu
      rw [hFdef]
      have hz : (fun x : ℝ³ => (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2) = fun _ => (0:ℝ) := by
        funext x
        rw [farSet_chiSmallB_zero hℓ hd hu x]
        ring
      simp only [hz]
      exact integral_zero _ _
    rw [setIntegral_congr_fun (measurableSet_farSet ℓ d μ) hpt]
    simp
  calc (∫ u in (goodSet ℓ d μ)ᶜ, F u)
      ≤ (∫ u in bandSet ℓ d μ ∪ farSet ℓ d μ, F u) :=
        setIntegral_mono_set hFint.integrableOn
          (Filter.Eventually.of_forall hF0)
          (Filter.Eventually.of_forall (fun u hu => hsub hu))
    _ = (∫ u in bandSet ℓ d μ, F u) + (∫ u in farSet ℓ d μ, F u) := hunion
    _ = (∫ u in bandSet ℓ d μ, F u) := by rw [hfar]; ring
    _ ≤ 12 * (1 + d) ^ 2 * (Submission.BoseGases.chiSmallBandDecay M d) * C₁
          * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3 := by
        rw [hFdef, bandSet_eq_chiSmallBadBand]
        exact Submission.BoseGases.chiSmallB_badband_integral_law hM hℓ hd hμ ha hAδ hC₁ hEst

end Work.SmallBoxSliding
