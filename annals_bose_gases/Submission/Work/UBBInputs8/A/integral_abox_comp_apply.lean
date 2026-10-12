import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.UBBInputs8.A

/-- Integration over the `N`-particle centred box of a function of the single coordinate `i`
factorises as the `(N-1)`-fold product of the one-particle box volume `L³` times the
one-particle integral over `acube L`.

This is the centred-box (`abox`/`acube`) version of the product-fibre computation: by
`restrict_abox_eq_pi` the restricted measure on `abox N L` is the product of `N` copies of
`(volume ↾ acube L)`; pushing forward along `Function.eval i` (`Measure.pi_map_eval`) replaces it
by the constant multiple `(∏_{j ≠ i} μ j univ) • μ i`, and `integral_smul_measure` produces the
scalar `(L³)^{N-1}`. -/
theorem integral_abox_comp_apply {N : ℕ} {L : ℝ} (hL : 0 ≤ L) (i : Fin N)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Submission.BoseGases.acube L)) :
    ∫ x in Submission.BoseGases.abox N L, f (x i)
      = (L ^ 3) ^ (N - 1) * ∫ y in Submission.BoseGases.acube L, f y := by
  let μ : Fin N → Measure (EuclideanSpace ℝ (Fin 3)) :=
    fun _ => (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube L)
  have hrestrict : (volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N L) = Measure.pi μ :=
    Submission.BoseGases.restrict_abox_eq_pi N L
  have hmap : (Measure.pi μ).map (Function.eval i) =
      (∏ j ∈ Finset.univ.erase i, μ j Set.univ) • μ i :=
    Measure.pi_map_eval μ i
  have hf' : AEStronglyMeasurable f ((Measure.pi μ).map (Function.eval i)) := by
    rw [hmap]
    exact (hf.aestronglyMeasurable.aemeasurable.smul_measure _).aestronglyMeasurable
  have step1 : ∫ x, f (x i) ∂Measure.pi μ
      = ∫ y, f y ∂((Measure.pi μ).map (Function.eval i)) :=
    (MeasureTheory.integral_map (φ := Function.eval i)
      (measurable_pi_apply i).aemeasurable hf').symm
  have hcard : (Finset.univ.erase i : Finset (Fin N)).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hμ : ∀ j : Fin N, μ j Set.univ = ENNReal.ofReal (L ^ 3) := fun j => by
    simp only [μ]
    rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume L hL]
  have hprod : (∏ j ∈ Finset.univ.erase i, μ j Set.univ) = ENNReal.ofReal ((L ^ 3) ^ (N - 1)) := by
    rw [Finset.prod_congr rfl (fun j _ => hμ j), Finset.prod_const, hcard]
    exact (ENNReal.ofReal_pow (pow_nonneg hL 3) (N - 1)).symm
  have htoReal : (ENNReal.ofReal ((L ^ 3) ^ (N - 1))).toReal = (L ^ 3) ^ (N - 1) :=
    ENNReal.toReal_ofReal (pow_nonneg (pow_nonneg hL 3) (N - 1))
  calc
    ∫ x in Submission.BoseGases.abox N L, f (x i)
        = ∫ x, f (x i)
            ∂(volume : Measure (Submission.BoseGases.X N)).restrict
              (Submission.BoseGases.abox N L) := rfl
    _ = ∫ x, f (x i) ∂Measure.pi μ := by rw [hrestrict]
    _ = ∫ y, f y ∂((Measure.pi μ).map (Function.eval i)) := step1
    _ = ∫ y, f y ∂((∏ j ∈ Finset.univ.erase i, μ j Set.univ) • μ i) := by rw [hmap]
    _ = (∏ j ∈ Finset.univ.erase i, μ j Set.univ).toReal * ∫ y, f y ∂μ i := by
        rw [MeasureTheory.integral_smul_measure, smul_eq_mul]
    _ = (L ^ 3) ^ (N - 1) * ∫ y, f y ∂μ i := by rw [hprod, htoReal]
    _ = (L ^ 3) ^ (N - 1) * ∫ y in Submission.BoseGases.acube L, f y := rfl

end Work.UBBInputs8.A
