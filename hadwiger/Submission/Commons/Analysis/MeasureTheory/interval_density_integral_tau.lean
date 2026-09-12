import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Measure ENNReal
open scoped ENNReal NNReal Topology

namespace Commons.Analysis.MeasureTheory

noncomputable section

/-- The radial density `t ↦ (1 - t²)^e` is nonnegative on the open interval
`(-1,1)` (there the base `1 - t²` is strictly positive). -/
lemma rpow_one_sub_sq_nonneg_Ioo {e : ℝ} :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ (1 - x ^ 2) ^ e := by
  intro x hx
  have hb : 0 < 1 - x ^ 2 := by
    have hx1 : -1 < x := hx.1
    have hx2 : x < 1 := hx.2
    nlinarith [sq_nonneg x]
  exact le_of_lt (Real.rpow_pos_of_pos hb e)

/-- The density `t ↦ ENNReal.ofReal ((1 - t²)^e)` is almost everywhere measurable
with respect to Lebesgue measure restricted to `(-1,1)` (it is continuous there). -/
lemma rpow_density_aemeasurable_Ioo {e : ℝ} :
    AEMeasurable (fun t : ℝ => ENNReal.ofReal ((1 - t ^ 2) ^ e))
      (volume.restrict (Set.Ioo (-1 : ℝ) 1)) := by
  let s : Set ℝ := Set.Ioo (-1) 1
  have hs : MeasurableSet s := measurableSet_Ioo
  refine aemeasurable_restrict_of_measurable_subtype hs
    (f := fun t : ℝ => ENNReal.ofReal ((1 - t ^ 2) ^ e)) ?_
  apply ENNReal.measurable_ofReal.comp
  let s' : Set ℝ := Set.Ioo (-1) 1
  have hcont : Continuous (fun x : s' => (1 - (x : ℝ) ^ 2) ^ e) := by
    have hcontOn : ContinuousOn (fun t : ℝ => (1 - t ^ 2) ^ e) s' := by
      refine ContinuousOn.rpow_const (f := fun t : ℝ => 1 - t ^ 2) ?_ (s := s') ?_
      · fun_prop
      · intro t ht
        have hb : 0 < 1 - t ^ 2 := by
          have ht1 : -1 < t := ht.1
          have ht2 : t < 1 := ht.2
          nlinarith [sq_nonneg t]
        exact Or.inl (ne_of_gt hb)
    rw [continuousOn_iff_continuous_domRestrict] at hcontOn
    exact hcontOn
  exact hcont.measurable

/-- Integrating over the subtype `{t : ℝ // -1 < t ∧ t < 1}` against the pullback
of the density measure `(volume.restrict (-1,1)).withDensity (ENNReal.ofReal ∘ rho)`
along `Subtype.val` equals the Lebesgue integral over `(-1,1)` of the function
times the density.  The integrand `F` is completely arbitrary. -/
lemma interval_density_integral_tau_subtype {e : ℝ} (F : ℝ → ℝ) :
    let It := {t : ℝ // t ∈ Set.Ioo (-1) 1}
    let tau : Measure ℝ :=
      (volume.restrict (Set.Ioo (-1) 1)).withDensity
        (fun t => ENNReal.ofReal ((1 - t ^ 2) ^ e))
    (∫ t : It, F t.1 ∂(tau.comap (Subtype.val : It → ℝ))) =
    (∫ t : ℝ in Set.Ioo (-1) 1, F t * (1 - t ^ 2) ^ e) := by
  change (∫ t : {t : ℝ // t ∈ Set.Ioo (-1) 1}, F t.1 ∂
      (((volume.restrict (Set.Ioo (-1) 1)).withDensity
          (fun t : ℝ => ENNReal.ofReal ((1 - t ^ 2) ^ e))).comap
          (Subtype.val : {t : ℝ // t ∈ Set.Ioo (-1) 1} → ℝ))) =
         (∫ t : ℝ in Set.Ioo (-1) 1, F t * (1 - t ^ 2) ^ e)
  let s : Set ℝ := Set.Ioo (-1) 1
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((1 - t ^ 2) ^ e)
  have hs : MeasurableSet s := measurableSet_Ioo
  have hτ : (((volume.restrict s).withDensity f).restrict s) =
      (volume.restrict s).withDensity f := by
    rw [MeasureTheory.restrict_withDensity hs]
    congr 1
    rw [Measure.restrict_restrict hs, Set.inter_self]
  have hf_meas : AEMeasurable f (volume.restrict s) := by
    simpa [s, f] using (rpow_density_aemeasurable_Ioo (e := e))
  have hf_top : ∀ᵐ x ∂(volume.restrict s), f x < ⊤ := by
    exact Filter.Eventually.of_forall (fun x => by simp [f])
  have hdensity :
      (∫ x : ℝ, F x ∂((volume.restrict s).withDensity f)) =
        (∫ x : ℝ, (f x).toReal • F x ∂(volume.restrict s)) :=
    integral_withDensity_eq_integral_toReal_smul₀ hf_meas hf_top (g := F)
  have hae : (fun x : ℝ => (f x).toReal • F x) =ᵐ[volume.restrict s]
      (fun x : ℝ => F x * (1 - x ^ 2) ^ e) := by
    refine (MeasureTheory.ae_restrict_mem hs).mono ?_
    intro x hx
    have hr : 0 ≤ (1 - x ^ 2) ^ e := rpow_one_sub_sq_nonneg_Ioo x hx
    have hxeq : (f x).toReal = (1 - x ^ 2) ^ e := by
      dsimp [f]
      exact ENNReal.toReal_ofReal hr
    calc
      (f x).toReal • F x = (f x).toReal * F x := by rw [smul_eq_mul]
      _ = ((1 - x ^ 2) ^ e) * F x := by rw [hxeq]
      _ = F x * (1 - x ^ 2) ^ e := by ring
  calc
    (∫ t : {t : ℝ // t ∈ Set.Ioo (-1) 1}, F t.1 ∂
        (((volume.restrict (Set.Ioo (-1) 1)).withDensity
            (fun t : ℝ => ENNReal.ofReal ((1 - t ^ 2) ^ e))).comap
            (Subtype.val : {t : ℝ // t ∈ Set.Ioo (-1) 1} → ℝ)))
        = ∫ x in s, F x ∂((volume.restrict s).withDensity f) := by
            simpa [s, f] using (MeasureTheory.integral_subtype_comap hs F)
    _ = ∫ x : ℝ, F x ∂((volume.restrict s).withDensity f) := by
            rw [hτ]
    _ = ∫ x : ℝ, (f x).toReal • F x ∂(volume.restrict s) := hdensity
    _ = ∫ x : ℝ, F x * (1 - x ^ 2) ^ e ∂(volume.restrict s) := integral_congr_ae hae
    _ = ∫ x in s, F x * (1 - x ^ 2) ^ e ∂volume := rfl

/-- The radial density integral identity needed in the zonal-coordinate treatment
of Hadwiger's theorem: integrating `F` over the subtype `(-1,1)` against the
pullback (via `Subtype.val`) of the measure
`volume.restrict (-1,1)` with density `t ↦ (1-t²)^((finrank ℝ W - 2)/2)`
equals the Lebesgue integral over `(-1,1)` of `F t * (1-t²)^((finrank ℝ W - 2)/2)`. -/
lemma interval_density_integral_tau
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] (F : ℝ → ℝ) :
    let expo : ℝ := (((Module.finrank ℝ W : ℝ) - 2) / 2)
    let rho : ℝ → ℝ := fun t => (1 - t ^ 2) ^ expo
    let It := {t : ℝ // t ∈ Set.Ioo (-1) 1}
    let tau : MeasureTheory.Measure ℝ :=
      (MeasureTheory.volume.restrict (Set.Ioo (-1) 1)).withDensity
        (fun t => ENNReal.ofReal (rho t))
    (∫ t : It, F t.1 ∂(tau.comap (Subtype.val : It → ℝ))) =
    (∫ t : ℝ in Set.Ioo (-1) 1, F t * rho t) := by
  exact interval_density_integral_tau_subtype
    (e := (((Module.finrank ℝ W : ℝ) - 2) / 2)) F

end

end Commons.Analysis.MeasureTheory