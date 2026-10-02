import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.QC.CompHolo.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC.CompHolo

open MeasureTheory Complex Function Filter
open scoped ENNReal Topology

/-! ## A holomorphic injection with nonvanishing derivative pulls null sets back to null sets

`f : ℂ → ℂ` holomorphic, injective, with `deriv f z ≠ 0` for all `z`, is a local biholomorphism;
in particular it is a local diffeomorphism, so it preserves null sets.  Rather than building the
inverse function theorem, we use Mathlib's change-of-variables formula
`MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image` on the measurable set
`s = f ⁻¹' M`, where `M ⊇ N` is a measurable null set: it gives
`∫⁻ z in s, |det (D f z)| = volume (f '' s)` and `f '' s = M ∩ range f ⊆ M` is null, so the
integrand `|det (D f z)| = ‖f' z‖² > 0` must vanish a.e. on `s`, forcing `volume s = 0`. -/

theorem null_preimage {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hinj : Function.Injective f)
    (hf' : ∀ z, deriv f z ≠ 0) {N : Set ℂ} (hN : MeasureTheory.volume N = 0) :
    MeasureTheory.volume (f ⁻¹' N) = 0 := by
  -- enlarge the null set `N` to a measurable null set `M`
  obtain ⟨M, hNM, hMmeas, hM0⟩ := MeasureTheory.exists_measurable_superset_of_null hN
  set s : Set ℂ := f ⁻¹' M with hsdef
  have hsmeas : MeasurableSet s := hMmeas.preimage hf.continuous.measurable
  -- `f` is differentiable on `s` with derivative `fderiv ℝ f`
  have hderiv : ∀ z ∈ s, HasFDerivWithinAt f (fderiv ℝ f z) s z := by
    intro z _
    have h : HasFDerivAt f (fderiv ℝ f z) z := by
      rw [fderiv_real_eq_smul_one (hf z)]
      exact (hf z).hasDerivAt.complexToReal_fderiv
    exact h.hasFDerivWithinAt
  -- change of variables
  have hcov := MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image (μ := MeasureTheory.volume)
    (f := f) (f' := fun z => fderiv ℝ f z) hsmeas hderiv (hinj.injOn)
  -- the image of `s` is contained in the null set `M`
  have himg : f '' s = M ∩ Set.range f := by
    rw [hsdef, Set.image_preimage_eq_inter_range]
  have hvol : MeasureTheory.volume (f '' s) = 0 :=
    himg ▸ MeasureTheory.measure_mono_null Set.inter_subset_left hM0
  have hzero : ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ f z).det| = 0 := by
    rw [hcov, hvol]
  -- the integrand is almost everywhere measurable and strictly positive on `s`
  have hae := MeasureTheory.aemeasurable_ofReal_abs_det_fderivWithin (μ := MeasureTheory.volume)
    (f := f) (f' := fun z => fderiv ℝ f z) hsmeas hderiv
  rw [MeasureTheory.setLIntegral_eq_zero_iff' hsmeas hae] at hzero
  have hne : ∀ z : ℂ, ENNReal.ofReal |(fderiv ℝ f z).det| ≠ 0 := by
    intro z
    have hpos : 0 < |(fderiv ℝ f z).det| := by
      rw [abs_det_fderiv_eq (hf z)]
      exact pow_pos (norm_pos_iff.mpr (hf' z)) 2
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  -- so `s` itself is a null set
  have hbot : MeasureTheory.ae (MeasureTheory.volume.restrict s) = ⊥ := by
    rw [← Filter.eventually_false_iff_eq_bot]
    filter_upwards [(MeasureTheory.ae_restrict_iff' hsmeas).mpr hzero,
      Filter.Eventually.of_forall hne] with x h1 h2
    exact h2 h1
  have hs0 : MeasureTheory.volume s = 0 :=
    MeasureTheory.Measure.restrict_eq_zero.mp (MeasureTheory.ae_eq_bot.mp hbot)
  exact MeasureTheory.measure_mono_null (Set.preimage_mono hNM) hs0

end Work.MRMT.QC.CompHolo
