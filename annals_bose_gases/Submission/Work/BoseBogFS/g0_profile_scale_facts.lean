import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.BoseFixR.LatGreen.W1funDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open MeasureTheory
open scoped Real Topology Pointwise

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The dilation `t ↦ R * t` (`R > 0`) pushes the Lebesgue measure restricted to `(0, ∞)`
forward to `R⁻¹` times itself. -/
private lemma map_mul_restrict_Ioi {R : ℝ} (hR : 0 < R) :
    Measure.map (fun t : ℝ => R * t) (volume.restrict (Set.Ioi (0 : ℝ)))
      = ENNReal.ofReal R⁻¹ • (volume.restrict (Set.Ioi (0 : ℝ))) := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul R) hs, Measure.smul_apply,
    Measure.restrict_apply (hs.preimage (measurable_const_mul R)), Measure.restrict_apply hs]
  have hset : (fun t : ℝ => R * t) ⁻¹' s ∩ Set.Ioi (0 : ℝ) = R⁻¹ • (s ∩ Set.Ioi (0 : ℝ)) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_smul_set]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨R * t, ⟨h1, mul_pos hR h2⟩, by
        rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hR), one_mul]⟩
    · rintro ⟨u, ⟨hu1, hu2⟩, ht⟩
      refine ⟨?_, ?_⟩
      · rw [← ht, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hR), one_mul]
        exact hu1
      · rw [← ht, smul_eq_mul]
        exact mul_pos (inv_pos.mpr hR) hu2
  rw [hset, Measure.addHaar_smul (volume : Measure ℝ) R⁻¹ (s ∩ Set.Ioi (0 : ℝ)),
    Module.finrank_self, pow_one, abs_of_pos (inv_pos.mpr hR)]
  rfl

/-- The dilation `t ↦ R * t` (`R > 0`) is quasi-measure-preserving for the Lebesgue
measure restricted to `(0, ∞)`. -/
private lemma quasiMeasurePreserving_mul_Ioi {R : ℝ} (hR : 0 < R) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => R * t)
      (volume.restrict (Set.Ioi (0 : ℝ))) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine ⟨measurable_const_mul R, ?_⟩
  rw [map_mul_restrict_Ioi hR]
  exact Measure.smul_absolutelyContinuous

/-- The rescaled profile facts for `g₀ = v(1-ω)`: the function `t ↦ g₀ v h ((R t) • axis0)`
vanishes for `t ≥ 1`, is a.e. strongly measurable on `(0,∞)`, and its first weighted moment is
`≤ 2/R²` (the scale-invariant moment `∫ r |g₀(r•e₀)| dr ≤ 2` of `G0WeightedMoment`, divided by
`R²` by the substitution `r = R t`). -/
theorem g0_profile_scale_facts {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    (∀ t : ℝ, 1 ≤ t →
        Submission.BoseGases.g0 v h ((R * t) • Work.BoseFixR.LatGreen.axis0) = 0) ∧
    MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => Submission.BoseGases.g0 v h ((R * t) • Work.BoseFixR.LatGreen.axis0))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
    MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        t * |Submission.BoseGases.g0 v h ((R * t) • Work.BoseFixR.LatGreen.axis0)|)
      (Set.Ioi (0 : ℝ)) ∧
    (∫ t in Set.Ioi (0 : ℝ),
        t * |Submission.BoseGases.g0 v h ((R * t) • Work.BoseFixR.LatGreen.axis0)|)
      ≤ 2 / R ^ 2 := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  -- the Lebesgue measure restricted to `(0,∞)`
  set ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ)) with hνdef
  -- the axis profile of `g₀ = v(1−ω)`
  set ψ : ℝ → ℝ := fun r => Submission.BoseGases.g0 v h (r • Work.BoseFixR.LatGreen.axis0)
    with hψdef
  -- ═══ (1) vanishing beyond the range ═══
  have hvan : ∀ t : ℝ, 1 ≤ t → ψ (R * t) = 0 := by
    intro t ht
    have hlt : R ≤ R * t := by nlinarith
    have hpos : 0 ≤ R * t := by nlinarith
    rw [hψdef]
    refine Submission.BoseGases.g0_zero_of_norm_ge hv_supp ?_ h
    rw [Work.BoseFixR.LatGreen.norm_smul_axis0, abs_of_nonneg hpos]
    exact hlt
  -- ═══ (2) a.e. strong measurability ═══
  have hψm : AEStronglyMeasurable ψ ν := by
    have hbase := Work.BoseFixR.LatGreen.aestronglyMeasurable_g0profile (v := v) (R := R)
      h hvrad hR hv_supp
    rw [hνdef]
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [hψdef]
    exact (Work.BoseFixR.LatGreen.g0_smul_single_eq_profile hvrad h hr).symm
  have hsm : AEStronglyMeasurable (fun t : ℝ => ψ (R * t)) ν :=
    hψm.comp_quasiMeasurePreserving (quasiMeasurePreserving_mul_Ioi hR)
  -- ═══ (3) the weighted moment of the profile (scale-invariant, `G0WeightedMoment`) ═══
  obtain ⟨hintφ, hleφ⟩ :=
    Work.BoseFixR.LatGreen.G0WeightedMoment (v := v) (R := R) h hv hvrad hR hv_supp
  have hintψ : IntegrableOn (fun u : ℝ => u * |ψ u|) (Set.Ioi (0 : ℝ)) := hintφ
  have hleψ : ∫ u in Set.Ioi (0 : ℝ), u * |ψ u| ≤ 2 := hleφ
  -- ═══ (4) the substitution `u = R t` ═══
  -- the profile function in the `u`-variable, with the `1/R` produced by the substitution
  set G : ℝ → ℝ := fun u => (u / R) * |ψ u| with hGdef
  have hGeq : G = fun u : ℝ => R⁻¹ * (u * |ψ u|) := by
    funext u
    simp only [hGdef]
    rw [div_eq_mul_inv]
    ring
  have hIntG : Integrable G ν := by
    rw [hGeq]
    exact hintψ.const_mul R⁻¹
  have hdil_ae : AEMeasurable (fun t : ℝ => R * t) ν := (measurable_const_mul R).aemeasurable
  have hmap : Measure.map (fun t : ℝ => R * t) ν = ENNReal.ofReal R⁻¹ • ν := by
    rw [hνdef]
    exact map_mul_restrict_Ioi hR
  have hIntGmap : Integrable G (Measure.map (fun t : ℝ => R * t) ν) := by
    rw [hmap]
    exact (integrable_smul_measure (f := G) (c := ENNReal.ofReal R⁻¹)
      (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hR))) ENNReal.ofReal_ne_top).2 hIntG
  have hIntF : Integrable (fun t : ℝ => t * |ψ (R * t)|) ν := by
    have hcomp : Integrable (G ∘ fun t : ℝ => R * t) ν :=
      (integrable_map_measure (f := fun t : ℝ => R * t) (g := G) (μ := ν)
        hIntGmap.aestronglyMeasurable hdil_ae).1 hIntGmap
    have heq : (G ∘ fun t : ℝ => R * t) = fun t : ℝ => t * |ψ (R * t)| := by
      funext t
      simp only [Function.comp_apply, hGdef]
      rw [mul_div_cancel_left₀ t hRne]
    rw [heq] at hcomp
    exact hcomp
  have hGint : ∫ u, G u ∂ν = R⁻¹ * ∫ u, u * |ψ u| ∂ν := by
    rw [hGeq, integral_const_mul]
  have hvalue : ∫ t in Set.Ioi (0 : ℝ), t * |ψ (R * t)|
      = R⁻¹ * (R⁻¹ * ∫ u in Set.Ioi (0 : ℝ), u * |ψ u|) := by
    have h₁ : ∫ t in Set.Ioi (0 : ℝ), t * |ψ (R * t)| = ∫ t, G (R * t) ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hGdef]
      rw [mul_div_cancel_left₀ t hRne]
    rw [h₁, (integral_map (μ := ν) (φ := fun t : ℝ => R * t) hdil_ae
      (f := G) hIntGmap.aestronglyMeasurable).symm, hmap, integral_smul_measure,
      ENNReal.toReal_ofReal hRinv, hGint, smul_eq_mul]
  -- ═══ assembly ═══
  refine ⟨hvan, hsm, hIntF, ?_⟩
  rw [hvalue]
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hleψ hRinv) hRinv) ?_
  have h2 : R⁻¹ * (R⁻¹ * 2) = 2 / R ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  rw [h2]

end Work.BoseBogFS
