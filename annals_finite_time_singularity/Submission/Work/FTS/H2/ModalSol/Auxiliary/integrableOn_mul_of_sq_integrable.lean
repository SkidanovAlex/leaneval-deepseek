/-
# Buildable copy of `Work.FTS.H2.ModalSol.Aux.integrableOn_mul_of_sq_integrable`

The assigned file lives at `Submission/Work/FTS/H2/ModalSol/Aux/integrableOn_mul_of_sq_integrable.lean`,
whose module name `Submission.Work.FTS.H2.ModalSol.Aux.integrableOn_mul_of_sq_integrable` contains
the component `Aux`, a file name reserved on some operating systems (`CON`, `PRN`, **`AUX`**, `NUL`,
…).  Lean 4.34 rejects such module names in `Lean.Elab.checkModuleNamePortability`, *before*
elaboration, so that module can never be built from sources and nothing can `import` it.

This file is the rehomed copy: it lives under `ModalSol/Auxiliary/`, so its module name is portable
and it can be built and imported, while declaring **the same** lemma name
`Work.FTS.H2.ModalSol.Aux.integrableOn_mul_of_sq_integrable` (the namespace is unchanged).  Import
this module, not the `Aux/` one.  The mathematical content is identical to the assigned file.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSol.Aux

open MeasureTheory Set Filter
open scoped ENNReal

/-- **Auxiliary integrability fact for the modal-solution construction.**

If `c : ℝ → ℝ` is a.e. strongly measurable on `(0,∞)` and `c ^ 2` is integrable there, and
`g : ℝ × ℝ → ℝ` is continuous on the compact rectangle `[a,b] × [c₀,d]` with `0 < a ≤ b`,
`0 < c₀ ≤ d`, then `p ↦ c p.1 * g p` is integrable on that rectangle.

Proof: `g` is bounded on the compact rectangle by some `M` (`IsCompact.exists_bound_of_continuousOn`),
`c` is integrable on `[a,b]` because `c ^ 2` is (Cauchy–Schwarz / `L² ⊂ L¹` on a finite measure
space), `volume` on `ℝ × ℝ` is the product measure and restricting to a rectangle is the product of
the restrictions (`Measure.volume_eq_prod`, `Measure.prod_restrict`), and the dominating function
`fun p => M * ‖c p.1‖` is integrable there by `Integrable.comp_fst`. -/
theorem integrableOn_mul_of_sq_integrable {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun z => c z ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    {a b c₀ d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c₀) (hcd : c₀ ≤ d)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g (Set.Icc a b ×ˢ Set.Icc c₀ d)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => c p.1 * g p)
      (Set.Icc a b ×ˢ Set.Icc c₀ d) := by
  -- `[a,b] ⊆ (0,∞)`, so all the `Ioi 0`-hypotheses may be restricted to `[a,b]`.
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  -- `volume` on `ℝ × ℝ` is a product measure and restricting to a rectangle is the product of
  -- the restrictions.
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Set.Icc a b ×ˢ Set.Icc c₀ d)
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c₀ d)) :=
    (Measure.prod_restrict (Set.Icc a b) (Set.Icc c₀ d)).symm
  -- the two restricted measures are finite, both rectangles being compact
  have hFab : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact isCompact_Icc.measure_lt_top⟩
  have hFcd : IsFiniteMeasure (volume.restrict (Set.Icc c₀ d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact isCompact_Icc.measure_lt_top⟩
  -- a.e. strong measurability of `c` on `[a,b]`
  have hcm_ab : AEStronglyMeasurable c (volume.restrict (Set.Icc a b)) := by
    have h1 : AEStronglyMeasurable c ((volume.restrict (Set.Ioi 0)).restrict (Set.Icc a b)) :=
      hcm.restrict
    rwa [Measure.restrict_restrict_of_subset hsub] at h1
  -- `c` is integrable on `[a,b]`: `c ∈ L²` there and the measure is finite
  have hc2_ab : Integrable (fun z => c z ^ 2) (volume.restrict (Set.Icc a b)) := hc.mono_set hsub
  have hc_ab : Integrable c (volume.restrict (Set.Icc a b)) := by
    have h2 : MemLp c 2 (volume.restrict (Set.Icc a b)) :=
      (memLp_two_iff_integrable_sq hcm_ab).2 hc2_ab
    exact memLp_one_iff_integrable.1 (h2.mono_exponent (by norm_num))
  -- `g` is bounded on the compact rectangle
  have hScomp : IsCompact (Set.Icc a b ×ˢ Set.Icc c₀ d) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hScomp.exists_bound_of_continuousOn hg
  -- the dominating function `p ↦ M * ‖c p.1‖`
  have hdom_int : Integrable (fun x : ℝ => M * ‖c x‖) (volume.restrict (Set.Icc a b)) :=
    hc_ab.norm.const_mul M
  have hdom : Integrable (fun p : ℝ × ℝ => M * ‖c p.1‖)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c₀ d))) :=
    hdom_int.comp_fst _
  -- a.e. strong measurability of `g` and of the product
  have hg_aesm : AEStronglyMeasurable g
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c₀ d))) := by
    rw [Measure.prod_restrict (Set.Icc a b) (Set.Icc c₀ d)]
    exact hg.aestronglyMeasurable_of_isCompact (μ := volume) hScomp
      (measurableSet_Icc.prod measurableSet_Icc)
  have hc_fst : AEStronglyMeasurable (fun p : ℝ × ℝ => c p.1)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c₀ d))) :=
    hcm_ab.comp_fst
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => c p.1 * g p)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c₀ d))) :=
    hc_fst.mul hg_aesm
  -- the a.e. domination `‖c p.1 * g p‖ ≤ M * ‖c p.1‖`
  have hae : ∀ᵐ p ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c₀ d))),
      ‖c p.1 * g p‖ ≤ M * ‖c p.1‖ := by
    have haeS : ∀ᵐ p ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c₀ d))),
        p ∈ Set.Icc a b ×ˢ Set.Icc c₀ d := by
      rw [Measure.prod_restrict (Set.Icc a b) (Set.Icc c₀ d)]
      exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
    filter_upwards [haeS] with p hp
    have hgp : ‖g p‖ ≤ M := hM p hp
    calc ‖c p.1 * g p‖ = ‖c p.1‖ * ‖g p‖ := norm_mul _ _
      _ ≤ ‖c p.1‖ * M := by gcongr
      _ = M * ‖c p.1‖ := by ring
  rw [IntegrableOn, hprod]
  exact Integrable.mono' hdom hmeas hae

end Work.FTS.H2.ModalSol.Aux
