/-
# `Work.FTS.EllSol.EllPkgAux.hasDerivAt_intervalIntegral_Kern`

Differentiation under the integral sign for the three-image kernel

  `Kern ρ θ s = ρ (θ - s) - ρ (θ + s) - ρ (θ + s - π)`

of `ThMollDefs`: if `ρ` is differentiable everywhere with derivative `ρ'` bounded by `C`, and
`g` is continuous on `uIcc a b`, then

  `θ ↦ ∫ s in a..b, Kern ρ θ s * g s`

is differentiable with derivative `θ ↦ ∫ s in a..b, Kern ρ' θ s * g s`.

The proof is an application of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the uniform dominating
function `t ↦ 3 C |g t|`:

* the pointwise derivative in `θ` of `s ↦ Kern ρ θ s * g s` is `s ↦ Kern ρ' θ s * g s`
  (`Kern_hasDerivAt`);
* `|Kern ρ' θ s| ≤ 3 C` for every `θ` and `s` (`hC`, triangle inequality);
* `g` is (a.e.) strongly measurable on `uIoc a b` because it is continuous on the larger set
  `uIcc a b`, and `ρ` is continuous (it is differentiable) while `ρ' = deriv ρ` is measurable
  (`measurable_deriv`); the product is measurable.
-/
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

theorem hasDerivAt_intervalIntegral_Kern {ρ ρ' g : ℝ → ℝ} {C a b : ℝ}
    (hd : ∀ t : ℝ, HasDerivAt ρ (ρ' t) t) (hC : ∀ t : ℝ, |ρ' t| ≤ C)
    (hg : ContinuousOn g (Set.uIcc a b)) :
    ∀ θ : ℝ, HasDerivAt (fun θ' : ℝ => ∫ s in a..b, Work.FTS.EllSol.EllPkgAux.Kern ρ θ' s * g s)
      (∫ s in a..b, Work.FTS.EllSol.EllPkgAux.Kern ρ' θ s * g s) θ := by
  intro θ
  -- `ρ` is continuous (it is differentiable everywhere) …
  have hcontρ : Continuous ρ := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  -- … and `ρ' = deriv ρ` is measurable.
  have hρ'eq : ρ' = deriv ρ := funext fun t => ((hd t).deriv).symm
  have hmeasρ' : Measurable ρ' := by rw [hρ'eq]; exact measurable_deriv ρ
  -- continuity of `s ↦ Kern ρ x s`.
  have hcontK : ∀ x : ℝ, Continuous fun s : ℝ => Kern ρ x s := by
    intro x
    have h1 : Continuous fun s : ℝ => ρ (x - s) := hcontρ.comp (continuous_const.sub continuous_id)
    have h2 : Continuous fun s : ℝ => ρ (x + s) := hcontρ.comp (continuous_const.add continuous_id)
    have h3 : Continuous fun s : ℝ => ρ (x + s - Real.pi) :=
      hcontρ.comp ((continuous_const.add continuous_id).sub continuous_const)
    have heq : (fun s : ℝ => Kern ρ x s)
        = fun s => ρ (x - s) - ρ (x + s) - ρ (x + s - Real.pi) := by
      funext s; exact Kern_apply ρ x s
    rw [heq]
    exact (h1.sub h2).sub h3
  -- measurability of `s ↦ Kern ρ' x s`.
  have hmeasK' : ∀ x : ℝ, Measurable fun s : ℝ => Kern ρ' x s := by
    intro x
    have h1 : Measurable fun s : ℝ => ρ' (x - s) :=
      hmeasρ'.comp (measurable_const.sub measurable_id)
    have h2 : Measurable fun s : ℝ => ρ' (x + s) :=
      hmeasρ'.comp (measurable_const.add measurable_id)
    have h3 : Measurable fun s : ℝ => ρ' (x + s - Real.pi) :=
      hmeasρ'.comp ((measurable_const.add measurable_id).sub measurable_const)
    have heq : (fun s : ℝ => Kern ρ' x s)
        = fun s => ρ' (x - s) - ρ' (x + s) - ρ' (x + s - Real.pi) := by
      funext s; exact Kern_apply ρ' x s
    rw [heq]
    exact (h1.sub h2).sub h3
  -- `g` is a.e. strongly measurable on `uIoc a b`, since it is continuous on `uIcc a b`.
  have hg_aem : AEMeasurable g (volume.restrict (Set.uIoc a b)) :=
    AEMeasurable.mono_set Set.uIoc_subset_uIcc (hg.aemeasurable measurableSet_uIcc)
  have hF_meas : ∀ᶠ x in 𝓝 θ, AEStronglyMeasurable (fun s : ℝ => Kern ρ x s * g s)
      (volume.restrict (Set.uIoc a b)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have hmul : ContinuousOn (fun s : ℝ => Kern ρ x s * g s) (Set.uIcc a b) :=
      ((hcontK x).continuousOn.mono (Set.subset_univ _)).mul hg
    exact AEStronglyMeasurable.mono_set Set.uIoc_subset_uIcc
      (hmul.aestronglyMeasurable measurableSet_uIcc)
  have hF_int : IntervalIntegrable (fun s : ℝ => Kern ρ θ s * g s) volume a b :=
    (((hcontK θ).continuousOn.mono (Set.subset_univ _)).mul hg).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable (fun s : ℝ => Kern ρ' θ s * g s)
      (volume.restrict (Set.uIoc a b)) :=
    (((hmeasK' θ).aemeasurable).mul hg_aem).aestronglyMeasurable
  -- the uniform dominating function `t ↦ 3 C |g t|`
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ (Set.univ : Set ℝ),
      ‖Kern ρ' x t * g t‖ ≤ 3 * C * |g t| := by
    filter_upwards with t _ht x _hx
    have hK : |Kern ρ' x t| ≤ 3 * C := by
      rw [Kern_apply]
      have h := abs_sub (ρ' (x - t) - ρ' (x + t)) (ρ' (x + t - Real.pi))
      have h2 := abs_sub (ρ' (x - t)) (ρ' (x + t))
      have h3 := hC (x - t); have h4 := hC (x + t); have h5 := hC (x + t - Real.pi)
      linarith [abs_nonneg (ρ' (x + t - Real.pi))]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hK (abs_nonneg _)
  have hbound_int : IntervalIntegrable (fun t : ℝ => 3 * C * |g t|) volume a b :=
    (hg.abs.intervalIntegrable).const_mul (3 * C)
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun y : ℝ => Kern ρ y t * g t) (Kern ρ' x t * g t) x := by
    filter_upwards with t _ht x _hx
    exact (Kern_hasDerivAt hd x t).mul_const (g t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y s => Kern ρ y s * g s)
    (F' := fun y s => Kern ρ' y s * g s)
    (x₀ := θ) (s := Set.univ) (a := a) (b := b) (μ := volume)
    (bound := fun t => 3 * C * |g t|)
    Filter.univ_mem hF_meas hF_int hF'_meas hbound hbound_int hdiff).2

end Work.FTS.EllSol.EllPkgAux
