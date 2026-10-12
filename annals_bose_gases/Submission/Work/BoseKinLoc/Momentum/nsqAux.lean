import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.nsqAux` — auxiliary lemmas for `‖PsiC‖²`-integrability

Elementary measure-theoretic lemmas underlying the integrability of
`‖PsiC ℓ p ψ‖ ^ 2` (`Submission/Work/BoseKinLoc/Momentum/integrable_norm_sq_PsiC.lean`).

The two ingredients of `PsiC ℓ p ψ = boxFTfun ℓ p ψ − boxMeanR ℓ ψ · boxHat ℓ p` are
*box-localised shifted integrals of `ψ`*,

  `x ↦ ∫_{z ∈ acube ℓ} c z · g (x+z)`.

Such an integral is

* strongly measurable in `x` (`∫` of a strongly measurable two-variable function, Fubini),
* supported in the compact set `(fun q : ℝ³ × ℝ³ => q.1 − q.2) '' (tsupport g ×ˢ acube ℓ)`
  when `0 < ℓ`,
* bounded by `B · C · |acube ℓ|` when `‖c‖ ≤ B`, `‖g‖ ≤ C`.

Consequently a strongly measurable `f` with compact support and a uniform bound has
integrable *square of the norm* (the function is `L²`): this is the last lemma below, and it
is what makes `‖PsiC‖²` integrable.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`L²` from compact support and a uniform bound.**  A strongly measurable `f : ℝ³ → ℂ`
with compact support and `‖f‖ ≤ C` has `‖f‖² ∈ L¹`. -/
lemma nsq_integrable_norm_sq_of_bound {f : ℝ³ → ℂ} (hf : StronglyMeasurable f)
    (hfs : HasCompactSupport f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x : ℝ³ => ‖f x‖ ^ 2) := by
  have hK : volume (tsupport f) < ⊤ := hfs.measure_lt_top
  refine (IntegrableOn.of_bound hK ?_ (C ^ 2) ?_).integrable_of_forall_notMem_eq_zero ?_
  · exact (hf.aestronglyMeasurable.restrict).norm.pow 2
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    simp

/-- **Strong measurability of a box-localised shifted integral.**  The two-variable
integrand `(x,z) ↦ c z · g (x+z)` is strongly measurable and `x ↦ ∫ z, c z · g (x+z)` is an
integral of it against `volume.restrict (acube ℓ)`. -/
lemma nsq_stronglyMeasurable_shiftIntegral (ℓ : ℝ) (c g : ℝ³ → ℂ)
    (hc : StronglyMeasurable c) (hg : StronglyMeasurable g) :
    StronglyMeasurable (fun x : ℝ³ => ∫ z in acube ℓ, c z * g (x + z)) := by
  have hmul : StronglyMeasurable (fun q : ℝ³ × ℝ³ => c q.2 * g (q.1 + q.2)) :=
    (hc.comp_measurable measurable_snd).mul (hg.comp_measurable (measurable_fst.add measurable_snd))
  exact StronglyMeasurable.integral_prod_right' (ν := volume.restrict (acube ℓ)) hmul

/-- **Compact support of a box-localised shifted integral.**  For `0 < ℓ` the shift integral
is supported in the compact set `(fun q : ℝ³ × ℝ³ => q.1 − q.2) '' (tsupport g ×ˢ acube ℓ)`:
a point `x` outside it has `x + z ∉ tsupport g` for every `z ∈ acube ℓ`. -/
lemma nsq_hasCompactSupport_shiftIntegral {ℓ : ℝ} (hℓ : 0 < ℓ) (c g : ℝ³ → ℂ)
    (hg : HasCompactSupport g) :
    HasCompactSupport (fun x : ℝ³ => ∫ z in acube ℓ, c z * g (x + z)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := (fun q : ℝ³ × ℝ³ => q.1 - q.2) '' (tsupport g ×ˢ acube ℓ)) ?_ ?_
  · exact ((show IsCompact (tsupport g) from hg).prod (acube_compact hℓ)).image continuous_sub
  · intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    have hzero : ∀ z ∈ acube ℓ, c z * g (x + z) = 0 := by
      intro z hz
      have hgz : g (x + z) = 0 := by
        by_contra hne
        exact hmem ⟨(x + z, z), ⟨subset_tsupport g (Function.mem_support.mpr hne), hz⟩, by simp⟩
      rw [hgz, mul_zero]
    rw [setIntegral_congr_fun (acube_measurable ℓ) hzero]
    simp

/-- **Uniform bound for a box-localised shifted integral.**  If `‖c‖ ≤ B` and `‖g‖ ≤ C`
with `B ≥ 0`, the shift integral is bounded by `B · C · |acube ℓ|`. -/
lemma nsq_norm_shiftIntegral_le {ℓ : ℝ} (hℓ : 0 < ℓ) (c g : ℝ³ → ℂ) {B C : ℝ}
    (hB : 0 ≤ B) (hcb : ∀ z, ‖c z‖ ≤ B) (hgb : ∀ y, ‖g y‖ ≤ C) (x : ℝ³) :
    ‖∫ z in acube ℓ, c z * g (x + z)‖ ≤ B * C * (volume (acube ℓ)).toReal := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := acube ℓ)
    (f := fun z => c z * g (x + z)) (C := B * C) (acube_lt_top ℓ hℓ.le) (fun z hz => by
      rw [norm_mul]
      exact mul_le_mul (hcb z) (hgb (x + z)) (norm_nonneg _) hB)
  simpa [Measure.real] using h

/-- A smooth compactly supported `ψ` is bounded (it is continuous and supported on the
compact set `tsupport ψ`). -/
lemma nsq_exists_norm_le_of_contDiff_hasCompactSupport {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖ψ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (show IsCompact (tsupport ψ) from hcs).exists_bound_of_continuousOn
    hψ.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport ψ
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

end Work.BoseKinLoc.Momentum
