import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Lzero_orthogonal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L²`-membership of the slice `θ ↦ a θ`, `θ ↦ a'θ` and `θ ↦ L₀(a)(0,θ)`

The elliptic estimates of §'Elliptic Regularity Estimates' of Elgindi's paper use the
angular operator `L₀(Ψ) = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` (see `Work.Elliptic.Lzero`).
When it is applied to a function which does not depend on `z`, the slice
`θ ↦ L₀(fun _ θ' => a θ') 0 θ` is a purely one dimensional expression in `a`; this file
proves that under the standing regularity assumption `a ∈ C²([0, π/2])` together with a
bound on `L₀ a` on the open interval, the three functions `a`, `a'` and `L₀ a` all belong
to `L²(Iθ)`, `Iθ = [0, π/2]`.

This is the `L²`-part of the hypothesis needed to make sense of the coercivity estimate
`∫_{Iθ} (a² + (a')²) ≤ (10/9) ∫_{Iθ} (L₀a)²` (see `Work.FTS.EllipticEst.Lzero_slice_coercive`),
which requires the three `L²`-integrals to be honest numbers rather than junk values.

The proofs are elementary: `volume.restrict Iθ` is a finite measure, so it suffices to
bound the functions almost everywhere on `Iθ`; the only subtlety is that the relevant
bounds are known on the *open* interval, the two endpoints `0` and `π/2` being null sets.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.style.haveILetI false

namespace Work.FTS.EllipticEst

/-- A property which holds on the open interval `(0, π/2)` holds almost everywhere for the
restriction of Lebesgue measure to `Iθ = [0, π/2]`: the only points lost are the two
endpoints `0` and `π/2`, a null set. -/
lemma ae_restrict_Iθ_of_Ioo_memLp {p : ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ := by
  change ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))), p θ
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_iff]
  suffices hsub : {x : ℝ | ¬(x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → p x)}
      ⊆ ({0, Real.pi / 2} : Set ℝ) by
    refine measure_mono_null hsub ?_
    rw [Set.insert_eq, measure_union_null_iff]
    exact ⟨measure_singleton 0, measure_singleton _⟩
  intro x hx
  simp only [Set.mem_ofPred_eq, not_imp] at hx
  by_contra hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
  exact hx.2 (h x ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hc.1), lt_of_le_of_ne hx.1.2 hc.2⟩)

/-- On a compact interval, the derivative of a `C²` function is bounded: `derivWithin a Iθ`
is continuous on the compact `Iθ`, and on the interior it agrees with `deriv a`. -/
lemma exists_bound_deriv_of_contDiffOn_Icc (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 2 a (Set.Icc 0 (Real.pi / 2))) :
    ∃ M, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖deriv a θ‖ ≤ M := by
  have hpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hUniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (Real.pi / 2)) := uniqueDiffOn_Icc hpos
  have hcont : ContinuousOn (derivWithin a (Set.Icc (0 : ℝ) (Real.pi / 2)))
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := ha.continuousOn_derivWithin hUniq (by norm_num)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨M, fun θ hθ => ?_⟩
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2)]
  exact hM θ ⟨hθ.1.le, hθ.2.le⟩

/-- The value of `L₀` at a `z`-independent function, in terms of the one variable function
alone: with the operator `L₀(Ψ) = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` of
`Work.Elliptic.Lzero`, applied to `Ψ z θ = a θ`, this is
`-(deriv (deriv a)) θ + deriv (fun θ' => tan θ' * a θ') θ - 6 a θ`. -/
lemma Lzero_const_apply (a : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => a θ') z θ
      = -(deriv (deriv a) θ) + deriv (fun θ' => Real.tan θ' * a θ') θ - 6 * a θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter, Work.Spaces.pth]

theorem memLp_Lzero_slice (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 2 a (Set.Icc 0 (Real.pi / 2))) (C : ℝ)
    (hC : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Elliptic.Lzero (fun _ θ' => a θ') 0 θ| ≤ C) :
    MeasureTheory.MemLp (fun θ => a θ) 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      MeasureTheory.MemLp (fun θ => deriv a θ) 2
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
        MeasureTheory.MemLp (fun θ => Work.Elliptic.Lzero (fun _ θ' => a θ') 0 θ) 2
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  -- `Iθ` is a bounded interval, so `volume.restrict Iθ` is a finite measure
  haveI : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    change MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))
    exact inferInstance
  -- bounds for the three functions
  obtain ⟨Ca, hCa⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  obtain ⟨Md, hMd⟩ := exists_bound_deriv_of_contDiffOn_Icc a ha
  refine ⟨?_, ?_, ?_⟩
  · -- `a` is continuous on the compact interval, hence bounded
    refine MeasureTheory.MemLp.of_bound ?_ Ca ?_
    · exact ha.continuousOn.aestronglyMeasurable measurableSet_Icc
    · exact ae_restrict_Iθ_of_Ioo_memLp (fun θ hθ => hCa θ ⟨hθ.1.le, hθ.2.le⟩)
  · -- `deriv a` is bounded on the open interval, and derivatives are measurable
    refine MeasureTheory.MemLp.of_bound ?_ Md ?_
    · exact aestronglyMeasurable_deriv a _
    · exact ae_restrict_Iθ_of_Ioo_memLp (fun θ hθ => hMd θ hθ)
  · -- `L₀ a` is bounded by `C` on the open interval by hypothesis
    have hfun : (fun θ => Work.Elliptic.Lzero (fun _ θ' => a θ') 0 θ)
        = fun θ => -(deriv (deriv a) θ) + deriv (fun θ' => Real.tan θ' * a θ') θ
            - 6 * a θ := funext (fun θ => Lzero_const_apply a 0 θ)
    rw [hfun]
    refine MeasureTheory.MemLp.of_bound ?_ C ?_
    · have h1 : AEStronglyMeasurable (fun θ => deriv (deriv a) θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        aestronglyMeasurable_deriv (deriv a) _
      have h2 : AEStronglyMeasurable (fun θ => deriv (fun θ' => Real.tan θ' * a θ') θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        aestronglyMeasurable_deriv (fun θ' => Real.tan θ' * a θ') _
      have h3 : AEStronglyMeasurable (fun θ => a θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ha.continuousOn.aestronglyMeasurable measurableSet_Icc
      exact ((h1.neg).add h2).sub (h3.const_mul 6)
    · exact ae_restrict_Iθ_of_Ioo_memLp (fun θ hθ => by
        have h := hC θ hθ
        rw [Lzero_const_apply a 0 θ] at h
        rwa [Real.norm_eq_abs])

end Work.FTS.EllipticEst
