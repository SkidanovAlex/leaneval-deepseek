import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.Trunc.PassAux2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAone

open MeasureTheory Set

/-- The particular solution `Gc N b u` of the shifted equation is continuous on the open
strip `ℝ × (0,π/2)`.

`Gc N b u t θ = χ_N(t)·u(t,θ) + e^{bt} ∫_s in t..(2N), e^{-bs}·(χ_N)'(s)·u(s,θ)`.
The first summand is a product of continuous functions.  For the second we use the joint
continuity of a parameter-dependent interval integral with a *moving* limit; the integrand
`(s,θ) ↦ e^{-bs}(χ_N)'(s)u(s,θ)` is only known to be continuous on the open strip, so
`intervalIntegral.continuous_parametric_primitive_of_continuous` is applied to the subtype
`↥(univ ×ˢ Ioo 0 (π/2))`, after inverting the interval (`∫_t^{2N} = -∫_{2N}^t`) to turn the
moving lower limit into a moving upper limit. -/
theorem continuousOn_Gc_strip (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.ShiftFT.Gc N b u p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  set F : ℝ → ℝ → ℝ :=
    fun s θ => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ with hFdef
  have hucont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have hFc : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : Continuous (fun p : ℝ × ℝ => Real.exp (-(b * p.1))) := by fun_prop
    have h2 : Continuous (fun p : ℝ × ℝ => deriv (Work.FTS.EllSol.Trunc.chi N) p.1) :=
      ((Work.FTS.EllSol.Trunc.chi_contDiff 1 N).continuous_deriv (by norm_num)).comp
        continuous_fst
    have h3 := (h1.continuousOn.mul h2.continuousOn).mul hucont
    rw [hFdef]
    exact h3
  -- joint continuity of the moving-limit interval integral
  have hint : ContinuousOn (fun p : ℝ × ℝ => ∫ s in p.1..(2 * N), F s p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hf : Continuous (fun q : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) × ℝ =>
        F q.2 q.1.val.2) := by
      have hmaps : ∀ q : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) × ℝ,
          ((q.2, q.1.val.2) : ℝ × ℝ) ∈ Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        fun q => ⟨trivial, q.1.property.2⟩
      have hcont : Continuous (fun q : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) × ℝ =>
          ((q.2, q.1.val.2) : ℝ × ℝ)) :=
        continuous_snd.prodMk ((continuous_snd.comp continuous_subtype_val).comp continuous_fst)
      exact hFc.comp_continuous hcont hmaps
    have h1 : Continuous (fun p : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) × ℝ =>
        ∫ t in (2 * N)..p.2, F t p.1.val.2) :=
      intervalIntegral.continuous_parametric_primitive_of_continuous
        (f := fun (x : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) (s : ℝ) =>
          F s x.val.2) (a₀ := 2 * N) hf
    have h2 : Continuous (fun x : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) =>
        ∫ t in (2 * N)..x.val.1, F t x.val.2) :=
      h1.comp (continuous_id.prodMk (continuous_fst.comp continuous_subtype_val))
    rw [continuousOn_iff_continuous_domRestrict]
    refine h2.neg.congr (fun x => ?_)
    rw [Set.domRestrict_apply, Pi.neg_apply]
    exact (intervalIntegral.integral_symm (f := fun s : ℝ => F s x.val.2) (2 * N) x.val.1).symm
  have hprod : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.Trunc.chi N p.1 * u p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((((Work.FTS.EllSol.Trunc.chi_contDiff 1 N).continuous).comp continuous_fst).continuousOn).mul
      hucont
  have hexp2 : ContinuousOn (fun p : ℝ × ℝ => Real.exp (b * p.1))
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ => Real.exp (b * p.1))).continuousOn
  have hg : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.Trunc.chi N p.1 * u p.1 p.2
      + Real.exp (b * p.1) * ∫ s in p.1..(2 * N), F s p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hprod.add (hexp2.mul hint)
  refine hg.congr (fun p hp => ?_)
  simp only [hFdef, Work.FTS.EllSol.ShiftFT.Gc]

theorem GcAesm (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.ShiftFT.Gc N b u p.1 p.2)
      (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
  exact Work.FTS.EllSol.Trunc.aesm_strip (continuousOn_Gc_strip N b u hu)

end Work.FTS.EllSol.ShiftFT.uTrAone
