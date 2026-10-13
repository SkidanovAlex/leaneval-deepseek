import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.BSIdent.Weyl.Corrected
import Submission.Work.Cyl.Coords

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl

open Filter Set
open scoped Topology

/-- **Continuity of the corrected stream-function field.**

The Lean field `Cyl.psiField ψ` is continuous off the axis (`hψ`) and has, at every point
`z • e₂` of the axis, the one-sided limit `-(2 L z) • e_Z` along the complement of the axis
(`hlim`).  The corrected field `psiFieldCorr ψ L` replaces the (junk) on-axis value of
`psiField` by exactly that limit; since the on-axis branch
`x ↦ -(2 L (axial x)) • e_Z` is continuous as soon as `L` is (`hL`), the piecewise field is
continuous everywhere.  Off the axis this is immediate; on the axis we use the decomposition
`𝓝 x = 𝓝[{r = 0}] x ⊔ 𝓝[{r ≠ 0}] x`. -/
theorem continuous_psiFieldCorr {ψ : ℝ → ℝ → ℝ} {L : ℝ → ℝ}
    (hψ : ContinuousOn (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.psiField ψ x)
        {x : Work.FTS.BSIdent.R3 | Work.Cyl.radial x ≠ 0})
    (hL : Continuous L)
    (hlim : ∀ z : ℝ, Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.psiField ψ x)
        (nhdsWithin (z • FiniteTimeSingularity.e 2)
          {x : Work.FTS.BSIdent.R3 | Work.Cyl.radial x ≠ 0})
        (nhds ((-(2 * L z)) • Work.Cyl.eZ))) :
    Continuous (Work.FTS.BSIdent.psiFieldCorr ψ L) := by
  have hAx : Continuous (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.axial x) := by
    have h : (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.axial x) = fun x => x 2 := rfl
    rw [h]; fun_prop
  have hrad : Continuous (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.radial x) := by
    have h : (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.radial x)
        = fun x => Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by funext x; rfl
    rw [h]; fun_prop
  -- the on-axis branch is continuous
  have hA : Continuous (fun x : Work.FTS.BSIdent.R3 =>
      (-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ) := by
    fun_prop
  -- axis ∪ off-axis = everything
  have hST : ({y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0} ∪
      {y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y ≠ 0}) = Set.univ := by
    ext y; by_cases h : Work.Cyl.radial y = 0 <;> simp [h]
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : Work.Cyl.radial x = 0
  · -- on the axis: glue the two one-sided limits
    have hxval : Work.FTS.BSIdent.psiFieldCorr ψ L x
        = (-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ :=
      Work.FTS.BSIdent.psiFieldCorr_of_radial_eq hx
    -- a point of the axis is a multiple of `e₂`
    have hxe : x = (Work.Cyl.axial x) • FiniteTimeSingularity.e 2 := by
      have hzero : Work.Cyl.radSq x = 0 := by
        have := congrArg (fun t : ℝ => t ^ 2) hx
        rw [Work.Cyl.radial] at this
        rwa [Real.sq_sqrt (by simp only [Work.Cyl.radSq]; positivity),
          zero_pow (by norm_num)] at this
      have h02 : x 0 ^ 2 + x 1 ^ 2 = 0 := by simpa [Work.Cyl.radSq] using hzero
      have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
      have h1' : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
      ext i
      fin_cases i <;> simp [Work.Cyl.axial, h0, h1', FiniteTimeSingularity.e, Pi.single]
    -- along the axis the corrected field is the continuous branch
    have hEqS : (fun y : Work.FTS.BSIdent.R3 => (-(2 * L (Work.Cyl.axial y))) • Work.Cyl.eZ)
        =ᶠ[𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0}] x]
        Work.FTS.BSIdent.psiFieldCorr ψ L := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (Work.FTS.BSIdent.psiFieldCorr_of_radial_eq hy).symm
    have hAll : Tendsto (Work.FTS.BSIdent.psiFieldCorr ψ L)
        (𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0}] x)
        (𝓝 ((-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ)) :=
      Tendsto.congr' hEqS (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    -- off the axis the corrected field is `psiField ψ`, whose limit is the on-axis value
    have hEqC : (fun y => Work.Cyl.psiField ψ y)
        =ᶠ[𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y ≠ 0}] x]
        Work.FTS.BSIdent.psiFieldCorr ψ L := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (Work.FTS.BSIdent.psiFieldCorr_of_radial_ne hy).symm
    have hlimx : Tendsto (fun y => Work.Cyl.psiField ψ y)
        (𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y ≠ 0}] x)
        (𝓝 ((-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ)) := by
      have h := hlim (Work.Cyl.axial x)
      rwa [← hxe] at h
    have hAc : Tendsto (Work.FTS.BSIdent.psiFieldCorr ψ L)
        (𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y ≠ 0}] x)
        (𝓝 ((-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ)) :=
      Tendsto.congr' hEqC hlimx
    have hcomb : Tendsto (Work.FTS.BSIdent.psiFieldCorr ψ L)
        (𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0}] x ⊔
          𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y ≠ 0}] x)
        (𝓝 ((-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ)) :=
      tendsto_sup.mpr ⟨hAll, hAc⟩
    rw [← nhdsWithin_union, hST, nhdsWithin_univ] at hcomb
    rw [ContinuousAt, hxval]
    exact hcomb
  · -- off the axis, `psiFieldCorr` agrees locally with the continuous `psiField ψ`
    have hSclosed : IsClosed {y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0} :=
      isClosed_eq hrad continuous_const
    have hcontOn : ContinuousOn (Work.FTS.BSIdent.psiFieldCorr ψ L)
        ({y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0}ᶜ) :=
      hψ.congr (fun y hy => Work.FTS.BSIdent.psiFieldCorr_of_radial_ne hy)
    exact hcontOn.continuousAt (hSclosed.isOpen_compl.mem_nhds hx)

end Work.FTS.BSIdent.Weyl
