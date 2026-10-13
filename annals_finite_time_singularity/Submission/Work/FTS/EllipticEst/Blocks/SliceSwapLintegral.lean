import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.DzAmgm.LintegralSwapTranslate

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open MeasureTheory Set

/-- If `Function.uncurry G` is `C^{n+1}` on an *open* set `U`, then the uncurried `z`-partial
`(z,θ) ↦ ∂_z G (z,θ)` is `C^n` on `U`.  The point is that on the open set `U` the `z`-partial
coincides with the Fréchet derivative of `Function.uncurry G` evaluated in the constant
direction `(1,0)`, and that composition is smooth. -/
theorem contDiffOn_uncurry_pz_of_succ {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) U := by
  have hchain : ∀ p ∈ U,
      Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) U := by
    have h' := h.fderivWithin hU.uniqueDiffOn (m := n) le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hU hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) U := by
    simpa using hfd.clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))
  exact hcomp.congr hchain

/-- **Tonelli plus translation of the radial variable** for the weighted square of the second
radial partial.  For `V` which is `C²` on the open quadrant `(0,∞) × (0,π/2)` and `wth`
measurable, `z₀ > 0`, `δ > 0`, the iterated `lintegral` of
`(θ,t) ↦ ofReal ((∂_z²V (z₀+t,θ) · wth θ)²)` over `(0,π/2) × (0,δ]` equals the iterated
`lintegral` over the rectangle `(z₀, z₀+δ) × (0,π/2)` in the other order.

Suggested sorry-free route: use the *clean* `DzAmgm.lintegralSwapTranslate_of_aem` (Tonelli,
translation invariance of Lebesgue measure, `Ioc = Ioo` a.e.) together with
`DzAmgm.aem_uncurry_translate`, which needs only joint continuity of
`(z,θ) ↦ ∂_z²V z θ` on the quadrant — prove that yourself, e.g. by the route described in
`FTS/EllipticEst/Blocks/PzIterTwoContinuousOn` (do NOT route through the still-`sorry`
`DzAmgm.LintegralSwapTranslate` / `DzAmgm.ContinuousOnUncurryPzIterTwo` /
`DzAmgm.SliceIteratedDerivFDeriv`). -/
theorem SliceSwapLintegral (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ) (hwthmeas : Measurable wth)
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z₀ δ : ℝ} (hz₀ : 0 < z₀) (hδ : 0 < δ) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ∫⁻ t in Set.Ioc 0 δ,
          ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))
      = ∫⁻ z in Set.Ioo z₀ (z₀ + δ),
          ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal ((Work.Spaces.pzIter 2 V z θ * wth θ) ^ 2) := by
  -- The open quadrant.
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  -- `∂_z V` is `C¹` on the quadrant.
  have h1 : ContDiffOn ℝ (1 : ℕ) (Function.uncurry (Work.Spaces.pz V))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_uncurry_pz_of_succ hU (n := 1) (by norm_num; exact hV)
  -- `∂_z²V` is continuous (i.e. `C⁰`) on the quadrant.
  have h2 : ContDiffOn ℝ (0 : ℕ) (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz V)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_uncurry_pz_of_succ hU (n := 0) (by norm_num; exact h1)
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 V))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have := contDiffOn_zero.mp h2
    simpa [Work.Spaces.pzIter_succ] using this
  -- Tonelli, translation invariance of Lebesgue measure, `Ioc = Ioo` a.e.
  exact Work.FTS.EllipticEst.DzAmgm.lintegralSwapTranslate_of_aem V wth
    (Work.FTS.EllipticEst.DzAmgm.aem_uncurry_translate V wth hwthmeas hcont hz₀ hδ)

end Work.FTS.EllipticEst.Blocks
