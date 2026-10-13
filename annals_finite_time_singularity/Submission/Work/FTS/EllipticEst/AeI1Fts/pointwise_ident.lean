import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.H2W.SlotA.radialDerivPointwiseOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise identity `(†)` of the `I₁` bound, in the weak class

With `u` of class `C³` on the **open** quadrant `qd = (0,∞) × (0,π/2)` and the vocabulary of
`AeI1Fts/Defs` (`U u = z ∂_z u`, `AA u = z²∂_zz u`, `BB u = ∂_θθ u`, `Hh u = z ∂_z ∂_θθ u`,
`w z = (1+z)²/z²`, `cw z = 2(z-1)/(1+z)`), the elementary product rule

`∂_z(z · U·B·w²) = w²·(A·B + cw·U·B + U·H)`

holds at every `(z,θ)` with `z > 0`, `θ ∈ (0,π/2)`.  Indeed the left-hand side is

`((2U + A)·B + U·H)·w² + (U·B)·2 z w w'`,

and the identity `2 + 2 z (w'/w) = cw` (equivalently `(w²)'·z/w² = -4/(1+z)`) collects the
`U·B`-terms into the drift `cw·U·B` of the right-hand side.  This file contains the pointwise
calculus only: the slice derivatives of `u` are supplied by the joint `C³` hypothesis through the
`Fréchet`-derivative description of the curried partials.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The open half-strip `(0,∞) × (0,π/2)`. -/
private abbrev qdO : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private theorem isOpen_qdO : IsOpen qdO := isOpen_Ioi.prod isOpen_Ioo

/-- `Work.Spaces.pth` lowers the order of smoothness by one on an open set, because the curried
`θ`-partial is the composition of the Fréchet derivative with the evaluation at `(0,1)`. -/
private theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (n := (n + 1 : ℕ)) (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The derivative of the square of the radial weight: `∂_z(w²) = -4 w² / ((1+z)·z)`. -/
private theorem hasDerivAt_wSq {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => (Work.Spaces.w z') ^ 2)
      (-4 * (Work.Spaces.w z) ^ 2 / ((1 + z) * z)) z := by
  have h : HasDerivAt (fun t : ℝ => ((1 + t) ^ 2 / t ^ 2) ^ 2)
      (-4 * ((1 + z) ^ 2 / z ^ 2) ^ 2 / ((1 + z) * z)) z := by
    have hnum : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + z)) z := by
      have h0 : HasDerivAt (fun t : ℝ => 1 + t) 1 z := (hasDerivAt_id z).const_add 1
      have h1 := h0.pow 2
      convert h1 using 1
      ring
    have hden : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
      have h0 := hasDerivAt_pow 2 z
      convert h0 using 1
      ring
    have hdiv := hnum.div hden (by positivity : z ^ 2 ≠ 0)
    refine (hdiv.pow 2).congr_deriv ?_
    simp only [Pi.div_apply]
    field_simp
    ring_nf
    simp only [inv_pow]
    field_simp
  simpa only [Work.Spaces.w] using h

theorem pointwise_ident {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun z' => Work.FTS.EllipticEst.AeI1Fts.Fd u z' θ) z
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ := by
  have hz0 : (0 : ℝ) < z := hz
  -- the `z`-slice of `u` is `C³` and its derivative is `∂_z u`
  have hslice3 : ContDiffOn ℝ 3 (fun z' => u z' θ) (Set.Ioi 0) :=
    hu.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z' hz' => ⟨hz', hθ⟩)
  have hsliceD : ContDiffOn ℝ 2 (fun z' => Work.Spaces.pz u z' θ) (Set.Ioi 0) := by
    have h := hslice3.deriv_of_isOpen isOpen_Ioi (m := 2) (by norm_num)
    simpa only [Work.Spaces.pz] using h
  have hA : HasDerivAt (fun z' => Work.Spaces.pz u z' θ) (Work.Spaces.pzIter 2 u z θ) z := by
    have hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz u z' θ) z :=
      (hsliceD.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz0)
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      using hd.hasDerivAt
  -- the `z`-slice of `∂_θθu` is `C¹` and its derivative is `∂_z∂_θθu`
  have hB : HasDerivAt (fun z' => Work.Spaces.pthIter 2 u z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z := by
    have h1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth u)) qdO :=
      contDiffOn_uncurry_pth_succ isOpen_qdO (n := 2) hu
    have h2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth u))) qdO :=
      contDiffOn_uncurry_pth_succ isOpen_qdO (n := 1) h1
    have hpth2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pthIter 2 u)) qdO := by
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h2
    have hsliceP : ContDiffOn ℝ 1 (fun z' => Work.Spaces.pthIter 2 u z' θ) (Set.Ioi 0) :=
      hpth2.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z' hz' => ⟨hz', hθ⟩)
    have hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pthIter 2 u z' θ) z :=
      (hsliceP.differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz0)
    simpa only [Work.Spaces.pz] using hd.hasDerivAt
  -- the product rule for the four factors `z'`, `z'·∂_zu`, `∂_θθu`, `w²`
  have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun z' => z' * Work.Spaces.pz u z' θ)
      (1 * Work.Spaces.pz u z θ + z * Work.Spaces.pzIter 2 u z θ) z := h1.mul hA
  have h3 := (h1.mul h2).mul hB
  have h4 := hasDerivAt_wSq hz
  have hmain : HasDerivAt (fun z' => Fd u z' θ)
      ((Work.Spaces.w z) ^ 2 * Fp u z θ) z := by
    refine (h3.mul h4).congr_deriv ?_
    rw [Fp]
    rw [show Work.FTS.EllipticEst.AngSecond.cw z = 2 * (z - 1) / (1 + z) from rfl]
    simp only [Pi.mul_apply]
    field_simp
    ring
  exact hmain.deriv

end

end Work.FTS.EllipticEst.AeI1Fts
