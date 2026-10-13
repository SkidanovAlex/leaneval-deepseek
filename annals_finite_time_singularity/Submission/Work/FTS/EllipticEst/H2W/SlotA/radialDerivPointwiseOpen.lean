import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise radial product rule for the open half-strip `(0,∞) × (0,π/2)`

This is the *weak-class* version of `Work.FTS.EllipticEst.H2W.radial_deriv_pointwise`:
the smoothness hypothesis is `C³` on the **open** half-strip `Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)`
(only the open quadrant, as in the almost-everywhere class `H2W.Ae.AeData`) instead of on the
neighbourhood `Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2+1)`.

For a function `Φ` of class `C³` on the open half-strip, at a point `(z,θ)` with `z > 0` and
`θ ∈ (0,π/2)`,

`deriv (fun z' => (z'^2 · ∂_zΦ(z',θ) · w(z')^2) · ∂_θ²Φ(z',θ)) z`
equals the four-term product rule expansion.

The proof is the one of the sibling file, with the two open sets replaced: the `θ`-slice
`z' ↦ Φ z' θ` is `C³` on `(0,∞)` because `Φ` is (`hsm.comp` with the embedding `z' ↦ (z',θ)`,
which lands in the open half-strip since `θ ∈ (0,π/2)`), and the curried `θ`-partials are
smooth in the pair by `ContDiffOn.fderiv_of_isOpen` — this needs only that the strip is open.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The open half-strip `(0,∞) × (0,π/2)`. -/
abbrev qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_qd : IsOpen qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## Two-variable calculus: slices and the curried partials -/

/-- The `z`-partial is the Fréchet derivative in the direction `(1,0)`. -/
private theorem pz_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    Work.Spaces.pz G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (1, 0) := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  exact (h.hasFDerivAt.comp_hasDerivAt z hcurve).deriv

/-- The `θ`-partial is the Fréchet derivative in the direction `(0,1)`. -/
private theorem pth_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    Work.Spaces.pth G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (0, 1) := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  exact (h.hasFDerivAt.comp_hasDerivAt θ hcurve).deriv

/-- The `θ`-partial of a function that is `C^{n+1}` on an open set is `C^n` there. -/
private theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact pth_eq_fderiv ((h.differentiableOn (n := (n + 1 : ℕ)) (by simp)).differentiableAt
      (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-! ## The product rule -/

theorem radial_deriv_pointwise_open (Φ : ℝ → ℝ → ℝ)
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun z' => (z' ^ 2 * Work.Spaces.pz Φ z' θ * (Work.Spaces.w z') ^ 2)
        * Work.Spaces.pthIter 2 Φ z' θ) z
      = (z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) * Work.Spaces.pthIter 2 Φ z θ
          * (Work.Spaces.w z) ^ 2
        + z ^ 2 * Work.Spaces.pz Φ z θ * Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ
          * (Work.Spaces.w z) ^ 2
        + z ^ 2 * Work.Spaces.pz Φ z θ * Work.Spaces.pthIter 2 Φ z θ
          * deriv (fun z' => (Work.Spaces.w z') ^ 2) z
        + 2 * (z * Work.Spaces.pz Φ z θ * Work.Spaces.pthIter 2 Φ z θ
          * (Work.Spaces.w z) ^ 2) := by
  have hVopen : IsOpen qd := isOpen_qd
  have hz0 : (0 : ℝ) < z := hz
  -- The first factor `z' ↦ z'^2`.
  have hz2 : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  -- The second factor `z' ↦ ∂_zΦ(z',θ)`
  have hA2 : HasDerivAt (fun z' => Work.Spaces.pz Φ z' θ) (Work.Spaces.pzIter 2 Φ z θ) z := by
    have hpair3 : ContDiffOn ℝ 3 (fun z' : ℝ => (z', θ)) (Set.Ioi 0) :=
      contDiffOn_id.prodMk contDiffOn_const
    have hslice3 : ContDiffOn ℝ 3 (fun z' => Φ z' θ) (Set.Ioi 0) :=
      hsm.comp hpair3 (fun z' hz' => ⟨hz', hθ⟩)
    have hsliceD : ContDiffOn ℝ 2 (fun z' => Work.Spaces.pz Φ z' θ) (Set.Ioi 0) := by
      have h := hslice3.deriv_of_isOpen isOpen_Ioi (m := 2) (by norm_num)
      simpa only [Work.Spaces.pz] using h
    have hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Φ z' θ) z :=
      (hsliceD.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hz0)
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      using hd.hasDerivAt
  -- The third factor `z' ↦ w(z')^2`
  have hw : HasDerivAt (fun z' => (Work.Spaces.w z') ^ 2)
      (deriv (fun z' => (Work.Spaces.w z') ^ 2) z) z := by
    have hd : DifferentiableAt ℝ (fun z' : ℝ => (Work.Spaces.w z') ^ 2) z := by
      show DifferentiableAt ℝ (fun z' : ℝ => (((1 + z') ^ 2 / z' ^ 2) ^ 2)) z
      have hnum : DifferentiableAt ℝ (fun z' : ℝ => (1 + z') ^ 2) z :=
        ((differentiableAt_const (1:ℝ)).add differentiableAt_id).pow 2
      have hden : DifferentiableAt ℝ (fun z' : ℝ => z' ^ 2) z := differentiableAt_id.pow 2
      have hne : z ^ 2 ≠ 0 := by positivity
      exact (hnum.div hden hne).pow 2
    exact hd.hasDerivAt
  -- The fourth factor `z' ↦ ∂_θ²Φ(z',θ)`
  have hB : HasDerivAt (fun z' => Work.Spaces.pthIter 2 Φ z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ) z := by
    have h1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Φ)) qd :=
      contDiffOn_uncurry_pth_succ hVopen hsm
    have h2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth Φ))) qd :=
      contDiffOn_uncurry_pth_succ hVopen h1
    have hpth2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pthIter 2 Φ)) qd := by
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h2
    have hpair : ContDiffOn ℝ 1 (fun z' : ℝ => (z', θ)) (Set.Ioi 0) :=
      contDiffOn_id.prodMk contDiffOn_const
    have hsliceP : ContDiffOn ℝ 1 (fun z' => Work.Spaces.pthIter 2 Φ z' θ) (Set.Ioi 0) :=
      hpth2.comp hpair (fun z' hz' => ⟨hz', hθ⟩)
    have hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pthIter 2 Φ z' θ) z :=
      (hsliceP.differentiableOn_one).differentiableAt
        (isOpen_Ioi.mem_nhds hz0)
    simpa only [Work.Spaces.pz] using hd.hasDerivAt
  have h := ((hz2.mul hA2).mul hw).mul hB
  exact h.deriv.trans (by simp only [Pi.mul_apply]; ring)

end Work.FTS.EllipticEst.H2W.SlotA
