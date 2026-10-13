import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.SourceBound.Lzero1PzComm
import Submission.Work.FTS.EllipticEst.remov.SourceBound.chainZero
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

/-- **The differentiated equation on a slice, in the degenerate case `α = -5`.**

Let `(F, Ψ)` be a datum of the weak class `EllWeakPos α k F Ψ` with `α = -5`.  Then for `z > 0`
and `θ ∈ (0, π/2)` the angular operator applied to the `z`-derivative of the slice is

`Lzero1 (fun t => pz Ψ z t) θ = pz F z θ + 25 * z^2 * pzIter 3 Ψ z θ + 50 * z * pzIter 2 Ψ z θ`.

Proof sketch.  For `α = -5` the equation `bslOp α Ψ = F` reads
`Lzero1 (fun t => Ψ z' t) θ = F z' θ + 25 * z'^2 * pzIter 2 Ψ z' θ` for every `z' > 0` and
`θ ∈ (0,π/2)` (`bslOp_slice_eq` plus `h.eq`; note `α² = 25` and `α(5+α) = 0`).  By `Lzero1PzComm`
(this directory, proved) the left hand side of the goal is
`deriv (fun z' => Lzero1 (fun t => Ψ z' t) θ) z`, and by `Filter.EventuallyEq.deriv_eq` (the two
functions agree for all `z' > 0`, a neighbourhood of `z` since `hz : 0 < z`) this is the
derivative of `z' ↦ F z' θ + 25 * z'^2 * pzIter 2 Ψ z' θ`.  Compute that derivative with the
product rule: `deriv (fun z' => F z' θ) z = pz F z θ` (definitional), and
`deriv (fun z' => 25 * z'^2 * pzIter 2 Ψ z' θ) z = 50 * z * pzIter 2 Ψ z θ
 + 25 * z^2 * pzIter 3 Ψ z θ` (`deriv_mul`, `deriv_pow`, and `deriv (fun z' => pzIter 2 Ψ z' θ) z =
 pzIter 3 Ψ z θ`, which is definitional).  The differentiability side conditions come from the
smoothness of `Ψ` on the open quadrant; the sibling
`Work.FTS.EllipticEst.remov.SourceBound.chainZero` provides `hasDerivAt_zslice` and
`contDiffOn_uncurry_pz_of_isOpen` for the slices of `pz`-iterates. -/
theorem diffEqAlphaNeg5 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (hα : α = -5) {z θ : ℝ} (hz : 0 < z)
    (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
      = Work.Spaces.pz F z θ + 25 * z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ
        + 50 * z * Work.Spaces.pzIter 2 Ψ z θ := by
  subst hα
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθ2⟩
  -- the equation, on every slice with `z' > 0`
  have hslice : ∀ z' ∈ Set.Ioi (0 : ℝ),
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z' t) θ
        = F z' θ + 25 * z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ := by
    intro z' hz'
    have h1 : Work.Elliptic.bslOp (-5) Ψ z' θ = F z' θ := h.eq z' hz' θ hθ hθ2
    rw [Work.Elliptic.bslOp_apply] at h1
    have hL : Work.Elliptic.Lzero Ψ z' θ
        = Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z' t) θ := rfl
    rw [hL] at h1
    norm_num at h1
    have h2 : Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z' t) θ
        = F z' θ + 25 * z' ^ 2 * Work.Spaces.pz (Work.Spaces.pz Ψ) z' θ := by
      linarith [h1]
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h2
  -- the two functions agree near `z`, so their derivatives agree
  have hderiv : deriv (fun z' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z' t) θ) z
      = deriv (fun z' => F z' θ + 25 * z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) z := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact hslice z' hz'
  -- smoothness of `F` on the open quadrant, from the equation
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
        (α := -5) (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth))
      (fun z' θ' hz' hθ' hθ2' => h.eq z' hz' θ' hθ' hθ2')
  have hFd : HasDerivAt (fun z' => F z' θ) (Work.Spaces.pz F z θ) z :=
    hFsm.hasDerivAt_slice hθm hz
  have hpz2 : HasDerivAt (fun z' => Work.Spaces.pzIter 2 Ψ z' θ)
      (Work.Spaces.pzIter 3 Ψ z θ) z :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth).hasDerivAt_slice_pzIter 2 hθm hz
  have hpoly : HasDerivAt (fun z' : ℝ => 25 * z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
      (25 * (2 * z) * Work.Spaces.pzIter 2 Ψ z θ
        + 25 * z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 25 * z' ^ 2) (25 * ((2 : ℕ) * z ^ (2 - 1))) z :=
      (hasDerivAt_pow 2 z).const_mul (25 : ℝ)
    refine (h1.mul hpz2).congr_deriv ?_
    ring
  have hsum : HasDerivAt (fun z' => F z' θ + 25 * z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
      (Work.Spaces.pz F z θ + (25 * (2 * z) * Work.Spaces.pzIter 2 Ψ z θ
        + 25 * z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)) z := hFd.add hpoly
  rw [Work.FTS.EllipticEst.remov.SourceBound.Lzero1PzComm h.smooth hz hθ hθ2, hderiv,
    hsum.deriv]
  ring

end Work.FTS.EllipticEst.remov.SourceBound
