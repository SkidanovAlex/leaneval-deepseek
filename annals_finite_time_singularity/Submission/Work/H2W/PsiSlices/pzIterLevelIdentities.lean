import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceFiber
import Submission.Work.FTS.EllipticEst.remov.SourceBound.Lzero1PzComm
import Submission.Work.FTS.EllipticEst.remov.SourceBound.SliceAlgebra
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-`1` and level-`2` slice identities of the weak class `WeakPos2`

Differentiating the elliptic equation `Work.Elliptic.bslOp α Ψ = F` once (resp. twice) in the
radial variable `z` and commuting `∂_z` with the angular operator `Lzero` (Clairaut/Schwarz)
gives, on the open quadrant,

  `Lzero1 (∂_zΨ(z,·)) = ∂_zF(z,·) + α²(2z∂_z²Ψ + z²∂_z³Ψ) + α(5+α)(∂_zΨ + z∂_z²Ψ)`

and

  `Lzero1 (∂_z²Ψ(z,·)) = ∂_z²F(z,·) + α²(2∂_z²Ψ + 4z∂_z³Ψ + z²∂_z⁴Ψ) + α(5+α)(2∂_z²Ψ + z∂_z³Ψ)`.

The first identity is the `pz`-companion of `remov.SourceBound.sliceShiftedDecomposition` (which
treats the undifferentiated equation); the second is obtained by differentiating the first, the
`z`-derivative of the `Lzero1`-slice being again a `Lzero1` of the next slice
(`remov.SourceBound.Lzero1PzComm`).

The only smoothness input is `C^∞` of `Ψ` on the open quadrant — which is the corresponding
field of `Work.FTS.EllipticEst.WeakPos2`.  Note that the source `F` is only known to agree with
`bslOp α Ψ` on the open quadrant, so its `z`-derivatives are computed from that local equality
(`Filter.EventuallyEq.deriv_eq`).  Everything rests on
`[propext, Classical.choice, Quot.sound]`.
-/
open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.H2W.PsiSlices

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `z`-derivative of the slice of `Lzero` -/

/-- **The derivative in `z` of the `θ`-slice of `Lzero`.**

For `Ψ` of class `C^∞` on the open quadrant, `z > 0` and `0 < θ < π/2`, the function
`z' ↦ Lzero Ψ z' θ` has derivative `Lzero1 (∂_zΨ(z,·))` at `z`.

The value is identified with the aid of the commutation `remov.Lzero1PzComm`
(`Lzero1 (∂_zΦ(z,·)) = ∂_z (z' ↦ Lzero1 (Φ(z',·)))`, with `Lzero1` of a slice definitionally
the slice of `Lzero`), which settles the Clairaut part; the differentiability itself is the
product rule for the three summands of `Lzero` (`∂_θ²Ψ`, `∂_θ(tan θ·Ψ)`, `Ψ`). -/
theorem hasDerivAt_Lzero_slice {Ψ : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    HasDerivAt (fun z' => Work.Elliptic.Lzero Ψ z' θ)
      (Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ) z := by
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsmooth
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hΨ
  have hd1 : HasDerivAt (fun z' => Work.Spaces.pthIter 2 Ψ z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z := (hΨ.pth.pth).hasDerivAt_slice hθm hz
  have hd2 : HasDerivAt (fun z' => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z' θ)
      (Work.Spaces.pz (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) z θ) z :=
    htan.pth.hasDerivAt_slice hθm hz
  have hd3 : HasDerivAt (fun z' => Ψ z' θ) (Work.Spaces.pz Ψ z θ) z := hΨ.hasDerivAt_slice hθm hz
  have hsum : HasDerivAt (fun z' => -(Work.Spaces.pthIter 2 Ψ z' θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z' θ - 6 * Ψ z' θ)
      ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) z θ)
        - 6 * Work.Spaces.pz Ψ z θ) z :=
    (hd1.neg.add hd2).sub (hd3.const_mul 6)
  have key : Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ
      = deriv (fun z' => Work.Elliptic.Lzero Ψ z' θ) z := by
    exact Work.FTS.EllipticEst.remov.SourceBound.Lzero1PzComm hsmooth hz hθ0 hθ1
  have hV : ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) z θ)
        - 6 * Work.Spaces.pz Ψ z θ)
      = deriv (fun z' => Work.Elliptic.Lzero Ψ z' θ) z := hsum.deriv.symm
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z' => ?_)) |>.congr_deriv ?_
  · exact (Work.FTS.EllipticEst.remov.Lzero1_slice_eq Ψ z' θ).symm
  · exact hV.trans key.symm

/-! ## The level-`1` identity -/

/-- **The level-`1` slice identity.**  Differentiating `bslOp α Ψ = F` once in `z` (and using
`hasDerivAt_Lzero_slice` for the angular part) gives, at every point of the open quadrant,

  `Lzero1 (∂_zΨ(z,·)) = ∂_zF(z,·) + α²(2z∂_z²Ψ + z²∂_z³Ψ) + α(5+α)(∂_zΨ + z∂_z²Ψ)`. -/
theorem levelOneIdent {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ
      = Work.Spaces.pzIter 1 F z θ
        + α ^ 2 * (2 * z * Work.Spaces.pzIter 2 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
        + α * (5 + α) * (Work.Spaces.pzIter 1 Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ) := by
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  -- the second-order term `-α²z²·∂_z²Ψ`
  have h1a : HasDerivAt (fun z' : ℝ => -(α ^ 2 * z' ^ 2)) (-(α ^ 2 * (2 * z))) z := by
    have h := ((hasDerivAt_id z).pow 2).const_mul (α ^ 2)
    exact h.neg.congr_deriv (by norm_num)
  have h1 : HasDerivAt (fun z' : ℝ => -(α ^ 2 * z' ^ 2) * Work.Spaces.pzIter 2 Ψ z' θ)
      (-(α ^ 2 * (2 * z)) * Work.Spaces.pzIter 2 Ψ z θ
        + (-(α ^ 2 * z ^ 2)) * Work.Spaces.pzIter 3 Ψ z θ) z :=
    h1a.mul (hΨ.hasDerivAt_slice_pzIter 2 hθm hz)
  -- the first-order term `-α(5+α)z·∂_zΨ`
  have h2a : HasDerivAt (fun z' : ℝ => -(α * (5 + α) * z')) (-(α * (5 + α))) z := by
    have h := (hasDerivAt_id z).const_mul (α * (5 + α))
    exact h.neg.congr_deriv (by ring)
  have h2 : HasDerivAt (fun z' : ℝ => -(α * (5 + α) * z') * Work.Spaces.pzIter 1 Ψ z' θ)
      (-(α * (5 + α)) * Work.Spaces.pzIter 1 Ψ z θ
        + (-(α * (5 + α) * z)) * Work.Spaces.pzIter 2 Ψ z θ) z :=
    h2a.mul (hΨ.hasDerivAt_slice_pzIter 1 hθm hz)
  -- the angular term `Lzero Ψ`
  have h3 : HasDerivAt (fun z' => Work.Elliptic.Lzero Ψ z' θ)
      (Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ) z :=
    hasDerivAt_Lzero_slice hsm hz hθ0 hθ1
  have hsum := (h1.add h2).add h3
  have hbsl : HasDerivAt (fun z' => Work.Elliptic.bslOp α Ψ z' θ)
      ((-(α ^ 2 * (2 * z)) * Work.Spaces.pzIter 2 Ψ z θ
        + (-(α ^ 2 * z ^ 2)) * Work.Spaces.pzIter 3 Ψ z θ)
       + (-(α * (5 + α)) * Work.Spaces.pzIter 1 Ψ z θ
        + (-(α * (5 + α) * z)) * Work.Spaces.pzIter 2 Ψ z θ)
       + Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ) z := by
    have hfun : (fun z' => Work.Elliptic.bslOp α Ψ z' θ)
        = ((fun z' : ℝ => -(α ^ 2 * z' ^ 2) * Work.Spaces.pzIter 2 Ψ z' θ)
            + fun z' : ℝ => -(α * (5 + α) * z') * Work.Spaces.pzIter 1 Ψ z' θ)
            + fun z' => Work.Elliptic.Lzero Ψ z' θ := by
      funext z'
      simp only [Pi.add_apply]
      rw [Work.Elliptic.bslOp_apply]
      rw [show (α * (5 + α) * z') * Work.Spaces.pz Ψ z' θ
          = (α * (5 + α) * z') * Work.Spaces.pzIter 1 Ψ z' θ from rfl]
      ring
    rw [hfun]
    exact hsum
  -- `∂_zF` computed from the local equality `F = bslOp α Ψ`
  have hloc : (fun z' => Work.Elliptic.bslOp α Ψ z' θ) =ᶠ[𝓝 z] (fun z' => F z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact hEq z' hz' θ hθ0 hθ1
  have hdF : Work.Spaces.pzIter 1 F z θ
      = deriv (fun z' => Work.Elliptic.bslOp α Ψ z' θ) z := by
    rw [show Work.Spaces.pzIter 1 F z θ = deriv (fun z' => F z' θ) z from rfl,
      ← hloc.deriv_eq]
  rw [hdF, hbsl.deriv]
  ring

/-! ## The level-`2` identity -/

/-- **The level-`2` slice identity.**  Differentiating the level-`1` identity once more in `z`
(the derivative of the `Lzero1`-slice being the `Lzero1` of the next slice, by
`remov.Lzero1PzComm`) gives, at every point of the open quadrant,

  `Lzero1 (∂_z²Ψ(z,·)) = ∂_z²F(z,·) + α²(2∂_z²Ψ + 4z∂_z³Ψ + z²∂_z⁴Ψ) + α(5+α)(2∂_z²Ψ + z∂_z³Ψ)`. -/
theorem levelTwoIdent {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hLev1 : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ
        = Work.Spaces.pzIter 1 F z θ
          + α ^ 2 * (2 * z * Work.Spaces.pzIter 2 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
          + α * (5 + α) * (Work.Spaces.pzIter 1 Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ))
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') θ
      = Work.Spaces.pzIter 2 F z θ
        + α ^ 2 * (2 * Work.Spaces.pzIter 2 Ψ z θ
            + 4 * z * Work.Spaces.pzIter 3 Ψ z θ
            + z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ)
        + α * (5 + α) * (2 * Work.Spaces.pzIter 2 Ψ z θ
            + z * Work.Spaces.pzIter 3 Ψ z θ) := by
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ)
      (fun z θ hz hθ0 hθ1 => hEq z hz θ hθ0 hθ1)
  -- differentiate the level-`1` identity, valid on the open half-line, at `z`
  have hev : (fun z' => Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z' θ') θ)
      =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter 1 F z' θ
        + α ^ 2 * (2 * z' * Work.Spaces.pzIter 2 Ψ z' θ + z' ^ 2 * Work.Spaces.pzIter 3 Ψ z' θ)
        + α * (5 + α) * (Work.Spaces.pzIter 1 Ψ z' θ + z' * Work.Spaces.pzIter 2 Ψ z' θ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact hLev1 z' hz' θ hθ0 hθ1
  have hderivEq := hev.deriv_eq
  have hL : deriv (fun z' => Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z' θ') θ) z
      = Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') θ := by
    exact (Work.FTS.EllipticEst.remov.SourceBound.Lzero1PzComm
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pz Ψ)).mp hΨ.pz) hz hθ0 hθ1).symm
  have hA : HasDerivAt (fun z' => Work.Spaces.pzIter 1 F z' θ) (Work.Spaces.pzIter 2 F z θ) z :=
    hFso.hasDerivAt_slice_pzIter 1 hθm hz
  have hT1 : HasDerivAt (fun z' : ℝ => 2 * z' * Work.Spaces.pzIter 2 Ψ z' θ)
      (2 * Work.Spaces.pzIter 2 Ψ z θ + 2 * z * Work.Spaces.pzIter 3 Ψ z θ) z := by
    have h := ((hasDerivAt_id z).const_mul 2).mul (hΨ.hasDerivAt_slice_pzIter 2 hθm hz)
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hT2 : HasDerivAt (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 3 Ψ z' θ)
      (2 * z * Work.Spaces.pzIter 3 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ) z := by
    have h := ((hasDerivAt_id z).pow 2).mul (hΨ.hasDerivAt_slice_pzIter 3 hθm hz)
    refine h.congr_deriv ?_
    norm_num
  have hT3 : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 1 Ψ z' θ
        + z' * Work.Spaces.pzIter 2 Ψ z' θ)
      (Work.Spaces.pzIter 2 Ψ z θ
        + (Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pzIter 3 Ψ z θ)) z := by
    have h := (hΨ.hasDerivAt_slice_pzIter 1 hθm hz).add
      ((hasDerivAt_id z).mul (hΨ.hasDerivAt_slice_pzIter 2 hθm hz))
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hg2 : HasDerivAt (fun z' : ℝ => α ^ 2 * (2 * z' * Work.Spaces.pzIter 2 Ψ z' θ
        + z' ^ 2 * Work.Spaces.pzIter 3 Ψ z' θ))
      (α ^ 2 * (2 * Work.Spaces.pzIter 2 Ψ z θ + 4 * z * Work.Spaces.pzIter 3 Ψ z θ
        + z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ)) z := by
    have h := (hT1.add hT2).const_mul (α ^ 2)
    refine h.congr_deriv ?_
    ring
  have hg3 : HasDerivAt (fun z' : ℝ => α * (5 + α) * (Work.Spaces.pzIter 1 Ψ z' θ
        + z' * Work.Spaces.pzIter 2 Ψ z' θ))
      (α * (5 + α) * (2 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pzIter 3 Ψ z θ)) z := by
    have h := hT3.const_mul (α * (5 + α))
    refine h.congr_deriv ?_
    ring
  have hB : HasDerivAt (fun z' => Work.Spaces.pzIter 1 F z' θ
        + α ^ 2 * (2 * z' * Work.Spaces.pzIter 2 Ψ z' θ + z' ^ 2 * Work.Spaces.pzIter 3 Ψ z' θ)
        + α * (5 + α) * (Work.Spaces.pzIter 1 Ψ z' θ + z' * Work.Spaces.pzIter 2 Ψ z' θ))
      (Work.Spaces.pzIter 2 F z θ
        + α ^ 2 * (2 * Work.Spaces.pzIter 2 Ψ z θ + 4 * z * Work.Spaces.pzIter 3 Ψ z θ
            + z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ)
        + α * (5 + α) * (2 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pzIter 3 Ψ z θ)) z := by
    have h := (hA.add hg2).add hg3
    refine h.congr_deriv ?_
    ring
  rw [← hL, hderivEq, hB.deriv]

/-! ## The requested statement -/

/-- The level-`1` and level-`2` slice identities of the weak class `WeakPos2`: differentiating the equation `bslOp α Ψ = F` one and two times in `z` and using Clairaut gives, on the open quadrant,
`Lzero1 (∂_zΨ(z,·)) = ∂_zF(z,·) + α²(2z∂_z²Ψ + z²∂_z³Ψ) + α(5+α)(∂_zΨ + z∂_z²Ψ)` and
`Lzero1 (∂_z²Ψ(z,·)) = ∂_z²F(z,·) + α²(2∂_z²Ψ + 4z∂_z³Ψ + z²∂_z⁴Ψ) + α(5+α)(2∂_z²Ψ + z∂_z³Ψ)`. -/
theorem pzIterLevelIdentities : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
        Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ
          = Work.Spaces.pzIter 1 F z θ
            + α ^ 2 * (2 * z * Work.Spaces.pzIter 2 Ψ z θ
                + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
            + α * (5 + α) * (Work.Spaces.pzIter 1 Ψ z θ
                + z * Work.Spaces.pzIter 2 Ψ z θ))
      ∧ (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
        Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') θ
          = Work.Spaces.pzIter 2 F z θ
            + α ^ 2 * (2 * Work.Spaces.pzIter 2 Ψ z θ
                + 4 * z * Work.Spaces.pzIter 3 Ψ z θ
                + z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ)
            + α * (5 + α) * (2 * Work.Spaces.pzIter 2 Ψ z θ
                + z * Work.Spaces.pzIter 3 Ψ z θ)) := by
  intro α F Ψ _ _ hW
  obtain ⟨hEq, -, -, -, -, -, hsm, -⟩ := hW
  have hLev1 : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ
        = Work.Spaces.pzIter 1 F z θ
          + α ^ 2 * (2 * z * Work.Spaces.pzIter 2 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
          + α * (5 + α) * (Work.Spaces.pzIter 1 Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ) :=
    fun z hz θ hθ0 hθ1 => levelOneIdent hsm hEq hz hθ0 hθ1
  exact ⟨hLev1, fun z hz θ hθ0 hθ1 => levelTwoIdent hsm hEq hLev1 hz hθ0 hθ1⟩

end Work.H2W.PsiSlices
