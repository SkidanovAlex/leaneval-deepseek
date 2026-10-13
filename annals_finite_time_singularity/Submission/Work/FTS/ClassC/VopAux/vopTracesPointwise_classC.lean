/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/VopAux/vopTracesPointwise_classC` — the angular traces of the radial iterates of `Ξ`

Target: `Work.FTS.ClassC.VopAux.vopTracesPointwise_classC`.  For `0 < α ≤ 1/4`, `g` of the
linear class `C` (`ClassC α g`) and a level-`7` stream function `Ψ` (`EllClassOk 7 α g Ψ`), the
angular slices of the radial iterates `D_z^j Ξ` of the elliptic residual
`Ξ = EllResid α g Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(g)` vanish at the two endpoints of `(0, π/2)`,
for every `j ≤ 6` and **every** `z > 0`.

This is the pointwise-in-`z` strengthening of `Work.FTS.ClassC.VopAux.vopTraces_classC`, whose
proof is in fact pointwise in `z` (the `∀ᵐ z` of that statement is a weakening); the present file
records the sharp form and reuses, from that module, the elementary transfer lemmas
(`tendsto_zero_nhdsGT_of_continuousOn_Icc`, `tendsto_zero_nhdsLT_pi_half_of_continuousOn_Icc`,
`tendsto_zero_const_mul_sin_two`), the pointwise additivity `DzIter_add_on_Q0` of the iterated
radial operator on the open quadrant, and the iterated radial shift
`ellWeakPos_dzIter_shift_classC` of the weak class.

## Route

Write `Ψ̂ := shiftSing α g Ψ = Ψ + Gsing α g · sin 2θ` for the *straight* unknown, so that
`Ξ = Ψ̂ - Ḡ(α,g)·sin 2θ` (`EllResid_eq_ellShift_sub_Gbar_point`, `EllSol/ropBasic`).  On the open
quadrant

  `D_z^j Ξ = D_z^j Ψ̂ + (rDzIter j (-Ḡ(α,g)))(z)·sin 2θ`

(additivity `DzIter_add_on_Q0` together with the unconditional separated-product rule
`DzIter_mul_of_radial`).  The second summand is a constant in `θ` times `sin 2θ`, hence tends to
`0` at both endpoints.

The first summand is handled by the `D_z`-shift of the weak class: `EllClassOk 7 α g Ψ` carries
`EllWeakPos α 7 (orthSource g) Ψ̂`, and `j ≤ 6` shifts
(`Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le`, iterated in
`ellWeakPos_dzIter_shift_classC`) give

  `EllWeakPos α (7-j) (D_z^j (orthSource g)) (D_z^j Ψ̂)`,   `7 - j ≥ 1`.

For a datum `EllWeakPos α k F Ψ` with `k ≥ 1`, `VthAux.AeClean.sliceContinuous_of_weakPos_fts`
shows that the slice `θ ↦ Ψ(z,θ)` is continuous on the *closed* interval `Iθ` for **every**
`z > 0`; the shifted datum also carries the pointwise endpoint *values*
`D_z^j Ψ̂(z,0) = D_z^j Ψ̂(z,π/2) = 0` (`EllWeakPos.zero`, `EllWeakPos.pi_half`), so the two
one-sided limits are `0`.

The proof rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.ClassC.VopAux.vopTraces_classC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The angular traces of the radial iterates of `Ξ`**, pointwise in `z`. -/
theorem vopTracesPointwise_classC (j : ℕ) (hj : j ≤ 6) :
    ∀ (α : ℝ) (g Ψ : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.ClassC.ClassC α g → Work.FTS.EllExist.EllClassOk 7 α g Ψ →
      ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro α g Ψ hα hα4 hC hO z hz
  have hzpos : 0 < z := hz
  -- the straight unknown `Ψ̂ = shiftSing α g Ψ` and its level-`7` weak class
  have hweak : Work.FTS.EllipticEst.TT.EllWeakPos α 7 (Work.Elliptic.orthSource g)
      (Work.FTS.EllExist.shiftSing α g Ψ) := hO.2.2
  have hshift := ellWeakPos_dzIter_shift_classC (α := α) (F := Work.Elliptic.orthSource g)
    (Ψ := Work.FTS.EllExist.shiftSing α g Ψ) (k := 7) (by norm_num) hweak j (by omega)
  have hPsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllExist.shiftSing α g Ψ) :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen hweak
  have hCsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ)) := by
    have hL := Work.FTS.ClassC.smoothOpen_GbarSin_classC (α := α) (g := g) hα hC.reg hC.fsm
      hC.mem
    refine Work.FTS.EllipticEst.SmoothOpen.congr (hL.const_mul' (-1)) ?_
    intro z θ _ _ _
    ring
  -- the functional identity `Ξ = Ψ̂ - Ḡ(α,g)·sin 2θ`
  have hfun : Work.Elliptic.EllResid α g Ψ
      = fun z θ => Work.FTS.EllExist.shiftSing α g Ψ z θ
          + (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ) := by
    funext z θ
    rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point]
    simp only [Work.FTS.EllExist.shiftSing]
    ring
  -- the pointwise decomposition of the radial iterates on the open quadrant
  have hdecomp : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ) := by
    intro z θ hz h1 h2
    rw [hfun]
    rw [DzIter_add_on_Q0 j hPsm hCsm z θ hz h1 h2]
    rw [Work.FTS.EllipticEst.DzIter_mul_of_radial j (fun z => -(Work.Elliptic.Gbar α g z))
      (fun θ => Real.sin (2 * θ)) z θ]
  -- continuity of the slice of `D_z^j Ψ̂` on the closed interval, and its endpoint values
  have hkj : 1 ≤ 7 - j := by omega
  have hcont := Work.FTS.EllSol.VthAux.AeClean.sliceContinuous_of_weakPos_fts (7 - j) hkj α
    (Work.Spaces.DzIter j (Work.Elliptic.orthSource g))
    (Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ)) hα hshift z hzpos
  have h0 : Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z 0 = 0 := hshift.zero z
  have hp : Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z (Real.pi / 2) = 0 :=
    hshift.pi_half z
  have htl : Filter.Tendsto (fun θ : ℝ =>
      Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_zero_nhdsGT_of_continuousOn_Icc hcont h0
  have htr : Filter.Tendsto (fun θ : ℝ =>
      Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    tendsto_zero_nhdsLT_pi_half_of_continuousOn_Icc hcont hp
  obtain ⟨hcl, hcr⟩ := tendsto_zero_const_mul_sin_two
    (Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z)
  -- the two eventual equalities, on the two one-sided filters
  have hev0 : (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ
        + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
            * Real.sin (2 * θ)) := by
    change ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity)] with θ hθ hθmem
    exact hdecomp z θ hzpos hθmem hθ
  have hev1 : (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ)
      =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ
        + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
            * Real.sin (2 * θ)) := by
    change ∀ᶠ θ : ℝ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity)] with θ hθ hθmem
    exact hdecomp z θ hzpos hθ hθmem
  exact ⟨Filter.Tendsto.congr' hev0.symm (by simpa using htl.add hcl),
    Filter.Tendsto.congr' hev1.symm (by simpa using htr.add hcr)⟩

end Work.FTS.ClassC.VopAux
