/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/VopAux/vopTraces_classC` — the angular traces of the radial iterates of `Ξ`

Target: `Work.FTS.ClassC.VopAux.vopTraces_classC`.  For `0 < α ≤ 1/4`, `g` of the linear class
`C` (`ClassC α g`) and a level-`7` stream function `Ψ` (`EllClassOk 7 α g Ψ`), the angular
slices of the radial iterates `D_z^j Ξ` of the elliptic residual
`Ξ = EllResid α g Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(g)` vanish at the two endpoints of `(0, π/2)`,
for every `j ≤ 6`, for almost every `z > 0` (in fact for every `z > 0`).

## Route

Write `Ψ̂ := shiftSing α g Ψ = Ψ + Gsing α g · sin 2θ` for the *straight* unknown, so that
`Ξ = Ψ̂ - Ḡ(α,g)·sin 2θ` (`EllResid_eq_ellShift_sub_Gbar_point`, `EllSol/ropBasic`).  On the
open quadrant

  `D_z^j Ξ = D_z^j Ψ̂ + (rDzIter j (-Ḡ(α,g)))(z)·sin 2θ`

(additivity of the iterated radial operator `DzIter_add_on_Q0` — proved here — together with the
unconditional separated-product rule `DzIter_mul_of_radial`).  The second summand is a constant
in `θ` times `sin 2θ`, hence tends to `0` at both endpoints.

The first summand is handled by the `D_z`-shift of the weak class: `EllClassOk 7 α g Ψ` carries
`EllWeakPos α 7 (orthSource g) Ψ̂`, and `j ≤ 6` shifts
(`Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le`, iterated here in
`ellWeakPos_dzIter_shift_classC`) give

  `EllWeakPos α (7-j) (D_z^j (orthSource g)) (D_z^j Ψ̂)`,   `7 - j ≥ 1`.

For a datum `EllWeakPos α k F Ψ` with `k ≥ 1`, `VthAux.AeClean.sliceContinuous_of_weakPos_fts`
shows that the slice `θ ↦ Ψ(z,θ)` is continuous on the *closed* interval `Iθ` for **every**
`z > 0`; the shifted datum also carries the endpoint *values* `D_z^j Ψ̂(z,0) = D_z^j Ψ̂(z,π/2) = 0`
(`EllWeakPos.zero`, `EllWeakPos.pi_half`), so the two one-sided limits are `0`.  This is
pointwise in `z`; the `∀ᵐ z` of the statement is a weakening.

All the ingredients are proved in the workspace and the proof rests on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.ClassC.pth_Vop_EllResid_classC
import Submission.Work.FTS.EllSol.VthAux.AeClean.SliceThree
import Submission.Work.FTS.EllipticEst.Cores.Repair.DzShift
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.FTS.EllSol.ropBasic

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

/-! ## Two elementary transfer lemmas: continuity on the closed interval gives the two
endpoint limits -/

/-- **Left endpoint.**  A function continuous on the closed interval `[0, π/2]` and vanishing at
`0` tends to `0` as `θ → 0⁺`. -/
theorem tendsto_zero_nhdsGT_of_continuousOn_Icc {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) :
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h1 : ContinuousWithinAt f (Set.Icc 0 (Real.pi / 2)) 0 :=
    hf.continuousWithinAt (Set.left_mem_Icc.mpr (by positivity))
  have h2 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Icc 0 (Real.pi / 2)))
      (nhds (f 0)) := h1
  rw [h0] at h2
  rw [nhdsWithin_Icc_eq_nhdsGE (by positivity : (0 : ℝ) < Real.pi / 2)] at h2
  exact h2.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

/-- **Right endpoint.**  The analogue at `π/2`. -/
theorem tendsto_zero_nhdsLT_pi_half_of_continuousOn_Icc {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (hp : f (Real.pi / 2) = 0) :
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have h1 : ContinuousWithinAt f (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2) :=
    hf.continuousWithinAt (Set.right_mem_Icc.mpr (by positivity))
  have h2 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2)))
      (nhds (f (Real.pi / 2))) := h1
  rw [hp] at h2
  rw [nhdsWithin_Icc_eq_nhdsLE (by positivity : (0 : ℝ) < Real.pi / 2)] at h2
  exact h2.mono_left (nhdsWithin_mono _ Set.Iio_subset_Iic_self)

/-- A constant times `sin 2θ` tends to `0` at the two endpoints of `(0, π/2)`. -/
theorem tendsto_zero_const_mul_sin_two (c : ℝ) :
    Filter.Tendsto (fun θ : ℝ => c * Real.sin (2 * θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ : ℝ => c * Real.sin (2 * θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
  have hleft : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := hcont.continuousAt (x := 0)
    have h' : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhds (0 : ℝ))
        (nhds (Real.sin (2 * 0))) := h
    rw [show Real.sin (2 * 0) = 0 by norm_num] at h'
    exact h'.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hright : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have h := hcont.continuousAt (x := Real.pi / 2)
    have h' : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhds (Real.pi / 2))
        (nhds (Real.sin (2 * (Real.pi / 2)))) := h
    rw [hsin] at h'
    exact h'.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))
  exact ⟨by simpa using hleft.const_mul c, by simpa using hright.const_mul c⟩

/-! ## Additivity of the iterated radial operator on the open quadrant -/

/-- `D_z^j (f + g) = D_z^j f + D_z^j g` at every point of the open quadrant, for `f, g` of class
`C^∞` there. -/
theorem DzIter_add_on_Q0 (j : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  induction j with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        ((hf.DzIter n).hasDerivAt_slice hθ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        ((hg.DzIter n).hasDerivAt_slice hθ hz).differentiableAt
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]
      rw [show (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ)
          = (fun z' => Work.Spaces.DzIter n f z' θ)
            + (fun z' => Work.Spaces.DzIter n g z' θ) from rfl, deriv_add hd1 hd2]
      ring

/-! ## The `D_z`-shift of the weak class, iterated -/

/-- **The iterated radial shift of the weak class.**  From a datum of `EllWeakPos α k F Ψ` with
`k ≥ 1` one obtains, for every `j ≤ k-1`, a datum of the same class at level `k - j` for the
`j`-fold radial iterate `D_z^j`.  The single-step shift is
`Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le` (which needs level `≥ 2`); the composition
`D_z (D_z^j ·) = D_z^{j+1} ·` is `Work.Spaces.DzIter_add_right`. -/
theorem ellWeakPos_dzIter_shift_classC {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ j, j ≤ k - 1 → Work.FTS.EllipticEst.TT.EllWeakPos α (k - j)
      (Work.Spaces.DzIter j F) (Work.Spaces.DzIter j Ψ) := by
  intro j
  induction j with
  | zero => intro _; simpa using h
  | succ n ih =>
      intro hn
      have hn' : n ≤ k - 1 := by omega
      have hk2 : 2 ≤ k - n := by omega
      have h1 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
        (α := α) (k := k - n) hk2 (ih hn')
      have hlev : k - n - 1 = k - (n + 1) := by omega
      have hF : Work.Spaces.DzIter 1 (Work.Spaces.DzIter n F)
          = Work.Spaces.DzIter (n + 1) F := by
        rw [← Work.Spaces.DzIter_add_right 1 n F, Nat.add_comm 1 n]
      have hP : Work.Spaces.DzIter 1 (Work.Spaces.DzIter n Ψ)
          = Work.Spaces.DzIter (n + 1) Ψ := by
        rw [← Work.Spaces.DzIter_add_right 1 n Ψ, Nat.add_comm 1 n]
      rw [hF, hP, hlev] at h1
      exact h1

/-! ## The target -/

theorem vopTraces_classC (j : ℕ) (hj : j ≤ 6) :
    ∀ (α : ℝ) (g Ψ : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.ClassC.ClassC α g → Work.FTS.EllExist.EllClassOk 7 α g Ψ →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro α g Ψ hα hα4 hC hO
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
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet (Set.Ioi (0 : ℝ)) from measurableSet_Ioi)] with z hz
  have hzpos : 0 < z := hz
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
