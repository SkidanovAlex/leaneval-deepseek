import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.dthU_c2m_bound6
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular jets of `c2m` up to order eight

`Work.Construction.c2m θ = cos(2θ) - sin²θ = (3cos(2θ) - 1)/2` is the angular coefficient
of the transport term.  Since `c2m` is a trigonometric polynomial of degree two and
`D_θ = sin(2θ)·∂_θ` (`Work.Spaces.dthU` in one variable), every iterate `D_θ^i c2m` with
`i ≥ 1` is `sin(2θ)²` times a polynomial in `sin(2θ)`, `cos(2θ)`; hence it is `O(sin(2θ)²)`
and a fortiori `O(sin(2θ))` on `Iθ`, where `0 ≤ sin(2θ) ≤ 1`.

This file supplies the requested `∃ C` bundle for `1 ≤ i ≤ 8`: the smoothness of `c2m` on
the open quadrant, the bound `|c2m| ≤ C` on `Iθ`, and the eight jet bounds
`|D_θ^i c2m| ≤ C·sin(2θ)` on `Iθ`.

Writing `u = sin(2θ)`, `v = cos(2θ)`, the closed forms are

* `D_θ^1 c2m = -3u²`,
* `D_θ^2 c2m = -12u²v`,
* `D_θ^3 c2m = 24u⁴ - 48u²v²`,
* `D_θ^4 c2m = 384u⁴v - 192u²v³`,
* `D_θ^5 c2m = 4224u⁴v² - 768u⁶ - 768u²v⁴`,
* `D_θ^6 c2m = 39936u⁴v³ - 26112u⁶v - 3072u²v⁵`,
* `D_θ^7 c2m = 350208u⁴v⁴ - 552960u⁶v² + 52224u⁸ - 12288u²v⁶`,
* `D_θ^8 c2m = 2949120u⁴v⁵ - 9437184u⁶v³ + 3047424u⁸v - 49152u²v⁷`,

the first four of which are `Work.FTS.Nonlinear.FstarPkg.dthU_c2m_iter_*`, the fifth and
sixth are the closed forms of `Work.FTS.StrongPersist.dthU_c2m_bound6`, and the last two are
computed here.  Every monomial in the last four has `u`-power `≥ 2`, so each is bounded by
`K·u²` with `K` the sum of the absolute values of its coefficients:

`|D_θ^5| ≤ 5760u²`, `|D_θ^6| ≤ 69120u²`, `|D_θ^7| ≤ 967680u²`, `|D_θ^8| ≤ 15482880u²`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

/-! ## Smoothness of `c2m` -/

private theorem contDiff_c2m (n : WithTop ℕ∞) : ContDiff ℝ n Work.Construction.c2m := by
  show ContDiff ℝ n (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
  exact (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub (Real.contDiff_sin.pow 2)

private theorem smoothOpen_c2m_ang :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0
  exact (contDiff_c2m Work.Stability.smoothOrder).contDiffOn.comp contDiffOn_snd
    (fun p _ => Set.mem_univ p.2)

private theorem abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq, abs_le]
  have h2 : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  constructor
  · nlinarith [Real.neg_one_le_cos (2 * θ), sq_nonneg (Real.sin θ), h2]
  · nlinarith [Real.cos_le_one (2 * θ), sq_nonneg (Real.sin θ)]

/-! ## The derivative of the fourth closed form -/

/-- `(θ ↦ 384 sin(2θ)⁴cos(2θ) - 192 sin(2θ)²cos(2θ)³)' = 4224 sin(2θ)³cos(2θ)²
- 768 sin(2θ)⁵ - 768 sin(2θ)cos(2θ)⁴`. -/
private lemma deriv_c2m_L4 (θ : ℝ) :
    deriv (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t)
        - 192 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3) θ
      = 4224 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 5
        - 768 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 4 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hc3 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 3)
      (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 3
  have hA : HasDerivAt (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t))
      ((384 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) * Real.cos (2 * θ)
        + (384 * (Real.sin (2 * θ)) ^ 4) * (-Real.sin (2 * θ) * 2)) θ :=
    (hs4.const_mul 384).mul hc
  have hB : HasDerivAt (fun t : ℝ => (192 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)
      ((192 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 3
        + (192 * (Real.sin (2 * θ)) ^ 2)
          * (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 192).mul hc3
  have hfin := hA.sub hB
  rw [show (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t)
        - 192 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)
      = ((fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t))
        - (fun t : ℝ => (192 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)) from by
    funext t; simp only [Pi.sub_apply],
    hfin.deriv]
  ring_nf

/-- `D_θ` of the fourth closed form: `D_θ^5 c2m = 4224u⁴v² - 768u⁶ - 768u²v⁴`. -/
private lemma dthU_L4_eq :
    Work.Spaces.dthU (fun θ : ℝ => (384 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
        - 192 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3)
      = fun θ : ℝ => 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
          - 768 * (Real.sin (2 * θ)) ^ 6
          - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4 := by
  funext θ
  rw [Work.Spaces.dthU_apply, deriv_c2m_L4 θ]
  ring_nf

/-! ## The derivative of the fifth closed form -/

/-- `(θ ↦ 4224 sin(2θ)⁴cos(2θ)² - 768 sin(2θ)⁶ - 768 sin(2θ)²cos(2θ)⁴)' =
39936 sin(2θ)³cos(2θ)³ - 26112 sin(2θ)⁵cos(2θ) - 3072 sin(2θ)cos(2θ)⁵`. -/
private lemma deriv_c2m_L5 (θ : ℝ) :
    deriv (fun t : ℝ => 4224 * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2
        - 768 * (Real.sin (2 * t)) ^ 6
        - 768 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4) θ
      = 39936 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 5 * Real.cos (2 * θ)
        - 3072 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 5 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hv2 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 2)
      (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 2
  have hs6 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 6)
      (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 6
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hv4 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 4)
      (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 4
  have hA : HasDerivAt (fun t : ℝ => (4224 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2)
      ((4224 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 2
        + (4224 * (Real.sin (2 * θ)) ^ 4)
          * (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs4.const_mul 4224).mul hv2
  have hB : HasDerivAt (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 6)
      (768 * (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2))) θ :=
    hs6.const_mul 768
  have hC : HasDerivAt (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)
      ((768 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 4
        + (768 * (Real.sin (2 * θ)) ^ 2)
          * (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 768).mul hv4
  have hfin := (hA.sub hB).sub hC
  rw [show (fun t : ℝ => 4224 * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2
        - 768 * (Real.sin (2 * t)) ^ 6
        - 768 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)
      = (((fun t : ℝ => (4224 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2)
          - (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 6))
        - (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)) from by
    funext t; simp only [Pi.sub_apply],
    hfin.deriv]
  ring_nf

/-- `D_θ` of the fifth closed form: `D_θ^6 c2m = 39936u⁴v³ - 26112u⁶v - 3072u²v⁵`. -/
private lemma dthU_L5_eq :
    Work.Spaces.dthU (fun θ : ℝ => 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 6
        - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4)
      = fun θ : ℝ => 39936 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
          - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
          - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5 := by
  funext θ
  rw [Work.Spaces.dthU_apply, deriv_c2m_L5 θ]
  ring_nf

/-! ## The derivative of the sixth closed form -/

/-- `(θ ↦ 39936 sin(2θ)⁴cos(2θ)³ - 26112 sin(2θ)⁶cos(2θ) - 3072 sin(2θ)²cos(2θ)⁵)' =
350208 sin(2θ)³cos(2θ)⁴ - 552960 sin(2θ)⁵cos(2θ)² + 52224 sin(2θ)⁷
- 12288 sin(2θ)cos(2θ)⁶`. -/
private lemma deriv_c2m_L6 (θ : ℝ) :
    deriv (fun t : ℝ => (39936 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 3
        - 26112 * (Real.sin (2 * t)) ^ 6 * Real.cos (2 * t)
        - 3072 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 5) θ
      = 350208 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 4
        - 552960 * (Real.sin (2 * θ)) ^ 5 * (Real.cos (2 * θ)) ^ 2
        + 52224 * (Real.sin (2 * θ)) ^ 7
        - 12288 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 6 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hc3 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 3)
      (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 3
  have hs6 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 6)
      (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 6
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hc5 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 5)
      (5 * (Real.cos (2 * θ)) ^ (5 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 5
  have hA : HasDerivAt (fun t : ℝ => (39936 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 3)
      ((39936 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 3
        + (39936 * (Real.sin (2 * θ)) ^ 4)
          * (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs4.const_mul 39936).mul hc3
  have hB : HasDerivAt (fun t : ℝ => (26112 : ℝ) * (Real.sin (2 * t)) ^ 6 * Real.cos (2 * t))
      ((26112 * (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2))) * Real.cos (2 * θ)
        + (26112 * (Real.sin (2 * θ)) ^ 6) * (-Real.sin (2 * θ) * 2)) θ :=
    (hs6.const_mul 26112).mul hc
  have hC : HasDerivAt (fun t : ℝ => (3072 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 5)
      ((3072 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 5
        + (3072 * (Real.sin (2 * θ)) ^ 2)
          * (5 * (Real.cos (2 * θ)) ^ (5 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 3072).mul hc5
  have hfin := (hA.sub hB).sub hC
  have hfun : (fun t : ℝ => (39936 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 3
        - 26112 * (Real.sin (2 * t)) ^ 6 * Real.cos (2 * t)
        - 3072 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 5)
      = (((fun t : ℝ => (39936 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 3)
          - (fun t : ℝ => (26112 : ℝ) * (Real.sin (2 * t)) ^ 6 * Real.cos (2 * t)))
        - (fun t : ℝ => (3072 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 5)) := by
    funext t; simp only [Pi.sub_apply]
  rw [hfun, hfin.deriv]
  ring_nf

/-- `D_θ` of the sixth closed form:
`D_θ^7 c2m = 350208u⁴v⁴ - 552960u⁶v² + 52224u⁸ - 12288u²v⁶`. -/
private lemma dthU_L6_eq :
    Work.Spaces.dthU (fun θ : ℝ => (39936 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
        - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5)
      = fun θ : ℝ => 350208 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 4
          - 552960 * (Real.sin (2 * θ)) ^ 6 * (Real.cos (2 * θ)) ^ 2
          + 52224 * (Real.sin (2 * θ)) ^ 8
          - 12288 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 6 := by
  funext θ
  rw [Work.Spaces.dthU_apply, deriv_c2m_L6 θ]
  ring_nf

/-! ## The derivative of the seventh closed form -/

/-- `(θ ↦ 350208 sin(2θ)⁴cos(2θ)⁴ - 552960 sin(2θ)⁶cos(2θ)² + 52224 sin(2θ)⁸
- 12288 sin(2θ)²cos(2θ)⁶)' = 2949120 sin(2θ)³cos(2θ)⁵ - 9437184 sin(2θ)⁵cos(2θ)³
+ 3047424 sin(2θ)⁷cos(2θ) - 49152 sin(2θ)cos(2θ)⁷`. -/
private lemma deriv_c2m_L7 (θ : ℝ) :
    deriv (fun t : ℝ => (350208 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 4
        - 552960 * (Real.sin (2 * t)) ^ 6 * (Real.cos (2 * t)) ^ 2
        + 52224 * (Real.sin (2 * t)) ^ 8
        - 12288 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 6) θ
      = 2949120 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 5
        - 9437184 * (Real.sin (2 * θ)) ^ 5 * (Real.cos (2 * θ)) ^ 3
        + 3047424 * (Real.sin (2 * θ)) ^ 7 * Real.cos (2 * θ)
        - 49152 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 7 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hc4 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 4)
      (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 4
  have hs6 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 6)
      (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 6
  have hc2 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 2)
      (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 2
  have hs8 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 8)
      (8 * (Real.sin (2 * θ)) ^ (8 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 8
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hc6 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 6)
      (6 * (Real.cos (2 * θ)) ^ (6 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 6
  have hA : HasDerivAt
      (fun t : ℝ => (350208 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 4)
      ((350208 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)))
          * (Real.cos (2 * θ)) ^ 4
        + (350208 * (Real.sin (2 * θ)) ^ 4)
          * (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs4.const_mul 350208).mul hc4
  have hB : HasDerivAt
      (fun t : ℝ => (552960 : ℝ) * (Real.sin (2 * t)) ^ 6 * (Real.cos (2 * t)) ^ 2)
      ((552960 * (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2)))
          * (Real.cos (2 * θ)) ^ 2
        + (552960 * (Real.sin (2 * θ)) ^ 6)
          * (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs6.const_mul 552960).mul hc2
  have hC : HasDerivAt (fun t : ℝ => (52224 : ℝ) * (Real.sin (2 * t)) ^ 8)
      (52224 * (8 * (Real.sin (2 * θ)) ^ (8 - 1) * (Real.cos (2 * θ) * 2))) θ :=
    hs8.const_mul 52224
  have hD : HasDerivAt
      (fun t : ℝ => (12288 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 6)
      ((12288 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)))
          * (Real.cos (2 * θ)) ^ 6
        + (12288 * (Real.sin (2 * θ)) ^ 2)
          * (6 * (Real.cos (2 * θ)) ^ (6 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 12288).mul hc6
  have hfin := ((hA.sub hB).add hC).sub hD
  have hfun : (fun t : ℝ => (350208 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 4
        - 552960 * (Real.sin (2 * t)) ^ 6 * (Real.cos (2 * t)) ^ 2
        + 52224 * (Real.sin (2 * t)) ^ 8
        - 12288 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 6)
      = ((((fun t : ℝ => (350208 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 4)
          - (fun t : ℝ => (552960 : ℝ) * (Real.sin (2 * t)) ^ 6 * (Real.cos (2 * t)) ^ 2))
        + (fun t : ℝ => (52224 : ℝ) * (Real.sin (2 * t)) ^ 8))
        - (fun t : ℝ => (12288 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 6)) := by
    funext t; simp only [Pi.sub_apply, Pi.add_apply]
  rw [hfun, hfin.deriv]
  ring_nf

/-- `D_θ` of the seventh closed form:
`D_θ^8 c2m = 2949120u⁴v⁵ - 9437184u⁶v³ + 3047424u⁸v - 49152u²v⁷`. -/
private lemma dthU_L7_eq :
    Work.Spaces.dthU (fun θ : ℝ =>
          (350208 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 4
        - 552960 * (Real.sin (2 * θ)) ^ 6 * (Real.cos (2 * θ)) ^ 2
        + 52224 * (Real.sin (2 * θ)) ^ 8
        - 12288 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 6)
      = fun θ : ℝ => 2949120 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 5
          - 9437184 * (Real.sin (2 * θ)) ^ 6 * (Real.cos (2 * θ)) ^ 3
          + 3047424 * (Real.sin (2 * θ)) ^ 8 * Real.cos (2 * θ)
          - 49152 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 7 := by
  funext θ
  rw [Work.Spaces.dthU_apply, deriv_c2m_L7 θ]
  ring_nf

/-! ## The iterates, as values -/

/-- `D_θ^5 c2m = 4224u⁴v² - 768u⁶ - 768u²v⁴`. -/
private lemma iter_five_pt (θ : ℝ) :
    (Work.Spaces.dthU^[5]) Work.Construction.c2m θ
      = 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 6
        - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply',
    show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f1_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f2_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f3_eq,
    dthU_L4_eq]

/-- `D_θ^6 c2m = 39936u⁴v³ - 26112u⁶v - 3072u²v⁵`. -/
private lemma iter_six_pt (θ : ℝ) :
    (Work.Spaces.dthU^[6]) Work.Construction.c2m θ
      = 39936 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
        - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, Function.iterate_succ_apply',
    show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply',
    show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f1_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f2_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f3_eq,
    dthU_L4_eq, dthU_L5_eq]

/-- `D_θ^7 c2m = 350208u⁴v⁴ - 552960u⁶v² + 52224u⁸ - 12288u²v⁶`. -/
private lemma iter_seven_pt (θ : ℝ) :
    (Work.Spaces.dthU^[7]) Work.Construction.c2m θ
      = 350208 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 4
        - 552960 * (Real.sin (2 * θ)) ^ 6 * (Real.cos (2 * θ)) ^ 2
        + 52224 * (Real.sin (2 * θ)) ^ 8
        - 12288 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 6 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_succ_apply',
    show (6 : ℕ) = 5 + 1 from rfl, Function.iterate_succ_apply',
    show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply',
    show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f1_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f2_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f3_eq,
    dthU_L4_eq, dthU_L5_eq, dthU_L6_eq]

/-- `D_θ^8 c2m = 2949120u⁴v⁵ - 9437184u⁶v³ + 3047424u⁸v - 49152u²v⁷`. -/
private lemma iter_eight_pt (θ : ℝ) :
    (Work.Spaces.dthU^[8]) Work.Construction.c2m θ
      = 2949120 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 5
        - 9437184 * (Real.sin (2 * θ)) ^ 6 * (Real.cos (2 * θ)) ^ 3
        + 3047424 * (Real.sin (2 * θ)) ^ 8 * Real.cos (2 * θ)
        - 49152 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 7 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, Function.iterate_succ_apply',
    show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_succ_apply',
    show (6 : ℕ) = 5 + 1 from rfl, Function.iterate_succ_apply',
    show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply',
    show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f1_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f2_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f3_eq,
    dthU_L4_eq, dthU_L5_eq, dthU_L6_eq, dthU_L7_eq]

/-! ## The monomial bound and the four jet bounds -/

/-- A monomial `K·s^a·c^b` with `a ≥ 2` and `|s|, |c| ≤ 1` is bounded by `K·s²`. -/
private lemma monomial_sq_le {K s c : ℝ} (hK : 0 ≤ K) (hs : |s| ≤ 1) (hc : |c| ≤ 1)
    {a b : ℕ} (ha : 2 ≤ a) : |K * s ^ a * c ^ b| ≤ K * s ^ 2 := by
  have hsa : |s| ^ a ≤ |s| ^ 2 := pow_le_pow_of_le_one (abs_nonneg s) hs ha
  have hcb : |c| ^ b ≤ 1 := pow_le_one₀ (abs_nonneg c) hc
  have hmul : |s| ^ a * |c| ^ b ≤ |s| ^ 2 * 1 :=
    mul_le_mul hsa hcb (pow_nonneg (abs_nonneg c) b) (pow_nonneg (abs_nonneg s) 2)
  calc |K * s ^ a * c ^ b| = K * (|s| ^ a * |c| ^ b) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hK, abs_pow, abs_pow]; ring
    _ ≤ K * (|s| ^ 2 * 1) := mul_le_mul_of_nonneg_left hmul hK
    _ = K * s ^ 2 := by rw [sq_abs]; ring

/-- The `c = 1` case of `monomial_sq_le`: `|K·s^a| ≤ K·s²` for `a ≥ 2`. -/
private lemma monomial_sq_le' {K s : ℝ} (hK : 0 ≤ K) (hs : |s| ≤ 1)
    {a : ℕ} (ha : 2 ≤ a) : |K * s ^ a| ≤ K * s ^ 2 := by
  simpa using monomial_sq_le (K := K) (c := (1 : ℝ)) hK hs (by norm_num) (a := a) (b := 0) ha

/-- `|D_θ^5 c2m| ≤ 5760·sin(2θ)²`. -/
private lemma iter_five_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[5]) Work.Construction.c2m θ|
      ≤ 5760 * (Real.sin (2 * θ)) ^ 2 := by
  rw [iter_five_pt θ]
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h1 := monomial_sq_le (K := (4224 : ℝ)) (by norm_num) hs hc (a := 4) (b := 2) (by norm_num)
  have h2 := monomial_sq_le' (K := (768 : ℝ)) (by norm_num) hs (a := 6) (by norm_num)
  have h3 := monomial_sq_le (K := (768 : ℝ)) (by norm_num) hs hc (a := 2) (b := 4) (by norm_num)
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- `|D_θ^6 c2m| ≤ 69120·sin(2θ)²`. -/
private lemma iter_six_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[6]) Work.Construction.c2m θ|
      ≤ 69120 * (Real.sin (2 * θ)) ^ 2 := by
  rw [iter_six_pt θ]
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h1 := monomial_sq_le (K := (39936 : ℝ)) (by norm_num) hs hc (a := 4) (b := 3) (by norm_num)
  have h2 := monomial_sq_le (K := (26112 : ℝ)) (by norm_num) hs hc (a := 6) (b := 1) (by norm_num)
  have h3 := monomial_sq_le (K := (3072 : ℝ)) (by norm_num) hs hc (a := 2) (b := 5) (by norm_num)
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- `|D_θ^7 c2m| ≤ 967680·sin(2θ)²`. -/
private lemma iter_seven_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[7]) Work.Construction.c2m θ|
      ≤ 967680 * (Real.sin (2 * θ)) ^ 2 := by
  rw [iter_seven_pt θ]
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h1 := monomial_sq_le (K := (350208 : ℝ)) (by norm_num) hs hc (a := 4) (b := 4) (by norm_num)
  have h2 := monomial_sq_le (K := (552960 : ℝ)) (by norm_num) hs hc (a := 6) (b := 2) (by norm_num)
  have h3 := monomial_sq_le' (K := (52224 : ℝ)) (by norm_num) hs (a := 8) (by norm_num)
  have h4 := monomial_sq_le (K := (12288 : ℝ)) (by norm_num) hs hc (a := 2) (b := 6) (by norm_num)
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

/-- `|D_θ^8 c2m| ≤ 15482880·sin(2θ)²`. -/
private lemma iter_eight_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[8]) Work.Construction.c2m θ|
      ≤ 15482880 * (Real.sin (2 * θ)) ^ 2 := by
  rw [iter_eight_pt θ]
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h1 := monomial_sq_le (K := (2949120 : ℝ)) (by norm_num) hs hc (a := 4) (b := 5) (by norm_num)
  have h2 := monomial_sq_le (K := (9437184 : ℝ)) (by norm_num) hs hc (a := 6) (b := 3) (by norm_num)
  have h3 := monomial_sq_le (K := (3047424 : ℝ)) (by norm_num) hs hc (a := 8) (b := 1) (by norm_num)
  have h4 := monomial_sq_le (K := (49152 : ℝ)) (by norm_num) hs hc (a := 2) (b := 7) (by norm_num)
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

/-! ## The assembly -/

/-- From `|X| ≤ K·s²` with `0 ≤ s ≤ 1`, `0 ≤ K` and `K ≤ C` conclude `|X| ≤ C·s`. -/
private lemma le_bound_of_sq_le_bound {X s K C : ℝ} (h : |X| ≤ K * s ^ 2)
    (hK : 0 ≤ K) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hKC : K ≤ C) : |X| ≤ C * s := by
  have hsq : s ^ 2 ≤ s := by
    have h1 := mul_nonneg hs0 (sub_nonneg.mpr hs1)
    nlinarith [h1]
  calc |X| ≤ K * s ^ 2 := h
    _ ≤ K * s := mul_le_mul_of_nonneg_left hsq hK
    _ ≤ C * s := mul_le_mul_of_nonneg_right hKC hs0

theorem c2mJets : ∃ C : ℝ, 0 < C ∧
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Work.Construction.c2m θ) ∧
    (∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ C) ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ 8 → ∀ (z θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        ≤ C * Real.sin (2 * θ) := by
  obtain ⟨C6, hC6pos, hC6⟩ := Work.FTS.StrongPersist.dthU_c2m_bound6
  refine ⟨max C6 15482880, lt_max_of_lt_right (by norm_num), smoothOpen_c2m_ang, ?_, ?_⟩
  · intro θ _
    exact le_trans (le_trans (abs_c2m_le_two θ) (by norm_num : (2 : ℝ) ≤ 15482880))
      (le_max_right C6 15482880)
  · intro i hi1 hi8 z θ hθ
    rw [Work.FTS.LocData.DthIter_rad_eq i Work.Construction.c2m z θ]
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    by_cases h6 : i ≤ 6
    · exact le_bound_of_sq_le_bound (hC6 i hi1 h6 θ) hC6pos.le hs0 hs1 (le_max_left C6 15482880)
    · have hi78 : i = 7 ∨ i = 8 := by omega
      rcases hi78 with rfl | rfl
      · refine le_bound_of_sq_le_bound (iter_seven_bound θ) (by norm_num) hs0 hs1 ?_
        exact le_trans (by norm_num : (967680 : ℝ) ≤ 15482880) (le_max_right C6 15482880)
      · exact le_bound_of_sq_le_bound (iter_eight_bound θ) (by norm_num) hs0 hs1
          (le_max_right C6 15482880)

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
