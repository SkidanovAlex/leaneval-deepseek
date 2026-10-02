/-
# The region of a ray polygon lies below the potential level `log R`

Let `ps` be an admissible list of co-landing pairs of rays of the dynamical plane of `T_c` and
let `1 < R`.  The ray polygon `Work.EL.polyCurve ps R` is the boundary of the region
`Work.EL.polyRegion ps R`: it consists of the ray pieces of the `2m` angles of `ps` up to the
level `R`, the landing points, and the equipotential arcs at level `R` through the *near* arcs.

This file proves that the whole region lies in the open sublevel set `{pot < log R}` of the
potential.  The argument is a local one, at the reference point

`p = rayPt hN (midNear ps) R`

of the polygon (the point of the equipotential arc through the *near* arc that follows the first
pair), and it uses the box

`B = {z ∉ K c | |(rayRot (midNear ps) (Φ z)).re - R| < a₀, |(rayRot (midNear ps) (Φ z)).im| < b₀}`

in the rotated Böttcher plane, for suitably small `a₀, b₀ > 0` (supplied by
`Work.ELTop.box_angular_thin`): a point of `B` which is not on the polygon has its external angle
within a small window of `midNear ps` (modulo `1`), so it lies on no ray of the polygon, and it
lies on no equipotential arc of the polygon either.  Hence

* `P = B ∩ {pot < log R}` and `Q = B ∩ {log R < pot}` are preconnected (images of convex boxes,
  via the homeomorphism `hN.e`), both avoid the polygon, and their union covers `B ∖ polyCurve`;
* `Q` meets the unbounded side `O` of the polygon (points of potential above `log R` are in `O`),
  while `p ∈ B ∩ polyCurve`;

so `Work.Top.Sides.sides_of_halves` places `P` in the bounded side `S.I`.  Since the inner piece
of the reference ray (levels in `(1,R)`) lies in both `P` and `polyRegion`, the region is
contained in `S.I`.  But every point of potential `≥ log R` lies in the *unbounded* side:
`{log R < pot} ⊆ O` (`Work.ELTop.gt_potential_subset_sidesO`) and `{pot = log R} ∩ polyCurveᶜ ⊆ O`
(`Work.ELTop.level_eq_subset_sidesO`).  The two sides are disjoint, so the region is contained in
`{pot < log R}`.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.notInArc_midNear
import Submission.Work.ELTop.notInArc_window_midNear
import Submission.Work.ELTop.level_eq_subset_sidesO
import Submission.Work.ELTop.gt_potential_subset_sidesO
import Submission.Work.ELTop.innerRay_subset_polyRegion
import Submission.Work.ELTop.box_angular_thin
import Submission.Work.Top.Jordan
import Submission.Work.Top.extAngle_rayPt
import Submission.Work.Top.reIm_box_inter_ball
import Submission.Work.Top.reIm_box_inter_exterior
import Submission.Work.Top.Phi_eq_norm_mul_exp_extAngle
import Submission.Work.ParamRays.isClosed_filledJulia

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ}

/- The auxiliary lemmas below are collected in a namespace of their own so that their names
cannot clash with the (many) helpers of the same shape that other files of the area define. -/
namespace PotLtAux

/-! ## Elementary angle arithmetic -/

/-- `InArc` depends on the angle only modulo `ℤ`. -/
theorem InArc_add_int (θ : ℝ) (k : ℤ) (a b : ℝ) :
    Work.EL.InArc (θ + (k : ℝ)) a b ↔ Work.EL.InArc θ a b := by
  have h : θ + (k : ℝ) - a = (θ - a) + (k : ℝ) := by ring
  unfold Work.EL.InArc
  rw [h, Int.fract_add_intCast]

/-- A point of a parameter ray has external angle the angle of the ray, modulo `ℤ`. -/
theorem exists_int_extAngle_paramRay (hN : Work.EL.DynB c φ) {β : ℝ} {z : ℂ}
    (hz : z ∈ Work.EL.paramRay hN β) :
    ∃ k : ℤ, Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z = β + (k : ℝ) := by
  obtain ⟨hzK, t, ht, hΦ⟩ := hz
  have hzt : z = Work.EL.rayPt hN β t := by
    refine hN.injOn_Phi hzK (Work.EL.rayPt_notMem_K hN ht) ?_
    rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht]
  rw [hzt]
  have hshift : Work.EL.rayPt hN β t = Work.EL.rayPt hN (Int.fract β) t := by
    have h := Work.ELTop.rayPt_add_int hN (Int.fract β) t (⌊β⌋ : ℤ)
    rw [Int.fract_add_floor] at h
    exact h
  rw [hshift]
  refine ⟨-(⌊β⌋ : ℤ), ?_⟩
  rw [Work.Top.extAngle_rayPt hN (Int.fract_nonneg β) (Int.fract_lt_one β) ht,
    show (((-(⌊β⌋ : ℤ)) : ℤ) : ℝ) = -((⌊β⌋ : ℤ) : ℝ) from by push_cast; ring]
  linarith [Int.fract_add_floor β]

/-! ## The sublevel and superlevel sets of the potential -/

theorem pot_lt_iff_norm_lt (hN : Work.EL.DynB c φ) {R : ℝ} (hR : 1 < R) {z : ℂ}
    (hzK : z ∉ Work.EL.K c) : Work.EL.pot hN z < Real.log R ↔ ‖Work.EL.dynPhi c φ z‖ < R := by
  rw [Work.EL.pot_of_notMem hN hzK]
  exact Real.log_lt_log_iff (lt_trans zero_lt_one (hN.Phi_mem_exteriorDisc hzK))
    (lt_trans zero_lt_one hR)

theorem log_lt_pot_iff_norm_lt (hN : Work.EL.DynB c φ) {R : ℝ} (hR : 1 < R) {z : ℂ}
    (hzK : z ∉ Work.EL.K c) : Real.log R < Work.EL.pot hN z ↔ R < ‖Work.EL.dynPhi c φ z‖ := by
  rw [Work.EL.pot_of_notMem hN hzK]
  exact Real.log_lt_log_iff (lt_trans zero_lt_one hR)
    (lt_trans zero_lt_one (hN.Phi_mem_exteriorDisc hzK))

/-! ## Preconnectedness of the pull-backs of the boxes along the Böttcher coordinate -/

/-- The `Φ`-preimage of a preconnected set of the exterior disc is preconnected. -/
theorem isPreconnected_preimage_dynPhi (hN : Work.EL.DynB c φ) {P : ℂ → Prop}
    (hP : IsPreconnected {w : ℂ | P w}) (hsub : ∀ w : ℂ, P w → w ∈ Work.Top.exteriorDisc) :
    IsPreconnected {z : ℂ | z ∉ Work.EL.K c ∧ P (Work.EL.dynPhi c φ z)} := by
  haveI : PreconnectedSpace {w : ℂ // P w} := Subtype.preconnectedSpace hP
  have hS : IsPreconnected {w : ↥Work.Top.exteriorDisc | P (w : ℂ)} := by
    have hcont : Continuous fun x : {w : ℂ // P w} =>
        (⟨(x : ℂ), hsub x.1 x.2⟩ : ↥Work.Top.exteriorDisc) :=
      Continuous.subtype_mk continuous_subtype_val _
    have himg : (fun x : {w : ℂ // P w} => (⟨(x : ℂ), hsub x.1 x.2⟩ : ↥Work.Top.exteriorDisc))
        '' Set.univ = {w : ↥Work.Top.exteriorDisc | P (w : ℂ)} := by
      ext w
      constructor
      · rintro ⟨x, -, hx⟩
        rw [← hx]
        exact x.2
      · intro hw
        exact ⟨⟨(w : ℂ), hw⟩, Set.mem_univ _, Subtype.ext rfl⟩
    rw [← himg]
    exact isPreconnected_univ.image _ hcont.continuousOn
  have heq : {z : ℂ | z ∉ Work.EL.K c ∧ P (Work.EL.dynPhi c φ z)}
      = Subtype.val '' (hN.e.symm '' {w : ↥Work.Top.exteriorDisc | P (w : ℂ)}) := by
    ext z
    constructor
    · rintro ⟨hzK, hzP⟩
      refine ⟨hN.e.symm (hN.e ⟨z, hzK⟩), ⟨hN.e ⟨z, hzK⟩, ?_, rfl⟩, ?_⟩
      · show P ((hN.e ⟨z, hzK⟩ : ↥Work.Top.exteriorDisc) : ℂ)
        exact hN.he ⟨z, hzK⟩ ▸ hzP
      · exact congrArg Subtype.val (Homeomorph.symm_apply_apply hN.e ⟨z, hzK⟩)
    · rintro ⟨y, ⟨w, hwP, rfl⟩, rfl⟩
      refine ⟨(hN.e.symm w).2, ?_⟩
      have h2 : Work.EL.dynPhi c φ ((hN.e.symm w : ↥(Work.EL.K c)ᶜ) : ℂ) = (w : ℂ) :=
        calc Work.EL.dynPhi c φ ((hN.e.symm w : ↥(Work.EL.K c)ᶜ) : ℂ)
            = ((hN.e (hN.e.symm w) : ↥Work.Top.exteriorDisc) : ℂ) := hN.he (hN.e.symm w)
          _ = (w : ℂ) := congrArg Subtype.val (Homeomorph.apply_symm_apply hN.e w)
      rw [h2]
      exact hwP
  rw [heq]
  exact ((hS.image _ (hN.e.symm.continuous.continuousOn)).image _
    continuous_subtype_val.continuousOn)

/-- `w ↦ rayRot θ w` is continuous. -/
theorem continuous_rayRot (θ : ℝ) : Continuous fun w : ℂ => Work.Top.rayRot θ w := by
  have h : (fun w : ℂ => Work.Top.rayRot θ w)
      = fun w : ℂ => w * Complex.exp (-(2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)) := rfl
  rw [h]
  exact continuous_id.mul continuous_const

/-- The rotated open box `{|Re - R| < a, |Im| < b, ‖w‖ < R}` is preconnected. -/
theorem isPreconnected_rotBox_inner {θ₀ R a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    IsPreconnected {w : ℂ | |(Work.Top.rayRot θ₀ w).re - R| < a ∧
      |(Work.Top.rayRot θ₀ w).im| < b ∧ ‖w‖ < R} := by
  set u : ℂ := Complex.exp (-(2 * (Real.pi : ℂ) * (θ₀ : ℂ) * Complex.I)) with hu
  have hu_ne : u ≠ 0 := by rw [hu]; exact Complex.exp_ne_zero _
  have hu_norm : ‖u‖ = 1 := by
    rw [hu, Complex.norm_exp]
    have hre : (-(2 * (Real.pi : ℂ) * (θ₀ : ℂ) * Complex.I)).re = 0 := by simp
    rw [hre, Real.exp_zero]
  have hrot : ∀ w : ℂ, Work.Top.rayRot θ₀ w = w * u := by intro w; rw [hu]; rfl
  have hmul : ∀ w : ℂ, Work.Top.rayRot θ₀ (w * u⁻¹) = w := by
    intro w
    rw [hrot, mul_assoc, inv_mul_cancel₀ hu_ne, mul_one]
  have hnorm : ∀ w : ℂ, ‖w * u⁻¹‖ = ‖w‖ := by
    intro w
    rw [norm_mul, norm_inv, hu_norm, inv_one, mul_one]
  have heq : {w : ℂ | |(Work.Top.rayRot θ₀ w).re - R| < a ∧
        |(Work.Top.rayRot θ₀ w).im| < b ∧ ‖w‖ < R}
      = (fun w' : ℂ => w' * u⁻¹) '' {w' : ℂ | |w'.re - R| < a ∧ |w'.im| < b ∧ ‖w'‖ < R} := by
    ext w
    constructor
    · intro hw
      obtain ⟨h1, h2, h3⟩ := hw
      refine ⟨Work.Top.rayRot θ₀ w, ⟨h1, h2, ?_⟩, ?_⟩
      · rw [hrot, norm_mul, hu_norm, mul_one]
        exact h3
      · show Work.Top.rayRot θ₀ w * u⁻¹ = w
        rw [hrot, mul_assoc, mul_inv_cancel₀ hu_ne, mul_one]
    · rintro ⟨w', hw', rfl⟩
      obtain ⟨h1, h2, h3⟩ := hw'
      exact ⟨by rw [hmul]; exact h1, by rw [hmul]; exact h2, by rw [hnorm]; exact h3⟩
  rw [heq]
  exact (Work.Top.reIm_box_inter_ball ha hb hR).image _
    (continuous_id.mul continuous_const).continuousOn

/-- The rotated open box `{|Re - R| < a, |Im| < b, R < ‖w‖}` is preconnected. -/
theorem isPreconnected_rotBox_outer {θ₀ R a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (haR : a < R) :
    IsPreconnected {w : ℂ | |(Work.Top.rayRot θ₀ w).re - R| < a ∧
      |(Work.Top.rayRot θ₀ w).im| < b ∧ R < ‖w‖} := by
  set u : ℂ := Complex.exp (-(2 * (Real.pi : ℂ) * (θ₀ : ℂ) * Complex.I)) with hu
  have hu_ne : u ≠ 0 := by rw [hu]; exact Complex.exp_ne_zero _
  have hu_norm : ‖u‖ = 1 := by
    rw [hu, Complex.norm_exp]
    have hre : (-(2 * (Real.pi : ℂ) * (θ₀ : ℂ) * Complex.I)).re = 0 := by simp
    rw [hre, Real.exp_zero]
  have hrot : ∀ w : ℂ, Work.Top.rayRot θ₀ w = w * u := by intro w; rw [hu]; rfl
  have hmul : ∀ w : ℂ, Work.Top.rayRot θ₀ (w * u⁻¹) = w := by
    intro w
    rw [hrot, mul_assoc, inv_mul_cancel₀ hu_ne, mul_one]
  have hnorm : ∀ w : ℂ, ‖w * u⁻¹‖ = ‖w‖ := by
    intro w
    rw [norm_mul, norm_inv, hu_norm, inv_one, mul_one]
  have heq : {w : ℂ | |(Work.Top.rayRot θ₀ w).re - R| < a ∧
        |(Work.Top.rayRot θ₀ w).im| < b ∧ R < ‖w‖}
      = (fun w' : ℂ => w' * u⁻¹) '' {w' : ℂ | |w'.re - R| < a ∧ |w'.im| < b ∧ R < ‖w'‖} := by
    ext w
    constructor
    · intro hw
      obtain ⟨h1, h2, h3⟩ := hw
      refine ⟨Work.Top.rayRot θ₀ w, ⟨h1, h2, ?_⟩, ?_⟩
      · rw [hrot, norm_mul, hu_norm, mul_one]
        exact h3
      · show Work.Top.rayRot θ₀ w * u⁻¹ = w
        rw [hrot, mul_assoc, mul_inv_cancel₀ hu_ne, mul_one]
    · rintro ⟨w', hw', rfl⟩
      obtain ⟨h1, h2, h3⟩ := hw'
      exact ⟨by rw [hmul]; exact h1, by rw [hmul]; exact h2, by rw [hnorm]; exact h3⟩
  rw [heq]
  exact (Work.Top.reIm_box_inter_exterior ha hb hR haR).image _
    (continuous_id.mul continuous_const).continuousOn

/-- The set `B ∩ {pot < log R}` of the box around a ray point of level `R` is preconnected. -/
theorem isPreconnected_eL_innerBox {θ₀ R a b : ℝ} (hN : Work.EL.DynB c φ) (ha : 0 < a)
    (hb : 0 < b) (hR : 1 < R) (hsmall : a + b < R - 1) :
    IsPreconnected {z : ℂ | z ∉ Work.EL.K c ∧
      |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).im| < b ∧ Work.EL.pot hN z < Real.log R} := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hinner := isPreconnected_rotBox_inner (θ₀ := θ₀) (R := R) (a := a) (b := b) ha hb hRpos
  have hsub : ∀ w : ℂ, (|(Work.Top.rayRot θ₀ w).re - R| < a ∧
      |(Work.Top.rayRot θ₀ w).im| < b ∧ ‖w‖ < R) → w ∈ Work.Top.exteriorDisc := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hw
    rw [Work.Top.mem_exteriorDisc]
    have hbd : ‖Work.Top.rayRot θ₀ w - (R : ℂ)‖ < a + b := norm_sub_of_re_im_lt h1 h2
    have habs := abs_norm_sub_norm_le (Work.Top.rayRot θ₀ w) ((R : ℝ) : ℂ)
    have hRc : ‖((R : ℝ) : ℂ)‖ = R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
    rw [hRc] at habs
    have hge : R - ‖Work.Top.rayRot θ₀ w - (R : ℂ)‖ ≤ ‖Work.Top.rayRot θ₀ w‖ := by
      have h := abs_le.mp habs
      linarith [h.2]
    rw [Work.Top.norm_rayRot] at hge
    linarith
  have heq : {z : ℂ | z ∉ Work.EL.K c ∧
        |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).im| < b ∧ Work.EL.pot hN z < Real.log R}
      = {z : ℂ | z ∉ Work.EL.K c ∧
        (|(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).im| < b ∧ ‖Work.EL.dynPhi c φ z‖ < R)} := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, (pot_lt_iff_norm_lt hN hR h1).mp h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, (pot_lt_iff_norm_lt hN hR h1).mpr h4⟩
  rw [heq]
  exact isPreconnected_preimage_dynPhi hN hinner hsub

/-- The set `B ∩ {log R < pot}` of the box around a ray point of level `R` is preconnected. -/
theorem isPreconnected_eL_outerBox {θ₀ R a b : ℝ} (hN : Work.EL.DynB c φ) (ha : 0 < a)
    (hb : 0 < b) (hR : 1 < R) (haR : a < R) :
    IsPreconnected {z : ℂ | z ∉ Work.EL.K c ∧
      |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).im| < b ∧ Real.log R < Work.EL.pot hN z} := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have houter := isPreconnected_rotBox_outer (θ₀ := θ₀) (R := R) (a := a) (b := b) ha hb hRpos haR
  have hsub : ∀ w : ℂ, (|(Work.Top.rayRot θ₀ w).re - R| < a ∧
      |(Work.Top.rayRot θ₀ w).im| < b ∧ R < ‖w‖) → w ∈ Work.Top.exteriorDisc := by
    intro w hw
    rw [Work.Top.mem_exteriorDisc]
    exact lt_trans hR hw.2.2
  have heq : {z : ℂ | z ∉ Work.EL.K c ∧
        |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).im| < b ∧ Real.log R < Work.EL.pot hN z}
      = {z : ℂ | z ∉ Work.EL.K c ∧
        (|(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).im| < b ∧ R < ‖Work.EL.dynPhi c φ z‖)} := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, (log_lt_pot_iff_norm_lt hN hR h1).mp h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, (log_lt_pot_iff_norm_lt hN hR h1).mpr h4⟩
  rw [heq]
  exact isPreconnected_preimage_dynPhi hN houter hsub

/-- The box `B` itself is open. -/
theorem isOpen_eL_box {θ₀ R a b : ℝ} (hN : Work.EL.DynB c φ) (ha : 0 < a) (hb : 0 < b)
    (hR : 1 < R) (hsmall : a + b < R - 1) :
    IsOpen {z : ℂ | z ∉ Work.EL.K c ∧
      |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).im| < b} := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hBoxopen : IsOpen {w : ℂ | |w.re - R| < a ∧ |w.im| < b} := by
    have h1 : IsOpen {w : ℂ | |w.re - R| < a} := by
      rw [show {w : ℂ | |w.re - R| < a}
          = {w : ℂ | w.re - R < a} ∩ {w : ℂ | -a < w.re - R} from by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
        tauto]
      exact (isOpen_lt (Complex.continuous_re.sub continuous_const) continuous_const).inter
        (isOpen_lt continuous_const (Complex.continuous_re.sub continuous_const))
    have h2 : IsOpen {w : ℂ | |w.im| < b} := by
      rw [show {w : ℂ | |w.im| < b} = {w : ℂ | w.im < b} ∩ {w : ℂ | -b < w.im} from by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
        tauto]
      exact (isOpen_lt Complex.continuous_im continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    exact h1.inter h2
  have hSopen : IsOpen {w : ℂ | |(Work.Top.rayRot θ₀ w).re - R| < a ∧
      |(Work.Top.rayRot θ₀ w).im| < b} :=
    hBoxopen.preimage (continuous_rayRot θ₀)
  have heq : {z : ℂ | z ∉ Work.EL.K c ∧
        |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ₀ (Work.EL.dynPhi c φ z)).im| < b}
      = Subtype.val '' (hN.e.symm '' {w : ↥Work.Top.exteriorDisc |
          |(Work.Top.rayRot θ₀ (w : ℂ)).re - R| < a ∧ |(Work.Top.rayRot θ₀ (w : ℂ)).im| < b}) := by
    ext z
    constructor
    · rintro ⟨hzK, h1, h2⟩
      refine ⟨hN.e.symm (hN.e ⟨z, hzK⟩), ⟨hN.e ⟨z, hzK⟩, ?_, rfl⟩, ?_⟩
      · show |(Work.Top.rayRot θ₀ ((hN.e ⟨z, hzK⟩ : ↥Work.Top.exteriorDisc) : ℂ)).re - R| < a ∧
            |(Work.Top.rayRot θ₀ ((hN.e ⟨z, hzK⟩ : ↥Work.Top.exteriorDisc) : ℂ)).im| < b
        exact hN.he ⟨z, hzK⟩ ▸ ⟨h1, h2⟩
      · exact congrArg Subtype.val (Homeomorph.symm_apply_apply hN.e ⟨z, hzK⟩)
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨(hN.e.symm w).2, ?_, ?_⟩
      · have h2 : Work.EL.dynPhi c φ ((hN.e.symm w : ↥(Work.EL.K c)ᶜ) : ℂ) = (w : ℂ) :=
          calc Work.EL.dynPhi c φ ((hN.e.symm w : ↥(Work.EL.K c)ᶜ) : ℂ)
              = ((hN.e (hN.e.symm w) : ↥Work.Top.exteriorDisc) : ℂ) := hN.he (hN.e.symm w)
            _ = (w : ℂ) := congrArg Subtype.val (Homeomorph.apply_symm_apply hN.e w)
        rw [h2]
        exact hw.1
      · have h2 : Work.EL.dynPhi c φ ((hN.e.symm w : ↥(Work.EL.K c)ᶜ) : ℂ) = (w : ℂ) :=
          calc Work.EL.dynPhi c φ ((hN.e.symm w : ↥(Work.EL.K c)ᶜ) : ℂ)
              = ((hN.e (hN.e.symm w) : ↥Work.Top.exteriorDisc) : ℂ) := hN.he (hN.e.symm w)
            _ = (w : ℂ) := congrArg Subtype.val (Homeomorph.apply_symm_apply hN.e w)
        rw [h2]
        exact hw.2
  rw [heq]
  have hU : IsOpen {w : ↥Work.Top.exteriorDisc |
      |(Work.Top.rayRot θ₀ (w : ℂ)).re - R| < a ∧ |(Work.Top.rayRot θ₀ (w : ℂ)).im| < b} :=
    hSopen.preimage continuous_subtype_val
  have hV : IsOpen (hN.e.symm '' {w : ↥Work.Top.exteriorDisc |
      |(Work.Top.rayRot θ₀ (w : ℂ)).re - R| < a ∧ |(Work.Top.rayRot θ₀ (w : ℂ)).im| < b}) :=
    (Homeomorph.isOpen_image hN.e.symm).mpr hU
  obtain ⟨V, hVopen, hVeq⟩ :=
    (isOpen_induced_iff (f := (Subtype.val : ↥(Work.EL.K c)ᶜ → ℂ))).mp hV
  have hVal : Subtype.val '' (Subtype.val ⁻¹' V : Set ↥(Work.EL.K c)ᶜ) = V ∩ (Work.EL.K c)ᶜ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨hzV, hzK⟩
      exact ⟨⟨z, hzK⟩, hzV, rfl⟩
  rw [← hVeq, hVal]
  exact hVopen.inter (Work.ParamRays.isClosed_filledJulia c).isOpen_compl

/-! ## The reference point of a polygon lies on the polygon -/

/-- The point of the reference ray of an admissible polygon at level `R` lies on the polygon:
it is a point of the equipotential part, over the *near* arc that contains `midNear ps`. -/
theorem midNear_rayPt_mem_polyCurve (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    (hA : Work.EL.PolyAdmissible ps) {R : ℝ} (hR : 1 < R) :
    Work.EL.rayPt hN (Work.EL.midNear ps) R ∈ Work.EL.polyCurve ps R := by
  have hshift : Work.EL.rayPt hN (Work.EL.midNear ps) R
      = Work.EL.rayPt hN (Int.fract (Work.EL.midNear ps)) R := by
    have h := Work.ELTop.rayPt_add_int hN (Int.fract (Work.EL.midNear ps)) R
      (⌊Work.EL.midNear ps⌋ : ℤ)
    rw [Int.fract_add_floor] at h
    exact h
  rw [hshift]
  refine Or.inr ⟨Int.fract (Work.EL.midNear ps),
    ⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩, ?_, rfl⟩
  intro P hP hIn
  have h2 : Work.EL.InArc (Int.fract (Work.EL.midNear ps)
      + (⌊Work.EL.midNear ps⌋ : ℝ)) P.a P.b :=
    (InArc_add_int (Int.fract (Work.EL.midNear ps)) (⌊Work.EL.midNear ps⌋) P.a P.b).mpr hIn
  rw [Int.fract_add_floor] at h2
  exact notInArc_midNear ps hA P hP h2

/-! ## A point of the level `log R` whose angle is in the window lies on the polygon -/

theorem mem_polyCurve_of_window (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN)) {R δ : ℝ}
    (hR : 1 < R) (hwin : ∀ θ : ℝ, |θ - Work.EL.midNear ps| < δ → ∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b)
    {z : ℂ} (hzK : z ∉ Work.EL.K c) (hpot : Work.EL.pot hN z = Real.log R)
    (hang : ∃ k : ℤ, |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z -
      (Work.EL.midNear ps + (k : ℝ))| < δ) :
    z ∈ Work.EL.polyCurve ps R := by
  obtain ⟨k, hk⟩ := hang
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hnorm : ‖Work.EL.dynPhi c φ z‖ = R := by
    have h := Work.EL.pot_of_notMem hN hzK
    rw [hpot] at h
    exact Real.log_injOn_pos (lt_trans zero_lt_one (hN.Phi_mem_exteriorDisc hzK)) hRpos h.symm
  have hΦ : Work.EL.dynPhi c φ z = Work.Top.NakaneData.rayPoint
      (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) R := by
    rw [Work.Top.Phi_eq_norm_mul_exp_extAngle hN (hN.Phi_ne_zero hzK), hnorm]
    rfl
  have hz_eq : z = Work.EL.rayPt hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) R := by
    refine hN.injOn_Phi hzK (Work.EL.rayPt_notMem_K hN hR) ?_
    rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN hR]
  refine Or.inr ⟨Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z,
    ⟨Work.Top.NakaneData.extAngle_nonneg _ _,
      le_of_lt (Work.Top.NakaneData.extAngle_lt_one _ _)⟩, ?_, hz_eq⟩
  intro P hP hIn
  have hθ : |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - (k : ℝ)
      - Work.EL.midNear ps| < δ := by
    have h : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - (k : ℝ)
        - Work.EL.midNear ps
        = Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z
          - (Work.EL.midNear ps + (k : ℝ)) := by ring
    rw [h]
    exact hk
  have hnot := hwin _ hθ P hP
  refine hnot ((InArc_add_int (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - (k : ℝ))
    k P.a P.b).mp ?_)
  rwa [show (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - (k : ℝ)) + (k : ℝ)
      = Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z from by ring]

end PotLtAux

open PotLtAux

/-! ## The main theorem -/

theorem polyRegion_subset_pot_lt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    Work.EL.polyRegion ps R ⊆ {z : ℂ | Work.EL.pot hN z < Real.log R} := by
  intro z hz
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  -- the window of angles around `midNear ps`
  obtain ⟨δ, hδpos, hwin⟩ := notInArc_window_midNear ps hA
  -- the box around the reference point of the polygon
  obtain ⟨a, b, ha, hb, haR, habox⟩ :=
    box_angular_thin (c := c) (φ := φ) hN (R := R) (θ := Work.EL.midNear ps) hR hδpos
  set a₀ : ℝ := min a ((R - 1) / 4) with ha₀
  set b₀ : ℝ := min b ((R - 1) / 4) with hb₀
  have ha₀pos : 0 < a₀ := lt_min ha (by linarith)
  have hb₀pos : 0 < b₀ := lt_min hb (by linarith)
  have ha₀a : a₀ ≤ a := min_le_left _ _
  have hb₀b : b₀ ≤ b := min_le_left _ _
  have hsmall : a₀ + b₀ < R - 1 := by
    have h1 : a₀ ≤ (R - 1) / 4 := min_le_right _ _
    have h2 : b₀ ≤ (R - 1) / 4 := min_le_right _ _
    linarith
  have ha₀R : a₀ < R := by linarith
  -- the angular control supplied by the box
  have hangle : ∀ ζ : ℂ,
      |(Work.Top.rayRot (Work.EL.midNear ps) (Work.EL.dynPhi c φ ζ)).re - R| < a₀ →
      |(Work.Top.rayRot (Work.EL.midNear ps) (Work.EL.dynPhi c φ ζ)).im| < b₀ →
      ∃ k : ℤ, |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) ζ
        - (Work.EL.midNear ps + (k : ℝ))| < δ := fun ζ h1 h2 =>
    habox ζ (lt_of_lt_of_le h1 ha₀a) (lt_of_lt_of_le h2 hb₀b)
  have hwin₁ : ∀ θ : ℝ, |θ - Work.EL.midNear ps| < δ →
      ∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b := fun θ h P hP => (hwin θ h).1 P hP
  have hwin₂ : ∀ θ : ℝ, |θ - Work.EL.midNear ps| < δ → ∀ P ∈ ps, ∀ k : ℤ,
      θ ≠ P.a + (k : ℝ) ∧ θ ≠ P.b + (k : ℝ) := fun θ h P hP k => (hwin θ h).2 P hP k
  -- the box, and its inner and outer halves
  set B : Set ℂ := {ζ : ℂ | ζ ∉ Work.EL.K c ∧
    |(Work.Top.rayRot (Work.EL.midNear ps) (Work.EL.dynPhi c φ ζ)).re - R| < a₀ ∧
    |(Work.Top.rayRot (Work.EL.midNear ps) (Work.EL.dynPhi c φ ζ)).im| < b₀} with hB
  set P : Set ℂ := {ζ : ℂ | ζ ∉ Work.EL.K c ∧
    |(Work.Top.rayRot (Work.EL.midNear ps) (Work.EL.dynPhi c φ ζ)).re - R| < a₀ ∧
    |(Work.Top.rayRot (Work.EL.midNear ps) (Work.EL.dynPhi c φ ζ)).im| < b₀ ∧
    Work.EL.pot hN ζ < Real.log R} with hP
  set Q : Set ℂ := {ζ : ℂ | ζ ∉ Work.EL.K c ∧
    |(Work.Top.rayRot (Work.EL.midNear ps) (Work.EL.dynPhi c φ ζ)).re - R| < a₀ ∧
    |(Work.Top.rayRot (Work.EL.midNear ps) (Work.EL.dynPhi c φ ζ)).im| < b₀ ∧
    Real.log R < Work.EL.pot hN ζ} with hQ
  have hBopen : IsOpen B := by
    rw [hB]
    exact isOpen_eL_box (θ₀ := Work.EL.midNear ps) hN ha₀pos hb₀pos hR hsmall
  have hPconn : IsPreconnected P := by
    rw [hP]
    exact isPreconnected_eL_innerBox (θ₀ := Work.EL.midNear ps) hN ha₀pos hb₀pos hR hsmall
  have hQconn : IsPreconnected Q := by
    rw [hQ]
    exact isPreconnected_eL_outerBox (θ₀ := Work.EL.midNear ps) hN ha₀pos hb₀pos hR ha₀R
  have hpB : Work.EL.rayPt hN (Work.EL.midNear ps) R ∈ B := by
    rw [hB]
    refine ⟨Work.EL.rayPt_notMem_K hN hR, ?_, ?_⟩
    · rw [Work.Top.NakaneData.Phi_rayPt hN hR, rayRot_rayPoint_self]
      simp [ha₀pos]
    · rw [Work.Top.NakaneData.Phi_rayPt hN hR, rayRot_rayPoint_self]
      simp [hb₀pos]
  have hpC : Work.EL.rayPt hN (Work.EL.midNear ps) R ∈ Work.EL.polyCurve ps R :=
    midNear_rayPt_mem_polyCurve hN ps hA hR
  have hBC : (B ∩ Work.EL.polyCurve ps R).Nonempty :=
    ⟨Work.EL.rayPt hN (Work.EL.midNear ps) R, hpB, hpC⟩
  -- the box minus the polygon is covered by the inner and outer halves
  have hcov : B \ Work.EL.polyCurve ps R ⊆ P ∪ Q := by
    intro ζ hζ
    obtain ⟨hζB, hζC⟩ := hζ
    rw [hB] at hζB
    obtain ⟨hζK, h1, h2⟩ := hζB
    by_cases hlt : Work.EL.pot hN ζ < Real.log R
    · refine Or.inl ?_
      rw [hP]
      exact ⟨hζK, h1, h2, hlt⟩
    · by_cases hgt : Real.log R < Work.EL.pot hN ζ
      · refine Or.inr ?_
        rw [hQ]
        exact ⟨hζK, h1, h2, hgt⟩
      · exfalso
        have heqpot : Work.EL.pot hN ζ = Real.log R :=
          le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
        exact hζC (mem_polyCurve_of_window hN ps hR hwin₁ hζK heqpot (hangle ζ h1 h2))
  have hPC : Disjoint P (Work.EL.polyCurve ps R) := by
    rw [Set.disjoint_left]
    intro ζ hζP hζC
    rw [hP] at hζP
    obtain ⟨hζK, h1, h2, hlt⟩ := hζP
    rw [Work.EL.polyCurve, Set.mem_ofPred_eq] at hζC
    rcases hζC with ⟨P', hP', hy | hr | hr⟩ | ⟨θ, hθmem, hfar, hζθ⟩
    · exact hζK (hy ▸ landsN_mem_K hN P'.lands_a)
    · obtain ⟨k₁, hk₁⟩ :=
        exists_int_extAngle_paramRay hN (Work.Top.NakaneData.rayPiece_subset_paramRay hr)
      obtain ⟨k₂, hk₂⟩ := hangle ζ h1 h2
      have hθ : |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) ζ - (k₂ : ℝ)
          - Work.EL.midNear ps| < δ := by
        have hh : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) ζ - (k₂ : ℝ)
            - Work.EL.midNear ps
            = Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) ζ
              - (Work.EL.midNear ps + (k₂ : ℝ)) := by ring
        rw [hh]
        exact hk₂
      have hne := (hwin₂ _ hθ P' hP' (k₁ - k₂)).1
      exact hne (by rw [hk₁]; push_cast; ring)
    · obtain ⟨k₁, hk₁⟩ :=
        exists_int_extAngle_paramRay hN (Work.Top.NakaneData.rayPiece_subset_paramRay hr)
      obtain ⟨k₂, hk₂⟩ := hangle ζ h1 h2
      have hθ : |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) ζ - (k₂ : ℝ)
          - Work.EL.midNear ps| < δ := by
        have hh : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) ζ - (k₂ : ℝ)
            - Work.EL.midNear ps
            = Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) ζ
              - (Work.EL.midNear ps + (k₂ : ℝ)) := by ring
        rw [hh]
        exact hk₂
      have hne := (hwin₂ _ hθ P' hP' (k₁ - k₂)).2
      exact hne (by rw [hk₁]; push_cast; ring)
    · have hpot : Work.EL.pot hN ζ = Real.log R := by
        rw [hζθ]
        exact Work.EL.pot_rayPt hN hR
      rw [hpot] at hlt
      exact lt_irrefl _ hlt
  have hQC : Disjoint Q (Work.EL.polyCurve ps R) := by
    rw [Set.disjoint_left]
    intro ζ hζQ hζC
    rw [hQ] at hζQ
    obtain ⟨hζK, h1, h2, hgt⟩ := hζQ
    rw [Work.EL.polyCurve, Set.mem_ofPred_eq] at hζC
    rcases hζC with ⟨P', hP', hy | hr | hr⟩ | ⟨θ, hθmem, hfar, hζθ⟩
    · exact hζK (hy ▸ landsN_mem_K hN P'.lands_a)
    · exact absurd (Work.Top.NakaneData.rayPiece_subset_le hr) (not_le.mpr hgt)
    · exact absurd (Work.Top.NakaneData.rayPiece_subset_le hr) (not_le.mpr hgt)
    · have hpot : Work.EL.pot hN ζ = Real.log R := by
        rw [hζθ]
        exact Work.EL.pot_rayPt hN hR
      rw [hpot] at hgt
      exact lt_irrefl _ hgt
  set S : Work.Top.Sides (Work.EL.polyCurve ps R) := hJ.sides (Work.EL.polyCurve ps R) hC with hS
  have hQz : ∃ ζ ∈ Q, ζ ∈ S.O := by
    refine ⟨Work.EL.rayPt hN (Work.EL.midNear ps) (R + a₀ / 2), ?_, ?_⟩
    · rw [hQ]
      refine ⟨Work.EL.rayPt_notMem_K hN (by linarith), ?_, ?_, ?_⟩
      · rw [Work.Top.NakaneData.Phi_rayPt hN (by linarith), rayRot_rayPoint_self,
          Complex.ofReal_re, abs_of_pos (by linarith)]
        linarith
      · rw [Work.Top.NakaneData.Phi_rayPt hN (by linarith), rayRot_rayPoint_self,
          Complex.ofReal_im, abs_zero]
        exact hb₀pos
      · rw [Work.EL.pot_rayPt hN (by linarith)]
        exact Real.log_lt_log (by linarith) (by linarith)
    · refine gt_potential_subset_sidesO hN hJ ps hR hC ?_
      show Real.log R < Work.EL.pot hN (Work.EL.rayPt hN (Work.EL.midNear ps) (R + a₀ / 2))
      rw [Work.EL.pot_rayPt hN (by linarith)]
      exact Real.log_lt_log (by linarith) (by linarith)
  have hPsub : P ⊆ S.I :=
    S.sides_of_halves hBopen hBC hcov hPconn hQconn hPC hQC hQz
  -- a point of `P` inside the region
  have hxP : ∃ t : ℝ, Work.EL.rayPt hN (Work.EL.midNear ps) t ∈ P ∩ Work.EL.polyRegion ps R := by
    refine ⟨R - a₀ / 2, ?_,
      innerRay_subset_polyRegion hN ps hA hR (by linarith) (by linarith)⟩
    rw [hP]
    refine ⟨Work.EL.rayPt_notMem_K hN (by linarith), ?_, ?_, ?_⟩
    · rw [Work.Top.NakaneData.Phi_rayPt hN (by linarith), rayRot_rayPoint_self,
        Complex.ofReal_re, abs_of_neg (by linarith)]
      linarith
    · rw [Work.Top.NakaneData.Phi_rayPt hN (by linarith), rayRot_rayPoint_self,
        Complex.ofReal_im, abs_zero]
      exact hb₀pos
    · rw [Work.EL.pot_rayPt hN (by linarith)]
      exact Real.log_lt_log (by linarith) (by linarith)
  -- the region lies in the bounded side
  have hregionI : Work.EL.polyRegion ps R ⊆ S.I := by
    rcases S.subset_of_preconnected (Work.EL.isPreconnected_polyRegion (hN := hN) ps R)
      (Work.EL.polyRegion_subset_compl (hN := hN) ps R) with h | h
    · exact h
    · exfalso
      obtain ⟨t, htP, htreg⟩ := hxP
      exact S.notMem_O_of_mem_I (hPsub htP) (h htreg)
  have hzI : z ∈ S.I := hregionI hz
  rcases lt_trichotomy (Work.EL.pot hN z) (Real.log R) with hlt | heq | hgt
  · exact hlt
  · exfalso
    have hzO : z ∈ S.O :=
      level_eq_subset_sidesO hN hJ ps hR hC
        ⟨heq, Work.EL.polyRegion_subset_compl (hN := hN) ps R hz⟩
    exact S.notMem_O_of_mem_I hzI hzO
  · exfalso
    have hzO : z ∈ S.O := gt_potential_subset_sidesO hN hJ ps hR hC hgt
    exact S.notMem_O_of_mem_I hzI hzO

end Work.ELTop
