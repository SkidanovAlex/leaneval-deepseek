/-
# Two-sidedness of a co-landing pair: the decomposition of the complement

This file proves `Work.ELTop.pairSides_decomposition`: for a co-landing pair `P` of rays of the
dynamical plane whose two angles are not congruent modulo `ℤ`, the complement of the pair curve
`pairCurve P` is the disjoint union of the far side `pairSide P` and the near side `pairSideNear P`,
and both sides have the pair curve as frontier.

The proof is self-contained and uses the plane topology of the truncated curves (the "lollipop"
`polyCurve [P] R` obtained by closing the two rays at level `R` with the equipotential arc through
the near arc):

* a point off the filled Julia set `K c` lies on the ray of its external angle, so the angular
  position decides which side it is on (an angle in the far arc gives the far side, an angle in
  the near arc the near side);
* the only component of `(pairCurve P)ᶜ` which could avoid that angular description would be
  contained in `K c`; but its boundary would then be contained in `K c ∩ pairCurve P = {P.y}`,
  forcing it to be the whole punctured plane, which is unbounded;
* the two reference points are separated by the truncated Jordan curve `polyCurve [P] R`.

The frontier statements follow from the fact that the sides are components of the open set
`(pairCurve P)ᶜ` (hence open and closed in it) and that every point of the pair curve is a limit
of points of each side.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.PolyCurve.Blocks
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.ELTop.rayPt_inj
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.continuous_rayPt_angle
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.midNear_nearArc_nbhd
import Submission.Work.ELTop.box_angular_thin
import Submission.Work.ELTop.rayPt_midNear_misses_polyCurve
import Submission.Work.ELTop.notInArc_midNear
import Submission.Work.ELTop.level_eq_subset_sidesO
import Submission.Work.ELTop.sides_I_subset_pot_lt
import Submission.Work.ELTop.gt_potential_subset_sidesO
import Submission.Work.ELTop.mem_pairSideNear_of_nearArc
import Submission.Work.ELTop.polyRegion_subset_pot_lt
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.Top.Jordan
import Submission.Work.Top.isPreconnected_box_gt
import Submission.Work.Top.isPreconnected_box_small
import Submission.Work.Top.isPreconnected_gt_potential
import Submission.Work.Top.Phi_eq_norm_mul_exp_extAngle
import Submission.Work.Top.extAngle_rayPt
import Submission.Work.Top.mem_eqArc_of
import Submission.Work.Top.continuousOn_rayPt
import Submission.Work.Top.mem_paramRay_extAngle
import Submission.Work.Top.closure_paramRay_subset
import Submission.Work.Top.paramRay_unbounded
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

/-! ## The local box around the equipotential point of the reference angle -/

theorem pot_le_log_of_mem_polyCurve (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R : ℝ} (hR : 1 < R) {z : ℂ} (hz : z ∈ Work.EL.polyCurve ps R) :
    Work.EL.pot hN z ≤ Real.log R :=
  polyCurve_subset_pot_le hN ps hR hz

/-- A point of a box around the point `R` of the rotated Böttcher plane does not lie in the
filled Julia set, provided `a < R`. -/
theorem notMem_K_of_box (hN : Work.EL.DynB c φ) {θ R a : ℝ} (hR : 1 < R) (haR : a < R)
    {z : ℂ} (h1 : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a) :
    z ∉ Work.EL.K c := by
  intro hzK
  have h0 : Work.Top.rayRot θ (Work.EL.dynPhi c φ z) = 0 := by
    rw [Work.EL.dynPhi_of_mem hzK]; simp [Work.Top.rayRot_apply]
  have hre : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| = R := by
    rw [h0]
    simp only [Complex.zero_re, zero_sub, abs_neg]
    exact abs_of_pos (by linarith)
  rw [hre] at h1
  linarith

/-- The box around the point `R` of the rotated Böttcher plane is open. -/
theorem isOpen_box (hN : Work.EL.DynB c φ) (θ R a b : ℝ) (hR : 1 < R) (haR : a < R) :
    IsOpen {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b} := by
  have hbox : IsOpen {w : ℂ | |w.re - R| < a ∧ |w.im| < b} := by
    have h1 : {w : ℂ | |w.re - R| < a} = (fun w : ℂ => w.re - R) ⁻¹' Set.Ioo (-a) a := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo]
      exact abs_lt
    have h2 : {w : ℂ | |w.im| < b} = (fun w : ℂ => w.im) ⁻¹' Set.Ioo (-b) b := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo]
      exact abs_lt
    have ho1 : IsOpen {w : ℂ | |w.re - R| < a} := by
      rw [h1]; exact isOpen_Ioo.preimage (Complex.continuous_re.sub continuous_const)
    have ho2 : IsOpen {w : ℂ | |w.im| < b} := by
      rw [h2]; exact isOpen_Ioo.preimage Complex.continuous_im
    exact ho1.inter ho2
  have hφc : ContinuousOn φ (Work.EL.K c)ᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_subtype_val.comp hN.e.continuous).congr ?_
    intro z
    exact (hN.he z).symm.trans (Work.EL.dynPhi_of_notMem z.2)
  have hcont : ContinuousOn (fun z : ℂ => Work.Top.rayRot θ (φ z)) (Work.EL.K c)ᶜ :=
    (Work.Top.continuous_rayRot θ).comp_continuousOn hφc
  have hset : {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b}
      = (Work.EL.K c)ᶜ ∩
        ((fun z : ℂ => Work.Top.rayRot θ (φ z)) ⁻¹'
          {w : ℂ | |w.re - R| < a ∧ |w.im| < b}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage]
    constructor
    · intro hz
      have hzK : z ∉ Work.EL.K c := by
        intro hzK
        have h0 : Work.Top.rayRot θ (Work.EL.dynPhi c φ z) = 0 := by
          rw [Work.EL.dynPhi_of_mem hzK]; simp [Work.Top.rayRot_apply]
        have hre : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| = R := by
          rw [h0]
          simp only [Complex.zero_re, zero_sub, abs_neg]
          exact abs_of_pos (by linarith)
        rw [hre] at hz
        exact absurd hz.1 (not_lt.mpr haR.le)
      refine ⟨hzK, ?_⟩
      rwa [Work.EL.dynPhi_of_notMem hzK] at hz
    · rintro ⟨hzK, hz⟩
      rwa [Work.EL.dynPhi_of_notMem hzK]
  rw [hset]
  exact hcont.isOpen_inter_preimage hN.isClosed_mb.isOpen_compl hbox

/-- The inner half of the box is the set of the `‖Φ z‖ < R`-form used by
`Work.Top.isPreconnected_box_small`. -/
theorem inner_eq (hN : Work.EL.DynB c φ) {θ R a b : ℝ} (hR : 1 < R) (haR : a < R) :
    {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧ Work.EL.pot hN z < Real.log R}
      = {z : ℂ | z ∉ Work.EL.K c ∧ |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧
        ‖Work.EL.dynPhi c φ z‖ < R} := by
  ext z
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hzK : z ∉ Work.EL.K c := notMem_K_of_box hN hR haR h1
    exact ⟨hzK, h1, h2, (PotLtAux.pot_lt_iff_norm_lt hN hR hzK).mp h3⟩
  · rintro ⟨hzK, h1, h2, h3⟩
    exact ⟨h1, h2, (PotLtAux.pot_lt_iff_norm_lt hN hR hzK).mpr h3⟩

/-- The outer half of the box is the set of the `R < ‖Φ z‖`-form used by
`Work.Top.isPreconnected_box_gt`. -/
theorem outer_eq (hN : Work.EL.DynB c φ) {θ R a b : ℝ} (hR : 1 < R) (haR : a < R) :
    {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧ Real.log R < Work.EL.pot hN z}
      = {z : ℂ | z ∉ Work.EL.K c ∧ |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧
        R < ‖Work.EL.dynPhi c φ z‖} := by
  ext z
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hzK : z ∉ Work.EL.K c := notMem_K_of_box hN hR haR h1
    exact ⟨hzK, h1, h2, (PotLtAux.log_lt_pot_iff_norm_lt hN hR hzK).mp h3⟩
  · rintro ⟨hzK, h1, h2, h3⟩
    exact ⟨h1, h2, (PotLtAux.log_lt_pot_iff_norm_lt hN hR hzK).mpr h3⟩

/-- The point of the reference ray at a level `t₀` just below `R` lies in the inner half of the
box. -/
theorem rayPt_mem_innerBox (hN : Work.EL.DynB c φ) {θ R a b t₀ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hR : 1 < R) (ht₀1 : 1 < t₀) (ht₀a : R - a < t₀) (ht₀R : t₀ < R) :
    |(Work.Top.rayRot θ (Work.EL.dynPhi c φ (Work.EL.rayPt hN θ t₀))).re - R| < a ∧
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ (Work.EL.rayPt hN θ t₀))).im| < b ∧
      Work.EL.pot hN (Work.EL.rayPt hN θ t₀) < Real.log R := by
  have hΦ : Work.EL.dynPhi c φ (Work.EL.rayPt hN θ t₀) =
      Work.Top.NakaneData.rayPoint θ t₀ := Work.Top.NakaneData.Phi_rayPt hN ht₀1
  have hrot : Work.Top.rayRot θ (Work.EL.dynPhi c φ (Work.EL.rayPt hN θ t₀)) = (t₀ : ℂ) := by
    rw [hΦ]; exact rayRot_rayPoint_self θ t₀
  refine ⟨?_, ?_, ?_⟩
  · rw [hrot]
    simp only [Complex.ofReal_re]
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  · rw [hrot]
    simpa using hb
  · rw [Work.EL.pot_rayPt hN ht₀1]
    exact Real.log_lt_log (by linarith) ht₀R

/-- The equipotential point of the reference angle of an admissible ray polygon lies on the
polygon. -/
theorem rayPt_midNear_mem_polyCurve (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    (hA : Work.EL.PolyAdmissible ps) {R : ℝ} (hR : 1 < R) :
    Work.EL.rayPt hN (Work.EL.midNear ps) R ∈ Work.EL.polyCurve ps R := by
  set θ : ℝ := Work.EL.midNear ps with hθdef
  set k : ℤ := ⌊θ⌋ with hkdef
  have hk₁ : (k : ℝ) ≤ θ := Int.floor_le θ
  have hk₂ : θ < (k : ℝ) + 1 := Int.lt_floor_add_one θ
  have hrepr : θ - (k : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hfar : ∀ P ∈ ps, ¬ Work.EL.InArc (θ - k) P.a P.b := by
    intro P hP
    have h1 : θ - (k : ℝ) = θ + ((-k : ℤ) : ℝ) := by push_cast; ring
    rw [h1, PotLtAux.InArc_add_int]
    exact notInArc_midNear ps hA P hP
  have key : Work.EL.rayPt hN θ R = Work.EL.rayPt hN (θ - (k : ℝ)) R := by
    have h := Work.ELTop.rayPt_add_int hN (θ - (k : ℝ)) R k
    rw [show θ - (k : ℝ) + (k : ℝ) = θ by ring] at h
    exact h
  exact Or.inr ⟨θ - k, hrepr, hfar, key⟩

/-- A point of the box whose potential is `log R` lies on the equipotential part of the ray
polygon, provided the box is angularly thin around the reference angle and no angle of the
polygon is met. -/
theorem mem_polyCurve_of_box_of_pot_eq (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R θ a b η : ℝ} (hR : 1 < R) (haR : a < R)
    (hthin : ∀ z : ℂ, |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a →
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b →
        ∃ k : ℤ, |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - (θ + k)| < η)
    (hnear : ∀ x : ℝ, (∃ k : ℤ, |x - (θ + k)| < η) → ∀ P ∈ ps, ¬ Work.EL.InArc x P.a P.b)
    {z : ℂ} (h1 : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a)
    (h2 : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b)
    (hpot : Work.EL.pot hN z = Real.log R) :
    z ∈ Work.EL.polyCurve ps R := by
  obtain ⟨k, hk⟩ := hthin z h1 h2
  have hzK : z ∉ Work.EL.K c := notMem_K_of_box hN hR haR h1
  have heq : Work.EL.rayPt hN
      (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) R = z :=
    Work.Top.rayPt_extAngle (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c φ) hN hR hzK hpot
  refine Or.inr ⟨Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z,
    ⟨(Work.Top.NakaneData.extAngle_mem_Ico _ _).1,
      (Work.Top.NakaneData.extAngle_mem_Ico _ _).2.le⟩,
    hnear _ ⟨k, hk⟩, heq.symm⟩

/-- A point of the inner half of the box does not lie on the ray polygon, provided the box is
angularly thin around the reference angle and no angle of the polygon is met. -/
theorem notMem_polyCurve_of_box_inner (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R θ a b η : ℝ} (hR : 1 < R) (haR : a < R)
    (hnotangle : ∀ x : ℝ, (∃ k : ℤ, |x - (θ + k)| < η) → ∀ P ∈ ps, ∀ k : ℤ,
      x ≠ P.a + k ∧ x ≠ P.b + k)
    {z : ℂ} (h1 : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a)
    (h2 : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b)
    (hpot : Work.EL.pot hN z < Real.log R)
    (hthin : ∃ k : ℤ, |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - (θ + k)| < η) :
    z ∉ Work.EL.polyCurve ps R := by
  intro hzC
  have hzK : z ∉ Work.EL.K c := notMem_K_of_box hN hR haR h1
  rcases hzC with ⟨P, hP, hPy | hPa | hPb⟩ | ⟨θ', hθ', _hfar, hz'⟩
  · exact hzK (by rw [hPy]; exact landsN_mem_K hN P.lands_a)
  · have hzparam : z ∈ Work.EL.paramRay hN P.a :=
      Work.Top.NakaneData.rayPiece_subset_paramRay hPa
    obtain ⟨-, t, ht, hΦt⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hzparam
    have htnorm : t = ‖Work.EL.dynPhi c φ z‖ := by
      have hnorm : ‖Work.Top.NakaneData.rayPoint P.a t‖ = ‖Work.EL.dynPhi c φ z‖ := by
        rw [← hΦt]
      rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)] at hnorm
      exact hnorm
    have hPhi := Work.Top.Phi_eq_norm_mul_exp_extAngle (Mb := Work.EL.K c)
      (Φ := Work.EL.dynPhi c φ) hN
      (Work.Top.NakaneData.Phi_ne_zero (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c φ) hN hzK)
    have hEq : Work.Top.NakaneData.rayPoint
          (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) t
        = Work.Top.NakaneData.rayPoint P.a t := by
      calc Work.Top.NakaneData.rayPoint (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) t
          = (t : ℂ) * Complex.exp (2 * (Real.pi : ℂ) *
              (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z : ℂ) * Complex.I) := rfl
        _ = (‖Work.EL.dynPhi c φ z‖ : ℂ) * Complex.exp (2 * (Real.pi : ℂ) *
              (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z : ℂ) * Complex.I) := by
              rw [htnorm]
        _ = Work.EL.dynPhi c φ z := hPhi.symm
        _ = Work.Top.NakaneData.rayPoint P.a t := hΦt
        _ = (t : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (P.a : ℂ) * Complex.I) := rfl
    obtain ⟨k', hk'⟩ := Work.ELTop.rayPoint_angle_eq_int ht hEq
    exact (hnotangle _ hthin P hP (-k')).1 (by rw [hk']; push_cast; ring)
  · have hzparam : z ∈ Work.EL.paramRay hN P.b :=
      Work.Top.NakaneData.rayPiece_subset_paramRay hPb
    obtain ⟨-, t, ht, hΦt⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hzparam
    have htnorm : t = ‖Work.EL.dynPhi c φ z‖ := by
      have hnorm : ‖Work.Top.NakaneData.rayPoint P.b t‖ = ‖Work.EL.dynPhi c φ z‖ := by
        rw [← hΦt]
      rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)] at hnorm
      exact hnorm
    have hPhi := Work.Top.Phi_eq_norm_mul_exp_extAngle (Mb := Work.EL.K c)
      (Φ := Work.EL.dynPhi c φ) hN
      (Work.Top.NakaneData.Phi_ne_zero (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c φ) hN hzK)
    have hEq : Work.Top.NakaneData.rayPoint
          (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) t
        = Work.Top.NakaneData.rayPoint P.b t := by
      calc Work.Top.NakaneData.rayPoint (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) t
          = (t : ℂ) * Complex.exp (2 * (Real.pi : ℂ) *
              (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z : ℂ) * Complex.I) := rfl
        _ = (‖Work.EL.dynPhi c φ z‖ : ℂ) * Complex.exp (2 * (Real.pi : ℂ) *
              (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z : ℂ) * Complex.I) := by
              rw [htnorm]
        _ = Work.EL.dynPhi c φ z := hPhi.symm
        _ = Work.Top.NakaneData.rayPoint P.b t := hΦt
        _ = (t : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (P.b : ℂ) * Complex.I) := rfl
    obtain ⟨k', hk'⟩ := Work.ELTop.rayPoint_angle_eq_int ht hEq
    exact (hnotangle _ hthin P hP (-k')).2 (by rw [hk']; push_cast; ring)
  · rw [hz', Work.EL.pot_rayPt hN hR] at hpot
    exact lt_irrefl _ hpot

/-- A point of the outer half of the box does not lie on the ray polygon. -/
theorem notMem_polyCurve_of_box_outer (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R : ℝ} (hR : 1 < R) {z : ℂ} (hpot : Real.log R < Work.EL.pot hN z) :
    z ∉ Work.EL.polyCurve ps R :=
  fun hz => absurd (pot_le_log_of_mem_polyCurve hN ps hR hz) (not_le.mpr hpot)

/-- **The inner ray of the reference angle lies in the bounded side of the ray polygon.**

Let `ps` be an admissible list of co-landing pairs and `1 < R`.  The bounded side `I` of the
Jordan curve `polyCurve ps R` (given by `Work.Top.JordanForm` as `hJ.sides`) contains the point
of the reference ray `rayPt hN (midNear ps) t` at every level `1 < t < R`.

The proof is a local one at the equipotential point `rayPt hN (midNear ps) R` of the polygon: a
small box in the rotated Böttcher plane is cut by the polygon into an inner half
`P` (potential `< log R`) and an outer half `Q` (potential `> log R`).  Both halves are
preconnected (pull-backs of convex boxes), the outer half lies in the unbounded side, and the
reference point of the polygon lies on the curve, so `Work.Top.Sides.sides_of_halves` places `P`
in the bounded side `I`.  The whole inner piece of the reference ray lies in `P`, hence in `I`. -/theorem rayPt_midNear_mem_sides_I {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) {t : ℝ}
    (ht1 : 1 < t) (htR : t < R) :
    Work.EL.rayPt hN (Work.EL.midNear ps) t ∈
      (hJ.sides (Work.EL.polyCurve ps R) hC).I := by
  classical
  set S : Work.Top.Sides (Work.EL.polyCurve ps R) := hJ.sides (Work.EL.polyCurve ps R) hC with hS
  set θ : ℝ := Work.EL.midNear ps with hθ
  obtain ⟨η, hηpos, hη⟩ := midNear_nearArc_nbhd (hN := hN) ps hA
  obtain ⟨a₀, b₀, ha₀, hb₀, _ha₀R, hthin₀⟩ :=
    box_angular_thin (hN := hN) (R := R) (θ := θ) hR hηpos
  set a : ℝ := min a₀ ((R - 1) / 4) with ha
  set b : ℝ := min b₀ ((R - 1) / 4) with hb
  have ha_pos : 0 < a := lt_min ha₀ (by linarith)
  have hb_pos : 0 < b := lt_min hb₀ (by linarith)
  have ha_le : a ≤ a₀ := min_le_left _ _
  have hb_le : b ≤ b₀ := min_le_left _ _
  have hab : a + b < R - 1 := by
    have h1 : a ≤ (R - 1) / 4 := min_le_right _ _
    have h2 : b ≤ (R - 1) / 4 := min_le_right _ _
    linarith
  have ha_ltR : a < R := by linarith
  have hthin : ∀ z : ℂ, |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a →
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b →
      ∃ k : ℤ, |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - (θ + k)| < η :=
    fun z h1 h2 => hthin₀ z (lt_of_lt_of_le h1 ha_le) (lt_of_lt_of_le h2 hb_le)
  set Bx : Set ℂ := {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b} with hBx
  set P : Set ℂ := {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧ Work.EL.pot hN z < Real.log R}
      with hP
  set Q : Set ℂ := {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧ Real.log R < Work.EL.pot hN z}
      with hQ
  have hPconn : IsPreconnected P := by
    have heq : P = {z : ℂ | z ∉ Work.EL.K c ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧
        Work.EL.pot hN z < Real.log R} := by
      rw [hP]
      ext z
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨notMem_K_of_box hN hR ha_ltR h1, h1, h2, h3⟩
      · rintro ⟨_, h1, h2, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [heq]
    exact PotLtAux.isPreconnected_eL_innerBox (c := c) (φ := φ) hN (θ₀ := θ) ha_pos hb_pos hR hab
  have hQconn : IsPreconnected Q := by
    have heq : Q = {z : ℂ | z ∉ Work.EL.K c ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧
        Real.log R < Work.EL.pot hN z} := by
      rw [hQ]
      ext z
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨notMem_K_of_box hN hR ha_ltR h1, h1, h2, h3⟩
      · rintro ⟨_, h1, h2, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [heq]
    exact PotLtAux.isPreconnected_eL_outerBox (c := c) (φ := φ) hN (θ₀ := θ) ha_pos hb_pos hR ha_ltR
  have hBopen : IsOpen Bx := by
    have heq : Bx = {z : ℂ | z ∉ Work.EL.K c ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b} := by
      rw [hBx]
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨notMem_K_of_box hN hR ha_ltR h1, h1, h2⟩
      · rintro ⟨_, h1, h2⟩
        exact ⟨h1, h2⟩
    rw [heq]
    exact PotLtAux.isOpen_eL_box (c := c) (φ := φ) hN (θ₀ := θ) ha_pos hb_pos hR hab
  have hBC : (Bx ∩ Work.EL.polyCurve ps R).Nonempty := by
    refine ⟨Work.EL.rayPt hN θ R, ?_, ?_⟩
    · rw [hBx]
      have hΦ : Work.EL.dynPhi c φ (Work.EL.rayPt hN θ R) =
          Work.Top.NakaneData.rayPoint θ R := Work.Top.NakaneData.Phi_rayPt hN hR
      refine ⟨?_, ?_⟩
      · rw [hΦ, rayRot_rayPoint_self]
        simp only [Complex.ofReal_re, sub_self, abs_zero]; exact ha_pos
      · rw [hΦ, rayRot_rayPoint_self]
        simpa only [Complex.ofReal_im, abs_zero] using hb_pos
    · rw [hθ]; exact PotLtAux.midNear_rayPt_mem_polyCurve hN ps hA hR
  have hcov : Bx \ Work.EL.polyCurve ps R ⊆ P ∪ Q := by
    intro z hz
    obtain ⟨hzb, hzc⟩ := hz
    rw [hBx] at hzb
    have hzK : z ∉ Work.EL.K c := notMem_K_of_box hN hR ha_ltR hzb.1
    have hne : Work.EL.pot hN z ≠ Real.log R := by
      intro heq
      refine hzc (PotLtAux.mem_polyCurve_of_window (c := c) (φ := φ) (δ := η) hN ps hR
        (fun x hx P hP => (hη x ⟨0, by simpa using hx⟩).1 P hP) hzK heq ?_)
      obtain ⟨k, hk⟩ := hthin z hzb.1 hzb.2
      exact ⟨k, by simpa [hθ] using hk⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (by rw [hP]; exact ⟨hzb.1, hzb.2, h⟩)
    · exact Or.inr (by rw [hQ]; exact ⟨hzb.1, hzb.2, h⟩)
  have hPC : Disjoint P (Work.EL.polyCurve ps R) := by
    rw [Set.disjoint_left]
    intro z hzP hzC
    rw [hP] at hzP
    refine notMem_polyCurve_of_box_inner hN ps hR ha_ltR (η := η) ?_
      hzP.1 hzP.2.1 hzP.2.2 (hthin z hzP.1 hzP.2.1) hzC
    intro x hx P hP k
    obtain ⟨k', hk'⟩ := hx
    exact (hη x ⟨k', by simpa [hθ] using hk'⟩).2 P hP k
  have hQC : Disjoint Q (Work.EL.polyCurve ps R) := by
    rw [Set.disjoint_left]
    intro z hzQ hzC
    rw [hQ] at hzQ
    exact notMem_polyCurve_of_box_outer hN ps hR hzQ.2.2 hzC
  have hQz : ∃ z ∈ Q, z ∈ S.O := by
    refine ⟨Work.EL.rayPt hN θ (R + a / 2), ?_, ?_⟩
    · have h1 : 1 < R + a / 2 := by linarith
      rw [hQ]
      have hΦ : Work.EL.dynPhi c φ (Work.EL.rayPt hN θ (R + a / 2)) =
          Work.Top.NakaneData.rayPoint θ (R + a / 2) := Work.Top.NakaneData.Phi_rayPt hN h1
      refine ⟨?_, ?_, ?_⟩
      · rw [hΦ, rayRot_rayPoint_self]
        simp only [Complex.ofReal_re]
        rw [abs_lt]; exact ⟨by linarith, by linarith⟩
      · rw [hΦ, rayRot_rayPoint_self]
        simpa only [Complex.ofReal_im, abs_zero] using hb_pos
      · rw [Work.EL.pot_rayPt hN h1]
        exact Real.log_lt_log (by linarith) (by linarith)
    · have hpot : Real.log R < Work.EL.pot hN (Work.EL.rayPt hN θ (R + a / 2)) := by
        rw [Work.EL.pot_rayPt hN (by linarith : 1 < R + a / 2)]
        exact Real.log_lt_log (by linarith) (by linarith)
      exact gt_potential_subset_sidesO hN hJ ps hR hC hpot
  have hPI : P ⊆ S.I :=
    S.sides_of_halves (B := Bx) (P := P) (Q := Q) hBopen hBC hcov hPconn hQconn hPC hQC hQz
  set t₀ : ℝ := (max 1 (R - a) + R) / 2 with ht₀
  have ht₀1 : 1 < t₀ := by rw [ht₀]; have := le_max_left (1:ℝ) (R-a); linarith
  have ht₀R : t₀ < R := by
    rw [ht₀]; have hm : max 1 (R-a) < R := max_lt hR (by linarith); linarith
  have ht₀a : R - a < t₀ := by rw [ht₀]; have := le_max_right (1:ℝ) (R-a); linarith
  have hqP : Work.EL.rayPt hN θ t₀ ∈ P := by
    rw [hP]; exact rayPt_mem_innerBox hN ha_pos hb_pos hR ht₀1 ht₀a ht₀R
  have hqI : Work.EL.rayPt hN θ t₀ ∈ S.I := hPI hqP
  set Seg : Set ℂ := (fun s : ℝ => Work.EL.rayPt hN θ s) ''
      Set.Icc (min t t₀) (max t t₀) with hSeg
  have hseg_pre : IsPreconnected Seg := by
    rw [hSeg]
    refine IsPreconnected.image isPreconnected_Icc _ ?_
    refine (Work.Top.continuousOn_rayPt hN θ).mono ?_
    intro s hs
    rw [Set.mem_Icc] at hs
    rw [Set.mem_Ioi]
    have hmin : 1 < min t t₀ := lt_min ht1 ht₀1
    linarith [hs.1]
  have hseg_sub : Seg ⊆ (Work.EL.polyCurve ps R)ᶜ := by
    intro z hz
    rw [hSeg] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    rw [Set.mem_compl_iff]
    rw [Set.mem_Icc] at hs
    have hmin : 1 < min t t₀ := lt_min ht1 ht₀1
    have hmax : max t t₀ < R := max_lt htR ht₀R
    rw [hθ]
    exact rayPt_midNear_misses_polyCurve hN ps hA hR (by linarith [hs.1]) (by linarith [hs.2])
  have hqSeg : Work.EL.rayPt hN θ t₀ ∈ Seg := by
    rw [hSeg]; exact ⟨t₀, ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩
  have htSeg : Work.EL.rayPt hN θ t ∈ Seg := by
    rw [hSeg]; exact ⟨t, ⟨min_le_left _ _, le_max_left _ _⟩, rfl⟩
  have hsegI : Seg ⊆ S.I := by
    rcases S.subset_of_preconnected hseg_pre hseg_sub with h | h
    · exact h
    · exact absurd (h hqSeg) (S.notMem_O_of_mem_I hqI)
  exact hsegI htSeg

/-! ## The angle-side lemmas for a co-landing pair -/

/-- The parameter rays depend on the angle only modulo `ℤ`. -/
theorem paramRay_add_int_aux (hN : Work.EL.DynB c φ) (θ : ℝ) (k : ℤ) :
    Work.EL.paramRay hN (θ + k) = Work.EL.paramRay hN θ := by
  ext z
  rw [Work.Top.NakaneData.mem_paramRay_iff, Work.Top.NakaneData.mem_paramRay_iff]
  constructor
  · rintro ⟨hc, t, ht, h⟩
    exact ⟨hc, t, ht, by rw [← rayPoint_add_int θ t k]; exact h⟩
  · rintro ⟨hc, t, ht, h⟩
    exact ⟨hc, t, ht, by rw [rayPoint_add_int θ t k]; exact h⟩

/-- The parameter rays are `1`-periodic in the angle. -/
theorem paramRay_add_one (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Work.EL.paramRay hN (θ + 1) = Work.EL.paramRay hN θ := by
  simpa using paramRay_add_int_aux hN θ 1

/-- The ray points are `1`-periodic in the angle. -/
theorem rayPt_add_one (hN : Work.EL.DynB c φ) (θ t : ℝ) :
    Work.EL.rayPt hN (θ + 1) t = Work.EL.rayPt hN θ t := by
  simpa using rayPt_add_int hN θ t 1

/-- An angle in the open arc `(a, b)` (`a ≤ b`) has an integral translate in `(a, b)`. -/
theorem InArc.exists_int_mem_Ioo {x a b : ℝ} (hab : a ≤ b) (h : Work.EL.InArc x a b) :
    ∃ m : ℤ, x + m ∈ Set.Ioo a b := by
  obtain ⟨z, h1, h2⟩ := midNear_InArc_exists_int hab h
  refine ⟨-z, ?_, ?_⟩
  · push_cast; linarith
  · push_cast; linarith

/-- A point of the far arc of a pair `P` (with `P.a < P.b`), at any level `> 1`, lies in the
far side `pairSide P`.

The proof reduces this to the *near*-arc statement `Work.ELTop.mem_pairSideNear_of_nearArc`
applied to the pair `Q = (P.b, P.a + 1)` (with the same landing point): the pair curves of `P`
and `Q` are equal, and the near side of `Q` through its near arc `(P.a + 1, P.b + 1)` is the far
side of `P` (the reference points differ by the period `1`). -/
theorem mem_pairSide_of_farArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) {θ t : ℝ}
    (hθ : θ ∈ Set.Ioo P.a P.b) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ Work.EL.pairSide P := by
  classical
  let Q : Work.EL.CoPair hN :=
    { toRawPair := ⟨P.b, P.a + 1, P.y⟩
      lands_a := P.lands_b
      lands_b := by simpa using LandsN_add_int hN P.lands_a 1 }
  have hQa : Q.a = P.b := rfl
  have hQb : Q.b = P.a + 1 := rfl
  have hQy : Q.y = P.y := rfl
  have hQab : Q.a < Q.b := by rw [hQa, hQb]; exact hb1
  have hθ' : θ + 1 ∈ Set.Ioo Q.b (Q.a + 1) := by
    rw [hQa, hQb]; exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hcurve : Work.EL.RawPair.curve hN Q.toRawPair = Work.EL.RawPair.curve hN P.toRawPair := by
    rw [show Q.toRawPair = ⟨P.b, P.a + 1, P.y⟩ from rfl,
      show P.toRawPair = ⟨P.a, P.b, P.y⟩ from rfl]
    simp only [Work.EL.RawPair.curve, paramRay_add_one hN P.a]
    ext z
    simp only [Set.mem_union, Set.mem_singleton_iff]
    tauto
  have harc : Work.EL.arcLen Q.b Q.a = Work.EL.arcLen P.a P.b := by
    rw [hQa, hQb, Work.EL.arcLen, Work.EL.arcLen]
    have h1 : P.b - (P.a + 1) = (P.b - P.a) + ((-1 : ℤ) : ℝ) := by push_cast; ring
    rw [h1, Int.fract_add_intCast]
  have href : Work.EL.rayPt hN (Q.b + Work.EL.arcLen Q.b Q.a / 2) 2 =
      Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2 := by
    have harg : Q.b + Work.EL.arcLen Q.b Q.a / 2
        = (P.a + Work.EL.arcLen P.a P.b / 2) + 1 := by
      rw [hQa, hQb, harc]; ring
    rw [harg, rayPt_add_one hN (P.a + Work.EL.arcLen P.a P.b / 2) 2]
  have hside : Work.EL.pairSideNear Q = Work.EL.pairSide P := by
    show connectedComponentIn (Work.EL.RawPair.curve hN Q.toRawPair)ᶜ
        (Work.EL.rayPt hN (Q.b + Work.EL.arcLen Q.b Q.a / 2) 2)
      = connectedComponentIn (Work.EL.RawPair.curve hN P.toRawPair)ᶜ
        (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2)
    rw [hcurve, href]
  have hmem : Work.EL.rayPt hN (θ + 1) t ∈ Work.EL.pairSideNear Q :=
    mem_pairSideNear_of_nearArc hN Q hQab hθ' ht
  rw [hside] at hmem
  rwa [rayPt_add_one hN θ t] at hmem

/-! ## Closeness of the pair curve -/

/-- A landing ray accumulates on the filled Julia set only at its landing point: if the level
tends to `1⁺`, the potential tends to `0` and the ray points converge to `y`. -/
theorem closure_paramRay_inter_K_subset {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {θ : ℝ} {y : ℂ} (h : Work.EL.LandsN hN θ y) :
    closure (Work.EL.paramRay hN θ) ∩ Work.EL.K c ⊆ {y} := by
  rintro z ⟨hzcl, hzK⟩
  rw [Set.mem_singleton_iff]
  set G := 𝓝[Work.EL.paramRay hN θ] z with hG
  have hGne : G.NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzcl
  have hle : G ≤ 𝓝 z := inf_le_left
  -- on `paramRay θ` we have `x = rayPt θ ‖Φ x‖`
  have hrepr : (fun x : ℂ => Work.EL.rayPt hN θ ‖Work.EL.dynPhi c φ x‖) =ᶠ[G] (fun x : ℂ => x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    obtain ⟨hxK, t, ht, hΦ⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hx
    have htn : ‖Work.EL.dynPhi c φ x‖ = t := by
      rw [hΦ, Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
    rw [htn]
    exact (hN.injOn_Phi hxK (Work.EL.rayPt_notMem_K hN ht)
      (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])).symm
  -- the levels tend to `1`
  have hT : Filter.Tendsto (fun x : ℂ => ‖Work.EL.dynPhi c φ x‖) G (𝓝 1) := by
    have hz0 : Work.EL.pot hN z = 0 := Work.EL.pot_of_mem hN hzK
    have hpot : Filter.Tendsto (fun x : ℂ => Work.EL.pot hN x) G (𝓝 0) := by
      have hc : Filter.Tendsto (fun x : ℂ => Work.EL.pot hN x) (𝓝 z)
          (𝓝 (Work.EL.pot hN z)) := hN.continuous_potential.continuousAt
      rw [hz0] at hc
      exact hc.mono_left hle
    have heq : (fun x : ℂ => Work.EL.pot hN x)
        =ᶠ[G] fun x => Real.log ‖Work.EL.dynPhi c φ x‖ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact Work.EL.pot_of_notMem hN ((Work.Top.NakaneData.paramRay_subset_compl hN θ) hx)
    have hlog : Filter.Tendsto (fun x : ℂ => Real.log ‖Work.EL.dynPhi c φ x‖) G (𝓝 0) :=
      hpot.congr' heq
    have hTpos : ∀ᶠ x in G, 0 < ‖Work.EL.dynPhi c φ x‖ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact norm_pos_iff.mpr
        (hN.Phi_ne_zero ((Work.Top.NakaneData.paramRay_subset_compl hN θ) hx))
    have h1 : Filter.Tendsto (fun x : ℂ => Real.exp (Real.log ‖Work.EL.dynPhi c φ x‖)) G (𝓝 1) := by
      have hc := Real.continuous_exp.continuousAt.tendsto.comp hlog
      simpa [Function.comp_def, Real.exp_zero] using hc
    refine h1.congr' ?_
    filter_upwards [hTpos] with x hx
    exact Real.exp_log hx
  have hmem : Filter.Tendsto (fun x : ℂ => ‖Work.EL.dynPhi c φ x‖) G (𝓝[Set.Ioi 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hT, by
      filter_upwards [self_mem_nhdsWithin] with x hx
      obtain ⟨-, t, ht, hΦ⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hx
      rw [hΦ, Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
      exact ht⟩
  have hray : Filter.Tendsto (fun x : ℂ => Work.EL.rayPt hN θ ‖Work.EL.dynPhi c φ x‖) G (𝓝 y) :=
    h.comp hmem
  have hid : Filter.Tendsto (fun x : ℂ => x) G (𝓝 y) := hray.congr' hrepr
  have hidz : Filter.Tendsto (fun x : ℂ => x) G (𝓝 z) := tendsto_id.mono_left hle
  exact tendsto_nhds_unique hidz hid

/-- The union of a landing ray with its landing point is closed. -/
theorem isClosed_paramRay_union_singleton {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {θ : ℝ} {y : ℂ} (hland : Work.EL.LandsN hN θ y) :
    IsClosed (Work.EL.paramRay hN θ ∪ {y}) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  rw [closure_union, closure_singleton] at hz
  rcases hz with hz | hz
  · rcases Work.Top.closure_paramRay_subset (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c φ) hN θ hz
      with h | h
    · exact Or.inl h
    · exact Or.inr (closure_paramRay_inter_K_subset hN hland ⟨hz, h⟩)
  · exact Or.inr hz

/-- The pair curve `R(a) ∪ {y} ∪ R(b)` is closed: the closure of each ray adds only the landing
point `y`, and `y` already belongs to the curve. -/
theorem isClosed_pairCurve_aux {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) : IsClosed (Work.EL.pairCurve P) := by
  have h1 := isClosed_paramRay_union_singleton hN P.lands_a
  have h2 := isClosed_paramRay_union_singleton hN P.lands_b
  have heq : Work.EL.pairCurve P
      = (Work.EL.paramRay hN P.a ∪ {P.y}) ∪ (Work.EL.paramRay hN P.b ∪ {P.y}) := by
    rw [Work.EL.pairCurve, Work.EL.RawPair.curve]
    ext z
    simp only [Set.mem_union, Set.mem_singleton_iff]
    tauto
  rw [heq]
  exact h1.union h2

/-! ## The complementary arc -/

/-- If `θ` is congruent to neither `a` nor `b` modulo `ℤ` (with `a < b < a + 1`), then it lies in
the open arc `(a, b)` or in the complementary arc `(b, a + 1)`. -/
theorem InArc_or_InArc_near {a b θ : ℝ} (hab : a < b) (hb1 : b < a + 1)
    (h1 : ∀ k : ℤ, θ ≠ a + k) (h2 : ∀ k : ℤ, θ ≠ b + k) :
    Work.EL.InArc θ a b ∨ Work.EL.InArc θ b (a + 1) := by
  have hℓa : Work.EL.arcLen a b = b - a := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hℓb : Work.EL.arcLen b (a + 1) = a + 1 - b :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hshift : Int.fract (θ - b) = Int.fract (Int.fract (θ - a) - (b - a)) := by
    have h : θ - b = (Int.fract (θ - a) - (b - a)) + ((⌊θ - a⌋ : ℤ) : ℝ) := by
      have := Int.fract_add_floor (θ - a)
      push_cast
      linarith
    rw [h, Int.fract_add_intCast]
  have hf0 : 0 < Int.fract (θ - a) := by
    rw [lt_iff_le_and_ne]
    refine ⟨Int.fract_nonneg _, ?_⟩
    intro hfeq
    have hfeq' : Int.fract (θ - a) = 0 := hfeq.symm
    rw [Int.fract_eq_zero_iff] at hfeq'
    obtain ⟨z, hz⟩ := hfeq'
    exact h1 z (by push_cast at hz ⊢; linarith)
  have hf1 : Int.fract (θ - a) < 1 := Int.fract_lt_one _
  have hfne : Int.fract (θ - a) ≠ b - a := by
    intro hfe
    have h0 : Int.fract (θ - b) = 0 := by
      rw [hshift, hfe, sub_self]; exact Int.fract_zero
    rw [Int.fract_eq_zero_iff] at h0
    obtain ⟨z, hz⟩ := h0
    exact h2 z (by push_cast at hz ⊢; linarith)
  rcases lt_or_gt_of_ne hfne with hlt | hgt
  · left
    exact ⟨hf0, by rw [hℓa]; exact hlt⟩
  · right
    have hpos : 0 < Int.fract (θ - a) - (b - a) := by linarith
    have hlt1 : Int.fract (θ - a) - (b - a) < 1 := by linarith
    have hfr : Int.fract (Int.fract (θ - a) - (b - a)) = Int.fract (θ - a) - (b - a) :=
      Int.fract_eq_self.mpr ⟨le_of_lt hpos, hlt1⟩
    refine ⟨?_, ?_⟩
    · rw [hshift, hfr]; exact hpos
    · rw [hshift, hfr, hℓb]; linarith

/-- A ray whose angle lies in the far arc of a pair lies in the far side. -/
theorem paramRay_subset_pairSide_of_InArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) {θ : ℝ}
    (hθ : Work.EL.InArc θ P.a P.b) :
    Work.EL.paramRay hN θ ⊆ Work.EL.pairSide P := by
  intro z hz
  obtain ⟨hzK, t, ht, hΦ⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hz
  have hzt : z = Work.EL.rayPt hN θ t :=
    hN.injOn_Phi hzK (Work.EL.rayPt_notMem_K hN ht)
      (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])
  rw [hzt]
  obtain ⟨m, hm⟩ := InArc.exists_int_mem_Ioo (le_of_lt hab) hθ
  rw [← rayPt_add_int hN θ t m]
  exact mem_pairSide_of_farArc hN P hab hb1 hm ht

/-- A ray whose angle lies in the complementary (near) arc of a pair lies in the near side. -/
theorem paramRay_subset_pairSideNear_of_InArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) {θ : ℝ}
    (hθ : Work.EL.InArc θ P.b (P.a + 1)) :
    Work.EL.paramRay hN θ ⊆ Work.EL.pairSideNear P := by
  intro z hz
  obtain ⟨hzK, t, ht, hΦ⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hz
  have hzt : z = Work.EL.rayPt hN θ t :=
    hN.injOn_Phi hzK (Work.EL.rayPt_notMem_K hN ht)
      (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])
  rw [hzt]
  obtain ⟨m, hm⟩ := InArc.exists_int_mem_Ioo (le_of_lt hb1) hθ
  rw [← rayPt_add_int hN θ t m]
  exact mem_pairSideNear_of_nearArc hN P hab hm ht

/-- The pair curve meets the filled Julia set only in its landing point. -/
theorem pairCurve_inter_K_subset {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) : Work.EL.pairCurve P ∩ Work.EL.K c ⊆ {P.y} := by
  rintro z ⟨hz1, hz2⟩
  rw [Work.EL.mem_pairCurve_iff] at hz1
  rcases hz1 with h | h | h
  · exact absurd ((Work.Top.NakaneData.paramRay_subset_compl hN P.a) h) (by simpa using hz2)
  · simpa using h
  · exact absurd ((Work.Top.NakaneData.paramRay_subset_compl hN P.b) h) (by simpa using hz2)

/-- The membership of the landing point in the pair curve. -/
theorem self_mem_pairCurve {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} (P : Work.EL.CoPair hN) :
    P.y ∈ Work.EL.pairCurve P :=
  (Work.EL.mem_pairCurve_iff P P.y).mpr (Or.inr (Or.inl rfl))

/-! ## The complement of the pair curve is the union of the two sides -/

theorem pairCurve_compl_eq {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    (Work.EL.pairCurve P)ᶜ = Work.EL.pairSide P ∪ Work.EL.pairSideNear P := by
  classical
  have hLopen : IsOpen (Work.EL.pairCurve P)ᶜ := (isClosed_pairCurve_aux hN P).isOpen_compl
  apply Set.Subset.antisymm
  · intro z hz
    rw [Set.mem_compl_iff] at hz
    have hstep1 : ∀ w : ℂ, w ∉ Work.EL.K c → w ∉ Work.EL.pairCurve P →
        w ∈ Work.EL.pairSide P ∪ Work.EL.pairSideNear P := by
      intro w hwK hwL
      set θ : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) w with hθ
      have hwray : w ∈ Work.EL.paramRay hN θ :=
        Work.Top.mem_paramRay_extAngle (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c φ) hN hwK
      have hθa : ∀ k : ℤ, θ ≠ P.a + k := by
        intro k hk
        refine hwL ((Work.EL.mem_pairCurve_iff P w).mpr (Or.inl ?_))
        have h2 : Work.EL.paramRay hN θ = Work.EL.paramRay hN P.a := by
          rw [hk]; exact paramRay_add_int_aux hN P.a k
        rwa [h2] at hwray
      have hθb : ∀ k : ℤ, θ ≠ P.b + k := by
        intro k hk
        refine hwL ((Work.EL.mem_pairCurve_iff P w).mpr (Or.inr (Or.inr ?_)))
        have h2 : Work.EL.paramRay hN θ = Work.EL.paramRay hN P.b := by
          rw [hk]; exact paramRay_add_int_aux hN P.b k
        rwa [h2] at hwray
      rcases InArc_or_InArc_near hab hb1 hθa hθb with hfar | hnear
      · exact Or.inl (paramRay_subset_pairSide_of_InArc hN P hab hb1 hfar hwray)
      · exact Or.inr (paramRay_subset_pairSideNear_of_InArc hN P hab hb1 hnear hwray)
    by_cases hzK : z ∈ Work.EL.K c
    · set C : Set ℂ := connectedComponentIn (Work.EL.pairCurve P)ᶜ z with hC
      have hzC : z ∈ C := mem_connectedComponentIn hz
      have hCsub : C ⊆ (Work.EL.pairCurve P)ᶜ := connectedComponentIn_subset _ _
      have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
      have hCopen : IsOpen C := IsOpen.connectedComponentIn hLopen
      by_cases hCK : C ⊆ Work.EL.K c
      · exfalso
        have hclK : closure C ⊆ Work.EL.K c := closure_minimal hCK hN.isClosed_mb
        have hCl : closure C ⊆ C ∪ Work.EL.pairCurve P := by
          intro w hw
          by_cases hwL : w ∈ Work.EL.pairCurve P
          · exact Or.inr hwL
          · left
            obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hLopen w hwL
            obtain ⟨c₁, hc₁C, hc₁d⟩ := Metric.mem_closure_iff.mp hw ε hεpos
            have hc₁B : c₁ ∈ Metric.ball w ε := by
              rw [Metric.mem_ball, dist_comm]; exact hc₁d
            have hballpre : IsPreconnected (Metric.ball w ε) := (convex_ball w ε).isPreconnected
            have hconn : IsPreconnected (C ∪ Metric.ball w ε) :=
              IsPreconnected.union c₁ hc₁C hc₁B hCpre hballpre
            have hsub : C ∪ Metric.ball w ε ⊆ (Work.EL.pairCurve P)ᶜ := by
              intro x hx
              rcases hx with hx | hx
              · exact hCsub hx
              · exact hε hx
            have hsubC : C ∪ Metric.ball w ε ⊆ connectedComponentIn (Work.EL.pairCurve P)ᶜ z :=
              IsPreconnected.subset_connectedComponentIn hconn (Or.inl hzC) hsub
            exact hsubC (Or.inr (Metric.mem_ball_self hεpos))
        have hCsub_y : C ⊆ ({P.y}ᶜ : Set ℂ) := by
          intro w hw
          rw [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro hwy
          exact hCsub hw (by rw [hwy]; exact self_mem_pairCurve P)
        have hCeq : C = ({P.y}ᶜ : Set ℂ) := by
          refine Set.Subset.antisymm hCsub_y ?_
          have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
            rw [Complex.rank_real_complex]; norm_num
          have hpu : IsPreconnected ({P.y}ᶜ : Set ℂ) :=
            (isConnected_compl_singleton_of_one_lt_rank hrank P.y).isPreconnected
          have hcov : ({P.y}ᶜ : Set ℂ) ⊆ C ∪ (closure C)ᶜ := by
            intro w hw
            rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
            by_cases hwc : w ∈ closure C
            · left
              rcases hCl hwc with h | h
              · exact h
              · exact absurd (pairCurve_inter_K_subset hN P ⟨h, hclK hwc⟩) hw
            · right; exact hwc
          have hdisj : ({P.y}ᶜ : Set ℂ) ∩ (C ∩ (closure C)ᶜ) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro x ⟨-, hxC, hxcl⟩
            exact hxcl (subset_closure hxC)
          rcases isPreconnected_iff_subset_of_disjoint.mp hpu C (closure C)ᶜ hCopen
            isClosed_closure.isOpen_compl hcov hdisj with h | h
          · exact h
          · exfalso
            exact h (hCsub_y hzC) (subset_closure hzC)
        obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp hN.isBounded_mb
        let c₀ : ℂ := (((max D 0 + ‖P.y‖ + 1 : ℝ)) : ℂ)
        have hc₀ : ‖c₀‖ = max D 0 + ‖P.y‖ + 1 := by
          rw [show c₀ = (((max D 0 + ‖P.y‖ + 1 : ℝ)) : ℂ) from rfl, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by linarith [norm_nonneg P.y, le_max_right D 0])]
        have hDlt : D < ‖P.y + c₀‖ := by
          have h2 : ‖c₀‖ ≤ ‖P.y + c₀‖ + ‖P.y‖ := by
            have h := norm_sub_le (P.y + c₀) P.y
            simpa using h
          rw [hc₀] at h2; linarith [le_max_left D 0]
        have hmem : P.y + c₀ ∈ C := by
          rw [hCeq, Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          have h2 : c₀ = 0 := by
            have := congrArg (fun u => u - P.y) h
            simpa using this
          rw [h2, norm_zero] at hc₀
          linarith [norm_nonneg P.y, le_max_right D 0]
        have hle := hD (P.y + c₀) (hCK hmem)
        linarith
      · obtain ⟨w, hwC, hwK⟩ := not_subset.mp hCK
        have hwL : w ∉ Work.EL.pairCurve P := fun h => hCsub hwC h
        rcases hstep1 w hwK hwL with hA | hB
        · left
          show z ∈ connectedComponentIn (Work.EL.pairCurve P)ᶜ
            (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2)
          have h1 : connectedComponentIn (Work.EL.pairCurve P)ᶜ z
              = connectedComponentIn (Work.EL.pairCurve P)ᶜ w :=
            connectedComponentIn_eq (F := (Work.EL.pairCurve P)ᶜ) (y := w) (x := z) hwC
          have h2 : connectedComponentIn (Work.EL.pairCurve P)ᶜ
                (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2)
              = connectedComponentIn (Work.EL.pairCurve P)ᶜ w :=
            connectedComponentIn_eq (F := (Work.EL.pairCurve P)ᶜ) (y := w)
              (x := Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2) hA
          have heq : connectedComponentIn (Work.EL.pairCurve P)ᶜ z
              = connectedComponentIn (Work.EL.pairCurve P)ᶜ
                (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2) :=
            h1.trans h2.symm
          rw [← heq]
          exact mem_connectedComponentIn hz
        · right
          show z ∈ connectedComponentIn (Work.EL.pairCurve P)ᶜ
            (Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2)
          have h1 : connectedComponentIn (Work.EL.pairCurve P)ᶜ z
              = connectedComponentIn (Work.EL.pairCurve P)ᶜ w :=
            connectedComponentIn_eq (F := (Work.EL.pairCurve P)ᶜ) (y := w) (x := z) hwC
          have h2 : connectedComponentIn (Work.EL.pairCurve P)ᶜ
                (Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2)
              = connectedComponentIn (Work.EL.pairCurve P)ᶜ w :=
            connectedComponentIn_eq (F := (Work.EL.pairCurve P)ᶜ) (y := w)
              (x := Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2) hB
          have heq : connectedComponentIn (Work.EL.pairCurve P)ᶜ z
              = connectedComponentIn (Work.EL.pairCurve P)ᶜ
                (Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2) :=
            h1.trans h2.symm
          rw [← heq]
          exact mem_connectedComponentIn hz
    · exact hstep1 z hzK hz
  · intro z hz
    rcases hz with hz | hz
    · exact connectedComponentIn_subset ((Work.EL.pairCurve P)ᶜ)
        (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2) hz
    · exact connectedComponentIn_subset ((Work.EL.pairCurve P)ᶜ)
        (Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2) hz

/-! ## Auxiliary: rays of an angle in the open unit interval around another angle -/

/-- A point of the ray whose angle lies in `(y, y + 1)` does not lie on the ray of angle `y`. -/
theorem notMem_paramRay_of_Ioo {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {x y s : ℝ}
    (hx1 : y < x) (hx2 : x < y + 1) (hs : 1 < s) :
    Work.EL.rayPt hN x s ∉ Work.EL.paramRay hN y :=
  notMem_paramRay_of_ne_int hN (fun j => unitIoo_ne_add_int hx1 hx2 j) hs

/-- The parameter ray of an angle is preconnected (it is the image of the interval `(1, ∞)`). -/
theorem isPreconnected_paramRay {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    IsPreconnected (Work.EL.paramRay hN θ) := by
  have heq : Work.EL.paramRay hN θ
      = (fun t : ℝ => Work.EL.rayPt hN θ t) '' Set.Ioi 1 := by
    ext z
    rw [Work.Top.NakaneData.mem_paramRay_iff]
    constructor
    · rintro ⟨hzK, t, ht, hΦ⟩
      exact ⟨t, ht, (hN.injOn_Phi hzK (Work.EL.rayPt_notMem_K hN ht)
        (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Work.EL.rayPt_notMem_K hN ht, t, ht, Work.Top.NakaneData.Phi_rayPt hN ht⟩
  rw [heq]
  exact IsPreconnected.image isPreconnected_Ioi (fun t : ℝ => Work.EL.rayPt hN θ t)
    (Work.Top.continuousOn_rayPt hN θ)

/-- The list of a single co-landing pair is admissible, provided its angles are strictly
increasing and less than `a + 1`. -/
theorem polyAdmissible_singleton {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    Work.EL.PolyAdmissible [P] := by
  have hcyc : Work.EL.CyclicStrict [P.a, P.b] := by
    refine ⟨by simp, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, by simp⟩
      intro y hy
      rw [List.mem_singleton] at hy
      rw [hy]
      exact hab
    · intro x hx
      have hx' : x = P.a ∨ x = P.b := by simpa using hx
      have hhead : ([P.a, P.b] : List ℝ).headD 0 = P.a := rfl
      rw [hhead]
      rcases hx' with rfl | rfl
      · linarith
      · linarith
  refine ⟨by simp, ?_, ?_⟩
  · have hflat : ([P].flatMap fun Q => [Q.a, Q.b]) = [P.a, P.b] := by simp
    rw [hflat]; exact hcyc
  · rw [List.pairwise_cons]
    exact ⟨fun b hb => absurd hb (by simp), by simp⟩

theorem paramRay_sub_one (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Work.EL.paramRay hN (θ - 1) = Work.EL.paramRay hN θ := by
  have h := paramRay_add_int_aux hN θ (-1)
  rwa [show θ + ((-1 : ℤ) : ℝ) = θ - 1 from by push_cast; ring] at h

/-- **The two sides of a co-landing pair are disjoint.**

The two reference points `rf` (of the far side) and `rn` (of the near side) are separated by the
truncated Jordan curve `polyCurve [P] R` at a level `R` chosen larger than the maximum of the
potential on a hypothetical path between them. -/
theorem pairSide_disjoint {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    Disjoint (Work.EL.pairSide P) (Work.EL.pairSideNear P) := by
  classical
  have hLopen : IsOpen (Work.EL.pairCurve P)ᶜ := (isClosed_pairCurve_aux hN P).isOpen_compl
  have harc : Work.EL.arcLen P.a P.b = P.b - P.a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have harcpos : 0 < Work.EL.arcLen P.a P.b := by rw [harc]; linarith
  have harclt : Work.EL.arcLen P.a P.b < 1 := Int.fract_lt_one _
  have harc2 : Work.EL.arcLen P.b P.a = P.a - P.b + 1 := by
    rw [Work.EL.arcLen]
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  let mf : ℝ := P.a + Work.EL.arcLen P.a P.b / 2
  let mn : ℝ := P.b + Work.EL.arcLen P.b P.a / 2
  let rf : ℂ := Work.EL.rayPt hN mf 2
  let rn : ℂ := Work.EL.rayPt hN mn 2
  have hmn_mid : Work.EL.midNear [P] = mn := by
    rw [Work.EL.midNear.eq_2]
    have h1 : Int.fract (P.a + 1 - P.b) = Work.EL.arcLen P.b P.a := by
      rw [Work.EL.arcLen]
      have h2 : P.a + 1 - P.b = (P.a - P.b) + ((1 : ℤ) : ℝ) := by push_cast; ring
      rw [h2, Int.fract_add_intCast]
    rw [h1]
  have hmf_gt : P.a < mf := by
    show P.a < P.a + Work.EL.arcLen P.a P.b / 2
    linarith [harcpos]
  have hmf_lt : mf < P.a + 1 := by
    show P.a + Work.EL.arcLen P.a P.b / 2 < P.a + 1
    linarith [harclt]
  have hmf_gt_b : P.b - 1 < mf := by
    show P.b - 1 < P.a + Work.EL.arcLen P.a P.b / 2
    rw [harc]; linarith
  have hmf_lt_b : mf < P.b := by
    show P.a + Work.EL.arcLen P.a P.b / 2 < P.b
    rw [harc]; linarith
  have hmn_gt : P.b < mn := by
    show P.b < P.b + Work.EL.arcLen P.b P.a / 2
    rw [harc2]; linarith
  have hmn_lt : mn < P.b + 1 := by
    show P.b + Work.EL.arcLen P.b P.a / 2 < P.b + 1
    rw [harc2]; linarith
  have hmn_ga : P.a < mn := by
    show P.a < P.b + Work.EL.arcLen P.b P.a / 2
    rw [harc2]; linarith
  have hmn_la : mn < P.a + 1 := by
    show P.b + Work.EL.arcLen P.b P.a / 2 < P.a + 1
    rw [harc2]; linarith
  have hmf_InArc : Work.EL.InArc mf P.a P.b := by
    have hmf : mf - P.a = Work.EL.arcLen P.a P.b / 2 := by
      show P.a + Work.EL.arcLen P.a P.b / 2 - P.a = Work.EL.arcLen P.a P.b / 2
      ring
    have hpos : 0 < Work.EL.arcLen P.a P.b / 2 := by linarith
    have hlt1 : Work.EL.arcLen P.a P.b / 2 < 1 := by linarith
    rw [Work.EL.InArc, hmf, Int.fract_eq_self.mpr ⟨le_of_lt hpos, hlt1⟩]
    exact ⟨hpos, by linarith [harcpos]⟩
  have hrf_notmem : rf ∉ Work.EL.pairCurve P := by
    rw [Work.EL.mem_pairCurve_iff]
    push_neg
    refine ⟨?_, ?_, ?_⟩
    · show Work.EL.rayPt hN mf 2 ∉ Work.EL.paramRay hN P.a
      exact notMem_paramRay_of_Ioo hN hmf_gt hmf_lt (by norm_num)
    · show rf ≠ P.y
      intro h
      have hK : rf ∈ Work.EL.K c := by rw [h]; exact landsN_mem_K hN P.lands_a
      exact (Work.EL.rayPt_notMem_K hN (θ := mf) (t := 2) (by norm_num)) hK
    · show rf ∉ Work.EL.paramRay hN P.b
      have h : Work.EL.rayPt hN mf 2 ∉ Work.EL.paramRay hN (P.b - 1) :=
        notMem_paramRay_of_Ioo hN hmf_gt_b (by linarith [hmf_lt_b]) (by norm_num)
      rwa [paramRay_sub_one hN P.b] at h
  have hrn_notmem : rn ∉ Work.EL.pairCurve P := by
    rw [Work.EL.mem_pairCurve_iff]
    push_neg
    refine ⟨?_, ?_, ?_⟩
    · show rn ∉ Work.EL.paramRay hN P.a
      exact notMem_paramRay_of_Ioo hN hmn_ga hmn_la (by norm_num)
    · show rn ≠ P.y
      intro h
      have hK : rn ∈ Work.EL.K c := by rw [h]; exact landsN_mem_K hN P.lands_b
      exact (Work.EL.rayPt_notMem_K hN (θ := mn) (t := 2) (by norm_num)) hK
    · show rn ∉ Work.EL.paramRay hN P.b
      exact notMem_paramRay_of_Ioo hN hmn_gt hmn_lt (by norm_num)
  have hrfA : rf ∈ Work.EL.pairSide P := mem_connectedComponentIn hrf_notmem
  have hrnB : rn ∈ Work.EL.pairSideNear P := mem_connectedComponentIn hrn_notmem
  have hrf_notMem_B : rf ∉ Work.EL.pairSideNear P := by
    intro hrB
    have hBopen : IsOpen (Work.EL.pairSideNear P) := IsOpen.connectedComponentIn hLopen
    have hBpre : IsPreconnected (Work.EL.pairSideNear P) := isPreconnected_connectedComponentIn
    have hBne : (Work.EL.pairSideNear P).Nonempty := ⟨rn, hrnB⟩
    have hBpc : IsPathConnected (Work.EL.pairSideNear P) :=
      (hBopen.isConnected_iff_isPathConnected).mp ⟨hBne, hBpre⟩
    obtain ⟨γ, hγ⟩ := hBpc.joinedIn rn hrnB rf hrB
    have hγL : ∀ t, γ t ∈ (Work.EL.pairCurve P)ᶜ := fun t =>
      connectedComponentIn_subset ((Work.EL.pairCurve P)ᶜ) rn (hγ t)
    have hcontpot : Continuous (Work.EL.pot hN) := hN.continuous_potential
    obtain ⟨x₀, -, hmax⟩ := (isCompact_range γ.continuous).exists_isMaxOn
      (Set.range_nonempty γ) (hcontpot.continuousOn.mono (Set.subset_univ _))
    set M : ℝ := Work.EL.pot hN x₀ with hM
    have hMbd : ∀ t, Work.EL.pot hN (γ t) ≤ M := fun t =>
      isMaxOn_iff.mp hmax (γ t) ⟨t, rfl⟩
    set R : ℝ := max 3 (Real.exp M + 1) with hRdef
    have hR1 : 1 < R := by
      rw [hRdef]; have := le_max_left (3 : ℝ) (Real.exp M + 1); linarith
    have hR2 : 2 < R := by
      rw [hRdef]; have := le_max_left (3 : ℝ) (Real.exp M + 1); linarith
    have hlogR : M < Real.log R := by
      rw [hRdef]
      have h2 : M < Real.log (Real.exp M + 1) := by
        have h : Real.log (Real.exp M) < Real.log (Real.exp M + 1) :=
          Real.log_lt_log (Real.exp_pos M) (by linarith)
        rwa [Real.log_exp M] at h
      have h3 : Real.log (Real.exp M + 1) ≤ Real.log (max 3 (Real.exp M + 1)) :=
        Real.log_le_log (by linarith [Real.exp_pos M]) (le_max_right _ _)
      linarith
    have hAP : Work.EL.PolyAdmissible [P] := polyAdmissible_singleton P hab hb1
    have hCj : Work.Top.IsJordanCurve (Work.EL.polyCurve [P] R) :=
      polyCurve_isJordan hN [P] hAP hR1
    set S : Work.Top.Sides (Work.EL.polyCurve [P] R) := hJ.sides _ hCj with hS
    have hrnI : rn ∈ S.I := by
      have h := rayPt_midNear_mem_sides_I (c := c) (φ := φ) hN hJ [P] hAP hR1 hCj (t := 2)
        (by norm_num) hR2
      rw [hmn_mid] at h
      exact h
    have hrfO : rf ∈ S.O := by
      have hsub : Work.EL.paramRay hN mf ⊆ (Work.EL.polyCurve [P] R)ᶜ := by
        intro z hz
        rw [Set.mem_compl_iff]
        intro hzC
        obtain ⟨t₀, ht₀, hΦ₀⟩ := hz.2
        have hzt : z = Work.EL.rayPt hN mf t₀ :=
          hN.injOn_Phi hz.1 (Work.EL.rayPt_notMem_K hN ht₀)
            (by rw [hΦ₀, Work.Top.NakaneData.Phi_rayPt hN ht₀])
        rw [Work.EL.polyCurve, Set.mem_ofPred_eq] at hzC
        rcases hzC with ⟨Q, hQ, hQy | hQa | hQb⟩ | ⟨θ, hθ, hfar, hθeq⟩
        · have hQP : Q = P := by simpa using hQ
          rw [hQP] at hQy
          exact ((Work.Top.NakaneData.paramRay_subset_compl hN mf) hz)
            (by rw [hQy]; exact landsN_mem_K hN P.lands_a)
        · have hQP : Q = P := by simpa using hQ
          rw [hQP] at hQa
          have hmem : Work.EL.rayPt hN mf t₀ ∈ Work.EL.paramRay hN P.a := by
            rw [← hzt]; exact Work.Top.NakaneData.rayPiece_subset_paramRay hQa
          exact notMem_paramRay_of_Ioo hN hmf_gt hmf_lt ht₀ hmem
        · have hQP : Q = P := by simpa using hQ
          rw [hQP] at hQb
          have hmem : Work.EL.rayPt hN mf t₀ ∈ Work.EL.paramRay hN P.b := by
            rw [← hzt]; exact Work.Top.NakaneData.rayPiece_subset_paramRay hQb
          have h2 : Work.EL.rayPt hN mf t₀ ∉ Work.EL.paramRay hN (P.b - 1) :=
            notMem_paramRay_of_Ioo hN hmf_gt_b (by linarith [hmf_lt_b]) ht₀
          rw [paramRay_sub_one hN P.b] at h2
          exact h2 hmem
        · have hfarP : ¬ Work.EL.InArc θ P.a P.b := hfar P (by simp)
          have hpot : Work.EL.pot hN z = Real.log R := by rw [hθeq, Work.EL.pot_rayPt hN hR1]
          have htR : t₀ = R := by
            have h2 : Work.EL.pot hN z = Real.log t₀ := by
              rw [hzt, Work.EL.pot_rayPt hN ht₀]
            rw [h2] at hpot
            have ht₀pos : (0 : ℝ) < t₀ := by linarith
            have hRpos : (0 : ℝ) < R := by linarith
            exact Real.log_injOn_pos ht₀pos hRpos hpot
          have heq' : Work.EL.rayPt hN θ R = Work.EL.rayPt hN mf R := by
            rw [← hθeq, hzt, htR]
          obtain ⟨j, hj⟩ := rayPt_inj hN hR1 heq'
          refine hfarP ?_
          have hθeq2 : θ = mf + ((-j : ℤ) : ℝ) := by push_cast; linarith [hj]
          rw [hθeq2, PotLtAux.InArc_add_int]
          exact hmf_InArc
      have hpre : IsPreconnected (Work.EL.paramRay hN mf) := isPreconnected_paramRay hN mf
      have hunb : ∀ n : ℕ, ∃ z ∈ Work.EL.paramRay hN mf, (n : ℝ) ≤ ‖z‖ :=
        Work.Top.paramRay_unbounded hN mf
      have hO := S.subset_O_of_unbounded hpre hsub hunb
      exact hO (Work.EL.rayPt_mem_paramRay hN (θ := mf) (t := 2) (by norm_num))
    have hγc : ∀ t, γ t ∈ (Work.EL.polyCurve [P] R)ᶜ := by
      intro t
      rw [Set.mem_compl_iff]
      intro hmem
      rw [Work.EL.polyCurve, Set.mem_ofPred_eq] at hmem
      rcases hmem with ⟨Q, hQ, hQy | hQa | hQb⟩ | ⟨θ, hθ, hfar, hθeq⟩
      · have hQP : Q = P := by simpa using hQ
        rw [hQP] at hQy
        exact hγL t (by rw [hQy]; exact self_mem_pairCurve P)
      · have hQP : Q = P := by simpa using hQ
        rw [hQP] at hQa
        exact hγL t ((Work.EL.mem_pairCurve_iff P (γ t)).mpr
          (Or.inl (Work.Top.NakaneData.rayPiece_subset_paramRay hQa)))
      · have hQP : Q = P := by simpa using hQ
        rw [hQP] at hQb
        exact hγL t ((Work.EL.mem_pairCurve_iff P (γ t)).mpr
          (Or.inr (Or.inr (Work.Top.NakaneData.rayPiece_subset_paramRay hQb))))
      · have hp : Work.EL.pot hN (γ t) = Real.log R := by
          rw [hθeq, Work.EL.pot_rayPt hN hR1]
        linarith [hMbd t, hlogR]
    exact S.not_joinedIn hrnI hrfO ⟨γ, hγc⟩
  rw [Set.disjoint_left]
  intro z hzA hzB
  have h1 : connectedComponentIn (Work.EL.pairCurve P)ᶜ rf
      = connectedComponentIn (Work.EL.pairCurve P)ᶜ z :=
    connectedComponentIn_eq (F := (Work.EL.pairCurve P)ᶜ) (x := rf) (y := z) hzA
  have h2 : connectedComponentIn (Work.EL.pairCurve P)ᶜ rn
      = connectedComponentIn (Work.EL.pairCurve P)ᶜ z :=
    connectedComponentIn_eq (F := (Work.EL.pairCurve P)ᶜ) (x := rn) (y := z) hzB
  exact hrf_notMem_B (by
    show rf ∈ connectedComponentIn (Work.EL.pairCurve P)ᶜ rn
    rw [h2, ← h1]
    exact mem_connectedComponentIn hrf_notmem)

/-! ## The pair curve is the frontier of each side -/

/-- A point of a ray whose angle lies in the closed far arc is a limit point of the far side. -/
theorem rayPt_mem_closure_pairSide {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) {θ t : ℝ}
    (hθa : P.a ≤ θ) (hθb : θ ≤ P.b) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ closure (Work.EL.pairSide P) := by
  have harc : Work.EL.arcLen P.a P.b = P.b - P.a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have harcpos : 0 < Work.EL.arcLen P.a P.b := by rw [harc]; linarith
  have harclt : Work.EL.arcLen P.a P.b < 1 := Int.fract_lt_one _
  let mf : ℝ := P.a + Work.EL.arcLen P.a P.b / 2
  have hmf_gt : P.a < mf := by
    show P.a < P.a + Work.EL.arcLen P.a P.b / 2
    linarith [harcpos]
  have hmf_lt : mf < P.b := by
    show P.a + Work.EL.arcLen P.a P.b / 2 < P.b
    rw [harc]; linarith
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ', hδ'pos, hδ'⟩ :=
    Metric.continuousAt_iff.mp ((continuous_rayPt_angle hN ht).continuousAt) ε hε
  set s : ℝ := min (δ' / (2 * (|mf - θ| + 1))) (1 / 2) with hs
  have hspos : 0 < s := lt_min (by positivity) (by norm_num)
  have hsle : s ≤ 1 / 2 := min_le_right _ _
  set x : ℝ := (1 - s) * θ + s * mf with hx
  have hx_gt : P.a < x := by
    have h : x - P.a = (1 - s) * (θ - P.a) + s * (mf - P.a) := by rw [hx]; ring
    have h1 : 0 < (1 - s) * (θ - P.a) + s * (mf - P.a) :=
      add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by linarith))
        (mul_pos hspos (by linarith))
    linarith
  have hx_lt : x < P.b := by
    have h : P.b - x = (1 - s) * (P.b - θ) + s * (P.b - mf) := by rw [hx]; ring
    have h1 : 0 < (1 - s) * (P.b - θ) + s * (P.b - mf) :=
      add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by linarith))
        (mul_pos hspos (by linarith))
    linarith
  refine ⟨Work.EL.rayPt hN x t, ?_, ?_⟩
  · refine paramRay_subset_pairSide_of_InArc hN P hab hb1 ?_
      (Work.EL.rayPt_mem_paramRay hN ht)
    rw [Work.EL.InArc, harc]
    have hx1 : 0 < x - P.a := by linarith
    have hx2 : x - P.a < 1 := by rw [harc] at harclt; linarith
    rw [Int.fract_eq_self.mpr ⟨le_of_lt hx1, hx2⟩]
    exact ⟨hx1, by linarith⟩
  · rw [dist_comm]
    refine hδ' ?_
    rw [Real.dist_eq, show x - θ = s * (mf - θ) from by rw [hx]; ring, abs_mul, abs_of_pos hspos]
    have hden : 0 < 2 * (|mf - θ| + 1) := by positivity
    have hb : s ≤ δ' / (2 * (|mf - θ| + 1)) := min_le_left _ _
    calc s * |mf - θ| ≤ (δ' / (2 * (|mf - θ| + 1))) * |mf - θ| :=
          mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = δ' * (|mf - θ| / (2 * (|mf - θ| + 1))) := by ring
      _ < δ' * 1 := by
          refine mul_lt_mul_of_pos_left ?_ hδ'pos
          rw [div_lt_one hden]
          linarith [abs_nonneg (mf - θ)]
      _ = δ' := mul_one _

/-- A point of a ray whose angle lies in the closed near arc is a limit point of the near side. -/
theorem rayPt_mem_closure_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) {θ t : ℝ}
    (hθb : P.b ≤ θ) (hθa : θ ≤ P.a + 1) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ closure (Work.EL.pairSideNear P) := by
  have harc2 : Work.EL.arcLen P.b (P.a + 1) = P.a + 1 - P.b :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have harc2pos : 0 < Work.EL.arcLen P.b (P.a + 1) := by rw [harc2]; linarith
  have harc2lt : Work.EL.arcLen P.b (P.a + 1) < 1 := Int.fract_lt_one _
  let mn : ℝ := P.b + Work.EL.arcLen P.b (P.a + 1) / 2
  have hmn_gt : P.b < mn := by
    show P.b < P.b + Work.EL.arcLen P.b (P.a + 1) / 2
    linarith [harc2pos]
  have hmn_lt : mn < P.a + 1 := by
    show P.b + Work.EL.arcLen P.b (P.a + 1) / 2 < P.a + 1
    rw [harc2]; linarith
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ', hδ'pos, hδ'⟩ :=
    Metric.continuousAt_iff.mp ((continuous_rayPt_angle hN ht).continuousAt) ε hε
  set s : ℝ := min (δ' / (2 * (|mn - θ| + 1))) (1 / 2) with hs
  have hspos : 0 < s := lt_min (by positivity) (by norm_num)
  have hsle : s ≤ 1 / 2 := min_le_right _ _
  set x : ℝ := (1 - s) * θ + s * mn with hx
  have hx_gt : P.b < x := by
    have h : x - P.b = (1 - s) * (θ - P.b) + s * (mn - P.b) := by rw [hx]; ring
    have h1 : 0 < (1 - s) * (θ - P.b) + s * (mn - P.b) :=
      add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by linarith))
        (mul_pos hspos (by linarith))
    linarith
  have hx_lt : x < P.a + 1 := by
    have h : P.a + 1 - x = (1 - s) * (P.a + 1 - θ) + s * (P.a + 1 - mn) := by rw [hx]; ring
    have h1 : 0 < (1 - s) * (P.a + 1 - θ) + s * (P.a + 1 - mn) :=
      add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by linarith))
        (mul_pos hspos (by linarith))
    linarith
  refine ⟨Work.EL.rayPt hN x t, ?_, ?_⟩
  · refine paramRay_subset_pairSideNear_of_InArc hN P hab hb1 ?_
      (Work.EL.rayPt_mem_paramRay hN ht)
    rw [Work.EL.InArc, harc2]
    have hx1 : 0 < x - P.b := by linarith
    have hx2 : x - P.b < 1 := by rw [harc2] at harc2lt; linarith
    rw [Int.fract_eq_self.mpr ⟨le_of_lt hx1, hx2⟩]
    exact ⟨hx1, by linarith⟩
  · rw [dist_comm]
    refine hδ' ?_
    rw [Real.dist_eq, show x - θ = s * (mn - θ) from by rw [hx]; ring, abs_mul, abs_of_pos hspos]
    have hden : 0 < 2 * (|mn - θ| + 1) := by positivity
    have hb : s ≤ δ' / (2 * (|mn - θ| + 1)) := min_le_left _ _
    calc s * |mn - θ| ≤ (δ' / (2 * (|mn - θ| + 1))) * |mn - θ| :=
          mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = δ' * (|mn - θ| / (2 * (|mn - θ| + 1))) := by ring
      _ < δ' * 1 := by
          refine mul_lt_mul_of_pos_left ?_ hδ'pos
          rw [div_lt_one hden]
          linarith [abs_nonneg (mn - θ)]
      _ = δ' := mul_one _

/-- The point of the reference ray of the far side is off the pair curve. -/
theorem rayPt_farMid_notMem_pairCurve {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2 ∉ Work.EL.pairCurve P := by
  have harc : Work.EL.arcLen P.a P.b = P.b - P.a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have harcpos : 0 < Work.EL.arcLen P.a P.b := by rw [harc]; linarith
  have harclt : Work.EL.arcLen P.a P.b < 1 := Int.fract_lt_one _
  have hmf_gt : P.a < P.a + Work.EL.arcLen P.a P.b / 2 := by linarith [harcpos]
  have hmf_lt : P.a + Work.EL.arcLen P.a P.b / 2 < P.a + 1 := by linarith [harclt]
  have hmf_gt_b : P.b - 1 < P.a + Work.EL.arcLen P.a P.b / 2 := by rw [harc]; linarith
  have hmf_lt_b : P.a + Work.EL.arcLen P.a P.b / 2 < P.b := by rw [harc]; linarith
  intro h
  rw [Work.EL.mem_pairCurve_iff] at h
  rcases h with h | h | h
  · exact notMem_paramRay_of_Ioo hN hmf_gt hmf_lt (by norm_num) h
  · exact (Work.EL.rayPt_notMem_K hN (θ := P.a + Work.EL.arcLen P.a P.b / 2) (t := 2)
      (by norm_num)) (h ▸ landsN_mem_K hN P.lands_a)
  · have h2 : Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2
        ∉ Work.EL.paramRay hN (P.b - 1) :=
      notMem_paramRay_of_Ioo hN hmf_gt_b (by linarith [hmf_lt_b]) (by norm_num)
    rw [paramRay_sub_one hN P.b] at h2
    exact h2 h

/-- The point of the reference ray of the near side is off the pair curve. -/
theorem rayPt_nearMid_notMem_pairCurve {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2 ∉ Work.EL.pairCurve P := by
  have harc2 : Work.EL.arcLen P.b P.a = P.a - P.b + 1 := by
    rw [Work.EL.arcLen]
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  have hmn_gt : P.b < P.b + Work.EL.arcLen P.b P.a / 2 := by rw [harc2]; linarith
  have hmn_lt : P.b + Work.EL.arcLen P.b P.a / 2 < P.b + 1 := by rw [harc2]; linarith
  have hmn_ga : P.a < P.b + Work.EL.arcLen P.b P.a / 2 := by rw [harc2]; linarith
  have hmn_la : P.b + Work.EL.arcLen P.b P.a / 2 < P.a + 1 := by rw [harc2]; linarith
  intro h
  rw [Work.EL.mem_pairCurve_iff] at h
  rcases h with h | h | h
  · exact notMem_paramRay_of_Ioo hN hmn_ga hmn_la (by norm_num) h
  · exact (Work.EL.rayPt_notMem_K hN (θ := P.b + Work.EL.arcLen P.b P.a / 2) (t := 2)
      (by norm_num)) (h ▸ landsN_mem_K hN P.lands_b)
  · exact notMem_paramRay_of_Ioo hN hmn_gt hmn_lt (by norm_num) h

/-- The pair curve is contained in the closure of the far side. -/
theorem pairCurve_subset_closure_pairSide {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    Work.EL.pairCurve P ⊆ closure (Work.EL.pairSide P) := by
  have hsuba : Work.EL.paramRay hN P.a ⊆ closure (Work.EL.pairSide P) := by
    intro z hz
    obtain ⟨hzK, t, ht, hΦ⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hz
    have hzt : z = Work.EL.rayPt hN P.a t :=
      hN.injOn_Phi hzK (Work.EL.rayPt_notMem_K hN ht)
        (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])
    rw [hzt]
    exact rayPt_mem_closure_pairSide hN P hab hb1 le_rfl (le_of_lt hab) ht
  have hsubb : Work.EL.paramRay hN P.b ⊆ closure (Work.EL.pairSide P) := by
    intro z hz
    obtain ⟨hzK, t, ht, hΦ⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hz
    have hzt : z = Work.EL.rayPt hN P.b t :=
      hN.injOn_Phi hzK (Work.EL.rayPt_notMem_K hN ht)
        (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])
    rw [hzt]
    exact rayPt_mem_closure_pairSide hN P hab hb1 (le_of_lt hab) le_rfl ht
  intro z hz
  rw [Work.EL.mem_pairCurve_iff] at hz
  rcases hz with h | h | h
  · exact hsuba h
  · rw [h]
    exact closure_minimal hsuba isClosed_closure
      (mem_closure_of_tendsto P.lands_a
        (by filter_upwards [self_mem_nhdsWithin] with t ht
            exact Work.EL.rayPt_mem_paramRay hN ht))
  · exact hsubb h

/-- The pair curve is contained in the closure of the near side. -/
theorem pairCurve_subset_closure_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    Work.EL.pairCurve P ⊆ closure (Work.EL.pairSideNear P) := by
  have hsubb : Work.EL.paramRay hN P.b ⊆ closure (Work.EL.pairSideNear P) := by
    intro z hz
    obtain ⟨hzK, t, ht, hΦ⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hz
    have hzt : z = Work.EL.rayPt hN P.b t :=
      hN.injOn_Phi hzK (Work.EL.rayPt_notMem_K hN ht)
        (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])
    rw [hzt]
    exact rayPt_mem_closure_pairSideNear hN P hab hb1 le_rfl (by linarith) ht
  have hsuba : Work.EL.paramRay hN P.a ⊆ closure (Work.EL.pairSideNear P) := by
    intro z hz
    obtain ⟨hzK, t, ht, hΦ⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hz
    have hzt : z = Work.EL.rayPt hN P.a t :=
      hN.injOn_Phi hzK (Work.EL.rayPt_notMem_K hN ht)
        (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])
    rw [hzt, ← rayPt_add_one hN P.a t]
    exact rayPt_mem_closure_pairSideNear hN P hab hb1 (by linarith) le_rfl ht
  intro z hz
  rw [Work.EL.mem_pairCurve_iff] at hz
  rcases hz with h | h | h
  · exact hsuba h
  · rw [h]
    exact closure_minimal hsubb isClosed_closure
      (mem_closure_of_tendsto P.lands_b
        (by filter_upwards [self_mem_nhdsWithin] with t ht
            exact Work.EL.rayPt_mem_paramRay hN ht))
  · exact hsubb h

/-- The far side has the pair curve as its frontier. -/
theorem frontier_pairSide {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    frontier (Work.EL.pairSide P) = Work.EL.pairCurve P := by
  have hLopen : IsOpen (Work.EL.pairCurve P)ᶜ := (isClosed_pairCurve_aux hN P).isOpen_compl
  have hAopen : IsOpen (Work.EL.pairSide P) := IsOpen.connectedComponentIn hLopen
  have hrf_notmem := rayPt_farMid_notMem_pairCurve hN P hab hb1
  have hAcl : closure (Work.EL.pairSide P) ⊆ Work.EL.pairSide P ∪ Work.EL.pairCurve P := by
    intro w hw
    by_cases hwL : w ∈ Work.EL.pairCurve P
    · exact Or.inr hwL
    · left
      obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hLopen w hwL
      obtain ⟨c₁, hc₁A, hc₁d⟩ := Metric.mem_closure_iff.mp hw ε hεpos
      have hc₁B : c₁ ∈ Metric.ball w ε := by rw [Metric.mem_ball, dist_comm]; exact hc₁d
      have hconn : IsPreconnected (Work.EL.pairSide P ∪ Metric.ball w ε) :=
        IsPreconnected.union c₁ hc₁A hc₁B isPreconnected_connectedComponentIn
          (convex_ball w ε).isPreconnected
      have hsub : Work.EL.pairSide P ∪ Metric.ball w ε ⊆ (Work.EL.pairCurve P)ᶜ := by
        intro x hx
        rcases hx with hx | hx
        · exact connectedComponentIn_subset _ _ hx
        · exact hε hx
      have hsubA := IsPreconnected.subset_connectedComponentIn hconn
        (Or.inl (mem_connectedComponentIn hrf_notmem)) hsub
      exact hsubA (Or.inr (Metric.mem_ball_self hεpos))
  have hLA := pairCurve_subset_closure_pairSide hN P hab hb1
  have hAsub : Work.EL.pairSide P ⊆ (Work.EL.pairCurve P)ᶜ := connectedComponentIn_subset _ _
  rw [hAopen.frontier_eq]
  apply Set.Subset.antisymm
  · rintro z ⟨hzcl, hzA⟩
    rcases hAcl hzcl with h | h
    · exact absurd h hzA
    · exact h
  · intro z hz
    exact ⟨hLA hz, fun h => hAsub h hz⟩

/-- The near side has the pair curve as its frontier. -/
theorem frontier_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    frontier (Work.EL.pairSideNear P) = Work.EL.pairCurve P := by
  have hLopen : IsOpen (Work.EL.pairCurve P)ᶜ := (isClosed_pairCurve_aux hN P).isOpen_compl
  have hBopen : IsOpen (Work.EL.pairSideNear P) := IsOpen.connectedComponentIn hLopen
  have hrn_notmem := rayPt_nearMid_notMem_pairCurve hN P hab hb1
  have hBcl : closure (Work.EL.pairSideNear P) ⊆ Work.EL.pairSideNear P ∪ Work.EL.pairCurve P := by
    intro w hw
    by_cases hwL : w ∈ Work.EL.pairCurve P
    · exact Or.inr hwL
    · left
      obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hLopen w hwL
      obtain ⟨c₁, hc₁B, hc₁d⟩ := Metric.mem_closure_iff.mp hw ε hεpos
      have hc₁B' : c₁ ∈ Metric.ball w ε := by rw [Metric.mem_ball, dist_comm]; exact hc₁d
      have hconn : IsPreconnected (Work.EL.pairSideNear P ∪ Metric.ball w ε) :=
        IsPreconnected.union c₁ hc₁B hc₁B' isPreconnected_connectedComponentIn
          (convex_ball w ε).isPreconnected
      have hsub : Work.EL.pairSideNear P ∪ Metric.ball w ε ⊆ (Work.EL.pairCurve P)ᶜ := by
        intro x hx
        rcases hx with hx | hx
        · exact connectedComponentIn_subset _ _ hx
        · exact hε hx
      have hsubB := IsPreconnected.subset_connectedComponentIn hconn
        (Or.inl (mem_connectedComponentIn hrn_notmem)) hsub
      exact hsubB (Or.inr (Metric.mem_ball_self hεpos))
  have hLB := pairCurve_subset_closure_pairSideNear hN P hab hb1
  have hBsub : Work.EL.pairSideNear P ⊆ (Work.EL.pairCurve P)ᶜ := connectedComponentIn_subset _ _
  rw [hBopen.frontier_eq]
  apply Set.Subset.antisymm
  · rintro z ⟨hzcl, hzB⟩
    rcases hBcl hzcl with h | h
    · exact absurd h hzB
    · exact h
  · intro z hz
    exact ⟨hLB hz, fun h => hBsub h hz⟩

/-- The parameter rays are periodic under subtracting an integer from the angle. -/
theorem paramRay_sub_natCast (hN : Work.EL.DynB c φ) (θ : ℝ) (k : ℤ) :
    Work.EL.paramRay hN (θ - (k : ℝ)) = Work.EL.paramRay hN θ := by
  have h := paramRay_add_int_aux hN θ (-k)
  rwa [show θ + ((-k : ℤ) : ℝ) = θ - (k : ℝ) from by push_cast; ring] at h

/-- **The two-sidedness of a co-landing pair.**  For a pair of rays whose two angles are not
congruent modulo `ℤ`, the complement of the pair curve is the disjoint union of the far side and
the near side, and both sides have the pair curve as frontier.

The two angles are normalised modulo `1` to the interval `(a, a + 1)`; all the objects involved
are invariant under this normalisation. -/
theorem pairSides_decomposition {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P : Work.EL.CoPair hN) (hnd : Work.EL.arcLen P.a P.b ≠ 0) :
    (Work.EL.pairCurve P)ᶜ = Work.EL.pairSide P ∪ Work.EL.pairSideNear P ∧
    Disjoint (Work.EL.pairSide P) (Work.EL.pairSideNear P) ∧
    frontier (Work.EL.pairSide P) = Work.EL.pairCurve P ∧
    frontier (Work.EL.pairSideNear P) = Work.EL.pairCurve P := by
  classical
  let m : ℤ := ⌊P.b - P.a⌋
  let Q : Work.EL.CoPair hN :=
    { toRawPair := ⟨P.a, P.b - (m : ℝ), P.y⟩
      lands_a := P.lands_a
      lands_b := by
        have := LandsN_add_int hN P.lands_b (-m)
        rwa [show P.b + ((-m : ℤ) : ℝ) = P.b - (m : ℝ) from by push_cast; ring] at this }
  have hm : (⌊P.b - P.a⌋ : ℝ) = (m : ℝ) := rfl
  have hfract : P.b - (m : ℝ) - P.a = Int.fract (P.b - P.a) := by
    have h := Int.fract_add_floor (P.b - P.a)
    linarith [h, hm]
  have hfpos : 0 < Int.fract (P.b - P.a) := by
    rcases lt_or_eq_of_le (Int.fract_nonneg (P.b - P.a)) with h | h
    · exact h
    · exact absurd h.symm hnd
  have hQab : Q.a < Q.b := by
    show P.a < P.b - (m : ℝ)
    linarith
  have hQb1 : Q.b < Q.a + 1 := by
    show P.b - (m : ℝ) < P.a + 1
    have h := Int.fract_lt_one (P.b - P.a)
    linarith
  have hQa : Q.a = P.a := rfl
  have hQb : Q.b = P.b - (m : ℝ) := rfl
  have hQy : Q.y = P.y := rfl
  have hrawcurve : Work.EL.RawPair.curve hN Q.toRawPair
      = Work.EL.RawPair.curve hN P.toRawPair := by
    rw [show Q.toRawPair = (⟨P.a, P.b - (m : ℝ), P.y⟩ : Work.EL.RawPair) from rfl,
      show P.toRawPair = (⟨P.a, P.b, P.y⟩ : Work.EL.RawPair) from rfl]
    simp only [Work.EL.RawPair.curve, paramRay_sub_natCast hN P.b m]
  have hcurve : Work.EL.pairCurve Q = Work.EL.pairCurve P := hrawcurve
  have harcQ : Work.EL.arcLen Q.a Q.b = Work.EL.arcLen P.a P.b := by
    show Int.fract (Q.b - Q.a) = Int.fract (P.b - P.a)
    have h1 : Q.b - Q.a = (P.b - P.a) + ((-m : ℤ) : ℝ) := by
      rw [hQa, hQb]; push_cast; ring
    rw [h1, Int.fract_add_intCast]
  have href : Work.EL.rayPt hN (Q.a + Work.EL.arcLen Q.a Q.b / 2) 2
      = Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2 := by
    rw [hQa, harcQ]
  have hfar : Work.EL.pairSide Q = Work.EL.pairSide P := by
    show connectedComponentIn (Work.EL.RawPair.curve hN Q.toRawPair)ᶜ
        (Work.EL.rayPt hN (Q.a + Work.EL.arcLen Q.a Q.b / 2) 2)
      = connectedComponentIn (Work.EL.RawPair.curve hN P.toRawPair)ᶜ
        (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2)
    rw [hrawcurve, href]
  have harcQ' : Work.EL.arcLen Q.b Q.a = Work.EL.arcLen P.b P.a := by
    show Int.fract (Q.a - Q.b) = Int.fract (P.a - P.b)
    have h1 : Q.a - Q.b = (P.a - P.b) + (m : ℝ) := by
      rw [hQa, hQb]; ring
    rw [h1, Int.fract_add_intCast]
  have href' : Work.EL.rayPt hN (Q.b + Work.EL.arcLen Q.b Q.a / 2) 2
      = Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2 := by
    have harg : Q.b + Work.EL.arcLen Q.b Q.a / 2
        = (P.b + Work.EL.arcLen P.b P.a / 2) + ((-m : ℤ) : ℝ) := by
      rw [hQb, harcQ']; push_cast; ring
    rw [harg, rayPt_add_int hN (P.b + Work.EL.arcLen P.b P.a / 2) 2 (-m)]
  have hnear : Work.EL.pairSideNear Q = Work.EL.pairSideNear P := by
    show connectedComponentIn (Work.EL.RawPair.curve hN Q.toRawPair)ᶜ
        (Work.EL.rayPt hN (Q.b + Work.EL.arcLen Q.b Q.a / 2) 2)
      = connectedComponentIn (Work.EL.RawPair.curve hN P.toRawPair)ᶜ
        (Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2)
    rw [hrawcurve, href']
  have hnorm : (Work.EL.pairCurve Q)ᶜ = Work.EL.pairSide Q ∪ Work.EL.pairSideNear Q ∧
      Disjoint (Work.EL.pairSide Q) (Work.EL.pairSideNear Q) ∧
      frontier (Work.EL.pairSide Q) = Work.EL.pairCurve Q ∧
      frontier (Work.EL.pairSideNear Q) = Work.EL.pairCurve Q :=
    ⟨pairCurve_compl_eq hN Q hQab hQb1, pairSide_disjoint hN hJ Q hQab hQb1,
      frontier_pairSide hN Q hQab hQb1, frontier_pairSideNear hN Q hQab hQb1⟩
  rw [← hcurve, ← hfar, ← hnear]
  exact hnorm

end Work.ELTop
