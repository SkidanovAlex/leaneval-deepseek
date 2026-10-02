import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.ELTop.notInArc_midNear
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.continuous_rayPt_angle
import Submission.Work.ELTop.rayPt_inj
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.Top.Jordan
import Submission.Work.Top.Phi_eq_norm_mul_exp_extAngle
import Submission.Work.Top.extAngle_rayPt
import Submission.Work.Top.mem_eqArc_of
import Submission.Work.Top.continuousOn_rayPt
import Submission.Work.ELTop.midNear_nearArc_nbhd
import Submission.Work.ELTop.rayPt_midNear_misses_polyCurve
import Submission.Work.ELTop.box_angular_thin
import Submission.Work.Top.isPreconnected_gt_potential
import Submission.Work.Top.isPreconnected_box_gt
import Submission.Work.Top.reIm_box_inter_ball

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

set_option linter.unusedVariables false

namespace Work.ELTop

open Work.EL

variable {c : ℂ} {φ : ℂ → ℂ}

/-! ## Elementary facts about `rayRot` and the Böttcher plane -/

/-- The box around the point `R` of the rotated Böttcher plane, measured as a distance to the
point `rayPoint θ R` of the Böttcher plane. -/
theorem norm_rayRot_sub_rayPoint (θ R : ℝ) (w : ℂ) :
    ‖Work.Top.rayRot θ w - (R : ℂ)‖ = ‖w - Work.Top.NakaneData.rayPoint θ R‖ := by
  rw [← rayRot_rayPoint_self θ R, ← rayRot_sub θ w (Work.Top.NakaneData.rayPoint θ R),
    Work.Top.norm_rayRot]

/-- `InArc` is invariant under integer translations of the angle. -/
theorem InArc_add_int (x a b : ℝ) (k : ℤ) :
    Work.EL.InArc (x + k) a b ↔ Work.EL.InArc x a b := by
  unfold Work.EL.InArc
  rw [show x + (k : ℝ) - a = (x - a) + (k : ℝ) by ring, Int.fract_add_intCast]

/-- The potential of a point of the ray polygon is at most `log R`. -/
theorem pot_le_log_of_mem_polyCurve_aux (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R : ℝ} (hR : 1 < R) {z : ℂ} (hz : z ∈ Work.EL.polyCurve ps R) :
    Work.EL.pot hN z ≤ Real.log R := by
  rcases hz with ⟨P, _, hPy | hPa | hPb⟩ | ⟨θ, hθ, _hfar, rfl⟩
  · rw [hPy, Work.EL.pot_of_mem hN (landsN_mem_K hN P.lands_a)]
    exact le_of_lt (Real.log_pos hR)
  · exact Work.Top.NakaneData.rayPiece_subset_le hPa
  · exact Work.Top.NakaneData.rayPiece_subset_le hPb
  · exact le_of_eq (Work.EL.pot_rayPt hN hR)

/-- The point of the equipotential arc at the reference angle `midNear ps` lies on the ray
polygon. -/
theorem rayPt_midNear_mem_polyCurve_aux (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
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
    rw [h1, InArc_add_int]
    exact notInArc_midNear ps hA P hP
  have key : Work.EL.rayPt hN θ R = Work.EL.rayPt hN (θ - (k : ℝ)) R := by
    have h := Work.ELTop.rayPt_add_int hN (θ - (k : ℝ)) R k
    rw [show θ - (k : ℝ) + (k : ℝ) = θ by ring] at h
    exact h
  exact Or.inr ⟨θ - k, hrepr, hfar, key⟩

/-! ## The local picture around the equipotential point of the reference angle -/

/-- A point of a box around the point `R` of the rotated Böttcher plane does not lie in the
filled Julia set, provided `a < R`. -/
theorem notMem_K_of_box_aux (hN : Work.EL.DynB c φ) {θ R a : ℝ} (hR : 1 < R) (haR : a < R)
    {z : ℂ} (h1 : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a) :
    z ∉ Work.EL.K c := by
  intro hzK
  have h0 : Work.Top.rayRot θ (Work.EL.dynPhi c φ z) = 0 := by
    rw [Work.EL.dynPhi_of_mem hzK]; simp [Work.Top.rayRot]
  have hre : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| = R := by
    rw [h0]
    simp only [Complex.zero_re, zero_sub, abs_neg]
    exact abs_of_pos (by linarith)
  rw [hre] at h1
  linarith

/-- The box around the point `R` of the rotated Böttcher plane is open. -/
theorem isOpen_box_aux (hN : Work.EL.DynB c φ) (θ R a b : ℝ) (hR : 1 < R) (haR : a < R) :
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
          rw [Work.EL.dynPhi_of_mem hzK]; simp [Work.Top.rayRot]
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

/-- The superlevel set `{log R < pot}` is an unbounded preconnected subset of the complement of
the ray polygon; it therefore lies in the unbounded side. -/
theorem superlevel_subset_O (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R : ℝ} (hR : 1 < R) (S : Work.Top.Sides (Work.EL.polyCurve ps R)) :
    {z : ℂ | Real.log R < Work.EL.pot hN z} ⊆ S.O := by
  refine S.subset_O_of_unbounded
    (Work.Top.isPreconnected_gt_potential (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c φ) hN hR)
    ?_ ?_
  · intro z hz
    rw [Set.mem_compl_iff]
    intro hzc
    exact absurd (pot_le_log_of_mem_polyCurve_aux hN ps hR hzc) (not_le.mpr hz)
  · intro n
    obtain ⟨R₀, hR₀⟩ := hN.tendsto_potential (Real.log R + 1)
    refine ⟨((max R₀ (n : ℝ) + 1 : ℝ) : ℂ), ?_, ?_⟩
    · have h1 : R₀ ≤ ‖(((max R₀ (n : ℝ) + 1 : ℝ)) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := le_max_left R₀ (n : ℝ)
        linarith
      have h2 := hR₀ _ h1
      show Real.log R < Work.EL.pot hN _
      simpa only [Work.EL.pot_apply] using lt_of_lt_of_le (lt_add_one (Real.log R)) h2
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have := le_max_right R₀ (n : ℝ)
      push_cast
      linarith

/-- The outer half of the box is the set of the `R < ‖Φ z‖`-form used by
`Work.Top.isPreconnected_box_gt`. -/
theorem outer_eq_aux (hN : Work.EL.DynB c φ) {θ R a b : ℝ} (hR : 1 < R) (haR : a < R) :
    {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧ Real.log R < Work.EL.pot hN z}
      = {z : ℂ | z ∉ Work.EL.K c ∧ |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧
        R < ‖Work.EL.dynPhi c φ z‖} := by
  ext z
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hzK : z ∉ Work.EL.K c := notMem_K_of_box_aux hN hR haR h1
    refine ⟨hzK, h1, h2, ?_⟩
    have hpot : Work.EL.pot hN z = Real.log ‖Work.EL.dynPhi c φ z‖ :=
      Work.EL.pot_of_notMem hN hzK
    rw [hpot] at h3
    exact (Real.log_lt_log_iff (by linarith) (norm_pos_iff.mpr (hN.Phi_ne_zero hzK))).mp h3
  · rintro ⟨hzK, h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [Work.EL.pot_of_notMem hN hzK]
    exact (Real.log_lt_log_iff (by linarith) (norm_pos_iff.mpr (hN.Phi_ne_zero hzK))).mpr h3

/-- The inner half of the box is preconnected, provided `a < R - 1` (so that the box lies in
the exterior of the unit disc and avoids the filled Julia set): in the Böttcher plane it becomes
the convex set `{w | |w.re - R| < a ∧ |w.im| < b ∧ ‖w‖ < R}`. -/
theorem innerBox_preconnected' {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {θ R a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 1 < R) (ha1 : a < R - 1) :
    IsPreconnected {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧ Work.EL.pot hN z < Real.log R} := by
  have hRpos : 0 < R := by linarith
  set B : Set ℂ := {w : ℂ | |w.re - R| < a ∧ |w.im| < b ∧ ‖w‖ < R} with hBdef
  have hBpre : IsPreconnected B := Work.Top.reIm_box_inter_ball ha hb hRpos
  have hpreB : PreconnectedSpace ↥B := isPreconnected_iff_preconnectedSpace.mp hBpre
  have hre_gt : ∀ w ∈ B, 1 < w.re := by
    intro w hw
    rw [Set.mem_ofPred_eq] at hw
    have h2 := (abs_lt.mp hw.1).1
    linarith
  have hBsub : B ⊆ Work.Top.exteriorDisc := by
    intro w hw
    rw [Work.Top.mem_exteriorDisc]
    exact lt_of_lt_of_le (hre_gt w hw) (Complex.re_le_norm w)
  have hmem : ∀ w : ↥B, Work.Top.rayRot (-θ) (w : ℂ) ∈ Work.Top.exteriorDisc := by
    intro w
    rw [Work.Top.mem_exteriorDisc, Work.Top.norm_rayRot]
    exact hBsub w.2
  let g : ↥B → ℂ := fun w =>
    ((hN.e.symm (⟨Work.Top.rayRot (-θ) (w : ℂ), hmem w⟩ : ↥Work.Top.exteriorDisc) :
      ↥(Work.EL.K c)ᶜ) : ℂ)
  have hgc : Continuous g := by
    have h1 : Continuous fun w : ↥B =>
        (⟨Work.Top.rayRot (-θ) (w : ℂ), hmem w⟩ : ↥Work.Top.exteriorDisc) :=
      Continuous.subtype_mk ((Work.Top.continuous_rayRot (-θ)).comp continuous_subtype_val) hmem
    exact continuous_subtype_val.comp (hN.e.symm.continuous.comp h1)
  have hnotMem : ∀ w : ↥B, g w ∉ Work.EL.K c := fun w =>
    (hN.e.symm (⟨Work.Top.rayRot (-θ) (w : ℂ), hmem w⟩ : ↥Work.Top.exteriorDisc) :
      ↥(Work.EL.K c)ᶜ).2
  have hPhi_g : ∀ w : ↥B, Work.EL.dynPhi c φ (g w) = Work.Top.rayRot (-θ) (w : ℂ) := by
    intro w
    have hcw := hnotMem w
    have h1 : Work.EL.dynPhi c φ (g w) =
        ((hN.e ⟨g w, hcw⟩ : ↥Work.Top.exteriorDisc) : ℂ) := hN.he ⟨g w, hcw⟩
    rw [h1]
    have hx : (⟨g w, hcw⟩ : ↥(Work.EL.K c)ᶜ) =
        hN.e.symm (⟨Work.Top.rayRot (-θ) (w : ℂ), hmem w⟩ : ↥Work.Top.exteriorDisc) := by
      apply Subtype.ext; rfl
    rw [hx, Homeomorph.apply_symm_apply]
  have hrange : Set.range g = {z : ℂ |
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧ Work.EL.pot hN z < Real.log R} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      have hcw := hnotMem w
      have hPhi := hPhi_g w
      have hw1 : (1 : ℝ) < ‖(w : ℂ)‖ :=
        lt_of_lt_of_le (hre_gt w w.2) (Complex.re_le_norm (w : ℂ))
      refine ⟨?_, ?_, ?_⟩
      · rw [hPhi, Work.Top.rayRot_rayRot_neg]; exact w.2.1
      · rw [hPhi, Work.Top.rayRot_rayRot_neg]; exact w.2.2.1
      · rw [Work.EL.pot_of_notMem hN hcw, hPhi, Work.Top.norm_rayRot]
        exact Real.log_lt_log (by linarith) w.2.2.2
    · intro hz
      rw [Set.mem_ofPred_eq] at hz
      have hzK : z ∉ Work.EL.K c := notMem_K_of_box_aux hN hR (by linarith : a < R) hz.1
      have hnormR : ‖Work.EL.dynPhi c φ z‖ < R := by
        have hpot : Work.EL.pot hN z = Real.log ‖Work.EL.dynPhi c φ z‖ :=
          Work.EL.pot_of_notMem hN hzK
        rw [hpot] at hz
        exact (Real.log_lt_log_iff (norm_pos_iff.mpr (hN.Phi_ne_zero hzK)) (by linarith)).mp hz.2.2
      have hw : Work.Top.rayRot θ (Work.EL.dynPhi c φ z) ∈ B := by
        rw [hBdef]
        exact ⟨hz.1, hz.2.1, by rw [Work.Top.norm_rayRot]; exact hnormR⟩
      refine ⟨⟨Work.Top.rayRot θ (Work.EL.dynPhi c φ z), hw⟩, ?_⟩
      have hmemw := hmem ⟨Work.Top.rayRot θ (Work.EL.dynPhi c φ z), hw⟩
      have hx : hN.e ⟨z, hzK⟩ =
          (⟨Work.Top.rayRot (-θ) (Work.Top.rayRot θ (Work.EL.dynPhi c φ z)), hmemw⟩ :
            ↥Work.Top.exteriorDisc) := by
        apply Subtype.ext
        show ((hN.e ⟨z, hzK⟩ : ↥Work.Top.exteriorDisc) : ℂ) =
          Work.Top.rayRot (-θ) (Work.Top.rayRot θ (Work.EL.dynPhi c φ z))
        rw [Work.Top.rayRot_neg_rayRot]
        exact (hN.he ⟨z, hzK⟩).symm
      show ((hN.e.symm (⟨Work.Top.rayRot (-θ) (Work.Top.rayRot θ (Work.EL.dynPhi c φ z)),
        hmemw⟩ : ↥Work.Top.exteriorDisc) : ↥(Work.EL.K c)ᶜ) : ℂ) = z
      rw [← hx, Homeomorph.symm_apply_apply]
  rw [← hrange]
  exact isPreconnected_range hgc

/-- A point of the box whose potential is `log R` lies on the equipotential part of the ray
polygon, provided the box is angularly thin around the reference angle. -/
theorem mem_polyCurve_of_box_of_pot_eq_aux (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
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
  have hzK : z ∉ Work.EL.K c := notMem_K_of_box_aux hN hR haR h1
  have heq : Work.EL.rayPt hN
      (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) R = z :=
    Work.Top.rayPt_extAngle (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c φ) hN hR hzK hpot
  refine Or.inr ⟨Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z,
    ⟨Work.Top.NakaneData.extAngle_nonneg _ _, (Work.Top.NakaneData.extAngle_lt_one _ _).le⟩,
    hnear _ ⟨k, hk⟩, heq.symm⟩

/-- A point of the inner half of the box does not lie on the ray polygon, provided the box is
angularly thin around the reference angle and sufficiently far from the polygon angles. -/
theorem notMem_polyCurve_of_box_inner_aux (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R θ a b η : ℝ} (hR : 1 < R) (haR : a < R)
    (hnotangle : ∀ x : ℝ, (∃ k : ℤ, |x - (θ + k)| < η) → ∀ P ∈ ps, ∀ k : ℤ,
      x ≠ P.a + k ∧ x ≠ P.b + k)
    {z : ℂ} (h1 : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a)
    (h2 : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b)
    (hpot : Work.EL.pot hN z < Real.log R)
    (hthin : ∃ k : ℤ, |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - (θ + k)| < η) :
    z ∉ Work.EL.polyCurve ps R := by
  intro hzC
  have hzK : z ∉ Work.EL.K c := notMem_K_of_box_aux hN hR haR h1
  rcases hzC with ⟨P, hP, hPy | hPa | hPb⟩ | ⟨θ', hθ', _hfar, hz'⟩
  · exact hzK (by rw [hPy]; exact landsN_mem_K hN P.lands_a)
  · -- the point lies on the ray of angle `P.a` and on the ray of its own external angle
    have hzparam : z ∈ Work.EL.paramRay hN P.a :=
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
theorem notMem_polyCurve_of_box_outer_aux (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R : ℝ} (hR : 1 < R) {z : ℂ} (hpot : Real.log R < Work.EL.pot hN z) :
    z ∉ Work.EL.polyCurve ps R :=
  fun hz => absurd (pot_le_log_of_mem_polyCurve_aux hN ps hR hz) (not_le.mpr hpot)

/-- The point of the ray of the reference angle at a level just below `R` lies in the inner half
of the box. -/
theorem rayPt_mem_innerBox_aux (hN : Work.EL.DynB c φ) {θ R a b t₀ : ℝ} (ha : 0 < a) (hb : 0 < b)
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

/-! ## The main theorem -/

theorem polyRegion_eq_bounded_side {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    ∃ S : Work.Top.Sides (Work.EL.polyCurve ps R), Work.EL.polyRegion ps R = S.I := by
  classical
  set S : Work.Top.Sides (Work.EL.polyCurve ps R) :=
    hJ.sides (Work.EL.polyCurve ps R) hC with hS
  set θ : ℝ := Work.EL.midNear ps with hθ
  obtain ⟨η, hηpos, hη⟩ := midNear_nearArc_nbhd (hN := hN) ps hA
  obtain ⟨a₀, b₀, ha₀, hb₀, ha₀R, hthin₀⟩ :=
    box_angular_thin (hN := hN) (R := R) (θ := θ) hR hηpos
  set a : ℝ := min a₀ ((R - 1) / 2) with ha
  set b : ℝ := b₀ with hb
  have ha : 0 < a := lt_min ha₀ (by linarith)
  have hb : 0 < b := hb₀
  have haR : a < R := lt_of_le_of_lt (min_le_left _ _) ha₀R
  have ha1 : a < R - 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hthin : ∀ z : ℂ, |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a →
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b →
      ∃ k : ℤ, |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - (θ + k)| < η := by
    intro z h1 h2
    exact hthin₀ z (lt_of_lt_of_le h1 (min_le_left _ _)) h2
  have hη' : ∀ x : ℝ, (∃ k : ℤ, |x - (θ + k)| < η) →
      (∀ P ∈ ps, ¬ Work.EL.InArc x P.a P.b) ∧
      (∀ P ∈ ps, ∀ k : ℤ, x ≠ P.a + k ∧ x ≠ P.b + k) := by
    intro x hx
    rw [hθ] at hx
    exact hη x hx
  set P : Set ℂ := {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧ Work.EL.pot hN z < Real.log R}
      with hP
  set Q : Set ℂ := {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b ∧ Real.log R < Work.EL.pot hN z}
      with hQ
  set Bx : Set ℂ := {z : ℂ | |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a ∧
      |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b} with hBx
  -- the two halves are preconnected
  have hPconn : IsPreconnected P := by
    rw [hP]
    exact innerBox_preconnected' (hN := hN) ha hb hR ha1
  have hQconn : IsPreconnected Q := by
    rw [hQ, outer_eq_aux (hN := hN) (θ := θ) hR haR]
    exact Work.Top.isPreconnected_box_gt (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c φ) hN
      (θ := θ) ha hb hR haR
  -- the box is open
  have hBopen : IsOpen Bx := by
    rw [hBx]
    exact isOpen_box_aux hN θ R a b hR haR
  -- the equipotential point of the reference angle lies in the box and on the curve
  have hBC : (Bx ∩ Work.EL.polyCurve ps R).Nonempty := by
    refine ⟨Work.EL.rayPt hN θ R, ?_, ?_⟩
    · rw [hBx]
      have hΦ : Work.EL.dynPhi c φ (Work.EL.rayPt hN θ R) =
          Work.Top.NakaneData.rayPoint θ R := Work.Top.NakaneData.Phi_rayPt hN hR
      refine ⟨?_, ?_⟩
      · rw [hΦ, rayRot_rayPoint_self]
        simp only [Complex.ofReal_re, sub_self, abs_zero]
        exact ha
      · rw [hΦ, rayRot_rayPoint_self]
        simpa only [Complex.ofReal_im, abs_zero] using hb
    · rw [hθ]
      exact rayPt_midNear_mem_polyCurve_aux hN ps hA hR
  -- the box minus the curve is covered by the two halves
  have hcov : Bx \ Work.EL.polyCurve ps R ⊆ P ∪ Q := by
    intro z hz
    obtain ⟨hzb, hzc⟩ := hz
    rw [hBx] at hzb
    have hbox1 : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a := hzb.1
    have hbox2 : |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b := hzb.2
    have hne : Work.EL.pot hN z ≠ Real.log R := by
      intro heq
      exact hzc (mem_polyCurve_of_box_of_pot_eq_aux hN ps hR haR hthin
        (fun x hx => (hη' x hx).1) hbox1 hbox2 heq)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (by rw [hP]; exact ⟨hbox1, hbox2, h⟩)
    · exact Or.inr (by rw [hQ]; exact ⟨hbox1, hbox2, h⟩)
  -- the two halves are disjoint from the curve
  have hPC : Disjoint P (Work.EL.polyCurve ps R) := by
    rw [Set.disjoint_left]
    intro z hzP hzC
    rw [hP] at hzP
    exact notMem_polyCurve_of_box_inner_aux hN ps hR haR (fun x hx => (hη' x hx).2)
      hzP.1 hzP.2.1 hzP.2.2 (hthin z hzP.1 hzP.2.1) hzC
  have hQC : Disjoint Q (Work.EL.polyCurve ps R) := by
    rw [Set.disjoint_left]
    intro z hzQ hzC
    rw [hQ] at hzQ
    exact notMem_polyCurve_of_box_outer_aux hN ps hR hzQ.2.2 hzC
  -- the outer half meets the unbounded side
  have hQz : ∃ z ∈ Q, z ∈ S.O := by
    refine ⟨Work.EL.rayPt hN θ (R + a / 2), ?_, ?_⟩
    · have h1 : 1 < R + a / 2 := by linarith
      rw [hQ]
      have hΦ : Work.EL.dynPhi c φ (Work.EL.rayPt hN θ (R + a / 2)) =
          Work.Top.NakaneData.rayPoint θ (R + a / 2) := Work.Top.NakaneData.Phi_rayPt hN h1
      refine ⟨?_, ?_, ?_⟩
      · rw [hΦ, rayRot_rayPoint_self]
        simp only [Complex.ofReal_re]
        rw [abs_lt]
        exact ⟨by linarith, by linarith⟩
      · rw [hΦ, rayRot_rayPoint_self]
        simpa only [Complex.ofReal_im, abs_zero] using hb
      · rw [Work.EL.pot_rayPt hN h1]
        exact Real.log_lt_log (by linarith) (by linarith)
    · refine superlevel_subset_O hN ps hR S ?_
      show Real.log R < Work.EL.pot hN (Work.EL.rayPt hN θ (R + a / 2))
      rw [Work.EL.pot_rayPt hN (by linarith : 1 < R + a / 2)]
      exact Real.log_lt_log (by linarith) (by linarith)
  -- local two-sidedness: the inner half lies in the bounded side
  have hPI : P ⊆ S.I :=
    S.sides_of_halves (B := Bx) (P := P) (Q := Q) hBopen hBC hcov hPconn hQconn hPC hQC hQz
  -- the reference point of the region lies in the bounded side
  set t₀ : ℝ := (max 1 (R - a) + R) / 2 with ht₀
  have ht₀1 : 1 < t₀ := by
    rw [ht₀]; have := le_max_left (1 : ℝ) (R - a); linarith
  have ht₀R : t₀ < R := by
    rw [ht₀]
    have hm : max 1 (R - a) < R := max_lt hR (by linarith)
    linarith
  have ht₀a : R - a < t₀ := by
    rw [ht₀]; have := le_max_right (1 : ℝ) (R - a); linarith
  have hqP : Work.EL.rayPt hN θ t₀ ∈ P := by
    rw [hP]
    exact rayPt_mem_innerBox_aux hN ha hb hR ht₀1 ht₀a ht₀R
  have hqI : Work.EL.rayPt hN θ t₀ ∈ S.I := hPI hqP
  have hsq_gt1 : 1 < Real.sqrt R := (Real.lt_sqrt zero_le_one).mpr (by simpa using hR)
  have hsq_lt_R : Real.sqrt R < R := by
    have hsq := Real.sq_sqrt (le_of_lt (by linarith : (0 : ℝ) < R))
    nlinarith
  set Seg : Set ℂ := (fun t : ℝ => Work.EL.rayPt hN θ t) ''
      Set.Icc (min (Real.sqrt R) t₀) (max (Real.sqrt R) t₀) with hSeg
  have hseg_pre : IsPreconnected Seg := by
    rw [hSeg]
    refine IsPreconnected.image isPreconnected_Icc _ ?_
    refine (Work.Top.continuousOn_rayPt hN θ).mono ?_
    intro t ht
    rw [Set.mem_Icc] at ht
    rw [Set.mem_Ioi]
    have hmin : 1 < min (Real.sqrt R) t₀ := lt_min hsq_gt1 ht₀1
    linarith [ht.1]
  have hseg_sub : Seg ⊆ (Work.EL.polyCurve ps R)ᶜ := by
    intro z hz
    rw [hSeg] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Set.mem_compl_iff]
    rw [Set.mem_Icc] at ht
    have hmin : 1 < min (Real.sqrt R) t₀ := lt_min hsq_gt1 ht₀1
    have hmax : max (Real.sqrt R) t₀ < R := max_lt hsq_lt_R ht₀R
    rw [hθ]
    exact rayPt_midNear_misses_polyCurve hN ps hA hR (by linarith [ht.1])
      (by linarith [ht.2])
  have hxSeg : Work.EL.rayPt hN θ (Real.sqrt R) ∈ Seg := by
    rw [hSeg]
    exact ⟨Real.sqrt R, ⟨min_le_left _ _, le_max_left _ _⟩, rfl⟩
  have hqSeg : Work.EL.rayPt hN θ t₀ ∈ Seg := by
    rw [hSeg]
    exact ⟨t₀, ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩
  have hxI : Work.EL.rayPt hN θ (Real.sqrt R) ∈ S.I := by
    have hsegI : Seg ⊆ S.I := by
      rcases S.subset_of_preconnected hseg_pre hseg_sub with h | h
      · exact h
      · exact absurd (h hqSeg) (S.notMem_O_of_mem_I hqI)
    exact hsegI hxSeg
  have hxI' : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈ S.I := by
    rw [← hθ]
    exact hxI
  have hreg_sub : Work.EL.polyRegion ps R ⊆ S.I := by
    rcases S.subset_of_preconnected (Work.EL.isPreconnected_polyRegion ps R)
      (Work.EL.polyRegion_subset_compl ps R) with h | h
    · exact h
    · exact absurd (h (Work.ELTop.seed_mem_polyRegion hN ps hA hR)) (S.notMem_O_of_mem_I hxI')
  have hI_sub : S.I ⊆ Work.EL.polyRegion ps R :=
    S.preconnected_I.subset_connectedComponentIn hxI' S.subset_compl_I
  exact ⟨S, Set.Subset.antisymm hreg_sub hI_sub⟩

end Work.ELTop
