import Mathlib
import Submission.Work.OddRadon.RadialDefs
import Submission.Work.Geometry.Ulam.radial_profile_reconstruction
import Submission.Work.Geometry.Ulam.profileGlue_continuous

namespace Work.OddRadon

open Set Filter
open scoped Topology ContDiff

theorem strictConcaveOn_profileGlue (R r : ℝ → ℝ) {η : ℝ} (hη : 0 < η)
    (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hR_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv R) α| ≤ η)
    (hr_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv r) α| ≤ η)
    (hf_smooth : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (Commons.Geometry.Ulam.profileGlue R r) (Set.Ioo (-(r 0)) (R 0))) :
    StrictConcaveOn ℝ (Set.Ioo (-(r 0)) (R 0)) (Commons.Geometry.Ulam.profileGlue R r) := by
  let f : ℝ → ℝ := Commons.Geometry.Ulam.profileGlue R r
  change StrictConcaveOn ℝ (Set.Ioo (-(r 0)) (R 0)) f
  have ha : -(r 0) < 0 := neg_lt_zero.mpr (Commons.Geometry.Ulam.left_zero_pos r hr_pos)
  have hb : 0 < R 0 := Commons.Geometry.Ulam.right_zero_pos R hR_pos
  -- continuity of the first derivative on the open interval
  have hderiv_cont : ContinuousOn (deriv f) (Set.Ioo (-(r 0)) (R 0)) :=
    hf_smooth.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  -- the second derivative of the glued profile is negative on the right half
  have hright2 : ∀ z ∈ Set.Ioo 0 (R 0), deriv (deriv f) z < 0 := by
    intro z hz
    have hev : f =ᶠ[𝓝 z] Commons.Geometry.Ulam.rightProfile R := by
      filter_upwards [Ioo_mem_nhds hz.1 hz.2] with t ht
      exact Commons.Geometry.Ulam.profileGlue_eq_rightProfile R r ht
    have h2 : deriv (deriv f) z = deriv (deriv (Commons.Geometry.Ulam.rightProfile R)) z :=
      hev.deriv.deriv_eq
    rw [h2]
    exact Commons.Geometry.Ulam.rightProfile_deriv2_neg R hη hηsmall hR_cont hR_pos hR_lower
      hR_deriv_bound hR_second_bound z hz
  -- the reflection of the glued profile
  let F : ℝ → ℝ := fun s => f (-s)
  have hF_eq : ∀ s ∈ Set.Ioo 0 (r 0), F s = Commons.Geometry.Ulam.rightProfile r s := by
    intro s hs
    have hs' : -s ∈ Set.Ioo (-(r 0)) 0 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h1 : f (-s) = Commons.Geometry.Ulam.leftProfile r (-s) :=
      Commons.Geometry.Ulam.profileGlue_eq_leftProfile R r hη hηsmall hr_cont hr_pos hr_lower
        hr_deriv_bound hs'
    simp only [F, h1, Commons.Geometry.Ulam.leftProfile, neg_neg]
  have hderivF : deriv F = fun s => -deriv f (-s) := by
    funext s
    have h := deriv_comp_mul_left (-1 : ℝ) f s
    simpa [F, neg_one_mul] using h
  -- the second derivative of the reflected profile is negative on the positive half
  have hF2 : ∀ z ∈ Set.Ioo 0 (r 0), deriv (deriv F) z < 0 := by
    intro z hz
    have hev : F =ᶠ[𝓝 z] Commons.Geometry.Ulam.rightProfile r := by
      filter_upwards [Ioo_mem_nhds hz.1 hz.2] with t ht
      exact hF_eq t ht
    have h2 : deriv (deriv F) z = deriv (deriv (Commons.Geometry.Ulam.rightProfile r)) z :=
      hev.deriv.deriv_eq
    rw [h2]
    exact Commons.Geometry.Ulam.rightProfile_deriv2_neg r hη hηsmall hr_cont hr_pos hr_lower
      hr_deriv_bound hr_second_bound z hz
  -- Comparison at the seam, from the right: `f'` is strictly decreasing on `[0, y]`
  have hright_cmp : ∀ y, y ∈ Set.Ioo 0 (R 0) → deriv f y < deriv f 0 := by
    intro y hy
    have hcont : ContinuousOn (deriv f) (Set.Icc 0 y) :=
      hderiv_cont.mono (by
        intro z hz
        exact ⟨by linarith [hz.1, ha], by linarith [hz.2, hy.2]⟩)
    have hneg : ∀ z ∈ interior (Set.Icc 0 y), deriv (deriv f) z < 0 := by
      intro z hz
      rw [interior_Icc] at hz
      exact hright2 z ⟨hz.1, by linarith [hz.2, hy.2]⟩
    exact strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) y) hcont hneg
      ⟨le_rfl, hy.1.le⟩ ⟨hy.1.le, le_rfl⟩ hy.1
  -- Comparison at the seam, from the left: `deriv F` is strictly decreasing on `[0, -x]`
  have hleft_cmp : ∀ x, x ∈ Set.Ioo (-(r 0)) 0 → deriv f 0 < deriv f x := by
    intro x hx
    have hxpos : 0 < -x := neg_pos.mpr hx.2
    have hnr : -x < r 0 := by linarith [hx.1]
    have hcont : ContinuousOn (deriv f) (Set.Icc x 0) :=
      hderiv_cont.mono (by
        intro z hz
        exact ⟨by linarith [hz.1, hx.1], by linarith [hz.2, hb]⟩)
    have hcontF : ContinuousOn (deriv F) (Set.Icc 0 (-x)) := by
      have hmaps : Set.MapsTo (fun z : ℝ => -z) (Set.Icc 0 (-x)) (Set.Icc x 0) := by
        intro z hz
        exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
      have hcomp : ContinuousOn (fun s : ℝ => deriv f (-s)) (Set.Icc 0 (-x)) :=
        hcont.comp continuous_neg.continuousOn hmaps
      have hcomp' : ContinuousOn (fun s : ℝ => -deriv f (-s)) (Set.Icc 0 (-x)) := hcomp.neg
      rw [hderivF]
      exact hcomp'
    have hneg : ∀ z ∈ interior (Set.Icc 0 (-x)), deriv (deriv F) z < 0 := by
      intro z hz
      rw [interior_Icc] at hz
      exact hF2 z ⟨hz.1, by linarith [hz.2, hnr]⟩
    have hSA := strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) (-x)) hcontF hneg
    have hlt : deriv F (-x) < deriv F 0 :=
      hSA ⟨le_rfl, hxpos.le⟩ ⟨hxpos.le, le_rfl⟩ hxpos
    have e1 : deriv F (-x) = -deriv f x := by rw [hderivF]; simp
    have e2 : deriv F 0 = -deriv f 0 := by rw [hderivF]; simp
    linarith
  -- `deriv f` is strictly antitone on the whole open interval
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioo (-(r 0)) (R 0)) hf_smooth.continuousOn ?_
  rw [interior_Ioo]
  intro x hx y hy hxy
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · rcases lt_trichotomy y 0 with hyneg | hyzero | hypos
    · -- x < y < 0 : reflect to the positive half
      have hcont : ContinuousOn (deriv f) (Set.Icc x y) :=
        hderiv_cont.mono (by
          intro z hz
          exact ⟨by linarith [hz.1, hx.1], by linarith [hz.2, hy.2]⟩)
      have hmaps : Set.MapsTo (fun z : ℝ => -z) (Set.Icc (-y) (-x)) (Set.Icc x y) := by
        intro z hz
        exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
      have hcontF : ContinuousOn (deriv F) (Set.Icc (-y) (-x)) := by
        have hcomp : ContinuousOn (fun s : ℝ => deriv f (-s)) (Set.Icc (-y) (-x)) :=
          hcont.comp continuous_neg.continuousOn hmaps
        have hcomp' : ContinuousOn (fun s : ℝ => -deriv f (-s)) (Set.Icc (-y) (-x)) := hcomp.neg
        rw [hderivF]
        exact hcomp'
      have hneg : ∀ z ∈ interior (Set.Icc (-y) (-x)), deriv (deriv F) z < 0 := by
        intro z hz
        rw [interior_Icc] at hz
        exact hF2 z ⟨by linarith [hz.1, hyneg], by linarith [hz.2, hx.1]⟩
      have hSA := strictAntiOn_of_deriv_neg (convex_Icc (-y) (-x)) hcontF hneg
      have hlt : deriv F (-x) < deriv F (-y) :=
        hSA ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
      have e1 : deriv F (-x) = -deriv f x := by rw [hderivF]; simp
      have e2 : deriv F (-y) = -deriv f y := by rw [hderivF]; simp
      linarith
    · -- y = 0
      subst hyzero
      exact hleft_cmp x ⟨hx.1, hxneg⟩
    · -- x < 0 < y
      have h1 : deriv f 0 < deriv f x := hleft_cmp x ⟨hx.1, hxneg⟩
      have h2 : deriv f y < deriv f 0 := hright_cmp y ⟨hypos, hy.2⟩
      linarith
  · -- x = 0 < y
    subst hxzero
    exact hright_cmp y ⟨hxy, hy.2⟩
  · -- 0 < x < y
    have hcont : ContinuousOn (deriv f) (Set.Icc x y) :=
      hderiv_cont.mono (by
        intro z hz
        exact ⟨by linarith [hz.1, hx.1], by linarith [hz.2, hy.2]⟩)
    have hneg : ∀ z ∈ interior (Set.Icc x y), deriv (deriv f) z < 0 := by
      intro z hz
      rw [interior_Icc] at hz
      exact hright2 z ⟨by linarith [hz.1, hxpos], by linarith [hz.2, hy.2]⟩
    exact strictAntiOn_of_deriv_neg (convex_Icc x y) hcont hneg
      ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy

end Work.OddRadon
