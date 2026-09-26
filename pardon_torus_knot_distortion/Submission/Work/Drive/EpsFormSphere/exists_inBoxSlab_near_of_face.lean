import Mathlib
import Submission.Work.Drive.EpsFormSphere.Sideways

namespace Work.Drive.EpsFormSphere

open LeanEval.KnotTheory.PardonDistortion
open Filter Set

/-!
# Slab points accumulate at a transversal face crossing

The knot model has a smooth curve `K.curve : ℝ → R3`.  Fix a slab
`slabZ c σ u h = {y : |y (σ 2) - (c (σ 2) + u)| < h}` and a parameter `t` at which the curve lies
*on the boundary* of the slab (`|K.curve t (σ 2) - (c (σ 2) + u)| = h`) and crosses it transversally
(`(deriv K.curve t) (σ 2) ≠ 0`).  Then arbitrarily close to `t` the curve enters the slab, i.e. the
parameters at which the curve lies in the slab accumulate at `t`.

The analytic content is the following elementary fact, proved here as
`exists_near_lt_self` / `exists_near_gt_self`: if `f : ℝ → ℝ` is continuous with continuous
derivative and `deriv f t ≠ 0`, then `f` takes values strictly below (respectively strictly above)
`f t` arbitrarily close to `t`.  Indeed `f` is strictly monotone on a neighbourhood of `t`; so from
`|f t| = h` and the continuity of `f`, one of the two one-sided branches of the curve at `t` lies in
`(-h, h)`.  The openness of `PBox` then upgrades the slab membership to membership of the box.
-/

/-- **Both one-sided values of a function with positive derivative.**  If `f` is continuous with
continuous derivative at `t` and `0 < deriv f t`, then `f` is strictly increasing on a neighbourhood
of `t`; in particular it takes values below `f t` (moving left) and above `f t` (moving right)
arbitrarily close to `t`. -/
private lemma near_lt_near_gt_of_deriv_pos {f : ℝ → ℝ} {t : ℝ}
    (hcont : Continuous f) (hdcont : Continuous (deriv f)) (ha : 0 < deriv f t) :
    ∀ ε : ℝ, 0 < ε → (∃ r : ℝ, |r - t| < ε ∧ f r < f t) ∧
      (∃ r : ℝ, |r - t| < ε ∧ f t < f r) := by
  intro ε hε
  have hev : ∀ᶠ r in nhds t, 0 < deriv f r := (isOpen_lt continuous_const hdcont).mem_nhds ha
  obtain ⟨δ1, hδ1pos, hδ1⟩ := Metric.mem_nhds_iff.mp hev
  have hmono : StrictMonoOn f (Set.Ioo (t - δ1) (t + δ1)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcont.continuousOn ?_
    intro x hx
    rw [interior_Ioo] at hx
    exact hδ1 (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]
                  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  set δ := min ε δ1 with hδdef
  have hδpos : 0 < δ := lt_min hε hδ1pos
  have hδδ1 : δ ≤ δ1 := min_le_right _ _
  have htmem : t ∈ Set.Ioo (t - δ1) (t + δ1) := ⟨by linarith, by linarith⟩
  constructor
  · refine ⟨t - δ / 2, ?_, ?_⟩
    · have hd : (t - δ / 2) - t = -(δ / 2) := by ring
      rw [hd, abs_neg, abs_of_pos (by linarith)]
      linarith [min_le_left ε δ1]
    · refine hmono ?_ htmem (by linarith)
      exact ⟨by linarith, by linarith⟩
  · refine ⟨t + δ / 2, ?_, ?_⟩
    · have hd : (t + δ / 2) - t = δ / 2 := by ring
      rw [hd, abs_of_pos (by linarith)]
      linarith [min_le_left ε δ1]
    · exact hmono htmem ⟨by linarith, by linarith⟩ (by linarith)

/-- **Both one-sided values of a function with negative derivative.**  If `f` is continuous with
continuous derivative at `t` and `deriv f t < 0`, then `f` is strictly decreasing on a neighbourhood
of `t`; in particular it takes values below `f t` (moving right) and above `f t` (moving left)
arbitrarily close to `t`. -/
private lemma near_lt_near_gt_of_deriv_neg {f : ℝ → ℝ} {t : ℝ}
    (hcont : Continuous f) (hdcont : Continuous (deriv f)) (ha : deriv f t < 0) :
    ∀ ε : ℝ, 0 < ε → (∃ r : ℝ, |r - t| < ε ∧ f r < f t) ∧
      (∃ r : ℝ, |r - t| < ε ∧ f t < f r) := by
  intro ε hε
  have hev : ∀ᶠ r in nhds t, deriv f r < 0 := (isOpen_lt hdcont continuous_const).mem_nhds ha
  obtain ⟨δ1, hδ1pos, hδ1⟩ := Metric.mem_nhds_iff.mp hev
  have hanti : StrictAntiOn f (Set.Ioo (t - δ1) (t + δ1)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) hcont.continuousOn ?_
    intro x hx
    rw [interior_Ioo] at hx
    exact hδ1 (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]
                  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  set δ := min ε δ1 with hδdef
  have hδpos : 0 < δ := lt_min hε hδ1pos
  have hδδ1 : δ ≤ δ1 := min_le_right _ _
  have htmem : t ∈ Set.Ioo (t - δ1) (t + δ1) := ⟨by linarith, by linarith⟩
  constructor
  · refine ⟨t + δ / 2, ?_, ?_⟩
    · have hd : (t + δ / 2) - t = δ / 2 := by ring
      rw [hd, abs_of_pos (by linarith)]
      linarith [min_le_left ε δ1]
    · exact hanti htmem ⟨by linarith, by linarith⟩ (by linarith)
  · refine ⟨t - δ / 2, ?_, ?_⟩
    · have hd : (t - δ / 2) - t = -(δ / 2) := by ring
      rw [hd, abs_neg, abs_of_pos (by linarith)]
      linarith [min_le_left ε δ1]
    · refine hanti ?_ htmem (by linarith)
      exact ⟨by linarith, by linarith⟩

/-- At a point with nonzero derivative, a `C¹` function takes values strictly below its value
arbitrarily close by. -/
private lemma exists_near_lt_self {f : ℝ → ℝ} {t : ℝ} (hcont : Continuous f)
    (hdcont : Continuous (deriv f)) (ha : deriv f t ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, |r - t| < ε ∧ f r < f t := by
  intro ε hε
  rcases lt_or_gt_of_ne ha with h | h
  · exact (near_lt_near_gt_of_deriv_neg hcont hdcont h ε hε).1
  · exact (near_lt_near_gt_of_deriv_pos hcont hdcont h ε hε).1

/-- At a point with nonzero derivative, a `C¹` function takes values strictly above its value
arbitrarily close by. -/
private lemma exists_near_gt_self {f : ℝ → ℝ} {t : ℝ} (hcont : Continuous f)
    (hdcont : Continuous (deriv f)) (ha : deriv f t ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, |r - t| < ε ∧ f t < f r := by
  intro ε hε
  rcases lt_or_gt_of_ne ha with h | h
  · exact (near_lt_near_gt_of_deriv_neg hcont hdcont h ε hε).2
  · exact (near_lt_near_gt_of_deriv_pos hcont hdcont h ε hε).2

/-- **At a transversal crossing of a slab face, the knot admits in-box slab points arbitrarily close.** -/
theorem exists_inBoxSlab_near_of_face {K : LeanEval.KnotTheory.PardonDistortion.Knot}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u h s : ℝ}
    {t : ℝ} (hpos : 0 < h)
    (hface : (deriv K.curve t) (σ 2) ≠ 0)
    (hbox : K.curve t ∈ Submission.PBox s c σ)
    (hlevel : |K.curve t (σ 2) - (c (σ 2) + u)| = h) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, |r - t| < ε ∧ K.curve r ∈ Work.Drive.EpsSphere.slabZ c σ u h ∧
      K.curve r ∈ Submission.PBox s c σ := by
  intro ε hε
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K.curve := K.smooth
  have hdiff : ∀ r : ℝ, HasDerivAt K.curve (deriv K.curve r) r := fun r =>
    ((K.smooth.differentiable (by simp)) r).hasDerivAt
  -- the level coordinate of the curve, shifted so that the slab is `{|f ·| < h}`
  let f : ℝ → ℝ := fun r => K.curve r (σ 2) - (c (σ 2) + u)
  have hf_cont : Continuous f := by
    show Continuous fun r : ℝ => K.curve r (σ 2) - (c (σ 2) + u)
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).comp hsm.continuous |>.sub
      (continuous_const : Continuous fun _ : ℝ => c (σ 2) + u)
  have hf_deriv : deriv f = fun r : ℝ => (deriv K.curve r) (σ 2) := by
    funext r
    show deriv (fun s : ℝ => K.curve s (σ 2) - (c (σ 2) + u)) r = (deriv K.curve r) (σ 2)
    rw [deriv_sub_const]
    exact ((PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) (σ 2)).hasFDerivAt.comp_hasDerivAt r
      (hdiff r)).deriv
  have hf_dcont : Continuous (deriv f) := by
    rw [hf_deriv]
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).comp (hsm.continuous_deriv (by simp))
  have hane : deriv f t ≠ 0 := by rw [hf_deriv]; exact hface
  have habs : |f t| = h := by
    have : f t = K.curve t (σ 2) - (c (σ 2) + u) := rfl
    rw [this]; exact hlevel
  -- the curve stays in the (open) box near `t`
  have hbox_nhds : ∀ᶠ r in nhds t, K.curve r ∈ Submission.PBox s c σ :=
    hsm.continuous.continuousAt.eventually
      ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hbox)
  obtain ⟨δ3, hδ3pos, hδ3⟩ := Metric.mem_nhds_iff.mp hbox_nhds
  have h3 : ∀ r : ℝ, |r - t| < δ3 → K.curve r ∈ Submission.PBox s c σ := fun r hr =>
    hδ3 (by rw [Metric.mem_ball, Real.dist_eq]; exact hr)
  -- and `f` stays within `2h` of `f t` near `t`
  have hct : ContinuousAt f t := hf_cont.continuousAt
  obtain ⟨δ2, hδ2pos, hδ2⟩ := (Metric.continuousAt_iff.mp hct) (2 * h) (by linarith)
  have h2 : ∀ r : ℝ, |r - t| < δ2 → |f r - f t| < 2 * h := by
    intro r hr
    have hh := hδ2 (x := r) (by rw [Real.dist_eq]; exact hr)
    rwa [Real.dist_eq] at hh
  have hmin : 0 < min (min ε δ2) δ3 := lt_min (lt_min hε hδ2pos) hδ3pos
  have hle1 : min (min ε δ2) δ3 ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hle2 : min (min ε δ2) δ3 ≤ δ2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hle3 : min (min ε δ2) δ3 ≤ δ3 := min_le_right _ _
  -- the curve is on one face of the slab: `f t = h` or `f t = -h`
  rcases (abs_eq (le_of_lt hpos)).mp habs with hft | hft
  · -- upper face: move to the side on which `f` decreases
    obtain ⟨r, hrt, hrlt⟩ := exists_near_lt_self hf_cont hf_dcont hane (min (min ε δ2) δ3) hmin
    have hr2 : |r - t| < δ2 := lt_of_lt_of_le hrt hle2
    refine ⟨r, lt_of_lt_of_le hrt hle1, ?_, ?_⟩
    · have h1 : f r < h := by rw [← hft]; exact hrlt
      have h2' : -h < f r := by
        have hh := (abs_lt.mp (h2 r hr2)).1
        linarith
      have h3' : |f r| < h := abs_lt.mpr ⟨h2', h1⟩
      simpa only [Work.Drive.EpsSphere.slabZ, Set.mem_ofPred_eq] using h3'
    · exact h3 r (lt_of_lt_of_le hrt hle3)
  · -- lower face: move to the side on which `f` increases
    obtain ⟨r, hrt, hrgt⟩ := exists_near_gt_self hf_cont hf_dcont hane (min (min ε δ2) δ3) hmin
    have hr2 : |r - t| < δ2 := lt_of_lt_of_le hrt hle2
    refine ⟨r, lt_of_lt_of_le hrt hle1, ?_, ?_⟩
    · have h1 : f r < h := by
        have hh := (abs_lt.mp (h2 r hr2)).2
        linarith
      have h2' : -h < f r := by linarith
      have h3' : |f r| < h := abs_lt.mpr ⟨h2', h1⟩
      simpa only [Work.Drive.EpsSphere.slabZ, Set.mem_ofPred_eq] using h3'
    · exact h3 r (lt_of_lt_of_le hrt hle3)

end Work.Drive.EpsFormSphere
