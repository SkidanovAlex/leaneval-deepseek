import Mathlib
import Submission.Work.Geometry.Ulam.radial_profile_reconstruction
import Submission.Work.Geometry.Ulam.right_profile_concave
import Submission.Work.Geometry.Ulam.right_profile_endpoint_deriv

namespace Commons.Geometry.Ulam

open Set
open scoped Topology ContDiff

noncomputable section

/-- The left-branch profile, defined as the reflection of the right-branch
profile.  On the actual left arc it agrees with
`r (leftAlpha r t) * sin (leftAlpha r t)`; the reflection form is the one that
makes the concavity statement a formal consequence of the right-branch one. -/
noncomputable def leftProfile (r : ℝ → ℝ) (t : ℝ) : ℝ := rightProfile r (-t)

/-- The left branch is strictly concave on `[-(r 0), 0]` as soon as the right
branch is continuous on `[0, r 0]`; concavity is transported by the reflection
`t ↦ -t`. -/
lemma leftProfile_strictConcaveOn_of_continuous
    (r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hr_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv r) α| ≤ η)
    (hcont : ContinuousOn (rightProfile r) (Set.Icc 0 (r 0))) :
    StrictConcaveOn ℝ (Set.Icc (-(r 0)) 0) (leftProfile r) := by
  have hsc := rightProfile_strictConcaveOn_of_continuous r hη hηsmall hr_cont hr_pos hr_lower
    hr_deriv_bound hr_second_bound hcont
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : -x ∈ Set.Icc 0 (r 0) := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : -y ∈ Set.Icc 0 (r 0) := by
    constructor <;> linarith [hy.1, hy.2]
  have hxy' : -x ≠ -y := by
    intro h
    exact hxy (by linarith)
  have h := hsc.2 hx' hy' hxy' ha hb hab
  dsimp [leftProfile] at h ⊢
  convert h using 1 <;> ring

end

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam

/-- Unconditional left-branch strict concavity. -/
lemma leftProfile_strictConcaveOn
    (r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hr_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv r) α| ≤ η) :
    StrictConcaveOn ℝ (Set.Icc (-(r 0)) 0) (leftProfile r) :=
  leftProfile_strictConcaveOn_of_continuous r hη hηsmall hr_cont hr_pos hr_lower
    hr_deriv_bound hr_second_bound
    (rightProfile_continuousOn r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound)

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam

/-- The left inverse branch at `t < 0` equals the right inverse branch at
`-t`. -/
lemma leftAlpha_eq_rightAlpha_neg
    (r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    {t : ℝ} (ht : t ∈ Set.Ioo (-(r 0)) 0) :
    leftAlpha r t = rightAlpha r (-t) := by
  have ht_left : t ∈ Set.Icc (-(r 0)) 0 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have ht_right : -t ∈ Set.Icc 0 (r 0) := by
    constructor <;> linarith [ht.1, ht.2]
  have hleft := leftAlpha_spec r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound ht_left
  have hright := rightAlpha_spec r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound ht_right
  have hmono := leftArc_fst_strictMonoOn r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
  apply hmono.injOn hleft.1 hright.1
  change -(r (leftAlpha r t) * Real.cos (leftAlpha r t)) =
    -(r (rightAlpha r (-t)) * Real.cos (rightAlpha r (-t)))
  rw [hleft.2, hright.2]
  ring

/-- On the negative half, `profileGlue` is the left branch. -/
lemma profileGlue_eq_leftProfile
    (R r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    {t : ℝ} (ht : t ∈ Set.Ioo (-(r 0)) 0) :
    profileGlue R r t = leftProfile r t := by
  have ht_left : t ∈ Set.Icc (-(r 0)) 0 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have ht_not_right : t ∉ Set.Icc 0 (R 0) := by
    intro h
    linarith [h.1, ht.2]
  have hα := leftAlpha_eq_rightAlpha_neg r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound ht
  dsimp [profileGlue, leftProfile, rightProfile]
  rw [if_neg ht_not_right, if_pos ht_left, hα]

/-- On the positive half, `profileGlue` is the right branch. -/
lemma profileGlue_eq_rightProfile
    (R r : ℝ → ℝ) {t : ℝ} (ht : t ∈ Set.Ioo 0 (R 0)) :
    profileGlue R r t = rightProfile R t := by
  have ht_right : t ∈ Set.Icc 0 (R 0) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  simp [profileGlue, ht_right, rightProfile]

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam

/-- The left branch as a concave function on its half-interval. -/
lemma leftProfile_concaveOn
    (r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hr_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv r) α| ≤ η) :
    ConcaveOn ℝ (Set.Icc (-(r 0)) 0) (leftProfile r) :=
  (leftProfile_strictConcaveOn r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
    hr_second_bound).concaveOn

end Commons.Geometry.Ulam


namespace Commons.Geometry.Ulam

/-- The left-branch endpoint derivative, by reflection of the right-branch
endpoint formula. -/
lemma leftProfile_derivWithin_zero
    (r : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hδ : 0 < δ)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_nhds : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α) :
    derivWithin (leftProfile r) (Set.Icc (-(r 0)) 0) 0 = deriv r (Real.pi / 2) / r (Real.pi / 2) := by
  have h := rightProfile_derivWithin_zero r hη hηsmall hδ hr_cont hr_nhds hr_pos hr_lower hr_deriv_bound
  rw [show leftProfile r = fun t => rightProfile r (-t) by rfl]
  rw [derivWithin_comp_neg]
  rw [show -(Set.Icc (-(r 0)) 0) = Set.Icc 0 (r 0) by ext t; simp [and_comm]]
  rw [neg_zero, h]
  ring

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam

/-- The seam comparison is exactly the field inequality
`deriv r (π/2)/r(π/2) + deriv R (π/2)/R(π/2) ≥ 0`. -/
lemma profileGlue_seam_inequality
    (R r : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hδ : 0 < δ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR_nhds : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hr_nhds : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hseam : 0 ≤ deriv r (Real.pi / 2) / r (Real.pi / 2) + deriv R (Real.pi / 2) / R (Real.pi / 2)) :
    derivWithin (rightProfile R) (Set.Icc 0 (R 0)) 0 ≤
      derivWithin (leftProfile r) (Set.Icc (-(r 0)) 0) 0 := by
  have hR := rightProfile_derivWithin_zero R hη hηsmall hδ hR_cont hR_nhds hR_pos hR_lower
    hR_deriv_bound
  have hL := leftProfile_derivWithin_zero r hη hηsmall hδ hr_cont hr_nhds hr_pos hr_lower
    hr_deriv_bound
  rw [hR, hL]
  rw [neg_div]
  linarith [hseam]

end Commons.Geometry.Ulam
