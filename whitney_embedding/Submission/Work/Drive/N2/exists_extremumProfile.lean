import Mathlib
import Submission.Work.Drive.N2.extremumCollapse

/-!
# Existence of the extremum profile `μ`

The extremum window block of the movie route (`Work.Drive.N2.extremumCollapseBlock`) consumes a
smooth positive profile `μ : ℝ → ℝ` which is `1` on `(-∞, a²]` and `1/√t` on `[b², ∞)`
(`0 < a < b`).  This file builds such a profile explicitly:

* `extremumCutoff a b t = smoothTransition ((t - a²)/(b² - a²))` — the smooth step which is `0` on
  `(-∞, a²]` and `1` on `[b², ∞)`;
* `extremumProfileArg a b t = 1 + extremumCutoff a b t * (t - 1)` — smooth, positive everywhere,
  equal to `1` for `t ≤ a²` and to `t` for `t ≥ b²`;
* `extremumProfile a b t = 1 / √(extremumProfileArg a b t)` — smooth, positive, equal to `1` for
  `t ≤ a²` and to `1/√t` for `t ≥ b²`.

Positivity of the argument is the only slightly non-formal point: on the transition region
`a² < t < b²` we have `t > 0`, so `1 + χ (t-1)` is a convex combination of `1` and `t` with weights
`1 - χ` and `χ`; equivalently, if `t < 1` then `1 + χ(t-1) ≥ 1 + (t-1) = t > 0`, and if `t ≥ 1`
then it is `≥ 1`.
-/

namespace Work.Drive.N2

open scoped ContDiff

/-- The smooth transition cutoff: `0` on `(-∞, a²]` and `1` on `[b², ∞)` (for `0 < a < b`). -/
noncomputable def extremumCutoff (a b : ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a ^ 2) / (b ^ 2 - a ^ 2))

/-- The argument of the profile: `1 + χ (t - 1)`, where `χ` is the transition cutoff.  It is `1`
for `t ≤ a²` and `t` for `t ≥ b²`. -/
noncomputable def extremumProfileArg (a b : ℝ) (t : ℝ) : ℝ :=
  1 + extremumCutoff a b t * (t - 1)

/-- **The extremum profile**: `t ↦ 1/√(1 + χ t (t-1))`. -/
noncomputable def extremumProfile (a b : ℝ) (t : ℝ) : ℝ :=
  1 / Real.sqrt (extremumProfileArg a b t)

lemma contDiff_extremumCutoff (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extremumCutoff a b) := by
  unfold extremumCutoff
  exact (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
    (((contDiff_id : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => x)).sub
      (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => a ^ 2))).div_const
        (b ^ 2 - a ^ 2))

lemma extremumCutoff_eq_zero {a b t : ℝ} (hab : 0 < a) (hab' : a < b) (ht : t ≤ a ^ 2) :
    extremumCutoff a b t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith)
  nlinarith [sq_nonneg a, sq_nonneg b]

lemma extremumCutoff_eq_one {a b t : ℝ} (hab : 0 < a) (hab' : a < b) (ht : b ^ 2 ≤ t) :
    extremumCutoff a b t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [one_le_div (by nlinarith : (0:ℝ) < b ^ 2 - a ^ 2)]
  linarith

lemma extremumProfileArg_eq_one {a b t : ℝ} (hab : 0 < a) (hab' : a < b) (ht : t ≤ a ^ 2) :
    extremumProfileArg a b t = 1 := by
  unfold extremumProfileArg
  rw [extremumCutoff_eq_zero hab hab' ht, zero_mul, add_zero]

lemma extremumProfileArg_eq_self {a b t : ℝ} (hab : 0 < a) (hab' : a < b) (ht : b ^ 2 ≤ t) :
    extremumProfileArg a b t = t := by
  unfold extremumProfileArg
  rw [extremumCutoff_eq_one hab hab' ht]
  ring

lemma extremumProfileArg_pos {a b t : ℝ} (hab : 0 < a) (hab' : a < b) :
    0 < extremumProfileArg a b t := by
  unfold extremumProfileArg
  have hnn : 0 ≤ extremumCutoff a b t := Real.smoothTransition.nonneg _
  have hle : extremumCutoff a b t ≤ 1 := Real.smoothTransition.le_one _
  by_cases ht : (1 : ℝ) ≤ t
  · have : 0 ≤ extremumCutoff a b t * (t - 1) := mul_nonneg hnn (by linarith)
    linarith
  · have ht1 : t < 1 := not_le.mp ht
    by_cases ht0 : t ≤ 0
    · have hz : extremumCutoff a b t = 0 :=
        extremumCutoff_eq_zero hab hab' (by nlinarith [sq_nonneg a])
      rw [hz]; norm_num
    · have h2 : (1 : ℝ) * (t - 1) ≤ extremumCutoff a b t * (t - 1) :=
        mul_le_mul_of_nonpos_right hle (by linarith)
      linarith

lemma contDiff_extremumProfile {a b : ℝ} (hab : 0 < a) (hab' : a < b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extremumProfile a b) := by
  have harg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extremumProfileArg a b) := by
    unfold extremumProfileArg
    exact contDiff_const.add ((contDiff_extremumCutoff a b).mul
      ((contDiff_id : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => x)).sub
        (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (1 : ℝ)))))
  unfold extremumProfile
  exact ContDiff.div contDiff_const
    (harg.sqrt (fun _ => ne_of_gt (extremumProfileArg_pos hab hab')))
    (fun _ => ne_of_gt (Real.sqrt_pos.mpr (extremumProfileArg_pos hab hab')))

lemma extremumProfile_pos {a b : ℝ} (hab : 0 < a) (hab' : a < b) (t : ℝ) :
    0 < extremumProfile a b t := by
  unfold extremumProfile
  exact div_pos one_pos (Real.sqrt_pos.mpr (extremumProfileArg_pos hab hab'))

lemma extremumProfile_eq_one {a b t : ℝ} (hab : 0 < a) (hab' : a < b) (ht : t ≤ a ^ 2) :
    extremumProfile a b t = 1 := by
  unfold extremumProfile
  rw [extremumProfileArg_eq_one hab hab' ht, Real.sqrt_one, div_one]

lemma extremumProfile_eq_inv_sqrt {a b t : ℝ} (hab : 0 < a) (hab' : a < b) (ht : b ^ 2 ≤ t) :
    extremumProfile a b t = 1 / Real.sqrt t := by
  unfold extremumProfile
  rw [extremumProfileArg_eq_self hab hab' ht]

/-- **The extremum profile exists.** -/
theorem exists_extremumProfile {a b : ℝ} (hab : 0 < a) (hab' : a < b) :
    ∃ μ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ ∧ (∀ t : ℝ, 0 < μ t) ∧
      (∀ t : ℝ, t ≤ a ^ 2 → μ t = 1) ∧
      (∀ t : ℝ, b ^ 2 ≤ t → μ t = 1 / Real.sqrt t) :=
  ⟨extremumProfile a b, contDiff_extremumProfile hab hab',
   fun t => extremumProfile_pos hab hab' t,
   fun _ ht => extremumProfile_eq_one hab hab' ht,
   fun _ ht => extremumProfile_eq_inv_sqrt hab hab' ht⟩

end Work.Drive.N2
