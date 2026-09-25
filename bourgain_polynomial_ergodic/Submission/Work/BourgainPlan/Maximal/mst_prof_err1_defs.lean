import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.mstHat_bound
import Submission.Work.BourgainPlan.Maximal.mstHat_decay
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation

/-!
# The a.e. dictionary for the MST bump, and the radial majorant of `mstHat`

The target of this lane is the `ℓ¹` bound for the Fourier coefficients of the *profile times bump*
`h_n = star (mstProf P (2^n) ·) · mstEta d χ η n`.  The two analytic inputs about the level bump are
already available in the sibling modules:

* `mstHat η t = ∫_{−1/2}^{1/2} η u · e(−t u) du` (`mst_err1_bump_defs`), the period-`1` Fourier
  transform of the fixed bump `η`, with the level scale `mstScale d χ n = 2^{n(d−χ)}`;
* `mstHat_bound` — `‖mstHat η t‖ ≤ M` when `‖η‖ ≤ M`;
* `mstHat_decay` — `‖mstHat η t‖ ≤ E / t²` when the fundamental bump
  `circleLift (mstEta d χ η 0)` is `C²` (two integrations by parts).

This file adds the two things the coefficient computation and the sampling bound need on top:

* `profEta_ae_eq_circleLift` / `aestronglyMeasurable_profEta` — the a.e. dictionary between the bump
  `η` and its fundamental lift `u ↦ circleLift (mstEta d χ η 0) (−u)`, in particular a.e. strong
  measurability of `η` (which is what makes the Fubini step of `profCoeff_eq` legitimate);
* `mstHat_le_radial` — the combination of the two bounds into a single radial majorant
  `‖mstHat η t‖ ≤ A · (1 + |t|)^{−2}`, the hypothesis of the sampling bound
  `Work.BourgainPlan.Maximal.profSampling_bound`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- **The a.e. dictionary for the MST bump.**  If `η` vanishes for `|x| > 1/2`, then `η` agrees a.e.
with the reflected fundamental bump `u ↦ ϑ (−u)`, `ϑ = circleLift (mstEta d χ η 0)`.  (The two
points `u = ±1/2` are the only possible exceptions.) -/
lemma profEta_ae_eq_circleLift {d : ℕ} {χ : ℝ} {η : ℝ → ℂ}
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    η =ᵐ[(volume : Measure ℝ)] fun u : ℝ =>
      if |u| < 1 / 2 then Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) else 0 := by
  show ∀ᵐ u ∂(volume : Measure ℝ), η u
    = (if |u| < 1/2 then Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) else 0)
  rw [MeasureTheory.ae_iff]
  have key : ∀ u : ℝ, u ≠ -(1/2) → u ≠ 1/2 →
      η u = (if |u| < 1/2 then Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) else 0) := by
    intro u hu1 hu2
    rcases lt_trichotomy |u| (1/2) with hlt | heq | hgt
    · have huI : u ∈ Set.Ioo (-(1/2) : ℝ) (1/2) := by
        simp only [Set.mem_Ioo]
        exact abs_lt.mp hlt
      have hneg : -u ∈ Set.Ioo (-(1/2) : ℝ) (1/2) := by
        simp only [Set.mem_Ioo]
        exact abs_lt.mp (by rwa [abs_neg])
      have h := circleLift_mstEta_zero_eq d χ η (-u) hneg
      rw [neg_neg] at h
      rw [if_pos hlt, ← h]
    · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp heq with h | h
      · exact absurd h hu2
      · exact absurd h hu1
    · rw [if_neg (not_lt.mpr (le_of_lt hgt)), hη2 u hgt]
  refine MeasureTheory.measure_mono_null (s := {u : ℝ | ¬ (η u
      = (if |u| < 1/2 then Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) else 0))})
    (t := ({-(1/2), 1/2} : Set ℝ)) ?_ ?_
  · intro u hu
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hne
    exact hu (key u (fun h => hne (Or.inl h)) (fun h => hne (Or.inr h)))
  · exact (Set.toFinite _).measure_zero volume

/-- **A.e. strong measurability of the MST bump.**  If the fundamental bump
`circleLift (mstEta d χ η 0)` is `C²`, then `η` is a.e. strongly measurable (it is a.e. equal to
the measurable function `u ↦ ϑ (−u)`). -/
lemma aestronglyMeasurable_profEta {d : ℕ} {χ : ℝ} {η : ℝ → ℂ}
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0))) :
    AEStronglyMeasurable η (volume : Measure ℝ) := by
  have hcont : Continuous (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0)) := hcd0.continuous
  have hgm : Measurable (fun u : ℝ =>
      if |u| < 1/2 then Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) else 0) := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_abs measurable_const
    · exact hcont.measurable.comp measurable_neg
  exact (hgm.aemeasurable.aestronglyMeasurable).congr
    (profEta_ae_eq_circleLift (d := d) (χ := χ) hη2).symm

/-- **Radial majorant of `mstHat`.**  A function bounded by `M` and decaying like `E / t²` off the
origin is dominated by `max (4 M) (4 E) · (1 + |t|)^{−2}` everywhere. -/
lemma radial_majorant {φ : ℝ → ℂ} {M E : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hbd : ∀ t : ℝ, ‖φ t‖ ≤ M)
    (hdec : ∀ t : ℝ, t ≠ 0 → ‖φ t‖ ≤ E / t ^ 2) :
    ∀ t : ℝ, ‖φ t‖ ≤ max (4 * M) (4 * E) * (1 + |t|) ^ (-(2 : ℝ)) := by
  intro t
  have hrpow : (1 + |t|) ^ (-(2 : ℝ)) = ((1 + |t|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    exact congrArg Inv.inv (Real.rpow_natCast (1 + |t|) 2)
  rw [hrpow, ← div_eq_mul_inv]
  rcases le_or_gt |t| 1 with h1 | h1
  · have h2 : (1 + |t|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg t]
    have h3 : M ≤ max (4 * M) (4 * E) / (1 + |t|) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [le_max_left (4 * M) (4 * E)]
    exact (hbd t).trans h3
  · have h2 : (1 + |t|) ^ 2 ≤ 4 * t ^ 2 := by
      have := sq_abs t
      nlinarith [abs_nonneg t]
    have ht2 : t ≠ 0 := abs_pos.mp (by linarith : 0 < |t|)
    have ht2pos : 0 < t ^ 2 := by
      have : 0 < |t| := by linarith
      rw [← sq_abs]
      positivity
    have h3 : E / t ^ 2 ≤ max (4 * M) (4 * E) / (1 + |t|) ^ 2 := by
      rw [div_le_div_iff₀ ht2pos (by positivity)]
      nlinarith [le_max_right (4 * M) (4 * E)]
    exact (hdec t ht2).trans h3

/-- **The MST inputs give a single radial majorant of `mstHat`.**  Under the standing hypotheses
`‖η‖ ≤ M` and `C²`-smoothness of the fundamental bump, there is `A ≥ 0` with
`‖mstHat η t‖ ≤ A (1 + |t|)^{−2}` for every `t`.  This is the hypothesis of the sampling bound
`profSampling_bound`. -/
theorem exists_mstHat_radial_majorant {d : ℕ} {χ : ℝ} (η : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, ‖mstHat η t‖ ≤ A * (1 + |t|) ^ (-(2 : ℝ)) := by
  obtain ⟨E, hE0, hE⟩ := mstHat_decay η hcd0
  refine ⟨max (4 * M) (4 * E), le_trans (by linarith) (le_max_left _ _), ?_⟩
  exact radial_majorant hM hE0 (mstHat_bound hM hηbd) hE

end

end Work.BourgainPlan.Maximal
