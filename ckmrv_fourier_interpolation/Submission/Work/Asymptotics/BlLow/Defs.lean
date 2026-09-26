import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs

/-!
# Definitions for the bad-line bound at heights in `[2/5, 1/2]`

This is the low-height companion of `Work.Asymptotics.HalfFunnel.lowBadSet`
(`{τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2, |Re τ| > 3/4}`): the region

  `blLowSet = {τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}`.

All the auxiliary objects of the `HalfFunnel` development (`lowT`, `lowRho`, `lowWin`,
`tpole`, `tsign`, `PhiOne`, `PhiTwo`, `PhiSpike`, `lowF2`) are generic in `τ` and are reused
verbatim; only the region predicate changes.
-/

noncomputable section

open MeasureTheory UpperHalfPlane

namespace Work.Asymptotics.BlLow

open Work.Kernels

/-- The region of the bad lines `Re τ = ±1` at heights `2/5 ≤ Im τ ≤ 1/2`. -/
def blLowSet : Set ℍ :=
  {τ | τ ∈ Work.Asymptotics.DomainD ∧ (2 : ℝ) / 5 ≤ τ.im ∧ τ.im ≤ 1 / 2 ∧
    (3 / 4 < τ.re ∨ τ.re < -(3 / 4))}

/-- The closed box containing the closure of `blLowSet`. -/
def blBox : Set ℍ :=
  {τ : ℍ | 3 / 4 ≤ |τ.re| ∧ |τ.re| ≤ 1 ∧ (2 : ℝ) / 5 ≤ τ.im ∧ τ.im ≤ 1 / 2}

lemma mem_blBox {τ : ℍ} (hτ : blLowSet τ) : τ ∈ blBox := by
  obtain ⟨hD, h1, h2, hre⟩ := hτ
  have habs : |τ.re| < 1 := by rw [abs_lt]; exact ⟨hD.1, hD.2.1⟩
  refine ⟨?_, habs.le, h1, h2⟩
  rcases hre with h | h
  · rw [abs_of_pos (by linarith)]; exact le_of_lt h
  · rw [abs_of_neg (by linarith)]; linarith

lemma blLowSet_re_abs_bounds {τ : ℍ} (hτ : blLowSet τ) : 3 / 4 < |τ.re| ∧ |τ.re| < 1 := by
  have h1 : 3 / 4 < τ.re ∨ τ.re < -(3 / 4) := hτ.2.2.2
  have habs : |τ.re| < 1 := by
    rw [abs_lt]; exact ⟨hτ.1.1, hτ.1.2.1⟩
  refine ⟨?_, habs⟩
  rcases h1 with h | h
  · rwa [abs_of_pos (by linarith)]
  · rw [abs_of_neg (by linarith)]; linarith

lemma blLowSet_im_bounds {τ : ℍ} (hτ : blLowSet τ) : (2 : ℝ) / 5 ≤ τ.im ∧ τ.im ≤ 1 / 2 :=
  ⟨hτ.2.1, hτ.2.2.1⟩


/-- The closed box `blBox` is bounded. -/
lemma isBounded_blBox : Bornology.IsBounded blBox := by
  rw [Metric.isBounded_iff_subset_closedBall (⟨Complex.I, by simp⟩ : ℍ)]
  refine ⟨10, fun τ hτ => ?_⟩
  rw [Metric.mem_closedBall]
  have hnum : ‖(τ : ℂ) - Complex.I‖ ≤ 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im ((τ : ℂ) - Complex.I)
    have hre : ((τ : ℂ) - Complex.I).re = τ.re := by simp
    have him : ((τ : ℂ) - Complex.I).im = τ.im - 1 := by simp
    rw [hre, him] at h
    have h4 : |τ.im - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hτ.2.2.1, hτ.2.2.2]
    linarith [hτ.2.1]
  have hI : (⟨Complex.I, by simp⟩ : ℍ).im = 1 := by
    rw [← UpperHalfPlane.coe_im]; simp
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (τ.im * (⟨Complex.I, by simp⟩ : ℍ).im) := by
    rw [hI, mul_one, Real.le_sqrt (by norm_num) (by positivity)]
    linarith [hτ.2.2.1]
  have hstep : dist τ (⟨Complex.I, by simp⟩ : ℍ) ≤
      ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * (⟨Complex.I, by simp⟩ : ℍ).im) := by
    have h := UpperHalfPlane.dist_le_dist_coe_div_sqrt τ (⟨Complex.I, by simp⟩ : ℍ)
    simpa [UpperHalfPlane.coe_I, Complex.dist_eq] using h
  calc dist τ (⟨Complex.I, by simp⟩ : ℍ)
      ≤ ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * (⟨Complex.I, by simp⟩ : ℍ).im) := hstep
    _ ≤ 2 / (1 / 2 : ℝ) := div_le_div₀ (by norm_num) hnum (by norm_num) hsqrt
    _ ≤ 10 := by norm_num

end Work.Asymptotics.BlLow
