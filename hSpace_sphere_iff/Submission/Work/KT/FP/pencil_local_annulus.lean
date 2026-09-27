import Mathlib
import Submission.Work.KT.FP.PencilDefs

namespace Work.KT.FP

/-- **Thickening of the annulus of invertibility of a pencil.**

If the pencil `z ↦ z • A + B` is invertible on the closed annulus `ρ ≤ ‖z‖ ≤ 1` (with `0 < ρ ≤ 1`),
then it is invertible on some *open-ended* annulus `r ≤ ‖z‖ ≤ s` with `r < ρ < s`, `r > 0`.

Route.  `K := {z : ℂ | ρ ≤ ‖z‖ ∧ ‖z‖ ≤ 1}` is compact (closed and bounded), `z ↦ z • A + B` is
continuous, so `U := {z : ℂ | IsUnit (z • A + B)}` is open (`Units.isOpen.preimage`, and
`HasSummableGeomSeries R` is an instance of `[NormedRing R] [CompleteSpace R]`, see
`Mathlib/Analysis/Normed/Ring/Units.lean`) and `K ⊆ U` by hypothesis.
`IsCompact.exists_thickening_subset_open` gives `δ > 0` with `Metric.thickening δ K ⊆ U`.  Take
`ε := min δ ρ / 2`, `r := ρ - ε`, `s := ρ + ε`: for `z` with `r ≤ ‖z‖ ≤ s` put
`w := (min (max ‖z‖ ρ) 1 / ‖z‖) • z` (note `‖z‖ ≥ ρ - ε > 0`); then `w ∈ K` and `‖w - z‖ ≤ ε < δ`,
so `z ∈ U`. -/
theorem pencil_local_annulus {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B : R) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • A + B)) :
    ∃ r s : ℝ, 0 < r ∧ r < ρ ∧ ρ < s ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ s → IsUnit (z • A + B) := by
  -- The compact annulus `K = {ρ ≤ ‖z‖} ∩ closedBall 0 1` is contained in the open set of
  -- invertibility, so some metric thickening of `K` is too.
  set K : Set ℂ := Metric.closedBall 0 1 ∩ {z : ℂ | ρ ≤ ‖z‖} with hK
  have hKcompact : IsCompact K := by
    rw [hK]
    exact (isCompact_closedBall (0 : ℂ) 1).inter_right
      (isClosed_Ici.preimage continuous_norm)
  have hUopen : IsOpen {z : ℂ | IsUnit (z • A + B)} :=
    Units.isOpen.preimage (by continuity)
  have hKU : K ⊆ {z : ℂ | IsUnit (z • A + B)} := by
    intro z hz
    rw [hK] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz1
    exact hunit z hz2 hz1
  obtain ⟨δ, hδpos, hδ⟩ := hKcompact.exists_thickening_subset_open hUopen hKU
  -- The pinched annulus.
  set ε : ℝ := min δ ρ / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; have := lt_min hδpos hρ0; linarith
  have hεδ : ε < δ := by rw [hεdef]; have := min_le_left δ ρ; linarith
  have hερ : ε < ρ := by rw [hεdef]; have := min_le_right δ ρ; linarith
  refine ⟨ρ - ε, ρ + ε, by linarith, by linarith, by linarith, ?_⟩
  intro z hzr hzs
  -- The radial rescaling of `z` to the annulus `K`.
  have hnpos : 0 < ‖z‖ := lt_of_lt_of_le (by linarith) hzr
  set M : ℝ := min (max ‖z‖ ρ) 1 with hM
  have hMge : ρ ≤ M := by rw [hM]; exact le_min (le_max_right _ _) hρ1
  set c : ℝ := M / ‖z‖ with hc
  have hcnonneg : 0 ≤ c := by
    rw [hc]; exact div_nonneg (le_trans (le_of_lt hρ0) hMge) (le_of_lt hnpos)
  have hcM : c * ‖z‖ = M := by rw [hc]; exact div_mul_cancel₀ M (ne_of_gt hnpos)
  set w : ℂ := c • z with hw
  have hnormw : ‖w‖ = M := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcnonneg]
    exact hcM
  have hwK : w ∈ K := by
    rw [hK]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hnormw]
      rw [hM]; exact min_le_right _ _
    · show ρ ≤ ‖w‖; rw [hnormw]; exact hMge
  -- The key estimate: `‖w - z‖ = |M - ‖z‖| ≤ ε`.
  have hbound : |M - ‖z‖| ≤ ε := by
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · have h1 : M ≤ max ‖z‖ ρ := by rw [hM]; exact min_le_left _ _
      have h2 : max ‖z‖ ρ ≤ ‖z‖ + ε := max_le (by linarith) (by linarith)
      linarith
    · have h1 : ‖z‖ - ε ≤ max ‖z‖ ρ := le_trans (by linarith) (le_max_left _ _)
      have h2 : ‖z‖ - ε ≤ 1 := by linarith
      have h3 : ‖z‖ - ε ≤ M := by rw [hM]; exact le_min h1 h2
      linarith
  have hdist : dist w z < δ := by
    rw [dist_eq_norm]
    have hwz : w - z = (c - 1) • z := by rw [hw]; simp [sub_smul]
    rw [hwz, norm_smul, Real.norm_eq_abs]
    have h2 : |c - 1| * ‖z‖ = |M - ‖z‖| := by
      rw [hc]
      have hthis : M / ‖z‖ - 1 = (M - ‖z‖) / ‖z‖ := by
        rw [sub_div, div_self (ne_of_gt hnpos)]
      rw [hthis, abs_div, abs_of_pos hnpos, div_mul_cancel₀ _ (ne_of_gt hnpos)]
    rw [h2]
    linarith
  have hzthick : z ∈ Metric.thickening δ K := by
    rw [Metric.mem_thickening_iff]
    exact ⟨w, hwK, by rwa [dist_comm]⟩
  exact hδ hzthick

end Work.KT.FP
