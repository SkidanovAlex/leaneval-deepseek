import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Analysis.PertCrux.tau0_step_bound
import Submission.Work.Analysis.PertCrux.exists_uniform_eventually_small
import Submission.Work.Analysis.PertCrux.orbit_harmonic_sum
import Submission.Work.Analysis.PertCrux.orbit_shift_close_head

namespace Work.Analysis.PertCrux

/-- **(W): the orbit-corrected location of `τ₀ p_w`.**  For `w ∈ K ⊆ d.DE` whose orbit avoids
`0`, the datum's Fatou coordinate of the orbit point `p_w = f₀^[m] (d.φ w)` satisfies
`d.Φ p_w = d.E w + m` exactly (`Φ_abel` along the walk), and the *inverse* coordinate `τ₀ p_w`
differs from it by `O(log m)`.

Proof (notes §2 of `Submission/Work/PertCrux/NOTES_CRUX_V2_SESSION2.md`): with
`x_j := f₀^[j] (d.φ w)` (and `d.φ (w+j) = x_j` by `walk_mem_Dphi`), the *exact* telescope
`τ₀ x_m - τ₀ x_0 - m = Σ_{j<m} (Θ x_j - 1)`, `Θ x = τ₀ (f₀ x) - τ₀ x`, together with
`d.Φ x_m = d.E w + m` (`walk_mem_Dphi` + `ParabData.E_add_nat`) gives
`τ₀ x_m - m - d.E w = (τ₀ x_0 - d.Φ x_0) + Σ_{j<m} (Θ x_j - 1)`.
`havoid` makes `d.φ '' K` a compact subset of the open basin away from `0`, so the first bracket
`τ₀ z - d.Φ z = -1/z - d.Φ z` is holomorphic on a neighbourhood of it, hence bounded.
`|Θ x - 1| = O(‖x‖)` on `‖x‖ ≤ r/2` with `r` from `Work.Analysis.PertCrux.germ_cubic_bound`;
finitely many initial terms with `‖x_j‖ > r/2` are absorbed by the uniform entry time of the basin
on the compact `d.φ '' K`; the rest is `orbit_harmonic_sum`. -/
theorem orbit_shift_close {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE)
    (havoid : ∀ w ∈ K, ∀ j : ℕ, f₀^[j] (d.φ w) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ m : ℕ,
      ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w)‖
        ≤ C * (1 + Real.log ((m : ℝ) + 1)) := by
  classical
  have hdiff : DifferentiableOn ℂ f₀ D₀ := hd.2.2.1
  -- The one-step `τ₀`-estimate of the germ, and the radius on which it holds.
  obtain ⟨R₀, hR₀pos, K₀, hK₀nn, hstep₀⟩ := tau0_step_bound hd
  set ε : ℝ := min R₀ (1 / (2 * (K₀ + 1))) with hεdef
  have hεpos : 0 < ε := lt_min hR₀pos (by positivity)
  have hεR₀ : ε ≤ R₀ := min_le_left _ _
  have hKε : K₀ * ε ≤ 1 / 2 := by
    have h1 : ε ≤ 1 / (2 * (K₀ + 1)) := min_le_right _ _
    have h2 : K₀ * ε ≤ K₀ * (1 / (2 * (K₀ + 1))) := mul_le_mul_of_nonneg_left h1 hK₀nn
    have h3 : K₀ * (1 / (2 * (K₀ + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hstepε : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ε →
      ‖MandelDim.tau0 (f₀ z) - MandelDim.tau0 z - 1‖ ≤ K₀ * ‖z‖ :=
    fun z hz hzε => (hstep₀ z hz (le_trans hzε hεR₀)).2
  -- Uniform entry of the basin on the compact `K`.
  obtain ⟨N, hN⟩ := exists_uniform_eventually_small d hd hKc hK hεpos
  -- The parabolic rate in summed form.
  obtain ⟨Ch, hChpos, hharm⟩ := orbit_harmonic_sum d hd hKc hK
  -- The head (compactness) bound, at the entry time `N`.
  obtain ⟨B, hBnn, hB⟩ :=
    orbit_shift_close_head d hdiff hKc hK (fun w hw => (hN w hw).1) havoid N
  have hKCh : 0 ≤ K₀ * Ch := mul_nonneg hK₀nn hChpos.le
  refine ⟨B + K₀ * Ch + 1, by linarith, ?_⟩
  intro w hw m
  -- the `j`-th telescoping defect `‖Θ x_j - 1‖`
  let g : ℕ → ℝ := fun j =>
    ‖MandelDim.tau0 (f₀^[j + 1] (d.φ w)) - MandelDim.tau0 (f₀^[j] (d.φ w)) - 1‖
  have hgnn : ∀ j, 0 ≤ g j := fun j => norm_nonneg _
  -- the exact telescope `τ₀ x_m - τ₀ x_0 - m = Σ_{j<m} (Θ x_j - 1)`
  have htel : MandelDim.tau0 (f₀^[m] (d.φ w)) - MandelDim.tau0 (d.φ w) - (m : ℂ)
      = ∑ j ∈ Finset.range m,
          (MandelDim.tau0 (f₀^[j + 1] (d.φ w)) - MandelDim.tau0 (f₀^[j] (d.φ w)) - 1) := by
    rw [Finset.sum_sub_distrib]
    rw [show (∑ j ∈ Finset.range m,
            (MandelDim.tau0 (f₀^[j + 1] (d.φ w)) - MandelDim.tau0 (f₀^[j] (d.φ w))))
          = MandelDim.tau0 (f₀^[m] (d.φ w)) - MandelDim.tau0 (d.φ w) from
        Finset.sum_range_sub (fun j => MandelDim.tau0 (f₀^[j] (d.φ w))) m]
    simp
  have hnormtel : ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - MandelDim.tau0 (d.φ w) - (m : ℂ)‖
      ≤ ∑ j ∈ Finset.range m, g j := by
    rw [htel]
    exact norm_sum_le _ _
  -- the small tail: the one-step estimate plus the harmonic bound
  have htail : ∑ j ∈ Finset.Ico N m, g j ≤ K₀ * (Ch * (1 + Real.log ((m : ℝ) + 1))) := by
    have h1 : ∑ j ∈ Finset.Ico N m, g j ≤ ∑ j ∈ Finset.Ico N m, K₀ * ‖f₀^[j] (d.φ w)‖ := by
      refine Finset.sum_le_sum ?_
      intro j hj
      obtain ⟨hjN, hjm⟩ := Finset.mem_Ico.mp hj
      have hz0 : 0 < ‖f₀^[j] (d.φ w)‖ := norm_pos_iff.mpr (havoid w hw j)
      have hzε : ‖f₀^[j] (d.φ w)‖ ≤ ε := le_of_lt ((hN w hw).2 j hjN)
      show ‖MandelDim.tau0 (f₀^[j + 1] (d.φ w)) - MandelDim.tau0 (f₀^[j] (d.φ w)) - 1‖
        ≤ K₀ * ‖f₀^[j] (d.φ w)‖
      rw [Function.iterate_succ_apply']
      exact hstepε (f₀^[j] (d.φ w)) hz0 hzε
    have h2 : ∑ j ∈ Finset.Ico N m, K₀ * ‖f₀^[j] (d.φ w)‖
        = K₀ * ∑ j ∈ Finset.Ico N m, ‖f₀^[j] (d.φ w)‖ :=
        (Finset.mul_sum (Finset.Ico N m) (fun j => ‖f₀^[j] (d.φ w)‖) K₀).symm
    have h3 : ∑ j ∈ Finset.Ico N m, ‖f₀^[j] (d.φ w)‖ ≤ ∑ j ∈ Finset.range m, ‖f₀^[j] (d.φ w)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj => Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2) (fun j _ _ => norm_nonneg _)
    have h4 := hharm w hw m
    rw [h2] at h1
    exact h1.trans ((mul_le_mul_of_nonneg_left h3 hK₀nn).trans
      (mul_le_mul_of_nonneg_left h4 hK₀nn))
  -- split the sum at the entry time `N`
  have hsplit2 : ∑ j ∈ Finset.range m, g j
      ≤ (∑ j ∈ Finset.range (min N m), g j) + ∑ j ∈ Finset.Ico N m, g j := by
    have hsub : Finset.range m ⊆ Finset.range (min N m) ∪ Finset.Ico N m := by
      intro j hj
      rw [Finset.mem_range] at hj
      rcases lt_or_ge j N with h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr (lt_min h' hj))
      · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨h', hj⟩)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hgnn j)
    have hunion : ∑ j ∈ Finset.range (min N m) ∪ Finset.Ico N m, g j
        = (∑ j ∈ Finset.range (min N m), g j) + ∑ j ∈ Finset.Ico N m, g j := by
      rw [Finset.sum_union]
      exact Finset.disjoint_left.mpr (fun j hj1 hj2 => by
        rw [Finset.mem_range] at hj1
        rw [Finset.mem_Ico] at hj2
        omega)
    linarith [hle, hunion]
  have hheadsum : ∑ j ∈ Finset.range (min N m), g j ≤ ∑ j ∈ Finset.range N, g j :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro j hj; rw [Finset.mem_range] at hj ⊢; exact lt_of_lt_of_le hj (min_le_left N m))
      (fun j _ _ => hgnn j)
  -- the head bound, in terms of `g`
  have hheadB : ‖MandelDim.tau0 (d.φ w) - d.E w‖ + ∑ j ∈ Finset.range N, g j ≤ B := hB w hw
  -- assemble
  have hdec : MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w)
      = (MandelDim.tau0 (f₀^[m] (d.φ w)) - MandelDim.tau0 (d.φ w) - (m : ℂ))
        + (MandelDim.tau0 (d.φ w) - d.E w) := by ring
  rw [hdec]
  have h1 := norm_add_le (MandelDim.tau0 (f₀^[m] (d.φ w)) - MandelDim.tau0 (d.φ w) - (m : ℂ))
    (MandelDim.tau0 (d.φ w) - d.E w)
  have h2 : ∑ j ∈ Finset.range m, g j ≤ (∑ j ∈ Finset.range N, g j) + ∑ j ∈ Finset.Ico N m, g j :=
    hsplit2.trans (add_le_add hheadsum (le_refl _))
  have hL : (0 : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
    apply Real.log_nonneg
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hkey : B + K₀ * (Ch * (1 + Real.log ((m : ℝ) + 1)))
      ≤ (B + K₀ * Ch + 1) * (1 + Real.log ((m : ℝ) + 1)) := by
    nlinarith [hL, hBnn, hK₀nn, hChpos.le]
  linarith [h1, hnormtel, h2, htail, hheadB, hkey]

end Work.Analysis.PertCrux
