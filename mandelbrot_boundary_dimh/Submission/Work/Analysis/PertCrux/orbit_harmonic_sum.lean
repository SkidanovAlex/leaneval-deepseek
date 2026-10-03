import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Analysis.PertCrux.tau0_step_bound
import Submission.Work.Analysis.PertCrux.exists_uniform_eventually_small
import Submission.Work.Analysis.PertCrux.tail_harmonic_bound

/-!
# The parabolic rate in summed form (`Work.Analysis.PertCrux.orbit_harmonic_sum`)

For a §4.1 datum `d` for a parabolic germ `f₀` and a compact `K ⊆ d.DE` the orbit of `d.φ w`
under `f₀` satisfies `∑_{j<m} ‖f₀^[j] (d.φ w)‖ ≤ C (1 + log (m+1))`.

The proof uses only two inputs:

* `ParabolicBasin` made uniform on the compact `K`: for every `ε > 0` there is a time `N` such
  that every orbit of the compact piece `d.φ '' K` lies in `D₀` and *stays* below `ε` from time
  `N` on (`exists_uniform_eventually_small`);
* the one-step compression estimate of the germ in the `τ₀`-chart
  (`τ₀ (f₀ z) = τ₀ z + 1 + O(‖z‖)`, `tau0_step_bound`), which on the small tail turns the
  `τ₀`-orbit into a walk moving right by at least `1/2` per step while staying outside the disc
  of radius `1/ε`; the harmonic sum `Work.Parab.leftCoord.sum_inv_norm_le_log` then bounds the
  small tail (`tail_harmonic_bound`).

The finitely many orbit values before `N` are bounded by continuity on the compact `K`
(`head_bound`), and the two pieces are added.
-/

namespace Work.Analysis.PertCrux

open Complex Set Metric Filter
open scoped Topology

/-- **The first `N` orbit values are uniformly bounded.**  If the whole orbit of `d.φ w` stays in
`D₀` for every `w ∈ K` (which holds for every `w ∈ K ⊆ d.DE` by the definition of the parabolic
basin), then `w ↦ f₀^[j] (d.φ w)` is continuous on `K` for every `j`, so the finite sum
`∑_{j<N} ‖f₀^[j] (d.φ w)‖` is a continuous function on the compact `K` and has a maximum. -/
theorem head_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hdiff : DifferentiableOn ℂ f₀ D₀) {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE)
    (hD₀ : ∀ w ∈ K, ∀ n : ℕ, f₀^[n] (d.φ w) ∈ D₀) {N : ℕ} :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ K, ∑ j ∈ Finset.range N, ‖f₀^[j] (d.φ w)‖ ≤ B := by
  classical
  rcases Set.eq_empty_or_nonempty K with hKe | hKne
  · exact ⟨0, le_refl 0, fun w hw => absurd (hKe ▸ hw) (Set.notMem_empty w)⟩
  have hKsub : K ⊆ d.Dφ := fun w hw => (hK hw).1
  have hcont : ∀ j : ℕ, ContinuousOn (fun w : ℂ => f₀^[j] (d.φ w)) K := by
    intro j
    induction j with
    | zero => simpa using d.φ_holo.continuousOn.mono hKsub
    | succ j ih =>
      have h2 : ContinuousOn (fun w : ℂ => f₀ (f₀^[j] (d.φ w))) K :=
        hdiff.continuousOn.comp ih (fun w hw => hD₀ w hw j)
      simpa only [Function.iterate_succ_apply'] using h2
  have hsum : ContinuousOn (fun w : ℂ => ∑ j ∈ Finset.range N, ‖f₀^[j] (d.φ w)‖) K :=
    continuousOn_finsetSum _ (fun j _ => (hcont j).norm)
  obtain ⟨w₀, hw₀K, hw₀max⟩ := hKc.exists_isMaxOn hKne hsum
  refine ⟨∑ j ∈ Finset.range N, ‖f₀^[j] (d.φ w₀)‖, Finset.sum_nonneg (fun j _ => norm_nonneg _),
    fun w hw => hw₀max hw⟩

/-- **The parabolic rate in summed form.**  For a §4.1 datum `d` for a parabolic germ `f₀` and a
compact `K ⊆ d.DE`, the orbit of `d.φ w` under `f₀` satisfies the harmonic bound

  `Σ_{j<m} ‖f₀^[j] (d.φ w)‖ ≤ C (1 + log (m+1))`.

Proof route (the hypotheses are enough -- the germ expansion comes from `hd`, not from
`ParabData`).  Put `x_j := f₀^[j] (d.φ w)` and `ψ_j := 1/x_j = τ₀ x_j`.
* the walk: `d.φ (w+j) = x_j` for all `j ≥ 0`, by `d.succ_iff` (`w+j ∈ d.Dφ ↔ d.φ (w+j) ∈ D₀`)
  together with the forward invariance of the basin (`d.basin_forward`-style: the basin point
  `d.φ w` has `f₀ (d.φ w)` again in the basin, hence in `D₀`), inductively;
* `x_j → 0` because `d.φ w` lies in the uniform basin;
* `IsParabolicGerm` gives `f₀ (z) = z + z² + z³ h₀(z)` with `h₀` holomorphic near `0`, hence the
  exact recursion `ψ_{j+1} = 1/f₀ (1/ψ_j)` satisfies `ψ_{j+1} = ψ_j + 1 + O(1/|ψ_j|)` for
  `|x_j| ≤ R₀ < 1` and `|ψ_{j+1}| ≤ 2 |ψ_j|²` for `|x_j| ≥ R₀` (with `R₀ < 1` a constant of the
  germ);
* if `|x_j| ≥ R₀` for all large `j` the second regime makes `|x_j|` grow at least quadratically,
  contradicting `x_j → 0`; so every orbit point in the second regime is part of a *finite*
  transient (at most `O(1)` steps), and the sum over the transient is `O(1)`;
* in the first regime `Re ψ_{j+1} ≥ Re ψ_j + (1 - R₀)`, so `‖x_j‖ = 1/‖ψ_j‖ ≤ 1/((1-R₀) j - ‖ψ_0‖)`
  and the tail is harmonic. -/
theorem orbit_harmonic_sum {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ m : ℕ,
      ∑ j ∈ Finset.range m, ‖f₀^[j] (d.φ w)‖ ≤ C * (1 + Real.log ((m : ℝ) + 1)) := by
  classical
  -- `ε` is the small radius of the germ estimate, with `Kc ε ≤ 1/2`
  obtain ⟨R₀, hR₀pos, Kc, hKc0, hstep⟩ := tau0_step_bound hd
  set ε : ℝ := min R₀ (min (1 / (2 * (Kc + 1))) 1) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min hR₀pos (lt_min (by positivity) one_pos)
  have hεR₀ : ε ≤ R₀ := by rw [hεdef]; exact min_le_left _ _
  have hεK : Kc * ε ≤ 1 / 2 := by
    have h1 : ε ≤ 1 / (2 * (Kc + 1)) :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : Kc * ε ≤ Kc * (1 / (2 * (Kc + 1))) := mul_le_mul_of_nonneg_left h1 hKc0
    have h3 : Kc * (1 / (2 * (Kc + 1))) ≤ 1 / 2 := by
      have hpos : (0 : ℝ) < 2 * (Kc + 1) := by linarith
      rw [mul_one_div, div_le_iff₀ hpos]
      nlinarith
    linarith
  -- the uniform smallness and the head bound
  obtain ⟨N, hN⟩ := exists_uniform_eventually_small d hd hKc hK hεpos
  obtain ⟨-, -, hdiff, hf₀0, -, -⟩ := hd
  obtain ⟨B, hBnn, hB⟩ := head_bound d hdiff hKc hK (fun w hw => (hN w hw).1) (N := N)
  -- the harmonic tail
  obtain ⟨Ct, hCt0, hCt⟩ := tail_harmonic_bound (f₀ := f₀) (N := N) (ε := ε) (Kc := Kc)
    hεpos hKc0 hεK hf₀0 (fun z hz0 hzε => (hstep z hz0 (le_trans hzε hεR₀)).2)
  refine ⟨B + Ct + 1, by linarith, ?_⟩
  intro w hw m
  have hsmall : ∀ n : ℕ, N ≤ n → ‖f₀^[n] (d.φ w)‖ < ε := fun n hn => (hN w hw).2 n hn
  have hrec : ∀ n : ℕ, (fun j : ℕ => f₀^[j] (d.φ w)) (n + 1) = f₀ ((fun j : ℕ => f₀^[j] (d.φ w)) n) :=
    fun n => Function.iterate_succ_apply' f₀ n (d.φ w)
  have htail := hCt (fun j : ℕ => f₀^[j] (d.φ w)) hrec hsmall m
  -- split the sum at `N`
  have hsplit : ∑ j ∈ Finset.range m, ‖f₀^[j] (d.φ w)‖
      ≤ (∑ j ∈ Finset.range N, ‖f₀^[j] (d.φ w)‖)
        + ∑ j ∈ Finset.Ico N m, ‖f₀^[j] (d.φ w)‖ := by
    have hsub : Finset.range m ⊆ Finset.range N ∪ Finset.Ico N m := by
      intro j hj
      rw [Finset.mem_range] at hj
      rcases lt_or_ge j N with h | h
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
      · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨h, hj⟩)
    have hle : ∑ j ∈ Finset.range m, ‖f₀^[j] (d.φ w)‖
        ≤ ∑ j ∈ Finset.range N ∪ Finset.Ico N m, ‖f₀^[j] (d.φ w)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => norm_nonneg _)
    have hunion : ∑ j ∈ Finset.range N ∪ Finset.Ico N m, ‖f₀^[j] (d.φ w)‖
        = (∑ j ∈ Finset.range N, ‖f₀^[j] (d.φ w)‖)
          + ∑ j ∈ Finset.Ico N m, ‖f₀^[j] (d.φ w)‖ := by
      rw [Finset.sum_union]
      exact Finset.disjoint_left.mpr (fun j hj1 hj2 => by
        rw [Finset.mem_range] at hj1
        rw [Finset.mem_Ico] at hj2
        omega)
    linarith [hle, hunion]
  have hL : (1 : ℝ) ≤ 1 + Real.log ((m : ℝ) + 1) := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have := Real.log_nonneg h1
    linarith
  calc ∑ j ∈ Finset.range m, ‖f₀^[j] (d.φ w)‖
      ≤ (∑ j ∈ Finset.range N, ‖f₀^[j] (d.φ w)‖)
        + ∑ j ∈ Finset.Ico N m, ‖f₀^[j] (d.φ w)‖ := hsplit
    _ ≤ B + Ct * (1 + Real.log ((m : ℝ) + 1)) := by linarith [hB w hw, htail]
    _ ≤ (B + Ct + 1) * (1 + Real.log ((m : ℝ) + 1)) := by nlinarith [hL, hCt0, hBnn]

end Work.Analysis.PertCrux
