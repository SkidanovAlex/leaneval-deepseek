import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup

/-!
# `0` is not in the parabolic basin

For a parabolic germ `f` on an open `D ∋ 0` (`f 0 = 0`, `f'(0) = 1`), the point `0` is *not* in
`MandelDim.ParabolicBasin f D`.  Indeed, if some neighbourhood `U` of `0` were mapped into `D` by
all iterates with `f^n → 0` uniformly on `U`, then for suitable `N` the map `g = f^N` would send
a disc `ball 0 R` into a strictly smaller disc `ball 0 R` (uniform convergence with `ε = R`), so
Cauchy's estimate gives `‖g'(0)‖ < 1`, while the chain rule gives `g'(0) = (f'(0))^N = 1`.

This is the reason why the requested statement `Work.Parab.basinEnters.basin_enters_petal` fails
only through *degenerate* basins (a point at which `f` is locally constant and `≡ 0`, so that a
whole neighbourhood collapses to `0`); see
`Submission/Work/Parab/basinEnters/counterexample.lean`.
-/

open Complex Set Metric Filter
open scoped Topology

namespace Work.Parab.basinEnters

noncomputable section

/-- The iterates of a parabolic germ at `0` have derivative `1` at `0`:
`(f^[n])'(0) = (f'(0))^n = 1`. -/
lemma deriv_iterate_zero {f : ℂ → ℂ} {D : Set ℂ} (hg : MandelDim.IsParabolicGerm f D)
    (n : ℕ) : deriv (f^[n]) (0 : ℂ) = 1 := by
  have hf0 : f 0 = 0 := hg.2.2.2.1
  have hdf : deriv f 0 = 1 := hg.2.2.2.2.1
  have hfdiff : DifferentiableAt ℂ f 0 := hg.2.2.1.differentiableAt (hg.1.mem_nhds hg.2.1)
  have hiter0 : ∀ k : ℕ, f^[k] (0 : ℂ) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, hf0]
  have hiterdiff : ∀ k : ℕ, DifferentiableAt ℂ (f^[k]) (0 : ℂ) := by
    intro k
    induction k with
    | zero => exact differentiableAt_id
    | succ j ih =>
        rw [Function.iterate_succ']
        exact DifferentiableAt.comp (0 : ℂ) (by rw [hiter0 j]; exact hfdiff) ih
  have hrec : ∀ k : ℕ, deriv (f^[k.succ]) (0 : ℂ) = deriv f (f^[k] 0) * deriv (f^[k]) 0 := by
    intro k
    rw [Function.iterate_succ']
    exact deriv_comp (0 : ℂ) (by rw [hiter0 k]; exact hfdiff) (hiterdiff k)
  induction n with
  | zero => simp
  | succ k ih => rw [hrec k, hiter0 k, hdf, ih, one_mul]

/-- **`0` is not in the parabolic basin.** -/
theorem zero_not_mem_parabolicBasin {f : ℂ → ℂ} {D : Set ℂ}
    (hg : MandelDim.IsParabolicGerm f D) :
    (0 : ℂ) ∉ MandelDim.ParabolicBasin f D := by
  rintro ⟨U, hU, hmap, hunif⟩
  -- an open ball around `0` inside the witness
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hmapU : ∀ n : ℕ, MapsTo (f^[n]) (ball (0 : ℂ) ε) D :=
    fun n z hz => hmap n (hεU hz)
  have hunifU : TendstoUniformlyOn (fun n : ℕ => f^[n]) (fun _ => (0 : ℂ)) atTop
      (ball (0 : ℂ) ε) := hunif.mono hεU
  -- all iterates are holomorphic on that ball
  have hiter_diff : ∀ n : ℕ, DifferentiableOn ℂ (f^[n]) (ball (0 : ℂ) ε) := by
    intro n
    induction n with
    | zero => simpa using differentiableOn_id
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hg.2.2.1.comp ih (fun z hz => hmapU k hz)
  -- uniform convergence: some iterate maps the half-ball into itself
  rw [Metric.tendstoUniformlyOn_iff] at hunifU
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hunifU (ε / 2) (by linarith))
  set R : ℝ := ε / 2 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have hball_sub : ball (0 : ℂ) R ⊆ ball (0 : ℂ) ε := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [hR] at hz; linarith
  have hcont : ContinuousOn (f^[N]) (closedBall (0 : ℂ) R) := by
    intro z hz
    have hzε : z ∈ ball (0 : ℂ) ε := by
      rw [mem_closedBall_zero_iff] at hz
      rw [mem_ball_zero_iff]
      rw [hR] at hz; linarith
    exact ((hiter_diff N).differentiableAt (isOpen_ball.mem_nhds hzε)).continuousAt.continuousWithinAt
  -- a point of the sphere maximising `‖f^N‖`
  have hsphere_ne : (sphere (0 : ℂ) R).Nonempty :=
    ⟨(R : ℂ), by rw [mem_sphere_iff_norm]; simp [Complex.norm_real, abs_of_nonneg hRpos.le]⟩
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMaxOn hsphere_ne
    ((hcont.mono sphere_subset_closedBall).norm) (f := fun z => ‖f^[N] z‖)
  have hz₀ε : z₀ ∈ ball (0 : ℂ) ε := by
    have h : ‖z₀‖ = R := by simpa using (mem_sphere_iff_norm.mp hz₀)
    rw [mem_ball_zero_iff, h, hR]; linarith
  have hgN₀ : ‖f^[N] z₀‖ < R := by
    have h := hN N le_rfl z₀ hz₀ε
    rw [dist_eq_norm, zero_sub, norm_neg] at h
    rw [hR]
    exact h
  -- Cauchy's estimate on the disc of radius `R`
  have hcauchy : ‖deriv (f^[N]) 0‖ ≤ ‖f^[N] z₀‖ / R := by
    refine norm_deriv_le_of_forall_mem_sphere_norm_le hRpos ⟨?_, ?_⟩ (fun z hz => hmax hz)
    · exact (hiter_diff N).mono hball_sub
    · simpa [closure_ball (0 : ℂ) (ne_of_gt hRpos)] using hcont
  rw [deriv_iterate_zero hg N, norm_one] at hcauchy
  have : ‖f^[N] z₀‖ / R < 1 := by
    rw [div_lt_one hRpos]
    exact hgN₀
  linarith

end
end Work.Parab.basinEnters
