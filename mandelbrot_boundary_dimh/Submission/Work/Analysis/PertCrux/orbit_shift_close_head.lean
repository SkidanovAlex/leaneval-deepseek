import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Analysis.PertCrux

/-- A finite sum of functions that are continuous on `K` is continuous on `K` (real-valued
version, convenient for the norm sums of the orbit-shift estimate). -/
private lemma continuousOn_finset_sum_real {ι : Type*} (s : Finset ι) {K : Set ℂ}
    {g : ι → ℂ → ℝ} (h : ∀ i ∈ s, ContinuousOn (g i) K) :
    ContinuousOn (fun w => ∑ i ∈ s, g i w) K := by
  classical
  induction s using Finset.induction with
  | empty => simpa using continuousOn_const (s := K) (c := (0 : ℝ))
  | insert a s ha ih =>
      have key : (fun w => ∑ i ∈ insert a s, g i w) = (fun w => g a w + ∑ i ∈ s, g i w) := by
        funext w
        rw [Finset.sum_insert ha]
      rw [key]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The compactness (head) bound for the orbit-shift estimate.  For a §4.1 datum `d`, a compact
`K ⊆ d.DE` on which the whole orbit of `d.φ w` stays in `D₀` and avoids `0`, the combined quantity
`‖τ₀ (d.φ w) - d.E w‖ + ∑_{j<N} ‖τ₀ (f₀^[j+1] (d.φ w)) - τ₀ (f₀^[j] (d.φ w)) - 1‖`
is uniformly bounded on `K` (for every fixed `N`).

Proof: `w ↦ f₀^[j] (d.φ w)` is continuous on `K` (induction, `DifferentiableOn ℂ f₀ D₀` and
`f₀^[j](d.φ w) ∈ D₀`); `w ↦ d.E w = d.Φ (d.φ w)` is continuous on `K` because `d.φ '' K` lies in
the parabolic basin on which `d.Φ` is holomorphic; `τ₀` is continuous off `0` and the points
`f₀^[j](d.φ w)` avoid `0`.  The sum of the norms of these finitely many continuous functions is
continuous on the compact `K`, hence bounded (`IsCompact.exists_bound_of_continuousOn`). -/
theorem orbit_shift_close_head {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hdiff : DifferentiableOn ℂ f₀ D₀) {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE)
    (hD₀ : ∀ w ∈ K, ∀ n : ℕ, f₀^[n] (d.φ w) ∈ D₀)
    (havoid : ∀ w ∈ K, ∀ j : ℕ, f₀^[j] (d.φ w) ≠ 0) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ K,
      ‖MandelDim.tau0 (d.φ w) - d.E w‖
        + ∑ j ∈ Finset.range N,
            ‖MandelDim.tau0 (f₀^[j + 1] (d.φ w)) - MandelDim.tau0 (f₀^[j] (d.φ w)) - 1‖ ≤ B := by
  -- `φ` is continuous on `K`: `K ⊆ d.DE ⊆ d.Dφ` and `φ` is holomorphic on `d.Dφ`.
  have hφ : ContinuousOn d.φ K := d.φ_holo.continuousOn.mono (fun w hw => (hK hw).1)
  -- all iterates of `φ` are continuous on `K`.
  have hiter : ∀ j : ℕ, ContinuousOn (fun w => f₀^[j] (d.φ w)) K := by
    intro j
    induction j with
    | zero => simpa using hφ
    | succ j ih =>
        have h1 : ContinuousOn (fun x => f₀ (f₀^[j] (d.φ x))) K :=
          hdiff.continuousOn.comp' ih (fun w hw => hD₀ w hw j)
        simpa only [Function.iterate_succ_apply'] using h1
  -- `τ₀ = -1/w` is continuous off `0`.
  have htau : ContinuousOn MandelDim.tau0 {z : ℂ | z ≠ 0} := by
    intro z hz
    exact (continuousAt_const.div continuousAt_id hz).continuousWithinAt
  have htau_iter : ∀ j : ℕ, ContinuousOn (fun w => MandelDim.tau0 (f₀^[j] (d.φ w))) K :=
    fun j => htau.comp' (hiter j) (fun w hw => havoid w hw j)
  -- `d.E = d.Φ ∘ d.φ` is continuous on `K` (the image of `K` lies in the basin).
  have hE : ContinuousOn d.E K := by
    have h2 : ContinuousOn (fun w => d.Φ (d.φ w)) K :=
      d.Φ_holo.continuousOn.comp' hφ (fun w hw => (hK hw).2)
    exact h2
  have hF : ContinuousOn (fun w : ℂ => ‖MandelDim.tau0 (d.φ w) - d.E w‖
        + ∑ j ∈ Finset.range N,
            ‖MandelDim.tau0 (f₀^[j + 1] (d.φ w)) - MandelDim.tau0 (f₀^[j] (d.φ w)) - 1‖) K := by
    refine ((htau_iter 0).sub hE).norm.add ?_
    apply continuousOn_finset_sum_real
    intro j hj
    exact (((htau_iter (j + 1)).sub (htau_iter j)).sub continuousOn_const).norm
  -- a continuous real function on a compact set is bounded.
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right _ _, fun w hw => ?_⟩
  have hnn : 0 ≤ ‖MandelDim.tau0 (d.φ w) - d.E w‖
        + ∑ j ∈ Finset.range N,
            ‖MandelDim.tau0 (f₀^[j + 1] (d.φ w)) - MandelDim.tau0 (f₀^[j] (d.φ w)) - 1‖ :=
    add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun j hj => norm_nonneg _)
  have := hC w hw
  rw [Real.norm_of_nonneg hnn] at this
  exact this.trans (le_max_left _ _)

end Work.Analysis.PertCrux
