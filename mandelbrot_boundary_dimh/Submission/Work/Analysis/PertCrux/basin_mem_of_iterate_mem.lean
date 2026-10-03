import Mathlib
import Submission.Work.Parab.basinBack.basin_backward

namespace Work.Analysis.PertCrux

open Set

/-- **The uniform parabolic basin pulls back along an orbit segment.**  Let `f₀` be complex
differentiable on the open set `D₀`.  If the iterates `w, f₀ w, …, f₀^[k-1] w` all lie in `D₀` and
the `k`-th iterate `f₀^[k] w` is a point of the uniform parabolic basin
`MandelDim.ParabolicBasin f₀ D₀` (some neighbourhood has all iterates in `D₀` and `f₀^[n] → 0`
uniformly), then `w` is itself a basin point.

This is the `k`-fold iteration of `Work.Parab.basinBack.basin_backward` (the case `k = 1`) along the
orbit; basin membership propagates *backwards* along an orbit segment whose points stay in `dom f₀`.
Proof by induction on `k`, the step being `basin_backward` applied at `f₀^[k-1] w`, with
`AnalyticAt ℂ f₀ (f₀^[k-1] w)` obtained from `hdiff` and `hopen.mem_nhds (hD …)`.  (Useful in the
`f₀^[k] w ∈ Ωp` form as well: with `1 ≤ k` it gives `f₀ w ∈ basin`, which is how
`Work.Analysis.PertCrux.basin_fwd_at_phi` transports petal membership back to `f₀ z`.) -/
theorem basin_mem_of_iterate_mem {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hopen : IsOpen D₀)
    (hdiff : DifferentiableOn ℂ f₀ D₀) {w : ℂ} {k : ℕ}
    (hD : ∀ j : ℕ, j < k → f₀^[j] w ∈ D₀)
    (hk : f₀^[k] w ∈ MandelDim.ParabolicBasin f₀ D₀) :
    w ∈ MandelDim.ParabolicBasin f₀ D₀ := by
  -- the general statement, at an arbitrary starting point, by induction on the length `k`
  have main : ∀ k : ℕ, ∀ z : ℂ, (∀ j : ℕ, j < k → f₀^[j] z ∈ D₀) →
      f₀^[k] z ∈ MandelDim.ParabolicBasin f₀ D₀ →
      z ∈ MandelDim.ParabolicBasin f₀ D₀ := by
    intro k
    induction k with
    | zero => intro z _ hz; simpa using hz
    | succ k ih =>
      intro z hDz hz
      -- `z` itself lies in `D₀`, so `f₀` is analytic at `z`
      have hz0 : z ∈ D₀ := hDz 0 (Nat.succ_pos k)
      -- the same hypotheses, shifted, at the point `f₀ z`
      have hD' : ∀ j : ℕ, j < k → f₀^[j] (f₀ z) ∈ D₀ := by
        intro j hj
        have h := hDz (j + 1) (by omega)
        rwa [Function.iterate_succ_apply] at h
      have hz' : f₀^[k] (f₀ z) ∈ MandelDim.ParabolicBasin f₀ D₀ := by
        have h := hz
        rwa [Function.iterate_succ_apply] at h
      -- pull the basin membership of `f₀ z` back to `z`
      exact Work.Parab.basinBack.basin_backward (hdiff.analyticAt (hopen.mem_nhds hz0))
        (hopen.mem_nhds hz0) (ih (f₀ z) hD' hz')
  exact main k w hD hk

end Work.Analysis.PertCrux
