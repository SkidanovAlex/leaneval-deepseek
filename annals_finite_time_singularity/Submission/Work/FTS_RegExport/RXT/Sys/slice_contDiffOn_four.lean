import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_deriv4_of_uniform_H6
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_RegExport.RXR1.slice_deriv_equi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

theorem slice_contDiffOn_four {α B : ℝ} (hα : 0 < α)
    {G : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
      Filter.Tendsto (fun n : ℕ => G n z θ) Filter.atTop (nhds (f z θ))) :
    ContDiffOn ℝ 4 (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  classical
  -- The extraction theorem produces a subsequence converging locally uniformly, together with
  -- its `C⁴`-limit `F` on the open quadrant.
  obtain ⟨φ, hφ, F, hunif, hcdF, -⟩ :=
    Work.FTS.StrongEps.LocUnif.exists_subseq_deriv4_of_uniform_H6 (α := α) (B := B)
      hα hsm hmem hb
  -- Because the *whole* sequence converges pointwise to `f`, the limit of any subsequence is `f`.
  have hFeq : Set.EqOn (Function.uncurry f) (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rintro ⟨z, θ⟩ hp
    simp only [Function.uncurry]
    have hsub : ({(z, θ)} : Set (ℝ × ℝ)) ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      simpa [Set.singleton_subset_iff] using hp
    have h1 : Filter.Tendsto (fun n : ℕ => G (φ n) z θ) Filter.atTop (nhds (F z θ)) :=
      (hunif {(z, θ)} isCompact_singleton hsub).tendsto_at (Set.mem_singleton (z, θ))
    have h2 : Filter.Tendsto (fun n : ℕ => G (φ n) z θ) Filter.atTop (nhds (f z θ)) :=
      (hconv z θ hp).comp hφ.tendsto_atTop
    exact (tendsto_nhds_unique h1 h2).symm
  exact hcdF.congr hFeq

end Work.FTS_RegExport.RXT.Sys
