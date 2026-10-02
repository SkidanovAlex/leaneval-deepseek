import Mathlib
import Submission.Work.NAKANE2.FarN.farSeries_strict

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Strict differentiability of `bottcher c (critZ c N)` in the parameter

`bottcher c (critZ c N) = critZ c N * exp (farSeries N c)`, and both factors are strictly
differentiable at `c₀ ∈ {farRadius (‖c₀‖+1) < ‖critZ c₀ N‖}`: the critical-orbit point is a
polynomial in `c` and `conj c`, and `exp ∘ farSeries` is strictly differentiable by
`farSeries_hasStrictFDerivAt` and the chain rule.  The product rule finishes.
-/

set_option maxHeartbeats 1000000

namespace Work.NAKANE2.FarN

open Filter Set
open scoped Topology
open Work.NAKANE2 (farTerm farSeries critZ)

noncomputable section

theorem farB_hasStrictFDerivAt {N : ℕ} {c₀ : ℂ}
    (hfar : Work.NAKANE.farRadius (‖c₀‖ + 1) < ‖critZ c₀ N‖) :
    ∃ L : ℂ →L[ℝ] ℂ,
      HasStrictFDerivAt (fun c : ℂ => Work.Bottcher.bottcher c (critZ c N)) L c₀ := by
  obtain ⟨L', hL'⟩ := farSeries_hasStrictFDerivAt (N := N) (c₀ := c₀) hfar
  have hZ : HasStrictFDerivAt (fun c : ℂ => critZ c N)
      (fderiv ℝ (fun c : ℂ => critZ c N) c₀) c₀ :=
    (contDiff_critZ_param N).contDiffAt.hasStrictFDerivAt (by simp)
  have hexp : HasStrictFDerivAt (fun c : ℂ => Complex.exp (farSeries N c))
      ((fderiv ℝ Complex.exp (farSeries N c₀)) ∘SL L') c₀ :=
    ((Complex.contDiff_exp (𝕜 := ℝ) (n := ⊤)).contDiffAt.hasStrictFDerivAt
      (by simp)).comp c₀ hL'
  exact ⟨_, hZ.mul hexp⟩

end

end Work.NAKANE2.FarN
