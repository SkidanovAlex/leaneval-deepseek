import Mathlib
import Submission.Work.FatouParabolic.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.FatouParabolic.Basin

theorem preimage_mem_puncturedBasin {f : ℂ → ℂ} {z₀ z w : ℂ} (hfix : f z₀ = z₀)
    (hz : z ∈ Work.FatouParabolic.puncturedBasin f z₀) (hw : f w = z) :
    w ∈ Work.FatouParabolic.puncturedBasin f z₀ := by
  rw [Work.FatouParabolic.mem_puncturedBasin] at hz ⊢
  obtain ⟨hzne, hzbasin⟩ := hz
  refine ⟨?_, ?_⟩
  · -- the orbit of `w` never hits `z₀`
    intro n
    cases n with
    | zero =>
      intro h
      have hwz : w = z₀ := by simpa using h
      exact hzne 0 (by simp only [Function.iterate_zero_apply]; rw [← hw, hwz, hfix])
    | succ k =>
      rw [Function.iterate_succ_apply, hw]
      exact hzne k
  · -- the orbit of `w` converges to `z₀`, being the orbit of `z` shifted by one
    have h2 : Tendsto (fun n : ℕ => f^[n + 1] w) atTop (𝓝 z₀) := by
      have he : (fun n : ℕ => f^[n + 1] w) = fun n => f^[n] z := by
        funext n; rw [Function.iterate_succ_apply, hw]
      rw [he]; exact hzbasin
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp h2

end Work.FatouParabolic.Basin
