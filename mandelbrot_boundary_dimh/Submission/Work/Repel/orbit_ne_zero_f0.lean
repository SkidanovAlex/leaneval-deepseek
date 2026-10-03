import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.F0Facts.Basic
import Submission.Work.Horn.basin
import Submission.Work.Parab.basinEnters.zero_not_mem_basin

/-!
# The `f₀`-orbit of a point of the parabolic basin never hits `0`

`f₀ z = z + z²` has the parabolic fixed point `0`, and `0` itself is *not* in the parabolic basin
(`Work.Parab.basinEnters.zero_not_mem_parabolicBasin`).  Since the basin is forward invariant under
`f₀` (`Work.F0Facts.f0_mem_Basin`), the orbit of any point of the basin stays in the basin and hence
can never reach `0`.

This is the non-degeneracy hypothesis `∀ z ∈ basin, ∀ n, f₀^[n] z ≠ 0` appearing in
`MandelDim.ParabStatement` (which excludes "degenerate" basins on which an iterate is locally
constant `≡ 0`).
-/

namespace Work.Repel

open MandelDim Set

noncomputable section

/-- The parabolic basin of `f₀` (with `D = univ`) is forward invariant along the whole orbit. -/
lemma iterate_mem_basin {z : ℂ} (hz : z ∈ ParabolicBasin f0 univ) (n : ℕ) :
    (f0^[n]) z ∈ ParabolicBasin f0 univ := by
  induction n with
  | zero => simpa using hz
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Work.F0Facts.f0_mem_Basin ih

theorem orbit_ne_zero_f0 :
    ∀ z ∈ MandelDim.ParabolicBasin MandelDim.f0 Set.univ, ∀ n : ℕ, (MandelDim.f0^[n]) z ≠ 0 := by
  intro z hz n hzn
  have hmem : (f0^[n]) z ∈ ParabolicBasin f0 univ := iterate_mem_basin hz n
  rw [hzn] at hmem
  exact Work.Parab.basinEnters.zero_not_mem_parabolicBasin Work.F0Facts.isParabolicGerm_f0 hmem

end

end Work.Repel
