import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.mem_escapeRegion_iterate
import Submission.Work.Escape.tendsto_norm_iterate_atTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Compactness of the filled Julia set

For a continuous map `f : ℂ → ℂ` with monic degree-`d` growth bounds, `d ≥ 2`, the filled Julia
set `K_f = {z | the orbit of z is bounded}` is compact.

The two ingredients are:

* **Boundedness.**  `K_f` is contained in the closed ball of radius `max 2 A`: if `‖z‖ > max 2 A`
  then `z` lies in the escaping region, so its orbit's norms tend to `+∞`
  (`tendsto_norm_iterate_atTop`) and the orbit is unbounded.
* **Closedness.**  By complete invariance, `z ∈ K_f` iff `(f^[n]) z ∈ K_f` for all `n`, so by the
  previous point `K_f = ⋂ n, (f^[n]) ⁻¹' closedBall 0 (max 2 A)`, an intersection of closed sets.

Since `ℂ` is proper, closed + bounded gives `IsCompact` (equivalently, `K_f` is a closed subset of
the compact ball of radius `max 2 A`).
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

variable {f : ℂ → ℂ} {d : ℕ} {A : ℝ} {z : ℂ} {n : ℕ}

/-- **A point of the filled Julia set never escapes.**  Contrapositive of the escape criterion:
if the norm of `z` exceeds the escape radius `max 2 A`, its orbit's norms tend to infinity and `z`
is not in `K_f`. -/
theorem norm_le_max_two_A_of_mem_filledJulia (h : MonicGrowth f d A) (hd : 2 ≤ d)
    {z : ℂ} (hz : z ∈ filledJulia f) : ‖z‖ ≤ max 2 A := by
  by_contra hle
  simp only [not_le] at hle
  have hzA : z ∈ escapeRegion A := hle
  have htend := tendsto_norm_iterate_atTop f d A h hd hzA
  obtain ⟨M, hM⟩ := norm_le_of_mem_filledJulia hz
  obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop M).exists
  exact absurd (hM n) (not_le.mpr hn)

/-- The filled Julia set is contained in the closed ball of radius the escape radius `max 2 A`. -/
theorem filledJulia_subset_closedBall (h : MonicGrowth f d A) (hd : 2 ≤ d) :
    filledJulia f ⊆ closedBall (0 : ℂ) (max 2 A) := by
  intro z hz
  rw [mem_closedBall_zero_iff]
  exact norm_le_max_two_A_of_mem_filledJulia h hd hz

/-- **The filled Julia set is closed**: it is the intersection over `n` of the closed sets
`{z | ‖(f^[n]) z‖ ≤ max 2 A}`. -/
theorem isClosed_filledJulia_monicGrowth (h : MonicGrowth f d A) (hd : 2 ≤ d) :
    IsClosed (filledJulia f) := by
  have heq : filledJulia f = ⋂ n, (f^[n]) ⁻¹' closedBall (0 : ℂ) (max 2 A) := by
    ext z
    simp only [mem_iInter, mem_preimage, mem_closedBall_zero_iff]
    constructor
    · intro hz n
      exact norm_le_max_two_A_of_mem_filledJulia h hd ((mem_filledJulia_iff_iterate f z n).mp hz)
    · intro hz
      exact mem_filledJulia_of_norm_le fun n => hz n
  rw [heq]
  exact isClosed_iInter fun n => IsClosed.preimage (h.continuous.iterate n) isClosed_closedBall

/-- **The filled Julia set of a monic-growth map of degree `d ≥ 2` is compact.** -/
theorem isCompact_filledJulia (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d) :
    IsCompact (filledJulia f) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) (max 2 A))
    (isClosed_filledJulia_monicGrowth h hd) (filledJulia_subset_closedBall h hd)

end Work.Escape
