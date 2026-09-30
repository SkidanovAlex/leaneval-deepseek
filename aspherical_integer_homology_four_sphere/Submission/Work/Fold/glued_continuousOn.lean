import Mathlib
import Submission.Work.Fold.GlueDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Fold

open Set Function

namespace FoldGlue

variable {Y : Type*} [TopologicalSpace Y] {c : ℕ}

/-- The map glued over the *closed* pieces `C r`: on the piece `C r` it agrees with `ψ r`. -/
noncomputable def gluedC (D : FoldGlue Y c) (y : Y) : E4 := by
  classical
  exact if h : ∃ r, y ∈ D.C r then D.ψ (Classical.choose h) y else 0

variable (D : FoldGlue Y c)

/-- The glued-over-`C` map is `ψ r` on the `r`-th closed piece. -/
theorem gluedC_apply {p : Y} {r : Sign c} (hp : p ∈ D.C r) : D.gluedC p = D.ψ r p := by
  have h : ∃ s, p ∈ D.C s := ⟨r, hp⟩
  rw [gluedC, dite_eq_left h]
  exact D.hagree (Classical.choose h) r (Classical.choose_spec h) hp

/-- **The map glued over the closed pieces is continuous.** The pieces `C r` are closed and,
in any space, a finite family of closed sets is locally finite, so the gluing lemma for a
locally finite closed cover applies. -/
theorem gluedC_continuousOn : ContinuousOn D.gluedC (⋃ r, D.C r) := by
  refine (locallyFinite_of_finite (fun r : Sign c => D.C r)).continuousOn_iUnion D.hC_closed
    (fun r => (D.hψ_cont r).congr (fun y hy => D.gluedC_apply hy))

/-- On the source, the glued map and the glued-over-`C` map coincide. -/
theorem glued_eq_gluedC_of_mem_source {y : Y} (hy : y ∈ D.source) : D.glued y = D.gluedC y := by
  obtain ⟨r, hr⟩ := D.mem_source_iff.mp hy
  rw [D.glued_apply hr, D.gluedC_apply (D.hU_subset r hr)]

end FoldGlue

theorem glued_continuousOn {Y : Type*} [TopologicalSpace Y] {c : ℕ} (D : FoldGlue Y c) :
    ContinuousOn D.glued D.source := by
  refine (D.gluedC_continuousOn.mono ?_).congr (fun y hy => D.glued_eq_gluedC_of_mem_source hy)
  intro y hy
  obtain ⟨r, hr⟩ := D.mem_source_iff.mp hy
  exact mem_iUnion.mpr ⟨r, D.hU_subset r hr⟩

end Work.Fold
