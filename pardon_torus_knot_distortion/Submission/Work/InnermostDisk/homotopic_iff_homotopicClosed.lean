import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.TorusCover.Homotopy

/-!
# Homotopy of curves on `F`, in the two vocabularies

`Work.CoreTopology.Homotopic P α β` says that the closed curves `α`, `β` of `F = P.carrier`
are joined by a continuous family `H : ℝ → ℝ → ℝ³` of closed curves all of whose values lie
in `F`.  `Work.TorusCover.HomotopicClosed P.psi γ₀ γ₁` says the same thing, except that the
family is a map `H : ℝ × ℝ → ℝ³` whose values lie in `Set.range (psiMap P.psi)`.  Since
`P.carrier` *is* `Set.range (psiMap P.psi)` (both are the range of `(x, y) ↦ P.psi x y`) and
`H : ℝ → ℝ → ℝ³` is the same thing as a map on `ℝ × ℝ`, the two relations are the same; this
file records that identification, transferring between the curried and the uncurried form of
the homotopy by `Function.uncurry` / `Function.curry`.

This is the dictionary which lets the covering-space results about `HomotopicClosed`
(`Work.TorusCover.Homotopic.hasWinding_eq`, `Work.TorusCover.homotopicClosed_iff_hasWinding`,
...) be applied to `Homotopic`, and conversely.
-/

namespace Work.InnermostDisk

theorem homotopic_iff_homotopicClosed (P : Work.CoreTopology.ParamTorus)
    (α β : Work.CoreTopology.ClosedCurve P) :
    Work.CoreTopology.Homotopic P α β ↔ Work.TorusCover.HomotopicClosed P.psi α.γ β.γ := by
  constructor
  · rintro ⟨H, hH, hmem, h0, h1, hper⟩
    exact ⟨Function.uncurry H, hH, fun t => h0 t, fun t => h1 t,
      fun s t => hper s t, fun s t => hmem s t⟩
  · rintro ⟨H, hH, h0, h1, hper, hmem⟩
    exact ⟨Function.curry H, hH, fun s t => hmem s t,
      fun t => h0 t, fun t => h1 t, fun s t => hper s t⟩

end Work.InnermostDisk
