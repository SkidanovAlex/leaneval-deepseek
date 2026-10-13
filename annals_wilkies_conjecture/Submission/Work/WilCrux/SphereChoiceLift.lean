import Mathlib
import Submission.Work.WilCrux.SphereChoiceDefs
import Submission.Work.WilG4a.subst_mem

namespace Work.WilCrux

/-- The set of `x : ℝ^{(a+1)+b}` whose "forgetting the radius coordinate" image
`Fin.append (blockW x) (blockZ x)` lies in `E` is precisely the pullback of `E` along the
coordinate map `tauSkip a b`, so it is an `Ω`-set by `Work.WilG4a.subst_mem`; the only work is
reindexing the set using `comp_tauSkip`.

This is the step that lifts an arbitrary `Ω`-definable set `E ⊆ ℝ^{a+b}` to the ambient space
`ℝ^{(a+1)+b}` of the sphere-choice problem, at the cost of one substitution atom. -/
theorem SphereChoiceLift (S : WilkiesDesign.SOMin) {a b F D : ℕ} (E : Set (Fin (a + b) → ℝ))
    (hE : E ∈ S.Ω F D (a + b)) :
    {x : Fin ((a + 1) + b) → ℝ |
        Fin.append (Work.WilCrux.blockW x) (Work.WilCrux.blockZ x) ∈ E} ∈
      S.Ω (F + 2 * (((a + 1) + b) + (a + b)) + 1) (D + 2) ((a + 1) + b) := by
  have h := Work.WilG4a.subst_mem S (tauSkip a b) hE
  have hset : {x : Fin ((a + 1) + b) → ℝ | x ∘ tauSkip a b ∈ E} =
      {x : Fin ((a + 1) + b) → ℝ |
        Fin.append (Work.WilCrux.blockW x) (Work.WilCrux.blockZ x) ∈ E} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, comp_tauSkip]
  rwa [← hset]

end Work.WilCrux
