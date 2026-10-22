import Mathlib
import Submission.Work.ATOM.ZS.Topo.Defs

open CategoryTheory Limits LightProfinite OnePoint

namespace Work.ATOM.ZS.Topo

/-- The first projection `T' ⟶ ℕ∪{∞}` is surjective: `(j,a_j)` lies over `j` and `(∞,x)` over `∞`
(`Work.ATOM.mem_tSet_graph`, `Work.ATOM.mem_tSet_infty`).  This is the cover along which the null
sequence `g` is glued. -/
theorem tSet_fst_surjective (S : LightProfinite.{0}) [Infinite S] :
    Function.Surjective (fun p : ↥(Work.ATOM.tSet S) => p.1.1) := by
  intro y
  rcases y with - | j
  · exact ⟨⟨((∞ : ℕ∪{∞}), (Work.ATOM.levelData S).s₀),
      Work.ATOM.mem_tSet_infty _⟩, rfl⟩
  · exact ⟨⟨(((j : ℕ) : ℕ∪{∞}), (Work.ATOM.levelData S).a j),
      Work.ATOM.mem_tSet_graph j⟩, rfl⟩

end Work.ATOM.ZS.Topo
