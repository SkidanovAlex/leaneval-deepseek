import Mathlib
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.Pi6.BOCK.bocksteinLES
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# AREA EMZ — the mod-`p` Bockstein long exact sequence (lead glue, 2026-09-28)

Glue on the ONE shared Bockstein lemma `Work.Pi6.BOCK.bocksteinLES` (area BOCK): keep its three
exactness conjuncts.  (The previous self-contained attempt imported two helper modules that were
deleted when its agent was cancelled; its text is in `REFS/bock_drafts/`.)
-/

namespace Work.Pi6.EMZ

theorem bocksteinLES (p : ℕ) (hp : p.Prime) : Work.Pi6.EMZ.BocksteinLES p := by
  obtain ⟨red, del, h1, h2, h3, -, -⟩ := Work.Pi6.BOCK.bocksteinLES p hp
  exact ⟨red, del, h1, h2, h3⟩

end Work.Pi6.EMZ
