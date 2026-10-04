import Mathlib
import Submission.Work.Diff.EXT.ATower.fixedRicTowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ATower

open Work.Diff.EXT.ConnCov.RicFlip

/-- The number of `comp`-nodes of a term `T` whose inserted atom has order `≥ k`. -/
noncomputable def highCount (k : ℕ) : {n : ℕ} → Term n → ℕ
  | _, Term.leaf _ => 0
  | _, @Term.comp a b ord Ψ T => highCount k T + (if k ≤ ord then 1 else 0)

end Work.Diff.EXT.ATower
