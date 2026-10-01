/-
# ZeroFreeTables — RowCert_all

The certificate `Work.ZeroFreeTables.RowCert` of **Tables 2 and 3** (`t23Defs.lean`) assembled
from its six batches:

* `rowA` — `Work.ZeroFreeTables.t23RowA`;
* `rowB ++ rowC` — `Work.ZeroFreeTables.t23RowBC`;
* `rowD ++ rowE` — `Work.ZeroFreeTables.t23RowDE`;
* `rowF` — `Work.ZeroFreeTables.t23RowF`.

Each batch lemma is a `∀ p ∈ <batch>, <RowCert inequality>` statement proved by the rational
certificate recipe of `t23ExpBounds.lean`/`t23Gclosed.lean` (`hb72G_closed` + `exp_bounds_quart`),
and `t23rows = rowA ++ rowB ++ rowC ++ rowD ++ rowE ++ rowF` definitionally.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.t23RowA
import Submission.Work.ZeroFreeTables.t23RowBC
import Submission.Work.ZeroFreeTables.t23RowDE
import Submission.Work.ZeroFreeTables.t23RowF

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- **The certificate of Tables 2 and 3** (`RowCert`), from the four batch lemmas. -/
theorem RowCert_all : Work.ZeroFreeTables.RowCert := by
  intro p hp
  simp only [Work.ZeroFreeTables.t23rows, List.mem_append] at hp
  rcases hp with (((((hA | hB) | hC) | hD) | hE) | hF)
  · exact Work.ZeroFreeTables.t23RowA p hA
  · exact Work.ZeroFreeTables.t23RowBC p (by simp only [List.mem_append]; exact Or.inl hB)
  · exact Work.ZeroFreeTables.t23RowBC p (by simp only [List.mem_append]; exact Or.inr hC)
  · exact Work.ZeroFreeTables.t23RowDE p (by simp only [List.mem_append]; exact Or.inl hD)
  · exact Work.ZeroFreeTables.t23RowDE p (by simp only [List.mem_append]; exact Or.inr hE)
  · exact Work.ZeroFreeTables.t23RowF p hF

end Work.ZeroFreeTables
