import Mathlib
import Submission.Work.Pi6.SQM.Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! # Value lemmas for the interval maps of `∪₃` and `∪₂`, and the degree transports

Auxiliary file for `Pi6/SQM/cup3Coboundary`: the value formulas of the vertex maps and the
`shmap` transports used to compare maps living in the various (equal) degree expressions.
-/

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-- Value of `cup3U` on a vertex. -/
lemma cup3U_val (n m a b c : ℕ) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c)
    (hac : a + c + 2 ≤ n) (i : Fin (n + 1)) :
    ((ConcreteCategory.hom (cup3U n m a b c hb1 hb2 hc hac)) i).val =
      if i.val ≤ a then i.val else if i.val ≤ a + c + 1 then i.val + b - 1 else i.val + m - 3 :=
  rfl

/-- Value of `cup3V` on a vertex. -/
lemma cup3V_val (n m a b c : ℕ) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c)
    (hac : a + c + 2 ≤ n) (i : Fin (m + 1)) :
    ((ConcreteCategory.hom (cup3V n m a b c hb1 hb2 hc hac)) i).val =
      if i.val ≤ b then a + i.val else i.val + a + c - 1 :=
  rfl

/-- Value of `cup2U` on a vertex. -/
lemma cup2U_val (n m a b : ℕ) (ha : a + 2 ≤ n) (hb1 : 1 ≤ b) (hb3 : b + 1 ≤ m)
    (i : Fin (n + 1)) :
    ((ConcreteCategory.hom (Work.Pi6.SQ.cup2U n m a b ha hb1 hb3)) i).val =
      if i.val ≤ a then i.val else i.val + (b - 1) :=
  rfl

/-- Value of `cup2V` on a vertex. -/
lemma cup2V_val (n m a b : ℕ) (ha : a + 2 ≤ n) (hb1 : 1 ≤ b) (hb3 : b + 1 ≤ m)
    (i : Fin (m + 1)) :
    ((ConcreteCategory.hom (Work.Pi6.SQ.cup2V n m a b ha hb1 hb3)) i).val =
      if i.val ≤ b then a + i.val else i.val + (n - 2) :=
  rfl

/-- The transport `⦋(n+m-3)+1⦌ ⟶ ⦋n+m-2⦌` (the two lengths are equal). -/
abbrev shL (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : ⦋(n+m-3)+1⦌ ⟶ ⦋n+m-2⦌ :=
  Work.Cohomology.shmap ((n+m-3)+1) (n+m-2) (by omega)

/-- The transport `⦋(n+1)+m-3⦌ ⟶ ⦋n+m-2⦌`. -/
abbrev sh3 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : ⦋(n+1)+m-3⦌ ⟶ ⦋n+m-2⦌ :=
  Work.Cohomology.shmap ((n+1)+m-3) (n+m-2) (by omega)

/-- The transport `⦋n+(m+1)-3⦌ ⟶ ⦋n+m-2⦌`. -/
abbrev sh4 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : ⦋n+(m+1)-3⦌ ⟶ ⦋n+m-2⦌ :=
  Work.Cohomology.shmap (n+(m+1)-3) (n+m-2) (by omega)

/-- The transport `⦋m+n-2⦌ ⟶ ⦋n+m-2⦌` (for the mirrored `∪₂` product). -/
abbrev shT2 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : ⦋m+n-2⦌ ⟶ ⦋n+m-2⦌ :=
  Work.Cohomology.shmap (m+n-2) (n+m-2) (by omega)

end

end Work.Pi6.SQM
