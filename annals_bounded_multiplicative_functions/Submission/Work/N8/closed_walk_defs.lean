import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Matrix

/-- The adjacency matrix of a relation, over `ℝ` (entries 1 or 0). -/
def AdjMat {V : Type} (Adj : V → V → Prop) [DecidableRel Adj] : Matrix V V ℝ :=
  fun i j => if Adj i j then 1 else 0

lemma AdjMat_apply {V : Type} (Adj : V → V → Prop) [DecidableRel Adj] (i j : V) :
    AdjMat Adj i j = if Adj i j then (1 : ℝ) else 0 := rfl

lemma AdjMat_isSymm {V : Type} (Adj : V → V → Prop) [DecidableRel Adj]
    (hsym : ∀ a b, Adj a b ↔ Adj b a) : (AdjMat Adj).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, AdjMat]
  by_cases h : Adj j i
  · rw [if_pos h, if_pos ((hsym j i).mp h)]
  · rw [if_neg h, if_neg (fun hh => h ((hsym j i).mpr hh))]

lemma AdjMat_nonneg {V : Type} (Adj : V → V → Prop) [DecidableRel Adj] (i j : V) :
    0 ≤ AdjMat Adj i j := by
  rw [AdjMat_apply]; split <;> norm_num

/-- The number of ordered adjacent pairs equals the sum of the entries of the adjacency
matrix. -/
lemma edges_eq_sum {V : Type} [Fintype V] (Adj : V → V → Prop) [DecidableRel Adj] :
    (∑ i, ∑ j, AdjMat Adj i j)
      = ((Finset.univ.filter (fun p : V × V => Adj p.1 p.2)).card : ℝ) := by
  rw [← Fintype.sum_prod_type (fun p : V × V => AdjMat Adj p.1 p.2)]
  simp only [AdjMat]
  rw [Finset.sum_boole]

end Work.N8
