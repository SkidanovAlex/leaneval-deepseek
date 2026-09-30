import Mathlib
import Submission.Work.Pi6.SQ.C2.Cup2Setup
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Invariance of the master-index term function under the pairing involution `cobSwap`

`Work.Pi6.SQ.C2.cobTerm` attaches to every element `x` of the master index set
`LIdx ⊕ C3Idx ⊕ C4Idx ⊕ T1 ⊕ T2` the corresponding summand `⟨u,F⟩ * ⟨v,G⟩` of one of the five
sums into which the two sides of the mod-2 `∪₂` coboundary formula expand.

Here we prove that this term function is invariant under the fixed-point-free involution
`cobSwap`: `cobTerm (cobSwap x) = cobTerm x` for every `x`.  Consequently the summands of the
difference of the two sides cancel in pairs, which is exactly what the coboundary formula needs.

The proof is a case analysis on `x` (five index families) together with the case analysis on the
branches of `cobSwap` (twenty-two branches, including the degenerate ones), and in every branch
the two underlying order maps — the `u`-face `⦋n⦌ ⟶ ⦋n+m-1⦌` and the `v`-face
`⦋m⦌ ⟶ ⦋n+m-1⦌` — agree on the nose; the two `genEval` factors therefore agree.  All vertex
identities are pure arithmetic on the explicit value formulas of `cup2U`, `cup2V`, `delv`, the
face maps `δ`, `Fface`, `Gface` and the degree transports `shmap`; they are closed by
`split_ifs <;> omega`.
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ.C2

open Work.Pi6.SQM (F2)

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-- Value of `Gface` on a vertex (the `Gfun` branch split is exposed for `split_ifs`). -/
lemma Gface_val'' (n m s : ℕ) (h : s + n ≤ n + m - 1) (j : Fin (m+1)) :
    ((ConcreteCategory.hom (Work.Cohomology.Gface n m s h)) j).val =
      if j.val ≤ s then j.val else j.val + n - 1 := by
  rw [Work.Cohomology.Gface_apply]
  simp only [Work.Cohomology.Gfun]
  split_ifs <;> rfl

/-- Two `genEval`s agree as soon as the two vertex maps agree. -/
lemma face_congr {X : SSet} {p q : ℕ} {f g : ⦋p⦌ ⟶ ⦋q⦌} (h : f = g) (w : Cochain F2 X p)
    (σ : X _⦋q⦌) : genEval F2 X w (X.map f.op σ) = genEval F2 X w (X.map g.op σ) := by
  rw [h]

/-- A product of two `genEval`s agrees when its two factors do. -/
lemma prod_congr {α : Type} [Mul α] {a b c d : α} (h1 : a = b) (h2 : c = d) :
    a * c = b * d := by
  rw [h1, h2]

/-- Vertexwise comparison of two order maps into `⦋n+m-1⦌`; all vertex formulas involved are
unfolded, all `if`s are split and the resulting arithmetic goals are closed by `omega`. -/
macro "faceeq" : tactic => `(tactic|
  (refine hom_ext_val (fun i => ?_)
   try (have hi := i.isLt)
   simp only [c3U, lU, c3V, lV, c4U, c4V, t1U, t1V, t2U, t2V, shv, shu, sh1, sh2,
     CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup2U_apply_val, cup2V_apply_val, delv_val,
     Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val, Work.Cohomology.Fface_val,
     Gface_val'']
   split_ifs <;> omega))

/-- In one branch of `cobSwap`: unfold the two terms (a product of a `u`-face and a `v`-face) and
compare the two pairs of faces vertexwise. -/
macro "branch" : tactic => `(tactic|
  (simp only [cobTerm, lTerm, c3Term, c4Term, t1Term, t2Term, Sum.elim_inl, Sum.elim_inr]
   refine prod_congr ?_ ?_ <;> (refine face_congr ?_ ?_ ?_ <;> faceeq)))

theorem cobTerm_swap (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (u : Work.Cohomology.Cochain Work.Pi6.SQM.F2 X n)
    (v : Work.Cohomology.Cochain Work.Pi6.SQM.F2 X m)
    (σ : X.obj (Opposite.op (SimplexCategory.mk (n + m - 1))))
    (x : Work.Pi6.SQ.C2.cobIdx n m) :
    Work.Pi6.SQ.C2.cobTerm X n m hn hm u v σ (Work.Pi6.SQ.C2.cobSwap n m hn hm x)
      = Work.Pi6.SQ.C2.cobTerm X n m hn hm u v σ x := by
  rcases x with ⟨k, a, b⟩ | ⟨A, B, j⟩ | ⟨A, B, j⟩ | s | s
  · -- `L`: the four regimes `k ≤ a < k ≤ a+b+1 < k ≤ n-1+b+1 < k`
    have hk := k.isLt; have ha := a.isLt; have hb := b.isLt
    rw [cobSwap]; split_ifs <;> branch
  · -- `C3`: deleted vertex `j` of the `u`-argument
    have hA := A.isLt; have hB := B.isLt; have hj := j.isLt
    rw [cobSwap]; split_ifs <;> branch
  · -- `C4`: deleted vertex `j` of the `v`-argument
    have hA := A.isLt; have hB := B.isLt; have hj := j.isLt
    rw [cobSwap]; split_ifs <;> branch
  · -- `T1`: the `∪₁`-terms of `u ∪₁ v`
    have hs := s.isLt
    rw [cobSwap]; split_ifs <;> branch
  · -- `T2`: the `∪₁`-terms of `v ∪₁ u`
    have hs := s.isLt
    rw [cobSwap]; split_ifs <;> branch

end

end Work.Pi6.SQ.C2
