import Mathlib
import Submission.Work.Pi6.SQ.C2.Cup2Setup
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ.C2

open Work.Pi6.SQM (F2)

noncomputable section

open Work.Cohomology (Cochain genEval)

/-! ## Rewriting the faces of the cup-1 terms

`Work.Pi6.SQ.cup1m X n m u v` is the library's `cup1` with the arguments interchanged, so
`genEval_cup1m` followed by `genEval_cup1` expands it as a sum over `Fin n` whose terms are
indexed by the faces `Fface m n s` (applied to `v`) and `Gface m n s` (applied to `u`),
composed with the degree shift `sh1 n m`.  The two lemmas below say that `t1U`, `t1V`
(resp. `t2U`, `t2V`) are exactly those composites, i.e. that evaluating them is the same as
evaluating the corresponding face of the shifted simplex, and they reduce the whole
identification to a `Finset.sum_congr`.  The bookkeeping of the degree shifts is handled once
and for all by `map_comp_op_apply` and by the definitional (proof-irrelevant) unfolding of
`sh1`/`sh2`/`shmap`. -/

/-- Application of a composite of order maps: `X` is a contravariant functor of
`SimplexCategory`, so `X.map (f ≫ g).op σ = X.map f.op (X.map g.op σ)`. -/
private lemma map_comp_op_apply {X : SSet} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (σ : X.obj (Opposite.op c)) :
    X.map (f ≫ g).op σ = X.map f.op (X.map g.op σ) := by
  rw [CategoryTheory.op_comp, CategoryTheory.Functor.map_comp_apply]

/-- `(-1)^k = 1` in `𝔽₂`. -/
private lemma neg_one_pow_F2 (k : ℕ) : (-1 : F2) ^ k = 1 := by
  have h : (-1 : F2) = 1 := by decide
  rw [h, one_pow]

/-- **First half of the RHS expansion**: `u ∪₁ v` evaluated on an `(n+m-1)`-simplex is the
sum over `Fin n` of the `t1Term`s. -/
private lemma rhsExpandT12_left (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m)
    (σ : X.obj (Opposite.op (SimplexCategory.mk (n + m - 1)))) :
    genEval F2 X (Work.Pi6.SQ.cup1m X n m u v) σ = ∑ s : Fin n, t1Term X n m u v σ s := by
  have _ := hn; have _ := hm
  -- the shift `m+n-1 = n+m-1` carried by `genEval_cup1m`
  let τ : X.obj (Opposite.op (SimplexCategory.mk (m + n - 1))) :=
    X.map (Work.Cohomology.shmap (m + n - 1) (n + m - 1)
      (congrArg (fun k => k - 1) (Nat.add_comm m n))).op σ
  have hstep : genEval F2 X (Work.Pi6.SQ.cup1m X n m u v) σ
      = genEval F2 X (Work.Cohomology.cup1 F2 X m n v u) τ :=
    Work.Pi6.SQ.genEval_cup1m X n m u v σ
  rw [hstep]
  rw [Work.Cohomology.genEval_cup1 F2 X m n v u τ]
  apply Finset.sum_congr rfl
  intro s _
  simp only [t1Term]
  rw [show t1U n m s = Work.Cohomology.Gface m n s.val _ ≫ sh1 n m from rfl]
  rw [show t1V n m s = Work.Cohomology.Fface m n s.val _ ≫ sh1 n m from rfl]
  rw [map_comp_op_apply, map_comp_op_apply]
  rw [show X.map (sh1 n m).op σ = τ from rfl]
  rw [neg_one_pow_F2]
  ring

/-- **Second half of the RHS expansion**: `v ∪₁ u` evaluated on an `(n+m-1)`-simplex is the
sum over `Fin m` of the `t2Term`s. -/
private lemma rhsExpandT12_right (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m)
    (σ : X.obj (Opposite.op (SimplexCategory.mk (n + m - 1))))
    (h1 : m + n - 1 = n + m - 1) :
    genEval F2 X (h1 ▸ Work.Pi6.SQ.cup1m X m n v u) σ
      = ∑ s : Fin m, t2Term X n m u v σ s := by
  have _ := hn; have _ := hm
  let τ1 : X.obj (Opposite.op (SimplexCategory.mk (m + n - 1))) :=
    X.map (Work.Cohomology.shmap (m + n - 1) (n + m - 1) h1).op σ
  let τ2 : X.obj (Opposite.op (SimplexCategory.mk (n + m - 1))) :=
    X.map (Work.Cohomology.shmap (n + m - 1) (m + n - 1)
      (congrArg (fun k => k - 1) (Nat.add_comm n m))).op τ1
  have hstep1 : genEval F2 X (h1 ▸ Work.Pi6.SQ.cup1m X m n v u) σ
      = genEval F2 X (Work.Pi6.SQ.cup1m X m n v u) τ1 :=
    Work.Cohomology.genEval_cast h1 (Work.Pi6.SQ.cup1m X m n v u) σ
  rw [hstep1]
  have hstep2 : genEval F2 X (Work.Pi6.SQ.cup1m X m n v u) τ1
      = genEval F2 X (Work.Cohomology.cup1 F2 X n m u v) τ2 :=
    Work.Pi6.SQ.genEval_cup1m X m n v u τ1
  rw [hstep2]
  rw [Work.Cohomology.genEval_cup1 F2 X n m u v τ2]
  apply Finset.sum_congr rfl
  intro s _
  simp only [t2Term]
  rw [show t2U n m s = Work.Cohomology.Fface n m s.val _ ≫ sh2 n m ≫ sh1 n m from rfl]
  rw [show t2V n m s = Work.Cohomology.Gface n m s.val _ ≫ sh2 n m ≫ sh1 n m from rfl]
  rw [map_comp_op_apply, map_comp_op_apply, map_comp_op_apply, map_comp_op_apply]
  rw [show X.map (sh1 n m).op σ = τ1 from rfl]
  rw [show X.map (sh2 n m).op τ1 = τ2 from rfl]
  rw [neg_one_pow_F2]
  ring

theorem rhsExpandT12 (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (u : Work.Cohomology.Cochain Work.Pi6.SQM.F2 X n)
    (v : Work.Cohomology.Cochain Work.Pi6.SQM.F2 X m)
    (σ : X.obj (Opposite.op (SimplexCategory.mk (n + m - 1))))
    (h1 : m + n - 1 = n + m - 1) :
    (Work.Cohomology.genEval Work.Pi6.SQM.F2 X (Work.Pi6.SQ.cup1m X n m u v) σ
        = ∑ s : Fin n, Work.Pi6.SQ.C2.t1Term X n m u v σ s) ∧
    (Work.Cohomology.genEval Work.Pi6.SQM.F2 X (h1 ▸ Work.Pi6.SQ.cup1m X m n v u) σ
        = ∑ s : Fin m, Work.Pi6.SQ.C2.t2Term X n m u v σ s) :=
  ⟨rhsExpandT12_left X n m hn hm u v σ, rhsExpandT12_right X n m hn hm u v σ h1⟩

end

end Work.Pi6.SQ.C2
