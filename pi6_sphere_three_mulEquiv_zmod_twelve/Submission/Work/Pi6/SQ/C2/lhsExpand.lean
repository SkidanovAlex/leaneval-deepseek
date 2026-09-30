import Mathlib
import Submission.Work.Pi6.SQ.C2.Cup2Setup
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Expansion of the left hand side of the mod-2 `∪₂` coboundary identity

This file proves `Work.Pi6.SQ.C2.lhsExpand`: for cochains `u ∈ C^n`, `v ∈ C^m` and a simplex
`σ` of dimension `n+m-1`, the evaluation of the coboundary of the cup-2 product,

`δ(u ∪₂ v)(σ) = ∑_k (u ∪₂ v)(δ_k σ)`,

is the explicit sum over the index family `LIdx n m = Fin (n+m) × (Fin (n-1) × Fin (m-1))` of
the terms `lTerm` of `Submission/Work/Pi6/SQM/Cup2CobSetup.lean`.

The proof is a direct unwinding:

* `genEval_cast` removes the degree transport `(n+m-2)+1 = n+m-1` (the transport map is the
  same `shmap` that appears in `delv`);
* `genEval_cochainDiff` expands the coboundary as the sum over the faces;
* `delv_eq` identifies the `k`-th face of the transported simplex with `delv n m k` and
  `genEval_cup2` expands the cup-2 product at a simplex, leaving the interval maps composed
  with `delv`, which are *by definition* the maps `lU`/`lV` of the `lTerm` family;
* finally the outer sum is reindexed from `Fin ((n+m-2)+2)` to `Fin (n+m)` (`Fintype.sum_equiv`
  along `finCongr`) and the two sides are matched definitionally.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ.C2

open Work.Pi6.SQM (F2)

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-- Application of a composite of order maps: `X` is a contravariant functor of
`SimplexCategory`, so `X.map (f ≫ g).op σ = X.map f.op (X.map g.op σ)`. -/
private lemma lhsExpand_map_comp_op {X : SSet} {p q N : ℕ} (f : ⦋p⦌ ⟶ ⦋q⦌)
    (g : ⦋q⦌ ⟶ ⦋N⦌) (σ : X _⦋N⦌) :
    X.map f.op (X.map g.op σ) = X.map (f ≫ g).op σ := by
  rw [show (f ≫ g).op = g.op ≫ f.op from rfl, Functor.map_comp]
  rfl

/-- `(-1)^k = 1` in `𝔽₂`. -/
private lemma lhsExpand_neg_one_pow (k : ℕ) : (-1 : F2) ^ k = 1 := by
  have h : (-1 : F2) = 1 := by decide
  rw [h, one_pow]

/-- **The per-face form of the expansion.**  Evaluating `u ∪₂ v` on the `i`-th face of the
transported simplex is the sum over the cut points `(a,b)` of the `lTerm`s with outer index
`⟨i.val, _⟩ : Fin (n+m)`. -/
private lemma lhsExpand_face (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m)
    (σ : X _⦋n + m - 1⦌) (hcast : (n + m - 2) + 1 = n + m - 1)
    (i : Fin ((n + m - 2) + 2)) :
    genEval F2 X (Work.Pi6.SQ.cup2 X n m u v)
        (X.δ i (X.map (Work.Cohomology.shmap ((n + m - 2) + 1) (n + m - 1) hcast).op σ))
      = ∑ a : Fin (n - 1), ∑ b : Fin (m - 1),
          lTerm X n m hn hm u v σ (⟨i.val, by omega⟩, (a, b)) := by
  rw [show X.δ i (X.map (Work.Cohomology.shmap ((n + m - 2) + 1) (n + m - 1) hcast).op σ)
      = X.map (delv n m i.val (by omega) (by omega)).op σ from by
    show X.map (SimplexCategory.δ i).op
        (X.map (Work.Cohomology.shmap ((n + m - 2) + 1) (n + m - 1) hcast).op σ)
      = X.map (delv n m i.val (by omega) (by omega)).op σ
    rw [delv_eq n m i.val (by omega) (by omega) hcast]
    simp only [lhsExpand_map_comp_op]]
  rw [Work.Pi6.SQ.genEval_cup2]
  simp only [lhsExpand_map_comp_op]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp only [lTerm]
  rfl

theorem lhsExpand (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (u : Work.Cohomology.Cochain Work.Pi6.SQM.F2 X n)
    (v : Work.Cohomology.Cochain Work.Pi6.SQM.F2 X m)
    (σ : X.obj (Opposite.op (SimplexCategory.mk (n + m - 1))))
    (hcast : (n + m - 2) + 1 = n + m - 1) :
    Work.Cohomology.genEval Work.Pi6.SQM.F2 X
        (hcast ▸ Work.Cohomology.cochainDiff Work.Pi6.SQM.F2 X (Work.Pi6.SQ.cup2 X n m u v)) σ
      = ∑ i : Work.Pi6.SQ.C2.LIdx n m, Work.Pi6.SQ.C2.lTerm X n m hn hm u v σ i := by
  rw [Work.Cohomology.genEval_cast (p := (n + m - 2) + 1) (q := n + m - 1) hcast]
  -- The right hand side, split over the product index type.
  have hR : (∑ i : LIdx n m, lTerm X n m hn hm u v σ i)
      = ∑ k : Fin (n + m), ∑ a : Fin (n - 1), ∑ b : Fin (m - 1),
          lTerm X n m hn hm u v σ (k, (a, b)) := by
    simp only [Fintype.sum_prod_type]
  rw [hR]
  -- The left hand side, expanded as the sum over the faces.
  have hB : genEval F2 X (cochainDiff F2 X (Work.Pi6.SQ.cup2 X n m u v))
      (X.map (Work.Cohomology.shmap ((n + m - 2) + 1) (n + m - 1) hcast).op σ)
      = ∑ i : Fin ((n + m - 2) + 2),
          genEval F2 X (Work.Pi6.SQ.cup2 X n m u v)
            (X.δ i (X.map (Work.Cohomology.shmap ((n + m - 2) + 1) (n + m - 1) hcast).op σ)) := by
    rw [Work.Cohomology.genEval_cochainDiff]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [lhsExpand_neg_one_pow, one_mul]
  rw [hB]
  -- Expansion of each face of the cup-2 product.
  rw [show (∑ i : Fin ((n + m - 2) + 2),
        genEval F2 X (Work.Pi6.SQ.cup2 X n m u v)
          (X.δ i (X.map (Work.Cohomology.shmap ((n + m - 2) + 1) (n + m - 1) hcast).op σ)))
      = ∑ i : Fin ((n + m - 2) + 2), ∑ a : Fin (n - 1), ∑ b : Fin (m - 1),
          lTerm X n m hn hm u v σ (⟨i.val, by omega⟩, (a, b)) from
    Finset.sum_congr rfl (fun i _ => lhsExpand_face X n m hn hm u v σ hcast i)]
  -- Reindexing `Fin ((n+m-2)+2) → Fin (n+m)`.
  have h2 : (n + m - 2) + 2 = n + m := by omega
  exact Fintype.sum_equiv (finCongr h2)
    (fun i : Fin ((n + m - 2) + 2) => ∑ a : Fin (n - 1), ∑ b : Fin (m - 1),
        lTerm X n m hn hm u v σ (⟨i.val, by omega⟩, (a, b)))
    (fun k : Fin (n + m) => ∑ a : Fin (n - 1), ∑ b : Fin (m - 1),
        lTerm X n m hn hm u v σ (k, (a, b)))
    (fun i => rfl)

end

end Work.Pi6.SQ.C2
