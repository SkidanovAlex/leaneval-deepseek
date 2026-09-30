import Mathlib
import Submission.Work.Pi6.SQ.C2.Cup2Setup
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The `C3`/`C4` summands of the mod-2 `∪₂`-coboundary identity

This file proves `Work.Pi6.SQ.C2.rhsExpandC34`: the evaluation of the two "coboundary" terms
`(δu)∪₂v` and `u∪₂(δv)` of the cup-2 coboundary formula (`Work.Pi6.SQM.Cup2Cob`) as the
explicit sums over the index families `C3Idx`/`C4Idx` of `Cup2CobSetup`.

Concretely, for `σ : X _⦋n+m-1⦌`,

* `genEval ((δu) ∪₂ v) σ = ∑_{A,B,j} u(c3U A B j · σ) · v(c3V A B j · σ)`,
* `genEval (u ∪₂ (δv)) σ = ∑_{A,B,j} u(c4U A B j · σ) · v(c4V A B j · σ)`,

which is the pointwise form of the `C3`- and `C4`-sums appearing in the statement of
`cup2Coboundary` (`Submission/Work/Pi6/SQM/cup2CoboundaryM.lean`).

The proof is a direct unwinding: transport along the degree equality (`genEval_cast`, with the
degree identification `shv`/`shu`), expand the cup-2 product at a simplex (`genEval_cup2`), push the
degree transport inside the interval maps (`map_comp_op`), expand the coboundary of a cochain on a
generator (`genEval_cochainDiff_F2`), push the face maps inside, distribute the multiplication over
the `Fin`-sum, and finally split the sum over the product index type `C3Idx`/`C4Idx`
(`Fintype.sum_prod_type`).  In the last step the two sides agree definitionally, because
`c3U`/`c3V` (resp. `c4U`/`c4V`) are *defined* as exactly those composites and the auxiliary
arithmetic proofs are proof-irrelevant.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ.C2

open Work.Pi6.SQM (F2)

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-! ## Two auxiliary lemmas -/

/-- Functoriality of the simplex map of a simplicial set, in the form used below: pulling back by
`g` and then by `f` is pull-back by the composite `f ≫ g`. -/
private lemma rhsExpandC34_map_comp_op {X : SSet} {p q N : ℕ} (f : ⦋p⦌ ⟶ ⦋q⦌)
    (g : ⦋q⦌ ⟶ ⦋N⦌) (σ : X _⦋N⦌) :
    X.map f.op (X.map g.op σ) = X.map (f ≫ g).op σ := by
  rw [show (f ≫ g).op = g.op ≫ f.op from rfl, Functor.map_comp]
  rfl

/-- The coboundary of a mod-2 cochain, evaluated on a generator: over `𝔽₂` the signs of
`genEval_cochainDiff` are all `1`. -/
private lemma genEval_cochainDiff_F2 {X : SSet} {k : ℕ} (γ : Cochain F2 X k)
    (τ : X _⦋k+1⦌) :
    genEval F2 X (cochainDiff F2 X γ) τ = ∑ i : Fin (k+2), genEval F2 X γ (X.δ i τ) := by
  rw [Work.Cohomology.genEval_cochainDiff]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-! ## The statement -/

/-- **The `C3` and `C4` sums of the cup-2 coboundary formula.**  Evaluating the two "coboundary"
terms `(δu) ∪₂ v` and `u ∪₂ (δv)` at a simplex `σ` of dimension `n+m-1` gives the explicit sums
over the index families `C3Idx n m` and `C4Idx n m` of `Cup2CobSetup`. -/
theorem rhsExpandC34 (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (u : Work.Cohomology.Cochain Work.Pi6.SQM.F2 X n)
    (v : Work.Cohomology.Cochain Work.Pi6.SQM.F2 X m)
    (σ : X.obj (Opposite.op (SimplexCategory.mk (n + m - 1))))
    (h2 : (n + 1) + m - 2 = n + m - 1) (h3 : n + (m + 1) - 2 = n + m - 1) :
    (Work.Cohomology.genEval Work.Pi6.SQM.F2 X
        (h2 ▸ Work.Pi6.SQ.cup2 X (n + 1) m (Work.Cohomology.cochainDiff Work.Pi6.SQM.F2 X u) v) σ
        = ∑ i : Work.Pi6.SQ.C2.C3Idx n m, Work.Pi6.SQ.C2.c3Term X n m u v σ i) ∧
    (Work.Cohomology.genEval Work.Pi6.SQM.F2 X
        (h3 ▸ Work.Pi6.SQ.cup2 X n (m + 1) u (Work.Cohomology.cochainDiff Work.Pi6.SQM.F2 X v)) σ
        = ∑ i : Work.Pi6.SQ.C2.C4Idx n m, Work.Pi6.SQ.C2.c4Term X n m u v σ i) := by
  constructor
  · -- the `(δu) ∪₂ v` side
    rw [Work.Cohomology.genEval_cast (p := (n + 1) + m - 2) (q := n + m - 1) h2]
    rw [show Work.Cohomology.shmap ((n + 1) + m - 2) (n + m - 1) h2 = shv n m from
      shmap_congr h2 (by omega)]
    rw [Work.Pi6.SQ.genEval_cup2]
    simp only [rhsExpandC34_map_comp_op]
    simp only [genEval_cochainDiff_F2]
    simp only [SimplicialObject.δ, rhsExpandC34_map_comp_op]
    simp only [Finset.sum_mul]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun x_1 _ =>
      Finset.sum_congr rfl (fun i _ => rfl))
  · -- the `u ∪₂ (δv)` side
    rw [Work.Cohomology.genEval_cast (p := n + (m + 1) - 2) (q := n + m - 1) h3]
    rw [show Work.Cohomology.shmap (n + (m + 1) - 2) (n + m - 1) h3 = shu n m from
      shmap_congr h3 (by omega)]
    rw [Work.Pi6.SQ.genEval_cup2]
    simp only [rhsExpandC34_map_comp_op]
    simp only [genEval_cochainDiff_F2]
    simp only [SimplicialObject.δ, rhsExpandC34_map_comp_op]
    simp only [Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun x_1 _ =>
      Finset.sum_congr rfl (fun i _ => rfl))

end

end Work.Pi6.SQ.C2
