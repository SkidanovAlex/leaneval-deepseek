import Mathlib
import Submission.Work.Pi6.SQM.Cup3CobSetup
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The five sums of the mod-2 `∪₃` coboundary identity, over the master index families

The expansion lemmas of `Submission/Work/Pi6/SQM/Cup3Identities.lean` express the five sums of

`δ(u ∪₃ v) = u ∪₂ v + v ∪₂ u + (δu) ∪₃ v + u ∪₃ (δv)`

as nested sums over `Fin` indices with `if`-guards.  This file rewrites them as sums over the
index families `L3Idx`, `T3Idx`, `T4Idx`, `T1Idx`, `T2Idx` of `Cup3CobSetup.lean` (via
`sum_subtype_eq_ite` and `Fintype.sum_prod_type`), so that the assembly can use
`Finset.sum_involution` on the disjoint union `Idx3`.

All statements use the degree transport `hcast` only through `Work.Cohomology.shmap` (never as a
`▸` cast), so that the statement has no side conditions; the assembly converts the transported
form with `Work.Cohomology.genEval_cast`.
-/

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-- `shmap` does not depend on the proof of the degree equality. -/
lemma shmap_congr' {p q : ℕ} (h h' : p = q) :
    Work.Cohomology.shmap p q h = Work.Cohomology.shmap p q h' := by
  simp only [Work.Cohomology.shmap]

/-- Pushing a constant `if` inside a sum. -/
lemma dite_sum {ι M : Type} [Fintype ι] [AddCommMonoid M] (P : Prop) [Decidable P]
    (F : P → ι → M) :
    (if h : P then ∑ j, F h j else 0) = ∑ j, (if h : P then F h j else 0) := by
  by_cases h : P <;> simp [h]

/-- The `L`-sum: `δ(u∪₃v)` evaluated at `σ` is the sum of `cup3Term` over `L3Idx`. -/
theorem lhsExpand3 (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌)
    (hcast : (n + m - 3) + 1 = n + m - 2) :
    genEval F2 X (cochainDiff F2 X (cup3 X n m u v))
        (X.map (Work.Cohomology.shmap ((n + m - 3) + 1) (n + m - 2) hcast).op σ)
      = ∑ p : L3Idx n m, cup3Term X n m hn hm u v σ (Sum.inl p) := by
  have h := lhs_expand (n := n) (m := m) X n m u v hn hm hcast σ
  rw [Work.Cohomology.genEval_cast (p := (n + m - 3) + 1) (q := n + m - 2) hcast] at h
  rw [h]
  rw [sum_subtype_eq_ite
    (p := fun x : Fin ((n + m - 3) + 2) × (Fin (n - 2) × Fin (m - 2) × Fin (n - 2)) =>
      x.2.1.val + x.2.2.2.val + 3 ≤ n)
    (g := fun p => cup3Term X n m hn hm u v σ (Sum.inl p))]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))))
  simp only [cup3Term_inl]
  by_cases h : a.val + c.val + 3 ≤ n
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]

/-- The `T1`-sum: `u∪₂v` evaluated at `σ` is the sum of `cup3Term` over `T1Idx`. -/
theorem t1Expand3 (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌) :
    genEval F2 X (Work.Pi6.SQ.cup2 X n m u v) σ
      = ∑ p : T1Idx n m, cup3Term X n m hn hm u v σ (idxT1 p) := by
  rw [t1_expand (n := n) (m := m) X n m u v hn hm σ]
  conv_rhs => rw [Fintype.sum_prod_type
    (f := fun x : Fin (n - 1) × Fin (m - 1) => cup3Term X n m hn hm u v σ (idxT1 x))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp only [idxT1, cup3Term_T1]
  rfl

/-- The `T2`-sum: `v∪₂u` evaluated at `σ` is the sum of `cup3Term` over `T2Idx`. -/
theorem t2Expand3 (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌)
    (hcast : m + n - 2 = n + m - 2) :
    genEval F2 X (Work.Pi6.SQ.cup2 X m n v u)
        (X.map (Work.Cohomology.shmap (m + n - 2) (n + m - 2) hcast).op σ)
      = ∑ p : T2Idx n m, cup3Term X n m hn hm u v σ (idxT2 p) := by
  have h := t2_expand (n := n) (m := m) X n m v u hn hm hcast σ
  rw [Work.Cohomology.genEval_cast (p := m + n - 2) (q := n + m - 2) hcast] at h
  rw [h]
  conv_rhs => rw [Fintype.sum_prod_type
    (f := fun x : Fin (m - 1) × Fin (n - 1) => cup3Term X n m hn hm u v σ (idxT2 x))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [show Work.Cohomology.shmap (m + n - 2) (n + m - 2) hcast = shT2 n m hn hm from
    shmap_congr' _ _]
  simp only [idxT2, cup3Term_T2, t2U, t2V]
  rw [mul_comm]

/-- The `T3`-sum: `(δu)∪₃v` evaluated at `σ` is the sum of `cup3Term` over `T3Idx`. -/
theorem t3Expand3 (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌)
    (hcast : (n + 1) + m - 3 = n + m - 2) :
    genEval F2 X (cup3 X (n + 1) m (cochainDiff F2 X u) v)
        (X.map (Work.Cohomology.shmap ((n + 1) + m - 3) (n + m - 2) hcast).op σ)
      = ∑ p : T3Idx n m, cup3Term X n m hn hm u v σ (idxC3 p) := by
  have h := t3_expand (n := n) (m := m) X n m u v hn hm hcast σ
  rw [Work.Cohomology.genEval_cast (p := (n + 1) + m - 3) (q := n + m - 2) hcast] at h
  rw [h]
  simp only [Finset.sum_mul]
  rw [sum_subtype_eq_ite
    (p := fun x : Fin (n - 1) × (Fin (m - 2) × Fin (n - 1) × Fin (n + 2)) =>
      x.1.val + x.2.2.1.val + 3 ≤ n + 1)
    (g := fun p => cup3Term X n m hn hm u v σ (idxC3 p))]
  simp only [dite_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun j _ => ?_))))
  by_cases h : a.val + c.val + 3 ≤ n + 1
  · rw [dif_pos h, dif_pos h]
    rw [show Work.Cohomology.shmap ((n + 1) + m - 3) (n + m - 2) hcast = sh3 n m hn hm from
      shmap_congr' _ _]
    simp only [idxC3, cup3Term_C3, c3U, c3V, Category.assoc]
    rfl
  · rw [dif_neg h, dif_neg h]

/-- The `T4`-sum: `u∪₃(δv)` evaluated at `σ` is the sum of `cup3Term` over `T4Idx`. -/
theorem t4Expand3 (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌)
    (hcast : n + (m + 1) - 3 = n + m - 2) :
    genEval F2 X (cup3 X n (m + 1) u (cochainDiff F2 X v))
        (X.map (Work.Cohomology.shmap (n + (m + 1) - 3) (n + m - 2) hcast).op σ)
      = ∑ p : T4Idx n m, cup3Term X n m hn hm u v σ (idxC4 p) := by
  have h := t4_expand (n := n) (m := m) X n m u v hn hm hcast σ
  rw [Work.Cohomology.genEval_cast (p := n + (m + 1) - 3) (q := n + m - 2) hcast] at h
  rw [h]
  simp only [Finset.mul_sum]
  rw [sum_subtype_eq_ite
    (p := fun x : Fin (n - 2) × (Fin (m - 1) × Fin (n - 2) × Fin (m + 2)) =>
      x.1.val + x.2.2.1.val + 3 ≤ n)
    (g := fun p => cup3Term X n m hn hm u v σ (idxC4 p))]
  simp only [dite_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun j _ => ?_))))
  by_cases h : a.val + c.val + 3 ≤ n
  · rw [dif_pos h, dif_pos h]
    rw [show Work.Cohomology.shmap (n + (m + 1) - 3) (n + m - 2) hcast = sh4 n m hn hm from
      shmap_congr' _ _]
    simp only [idxC4, cup3Term_C4, c4U, c4V, Category.assoc]
    rfl
  · rw [dif_neg h, dif_neg h]

end

end Work.Pi6.SQM
