/-
  WilE7 (`Submission.Work.WilE7.BelowAux.kProd`): the `k`-fold product of a semi-Pfaffian set.

  The counting realisation of the open cells (`Work.WilE7.belowCell_star_open`) needs, for a
  fixed `X : SemiPf n`, the `k`-fold product

    `funPower X k = {z : ℝ^{n*k} | ∀ i : Fin k, block i z ∈ X.set}`,

  as a single restricted semi-Pfaffian set in `ℝ^{n*k}`.  The ambient dimension is written
  `n * k` (not `k * n`) so that the recursive construction

    `funPower X 0 = cubeSemiPf 0`,   `funPower X (k+1) = SemiPf.prod (funPower X k) X`

  typechecks without a cast (`n * (k+1)` is definitionally `n * k + n`).

  The `i`-th block of `z : Fin (n*k) → ℝ` is read off by `blk i z`; the two structural lemmas
  `blk_castSucc` / `blk_last` express the block of the `Fin`-successor / last index through
  `projFirst` / `projSnd` of the product.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.ProdDefs
import Submission.Work.WilE8.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The index of the `l`-th coordinate of the `i`-th block inside `Fin (n * k)`. -/
def blkIdx {n k : ℕ} (i : Fin k) (l : Fin n) : Fin (n * k) :=
  ⟨i.val * n + l.val, by
    calc i.val * n + l.val < i.val * n + n := Nat.add_lt_add_left l.isLt _
      _ = (i.val + 1) * n := (Nat.succ_mul i.val n).symm
      _ ≤ k * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
      _ = n * k := Nat.mul_comm k n⟩

/-- The `i`-th block (`i < k`) of a point of `ℝ^{n*k}`. -/
def blk {n k : ℕ} (i : Fin k) (z : Fin (n * k) → ℝ) : Fin n → ℝ := fun l => z (blkIdx i l)

/-- The block of the `Fin`-successor index is read off from `projFirst`. -/
theorem blk_castSucc {n k : ℕ} (i : Fin k) (z : Fin (n * (k + 1)) → ℝ) :
    blk (Fin.castSucc i) z = blk i (projFirst (n * k) n z) := by
  funext l
  have h : blkIdx (Fin.castSucc i) l = Fin.castAdd n (blkIdx i l) := rfl
  show z (blkIdx (Fin.castSucc i) l) = z (Fin.castAdd n (blkIdx i l))
  rw [h]

/-- The block of the last index is `projSnd`. -/
theorem blk_last {n k : ℕ} (z : Fin (n * (k + 1)) → ℝ) :
    blk (Fin.last k) z = projSnd (n * k) n z := by
  funext l
  have h : blkIdx (Fin.last k) l = Fin.natAdd (n * k) l := by
    apply Fin.ext
    show k * n + l.val = n * k + l.val
    rw [Nat.mul_comm k n]
  show z (blkIdx (Fin.last k) l) = z (Fin.natAdd (n * k) l)
  rw [h]

/-- The `k`-fold product of `X` with itself, as a semi-Pfaffian set in `ℝ^{n*k}`. -/
noncomputable def iterProd {n : ℕ} (X : SemiPf n) : (k : ℕ) → SemiPf (n * k)
  | 0 => Work.WilE8.cubeSemiPf 0
  | (k + 1) => SemiPf.prod (iterProd X k) X

end Work.WilE7
