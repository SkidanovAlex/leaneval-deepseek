import Mathlib
import Submission.Work.WilE7.AboveAux.AboveLevelDefs
import Submission.Work.WilE7.prodSet
import Submission.Work.WilE7.prod_semiPf

namespace Work.WilE7.AboveAux

open WilkiesDesign WilkiesDesign.E

/-! ## The blocks of the two halves of `ℝ^{N*m+N}`

`fibBlocks X (m+1)` is `SemiPf.prod (fibBlocks X m) X`, which lives in `ℝ^{N*m+N}`: the first
`N*m` coordinates carry the `m` blocks of `fibBlocks X m` and the last `N` coordinates carry the
single block of `X`.  The two lemmas below identify the `m+1` blocks of a point of `ℝ^{N*m+N}`
with the blocks of the two halves. -/

/-- The `l`-th block of a point of `ℝ^{N*m+N}` depends only on its first `N*m` coordinates. -/
theorem fibBlk_projFirst {N m : ℕ} (z : Fin (N * m + N) → ℝ) (l : Fin m) :
    fibBlk (projFirst (N * m) N z) l = fibBlk z (Fin.castSucc l) := by
  funext i
  simp only [fibBlk_apply, projFirst]
  congr 1

/-- The last `N` coordinates of a point of `ℝ^{N*m+N}` are its last block. -/
theorem fibBlk_projSnd {N m : ℕ} (z : Fin (N * m + N) → ℝ) :
    projSnd (N * m) N z = fibBlk z (Fin.last m) := by
  funext i
  simp only [fibBlk_apply, projSnd]
  congr 1
  apply Fin.ext
  simp [Fin.natAdd, Nat.mul_comm]

/-- The point set of the `m`-fold product `fibBlocks X m` of `X` with itself is the set of
points of `ℝ^{N*m}` whose `m` blocks all lie in `X`. -/
theorem fibBlocks_set {N : ℕ} (X : WilkiesDesign.E.SemiPf N) (m : ℕ) :
    (Work.WilE7.AboveAux.fibBlocks X m).set =
      {Z : Fin (N * m) → ℝ | ∀ l : Fin m, Work.WilE7.AboveAux.fibBlk Z l ∈ X.set} := by
  induction m with
  | zero =>
    rw [fibBlocks_zero]
    ext Z
    simp [SemiPf.set, cubeC, Basic.holds]
  | succ m ih =>
    rw [fibBlocks_succ, Work.WilE7.prodSet]
    ext Z
    rw [ih]
    simp only [Set.mem_ofPred_eq, fibBlk_projFirst, fibBlk_projSnd]
    constructor
    · rintro ⟨h1, h2⟩ l
      induction l using Fin.lastCases with
      | last => exact h2
      | cast l => exact h1 l
    · exact fun h => ⟨fun l => h (Fin.castSucc l), h (Fin.last m)⟩

end Work.WilE7.AboveAux
