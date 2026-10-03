import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.ampDefs

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The entrywise `τ`-twist commutes with flattening blocks: the "block entry"
`(A.map (m • ·)) (i, j)` is the inner matrix `m • A i j`, whose entries are `m • (A i j) a b`, and
this is exactly the value of `flattenBlocks` applied to `A` and then twisted entrywise. -/
theorem flattenBlocks_map_smul {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    {k l N : ℕ} (m : Multiplicative ℤ)
    (A : Matrix (Fin k) (Fin l) (Matrix (Fin N) (Fin N) R)) :
    Work.ORHughesFree.flattenBlocks (A.map (fun a => m • a))
      = (Work.ORHughesFree.flattenBlocks A).map (fun b => m • b) := by
  ext i j
  simp [Work.ORHughesFree.flattenBlocks, Matrix.map_apply]

theorem amplifiedRank_tauCompatible {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    {rk : Work.ORHughesFree.SylvesterRank R}
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (N : ℕ) (hN : 0 < N) :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (Matrix (Fin N) (Fin N) R)),
      (Work.ORHughesFree.NaturalExtension.amplifiedRank rk N hN).rk n m
          (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a))
        = (Work.ORHughesFree.NaturalExtension.amplifiedRank rk N hN).rk n m A := by
  intro n m A
  rw [amplifiedRank_apply, amplifiedRank_apply, flattenBlocks_map_smul]
  exact congrArg (fun x => x / (N : ℝ))
    (hτ (n * N) (m * N) (Work.ORHughesFree.flattenBlocks A))

end Work.ORHughesFree.NaturalExtension
