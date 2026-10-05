import Mathlib
import Submission.Work.RPCore.Chain.C4Defs
import Submission.Work.RPCore.Chain.BvForm_diag
import Submission.Work.RPCore.Chain.sum_ite_Wrot

/-!
# C4: the reference chain action is quadratic

`chainAction n (refGF N δ) z = BvForm n N δ z z / 2 + Lav n N δ z`
for `n = 3N - 1`, `N ≥ 1`.

## Proof outline

Write `z = (q, P)` with `q : Fin (n+1) → ℝ²` and `P : Fin n → ℝ²`.
The reference generating functions vanish outside the middle block `N ≤ j < 2N`
(where they equal `Wrot δ`).  Since `2N ≤ 3N - 1 = n` for `N ≥ 1`, the middle block is
contained in `{j : j < n}`, so both the last index of the `Fin (n+1)`-sum and the "far end"
`Peff` slot carry no contribution: the generating-function sum collapses to the
`Fin n`-sum over the middle-block indices.  The definitional expansion of `Wrot`

`Wrot δ x = (1/cos δ - 1) q¹p¹ - (tan δ)/2 (q¹² + p¹²) + δ p²`

then produces, term by term, the three sums appearing in `BvForm`/`Lav`; the factor `1/2`
in front of `BvForm` turns the doubled diagonal terms of the bilinear form into exactly the
`Wrot` contributions.
-/

namespace Work.RPCore.Chain

open Work.RPV
open scoped BigOperators

/-- The `j`-term of the reference generating-function sum is `Wrot δ` on the middle block and
`0` elsewhere; for `j : Fin n` the momentum slot `Peff n P j.castSucc` is `P j`. -/
theorem refGF_chain_sum (n N : ℕ) (hN : 1 ≤ N) (hn : n = 3 * N - 1) (δ : ℝ)
    (z : ChainSp n) :
    (∑ j : Fin (n + 1),
        refGF N δ (j : ℕ) (z.1 j, (if h : (j : ℕ) < n then z.2 ⟨j, h⟩ else 0)))
      = ∑ j : Fin n, (if midBlock N (j : ℕ) then Wrot δ (z.1 j.castSucc, z.2 j) else 0) := by
  -- the last index `n = 3N - 1` is never in the middle block, since `2N ≤ 3N - 1` for `N ≥ 1`
  have hmid : ¬ midBlock N n := by
    simp only [midBlock]
    omega
  rw [Fin.sum_univ_castSucc]
  have hlast : refGF N δ (↑(Fin.last n))
      (z.1 (Fin.last n), (if h : (↑(Fin.last n)) < n then z.2 ⟨↑(Fin.last n), h⟩ else 0))
      = 0 := by
    simp only [refGF]
    rw [ite_eq_right]
    intro h
    exact hmid (by simpa only [Fin.val_last] using h)
  rw [hlast, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [refGF, Fin.val_castSucc, dite_eq_left i.isLt]

theorem ref_action_quadratic (n N : ℕ) (hN : 1 ≤ N) (hn : n = 3 * N - 1) (δ : ℝ)
    (z : Work.RPCore.Chain.ChainSp n) :
    Work.RPV.chainAction n (fun j => Work.RPCore.Chain.refGF N δ (j : ℕ)) z.1 z.2
      = Work.RPCore.Chain.BvForm n N δ z z / 2 + Work.RPCore.Chain.Lav n N δ z := by
  simp only [chainAction]
  rw [refGF_chain_sum n N hN hn δ z, BvForm_diag]
  rw [sum_ite_Wrot (c := fun j : Fin n => midBlock N (j : ℕ))
    (q := fun j => z.1 j.castSucc) (P := fun j => z.2 j)]
  unfold Lav
  ring

end Work.RPCore.Chain
