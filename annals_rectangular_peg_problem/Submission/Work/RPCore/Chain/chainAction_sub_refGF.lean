import Mathlib
import Submission.Work.RPCore.Chain.ChainProj

/-!
# `Work.RPCore.Chain.chainAction_sub_refGF`

The perturbation of the reference action.  If the generating functions `W j` agree with the
reference data `refGF N δ` on the middle block (the rotation steps), then

`chainAction n W - chainAction n (refGF N δ) = -∑_j stepFun n N δ W j`,

i.e. the difference of the two actions is the sum of the *off-middle-block* terms of the chain.
This is the elementary bookkeeping identity that turns the action difference into the function
`-∑_j stepFun` whose compact support (in the slab) is what `chainPert_bounds` controls.

## Proof

Both actions have the same kinetic part `∑_{j : Fin n} ⟨P_j, q_{j+1} - q_j⟩`, so their
difference is the difference of the two generating-function sums.  Both sums are evaluated at
the same point `projPS n j z = (z.1 j, Peff n z.2 j)` (`projPS_apply`), hence the difference is
`-∑_j (W j - refGF N δ j)` evaluated there.  Termwise, on the middle block `W j = Wrot δ`
agrees with `refGF N δ j = Wrot δ`, so the term vanishes while `stepFun` is `0` there too; off
the middle block `refGF N δ j = 0`, and the term is `W j (projPS n j z)`, exactly
`stepFun n N δ W j z`.
-/

namespace Work.RPCore.Chain

open Work.RPV
open scoped BigOperators

theorem chainAction_sub_refGF (n N : ℕ) (δ : ℝ) (W : Fin (n + 1) → Work.RPV.PS → ℝ)
    (hWmid : ∀ j : Fin (n + 1), midBlock N (j : ℕ) → W j = Work.RPV.Wrot δ) (z : ChainSp n) :
    Work.RPV.chainAction n W z.1 z.2
      - Work.RPV.chainAction n (fun j => refGF N δ (j : ℕ)) z.1 z.2
      = - ∑ j : Fin (n + 1), stepFun n N δ W j z := by
  -- Termwise comparison of the `j`-th summands of the two generating-function sums:
  -- the two sums are evaluated at the same point `(z.1 j, Peff n z.2 j)`.
  have hterm : ∀ j : Fin (n + 1),
      W j (z.1 j, (if h : (j : ℕ) < n then z.2 ⟨j, h⟩ else 0))
        - refGF N δ (j : ℕ) (z.1 j, (if h : (j : ℕ) < n then z.2 ⟨j, h⟩ else 0))
      = stepFun n N δ W j z := by
    intro j
    by_cases h : midBlock N (j : ℕ)
    · -- on the middle block both summands are `Wrot δ`, and `stepFun` vanishes
      rw [stepFun_of_mid h, hWmid j h]
      simp only [refGF, ite_eq_left h, sub_self]
    · -- off the middle block `refGF` is `0` and only `W j` survives
      rw [stepFun_of_not_mid h, projPS_apply]
      simp only [Peff, refGF, ite_eq_right h, sub_zero]
  have hsum : (∑ j : Fin (n+1), W j (z.1 j, if h : (j:ℕ) < n then z.2 ⟨j,h⟩ else 0))
      - (∑ j : Fin (n+1), refGF N δ (j:ℕ) (z.1 j, if h : (j:ℕ) < n then z.2 ⟨j,h⟩ else 0))
      = ∑ j : Fin (n + 1), stepFun n N δ W j z := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm j
  -- the kinetic parts coincide, so only the two generating-function sums are left
  simp only [Work.RPV.chainAction]
  linarith [hsum]

end Work.RPCore.Chain
