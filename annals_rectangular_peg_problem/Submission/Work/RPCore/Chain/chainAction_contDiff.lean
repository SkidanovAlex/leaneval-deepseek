import Mathlib
import Submission.Work.RPCore.Chain.C4Defs
import Submission.Work.RPCore.Chain.ChainDefs

/-!
# `Work.RPCore.Chain.chainAction_contDiff`

The broken-geodesic (chain) action `chainAction n W (q, P)` is the sum of

* the momentum term `∑ j, ⟨P j, q (j+1) - q j⟩`, a homogeneous quadratic polynomial in
  `z = (q, P)`, and
* the generating-function terms `- ∑ j, W j (q j, Peff n P j)`, each of which is the composition of
  `W j` with the insertion `z ↦ (z.1 j, Peff n z.2 j)` of `z` at the `j`-th phase point — a
  continuous *linear* map `ChainSp n → PS`.

Hence if every generating function is `C³`, the chain action is `C²`, which is the smoothness one
needs before speaking about its critical points (`chainAction_crit`).

The auxiliary statements `Peff_lt`, `Peff_castSucc`, `Peff_last` used below live in
`Submission.Work.RPCore.Chain.ChainDefs`.
-/

namespace Work.RPCore.Chain

open Work.RPV

noncomputable section

/-- `chainAction`, with the (discarded) last momentum slot written through `Peff`. -/
theorem chainAction_eq_sumPeff (n : ℕ) (W : Fin (n + 1) → PS → ℝ)
    (q : Fin (n + 1) → ℝ × ℝ) (P : Fin n → ℝ × ℝ) :
    chainAction n W q P =
      (∑ j : Fin n, ((P j).1 * ((q j.succ).1 - (q j.castSucc).1) +
        (P j).2 * ((q j.succ).2 - (q j.castSucc).2)))
        - ∑ j : Fin (n + 1), W j (q j, Peff n P j) := by
  simp only [chainAction, Peff]

/-- The insertion `z ↦ (z.1 j, Peff n z.2 j)` of a chain state at its `j`-th phase point is
smooth (in fact `C³`): both coordinates are continuous linear functions of `z`. -/
theorem chainAction_contDiff_insert (n : ℕ) (j : Fin (n + 1)) :
    ContDiff ℝ 3 (fun z : ChainSp n => (z.1 j, Peff n z.2 j)) := by
  apply ContDiff.prodMk
  · fun_prop
  · by_cases h : (j : ℕ) < n
    · have hEq : (fun z : ChainSp n => Peff n z.2 j) = (fun z : ChainSp n => z.2 ⟨j, h⟩) := by
        funext z; exact Peff_lt h
      rw [hEq]; fun_prop
    · have hEq : (fun z : ChainSp n => Peff n z.2 j) = (fun _ : ChainSp n => (0 : ℝ × ℝ)) := by
        funext z; simp only [Peff, h, dite_false]
      rw [hEq]; exact contDiff_const

/-- The quadratic (momentum) part of the chain action is smooth in `z = (q, P)`. -/
theorem chainAction_contDiff_quad (n : ℕ) :
    ContDiff ℝ 2 (fun z : ChainSp n =>
      ∑ j : Fin n, ((z.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
        (z.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2))) := by
  apply ContDiff.sum
  intro j _
  fun_prop

/-- If all the generating functions `W j` are `C³`, then the chain action is `C²` as a function of
the chain state `z = (q, P)`. -/
theorem chainAction_contDiff (n : ℕ) (W : Fin (n + 1) → Work.RPV.PS → ℝ)
    (hWc : ∀ j, ContDiff ℝ 3 (W j)) :
    ContDiff ℝ 2 (fun z : ChainSp n => Work.RPV.chainAction n W z.1 z.2) := by
  have hterm : ∀ j : Fin (n + 1), ContDiff ℝ 2 (fun z : ChainSp n => W j (z.1 j, Peff n z.2 j)) :=
    fun j => (ContDiff.comp (hWc j) (chainAction_contDiff_insert n j)).of_le (by norm_num)
  have hsum : ContDiff ℝ 2 (fun z : ChainSp n => ∑ j : Fin (n + 1), W j (z.1 j, Peff n z.2 j)) :=
    ContDiff.sum (fun j _ => hterm j)
  rw [show (fun z : ChainSp n => Work.RPV.chainAction n W z.1 z.2) = (fun z : ChainSp n =>
      (∑ j : Fin n, ((z.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
        (z.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2)))
      - ∑ j : Fin (n + 1), W j (z.1 j, Peff n z.2 j)) from by
    funext z; exact chainAction_eq_sumPeff n W z.1 z.2]
  exact (chainAction_contDiff_quad n).sub hsum

end

end Work.RPCore.Chain
