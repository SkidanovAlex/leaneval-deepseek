import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the formal time-derivative tower of the nonlinearity (flat DeTurck case)

`towerExp Φ j` is the `j`-th formal time derivative of the nonlinearity `Φ`, expressed as a
function of the space point `x` and of the spatial `2`-jets of the first `j` time derivatives of the
unknown (see `Submission.Work.Diff.STE.flat.TowerDefs`).  The recursion is

`towerExp Φ (j+2) p = ∑ i, (D_i H_{j+1})(base p) [J_{i+1}]`,

i.e. the chain rule for `∂_t (H_{j+1}(x, jets))` using `∂_t J_i = J_{i+1}`.

This file proves that `towerExp Φ j` is `C^∞` whenever `Φ` is.  The only non-trivial point is that
the recursion involves `fderiv` of the previous tower entry: the map
`z ↦ fderiv ℝ (fun y => F (z.1, y)) z.2` is smooth whenever `F` is (a "partial derivative"
smoothness statement, obtained from `ContDiff.fderiv` applied to the uncurried function).  The
induction is the two-step induction `Nat.twoStepInduction`, matching the two base cases `j = 0`
(the dummy value) and `j = 1` (`Φ` itself).
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped BigOperators

theorem towerExp_contDiff {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.flat.towerExp Φ j) := by
  induction j using Nat.twoStepInduction with
  | zero =>
    rw [show towerExp Φ 0 = fun _ : (Fin n → ℝ) × (Fin 0 → Jet n) => (0 : MatC n) from
      funext (fun p => towerExp_zero Φ p)]
    exact contDiff_const
  | one =>
    rw [show towerExp Φ 1 = fun p : (Fin n → ℝ) × (Fin 1 → Jet n) => Φ (p.1, p.2 0) from
      funext (fun p => towerExp_one Φ p)]
    fun_prop
  | more j ih ihs =>
    rw [show towerExp Φ (j + 2) = fun p : (Fin n → ℝ) × (Fin (j + 2) → Jet n) =>
        ∑ i : Fin (j + 1),
          (fderiv ℝ (fun Js : Fin (j + 1) → Jet n => towerExp Φ (j + 1) (p.1, Js))
            (fun i' : Fin (j + 1) => p.2 i'.castSucc))
            (Function.update (0 : Fin (j + 1) → Jet n) i (p.2 i.succ)) from
      funext (fun p => towerExp_succ_succ Φ j p)]
    refine ContDiff.sum (fun i _ => ?_)
    -- smoothness of the partial derivative of the previous tower entry
    have hL : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin n → ℝ) × (Fin (j + 2) → Jet n) =>
        fderiv ℝ (fun Js : Fin (j + 1) → Jet n => towerExp Φ (j + 1) (p.1, Js))
          (fun i' : Fin (j + 1) => p.2 i'.castSucc)) := by
      refine ContDiff.fderiv ?_ ?_ le_rfl
      · show ContDiff ℝ (⊤ : ℕ∞)
          (fun q : ((Fin n → ℝ) × (Fin (j + 2) → Jet n)) × (Fin (j + 1) → Jet n) =>
            towerExp Φ (j + 1) (q.1.1, q.2))
        fun_prop
      · fun_prop
    -- smoothness of the direction in which the derivative is evaluated
    have hu : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin n → ℝ) × (Fin (j + 2) → Jet n) =>
        Function.update (0 : Fin (j + 1) → Jet n) i (p.2 i.succ)) := by
      rw [contDiff_pi]
      intro a
      simp only [Function.update_apply]
      split_ifs with ha
      · fun_prop
      · simp only [Pi.zero_apply]
        fun_prop
    exact hL.clm_apply hu

end Work.Diff.STE.flat
