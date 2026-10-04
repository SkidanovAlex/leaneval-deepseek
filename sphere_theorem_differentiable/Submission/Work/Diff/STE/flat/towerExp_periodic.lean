import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Periodicity of the formal time-derivative tower

`Work.Diff.STE.flat.towerExp Φ j (x, Js)` is the `j`-th formal time derivative of the flat DeTurck
nonlinearity `Φ` along a solution (see `Submission/Work/Diff/STE/flat/TowerDefs.lean`), with the
recursion `H₁ = Φ` and

`H_{j+2}(x, J₀, …, J_{j+1}) = Σ_{i : Fin (j+1)} (D_i H_{j+1})(x, J₀, …, J_j) [J_{i+1}]`.

If `Φ` is invariant under a unit translation of the space variable in the `i`-th coordinate,
`Φ (x + eᵢ, w) = Φ (x, w)`, then so is every level of the tower.  This is the step that makes the
tower of the nonlinearity usable on the flat torus `ℝⁿ/ℤⁿ` (realised as `1`-periodic functions):
the nonlinearities of the tower are again `1`-periodic in each coordinate.

The proof is the obvious induction, carried out with `Nat.twoStepInduction` because the recursion
relates level `j + 2` to level `j + 1`: levels `0` and `1` are the base cases.  In the induction
step the two `(j+1)`-st towers appearing under the `fderiv` of `towerExp_succ_succ` are equal
*everywhere* by the induction hypothesis, hence have the same Fréchet derivative
(`Filter.EventuallyEq.fderiv_eq`).
-/

open Work.Diff.STE.Flat
open Filter
open scoped BigOperators Topology

namespace Work.Diff.STE.flat

theorem towerExp_periodic {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hper : ∀ (x : Fin n → ℝ) (w : Work.Diff.STE.Flat.Jet n) (i : Fin n),
      Φ (x + Pi.single i 1, w) = Φ (x, w)) :
    ∀ (j : ℕ) (x : Fin n → ℝ) (Js : Fin j → Work.Diff.STE.Flat.Jet n) (i : Fin n),
      Work.Diff.STE.flat.towerExp Φ j (x + Pi.single i 1, Js)
        = Work.Diff.STE.flat.towerExp Φ j (x, Js) := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero =>
      -- level `0` is the constant value `0`
      intro x Js i
      simp
  | one =>
      -- level `1` is `Φ` itself, so the hypothesis applies directly
      intro x Js i
      rw [towerExp_one, towerExp_one]
      exact hper x (Js 0) i
  | more k _ih1 ih2 =>
      -- level `k+2` only involves the `(k+1)`-st tower, which is periodic by `ih2`
      intro x Js i
      rw [towerExp_succ_succ (Φ := Φ) (j := k), towerExp_succ_succ (Φ := Φ) (j := k)]
      refine Finset.sum_congr rfl fun i₀ _ => ?_
      have hev : (fun Js' : Fin (k + 1) → Jet n => towerExp Φ (k + 1) (x + Pi.single i 1, Js'))
          =ᶠ[𝓝 (fun i' : Fin (k + 1) => Js i'.castSucc)]
          (fun Js' : Fin (k + 1) → Jet n => towerExp Φ (k + 1) (x, Js')) :=
        Filter.Eventually.of_forall fun Js' => ih2 x Js' i
      rw [hev.fderiv_eq]

end Work.Diff.STE.flat
