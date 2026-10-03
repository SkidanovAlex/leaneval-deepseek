import Mathlib
import Submission.Work.Peluse.UControl.PetStepChain

/-!
# The tower of PET windows

Each PET step introduces one new window parameter `h ∈ [-H,H]`, and `PetState.step` models it by
`Ω ↦ Ω × Fin (2*H+1)`.  `WinTower H n` is the resulting parameter type after `n` steps (starting
from the trivial parameter set `Fin 1` of `LambdaMDPetState`), so that a chain of `n` concrete PET
steps has parameter type *literally* `WinTower H n` — no reindexing is needed along the chain.

* `WinTower.nu H n a` is the weight of the tower point `a`: the product of the window weights
  `muL H (winVal H k_j)`, i.e. exactly the `ν` of the states built by `PetState.step`;
* `WinTower.param H n a : Fin n → ℤ` is the corresponding parameter of the *symbolic* state
  `PetStateSym n` (whose `j`-th coefficient ring variable is the `j`-th window position); the two
  compatibility lemmas `param_last`/`param_castSucc` are exactly what is needed to see that
  `PetStateSym.step` (which renames `Fin n → Fin (n+1)` along `Fin.castSucc` and introduces
  `MvPolynomial.X (Fin.last n)`) evaluates to the concrete `PetState.step` (which shifts the `y`
  argument by the new window position).

`Σ_a WinTower.nu H n a = 1` (and the nonnegativity) is delegated as `petWinTowerSumNu`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

/-- The tower of `n` windows `Fin (2H+1)`, matching the parameter shape of `PetState.step`. -/
def WinTower (H : ℕ) : ℕ → Type
  | 0 => Fin 1
  | (n + 1) => WinTower H n × Fin (2 * H + 1)

instance (H n : ℕ) : Fintype (WinTower H n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 1))
  | succ n ih =>
    haveI : Fintype (WinTower H n) := ih
    exact inferInstanceAs (Fintype (WinTower H n × Fin (2 * H + 1)))

instance (H n : ℕ) : DecidableEq (WinTower H n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq (Fin 1))
  | succ n ih =>
    haveI : DecidableEq (WinTower H n) := ih
    exact inferInstanceAs (DecidableEq (WinTower H n × Fin (2 * H + 1)))

/-- The weight of a tower point: the product of the window weights. -/
noncomputable def WinTower.nu (H : ℕ) : ∀ n, WinTower H n → ℝ
  | 0, _ => 1
  | (n + 1), a => WinTower.nu H n a.1 * Work.Peluse.muL H (PetStep.winVal H a.2)

/-- The parameter of the symbolic state `PetStateSym n` attached to a point of the tower: the first
`n` window positions. -/
def WinTower.param (H : ℕ) : ∀ n, WinTower H n → Fin n → ℤ
  | 0, _, j => j.elim0
  | (n + 1), a, j => Fin.lastCases (PetStep.winVal H a.2)
      (fun i => WinTower.param H n a.1 i) j

lemma WinTower.param_last (H n : ℕ) (a : WinTower H n) (k : Fin (2 * H + 1)) :
    WinTower.param H (n + 1) (a, k) (Fin.last n) = PetStep.winVal H k := by
  simp [WinTower.param]

lemma WinTower.param_castSucc (H n : ℕ) (a : WinTower H n) (k : Fin (2 * H + 1)) (i : Fin n) :
    WinTower.param H (n + 1) (a, k) (Fin.castSucc i) = WinTower.param H n a i := by
  simp [WinTower.param]

end

end Work.Peluse.UControl
