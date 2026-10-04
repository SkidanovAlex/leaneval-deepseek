import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! NOTE ON LOCATION.

The requested path of this lemma was `Submission/Work/Diff/EXT/Aux/norm_iteratedFDeriv_prod_le.lean`.
Lean 4.34 refuses to elaborate any file whose module name contains a component `Aux`
(`Lean/Elab/Import.lean`, `osForbiddenNames` contains `"AUX"`, compared case-insensitively):
`error: module name '...Aux...' is not portable: 'Aux' is a reserved file name on some operating systems`.
So the file was moved to the portable directory `Auxiliary/`. The *declaration name* is unchanged:
`Work.Diff.EXT.Aux.norm_iteratedFDeriv_prod_le`, and the namespace is kept as `Work.Diff.EXT.Aux`. -/

namespace Work.Diff.EXT.Aux

/-- Jet bound for a pair of functions: if `w` and `v` are `C^∞` at `x` and their `n`-th iterated Fréchet derivatives at `x` are bounded by `C`, then so is the `n`-th iterated Fréchet derivative of the pair `y ↦ (w y, v y)` at `x` (with bound `max C 0`).

Route: `iteratedFDeriv_prodMk` (Mathlib) gives `iteratedFDeriv ℝ n (fun y => (w y, v y)) x = (iteratedFDeriv ℝ n w x).prod (iteratedFDeriv ℝ n v x)`, and `ContinuousMultilinearMap.opNorm_prod` gives the norm of a product as `max` of the norms. -/
theorem norm_iteratedFDeriv_prod_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (w : E → J) (v : E → K) (x : E) (n : ℕ)
    (hw : ContDiffAt ℝ (⊤ : ℕ∞) w x) (hv : ContDiffAt ℝ (⊤ : ℕ∞) v x) {C : ℝ}
    (hC : ‖iteratedFDeriv ℝ n w x‖ ≤ C) (hC' : ‖iteratedFDeriv ℝ n v x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y : E => (w y, v y)) x‖ ≤ max C 0 := by
  rw [iteratedFDeriv_prodMk hw hv (by simp : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))]
  rw [ContinuousMultilinearMap.opNorm_prod]
  exact max_le (hC.trans (le_max_left _ _)) (hC'.trans (le_max_left _ _))

end Work.Diff.EXT.Aux
