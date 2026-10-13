/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `D_z F_*` package: the radial factor `Hz` and its weighted bound `HB`

This is the shared vocabulary for the design statement `DzFstar_W` of
`FTS/N45_DESIGN_LEAD.md` §3.2 (the `D_z F_*` row of the `F_*`-package), proved in
`Submission/Work/FTS/Nonlinear/FstarPkg/DzFstar_W.lean`.

## Mathematics

`Work.Construction.Dz_Fstar_eq` computes the radial derivative of the fundamental profile:
for `z > -1`

  `D_z F_*(z,θ) = α · (Γ(θ)/c(α)) · H(z)`,   `H(z) = 2z(1-z)/(1+z)³`.

So `D_z F_*` is again a product `(angular factor) · (radial factor)`, exactly as
`F_* = (2α/c) Γ(θ) · z/(1+z)²` is, and the `𝒲^{4,∞}`-norm of `D_z F_*` is controlled by
the weighted derivatives `(z+1)^k H^{(k)}(z)`, `z ≥ 0`.

On `(-1,∞)` the radial factor is `H = 2 · (id · h')` with `h(z) = z/(1+z)²`, whose
iterated derivatives are known in closed form (`Work.Spaces.iter_deriv_hKerClosed`), so
`(z+1)^k H^{(k)}(z)` is bounded *uniformly in `k`* by an explicit sequence `HB k`; this
is proved in `Submission/Work/FTS/Nonlinear/FstarPkg/Hz_deriv_bound.lean`.

The exponent chosen for the angular weight is the same as in `F_*`
(`sin(2θ)^{-α/5}/(α + sin 2θ)`), so the generic `Γ ⊗ H` estimate
(`Submission/Work/FTS/Nonlinear/FstarPkg/WlInf_Gamma_radial.lean`) applies verbatim.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.NormNum.NatFactorial
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Spaces.pzIter_hKer_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-- The radial factor `H(z) = 2z(1-z)/(1+z)³` of `D_z F_*`:
`D_z F_*(z,θ) = α · (Γ(θ)/c(α)) · H(z)` for `z > -1` (the value at `z ≤ -1` is irrelevant,
only `z ≥ 0` is ever used). -/
noncomputable def Hz (z : ℝ) : ℝ := 2 * z * (1 - z) / (1 + z) ^ 3

/-- The universal weighted bound for the radial factor of `D_z F_*`:
`|(z+1)^k H^{(k)}(z)| ≤ HB k` for all `z ≥ 0`.  The constant comes from
`pzIter_hKer_bound` at the orders `k` and `k+1`:
`HB k = 2 · ((k+1)!(k+2) + k·k!(k+1))`. -/
noncomputable def HB (k : ℕ) : ℝ :=
  2 * (((k + 1).factorial : ℝ) * (k + 2) + (k : ℝ) * ((k.factorial : ℝ) * (k + 1)))

lemma HB_nonneg (k : ℕ) : 0 ≤ HB k := by
  rw [HB]; positivity

/-- On `z > -1` the radial factor of `D_z F_*` is `2 · z · h'(z)` for `h = hKer`; this is
the form in which its iterated derivatives are computed from the closed form
`Work.Spaces.iter_deriv_hKerClosed`. -/
lemma Hz_eq_mul_deriv {z : ℝ} (hz : -1 < z) :
    Hz z = 2 * (z * deriv Work.Spaces.hKer z) := by
  have hderiv : deriv Work.Spaces.hKer z = (1 - z) / (1 + z) ^ 3 := by
    have h := Work.Spaces.iter_deriv_hKerClosed 1 z hz
    simp only [Function.iterate_one] at h
    rw [show Work.Spaces.hKer = (fun z : ℝ => z / (1 + z) ^ 2) from rfl]
    rw [h, Work.Spaces.hKerClosed]
    norm_num
    field_simp
    ring
  rw [Hz, hderiv]
  field_simp

end Work.FTS.Nonlinear.FstarPkg
