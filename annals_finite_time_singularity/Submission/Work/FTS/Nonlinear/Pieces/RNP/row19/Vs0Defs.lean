/-
# Row 19 — the split of `V(Φ̃_*)(0,·) · D_zF_*` into an angular profile times a radial profile

The lemma `Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_Vs0_mul_Gs_eq_zero` is about the function

  `f(z,θ) = V(Φ̃_*)(0,θ) · D_zF_*(z,θ)`,   `Vs0 α Φs θ = Vs α Φs 0 θ`,  `Gs α = D_z(F_*)`,

i.e. the `z = 0` slice of the coefficient `V(Φ̃_*)` times the radial derivative of the profile.

The key structural fact (proved here, from `Work.Construction.Dz_Fstar_eq`) is that this is a
*factorised* function on the domain:

  `f(z,θ) = U(θ) · prof(z)`,

with the **angular factor** `Ufun α Φs θ = Vs0 α Φs θ · (α Γ(α,θ)/c α)` and the **radial
factor** `prof(z) = 2z(1−z)/(1+z)³`.  This is what makes every mixed derivative factorise as
well (`D_z^j D_θ^i f = (D_z^j prof) · (D_θ^i U)`, see `factor_prod_prof`), which is the form in
which the pointwise estimates of the row become tractable: the `z`-part is an explicit rational
function and the `θ`-part involves only the `θ`-derivatives of `V` (controlled by `StarPkg.V`)
and of `Γ` (explicit).

All constants are of the form `K · max Cs 0 · α`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split
import Submission.Work.Construction.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The **radial profile** `2z(1−z)/(1+z)³` of `D_zF_*/(αΓ/c)`. -/
abbrev prof (z : ℝ) : ℝ := 2 * z * (1 - z) / (1 + z) ^ 3

/-- The radial profile as a function of the two self-similar variables (constant in `θ`). -/
abbrev proff : ℝ → ℝ → ℝ := fun z _ => 2 * z * (1 - z) / (1 + z) ^ 3

/-- The **angular factor** `V(Φ̃_*)(0,θ)·αΓ(α,θ)/c α` of the row-19 coefficient. -/
abbrev Ufun (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ :=
  fun θ => Vs0 α Φs θ * (α * Work.Spaces.Gam α θ / Work.Spaces.c α)

/-- `D_zF_*(z,θ) = (αΓ(θ)/c)·prof(z)` for `z > -1`. -/
theorem Gs_eq_prof {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hz : -1 < z) :
    Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ
      = (α * Work.Spaces.Gam α θ / Work.Spaces.c α) * prof z := by
  rw [Work.FTS.Nonlinear.Pieces.RNP.Gs, Work.Construction.Dz_Fstar_eq hα hz, prof]
  ring

/-- **The factorisation of the row-19 coefficient**: `Vs0(θ)·D_zF_*(z,θ) = prof(z)·Ufun(θ)`
for `z > -1`. -/
theorem Vs0_mul_Gs_eq_prof {α : ℝ} (hα : 0 < α) (Φs : Work.FTS.Galerkin.Fn) {z θ : ℝ}
    (hz : -1 < z) :
    Vs0 α Φs θ * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ = prof z * Ufun α Φs θ := by
  rw [Gs_eq_prof hα hz, Ufun]
  ring

end Work.FTS.Nonlinear.Pieces.RNP.row19
