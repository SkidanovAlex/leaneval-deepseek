import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## The one-variable operators -/

/-- The one-variable operator `z ↦ z · ψ'(z)`. -/
noncomputable def vz (ψ : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv ψ z

/-- The `j`-fold iterate of `vz`. -/
noncomputable def vzIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, ψ => ψ
  | k + 1, ψ => vz (vzIter k ψ)

/-- The one-variable operator `θ ↦ sin(2θ) · h'(θ)`. -/
noncomputable def vth (g : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv g θ

/-- The `i`-fold iterate of `vth`. -/
noncomputable def vthIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, g => g
  | i + 1, g => vth (vthIter i g)

@[simp] theorem vzIter_zero (ψ : ℝ → ℝ) : vzIter 0 ψ = ψ := rfl
@[simp] theorem vzIter_succ (k : ℕ) (ψ : ℝ → ℝ) : vzIter (k + 1) ψ = vz (vzIter k ψ) := rfl
@[simp] theorem vthIter_zero (g : ℝ → ℝ) : vthIter 0 g = g := rfl
@[simp] theorem vthIter_succ (i : ℕ) (g : ℝ → ℝ) : vthIter (i + 1) g = vth (vthIter i g) := rfl



/-! ## The two slot integrals -/

/-- The radial slot `Z_j = ∫_z (D_z^j ψ · w)^2`. -/
noncomputable def Zc (ψ : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (vzIter j ψ z * Work.Spaces.w z) ^ 2

/-- The angular slot `S^i_q = ∫_θ (D_θ^i h)^2 · sin(2θ)^{-q}`. -/
noncomputable def Sc (g : ℝ → ℝ) (i : ℕ) (q : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (vthIter i g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)

/-! ## The concrete bumps and the ansatz -/

/-- The angular centre `θ₀ = 1/2` of the counterexample. -/
def th0 : ℝ := 1 / 2

/-- The radial bump `ψ(z) = χ(z - 5/2)`, supported in `(1/2, 9/2)`. -/
noncomputable def psiA : ℝ → ℝ := fun z => Work.Stability.chi (z - 5 / 2)

/-- The angular bump `h_δ(θ) = χ((θ - θ₀)/δ)`, supported in `(θ₀ - 2δ, θ₀ + 2δ)`. -/
noncomputable def hA (δ : ℝ) : ℝ → ℝ := fun θ => Work.Stability.chi ((θ - th0) / δ)

/-- **THE COUNTEREXAMPLE**: `f_δ(z,θ) = ψ(z)·h_δ(θ)`. -/
noncomputable def ansatz (δ : ℝ) : ℝ → ℝ → ℝ := fun z θ => psiA z * hA δ θ

@[simp] theorem psiA_apply (z : ℝ) : psiA z = Work.Stability.chi (z - 5 / 2) := rfl
@[simp] theorem hA_apply (δ θ : ℝ) : hA δ θ = Work.Stability.chi ((θ - th0) / δ) := rfl
@[simp] theorem ansatz_apply (δ z θ : ℝ) : ansatz δ z θ = psiA z * hA δ θ := rfl

/-! ## The pure and mixed parts of the `ℋ^k`-integrand

Splitting `Work.Spaces.HkIntegrand` into its radial part (`Pure`) and its genuinely mixed
part (`Mixed`) is what makes the level shift `n ↦ n+1` transparent: `Mixed` is shifted by
one under `D_θ` (this is `Mixed_succ`), while `Pure` simply grows by the top slot. -/




end Work.FTS.CoercivityFix.Assembly
