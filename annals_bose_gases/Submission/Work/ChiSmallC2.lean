import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.ConvQuadDev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A2 — `chiSmall M` is `C²` with compact support (`3 ≤ M`)

The second stage of `conv3Small_quadratic_dev`: the small-box bump
`χ_M(z) = C_M·(ζ(z₀)ζ(z₁)ζ(z₂))^M` (`ChiSmall.chiSmall`,
`C_M = 1/√∫(base)²`) is `C²` on `ℝ³`, with compact support already
established (`ChiSmall.chiSmall_hasCompactSupport`).

Ingredients: the 1D `zeta1d^M` is `C²` for `3 ≤ M` (`zeta1d_pow_contDiff_two`,
module `ConvQuadDev`); each coordinate factor `z ↦ ζ(z_j)^M` is the
composition of that with the (smooth, continuous-linear) coordinate
projection `coordCLM j`; the three factors multiply via `ContDiff.mul` (and
`(ζ₀ζ₁ζ₂)^M = ζ₀^M ζ₁^M ζ₂^M` by `mul_pow`); dividing by the constant
`√(chiSmallNormSq M)` is multiplication by a constant.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Real Topology ContDiff
namespace Submission
set_option autoImplicit false
set_option linter.unusedVariables false
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the `j`-th coordinate of `ℝ³` as a continuous linear functional. -/
noncomputable def coordCLM (j : Fin 3) : ℝ³ →L[ℝ] ℝ :=
  { toFun := fun z => z.ofLp j
    map_add' := by intro a b; rfl
    map_smul' := by intro c a; rfl
    cont := by fun_prop }

/-- **each coordinate factor `z ↦ ζ(z_j)^M` is `C²`** (`3 ≤ M`): the
composition of the 1D `zeta1d^M` (`zeta1d_pow_contDiff_two`) with the
smooth coordinate projection. -/
lemma coord_zeta1d_pow_contDiff_two {M : ℕ} (hM : 3 ≤ M) (j : Fin 3) :
    ContDiff ℝ 2 (fun z : ℝ³ => zeta1d (z.ofLp j) ^ M) := by
  have h1 : ContDiff ℝ 2 (fun y : ℝ => zeta1d y ^ M) := zeta1d_pow_contDiff_two hM
  have h2 : ContDiff ℝ 2 (fun z : ℝ³ => z.ofLp j) :=
    (ContinuousLinearMap.contDiff (coordCLM j) : ContDiff ℝ 2 ⇑(coordCLM j))
  simpa [coordCLM, Function.comp_def] using h1.comp h2

/-- **`chiSmallBase M` is `C²`** (`3 ≤ M`): the pointwise identity
`(ζ₀ζ₁ζ₂)^M = ζ₀^M ζ₁^M ζ₂^M` (`mul_pow`) and the product of the three
`C²` coordinate factors. -/
lemma chiSmallBase_contDiff_two {M : ℕ} (hM : 3 ≤ M) :
    ContDiff ℝ 2 (chiSmallBase M) := by
  have hfac : ∀ j : Fin 3, ContDiff ℝ 2 (fun z : ℝ³ => zeta1d (z.ofLp j) ^ M) :=
    fun j => coord_zeta1d_pow_contDiff_two hM j
  have hprod : ContDiff ℝ 2 (fun z : ℝ³ =>
      zeta1d (z.ofLp 0) ^ M * zeta1d (z.ofLp 1) ^ M * zeta1d (z.ofLp 2) ^ M) :=
    ((hfac 0).mul (hfac 1)).mul (hfac 2)
  have heq : chiSmallBase M = fun z : ℝ³ =>
      zeta1d (z.ofLp 0) ^ M * zeta1d (z.ofLp 1) ^ M * zeta1d (z.ofLp 2) ^ M := by
    funext z
    dsimp [chiSmallBase]
    rw [mul_pow, mul_pow]
  rwa [heq]

/-- **`chiSmall M` is `C²`** (`3 ≤ M`): `chiSmall = chiSmallBase / √(normSq)`,
i.e. the `C²` base times the constant `(√(chiSmallNormSq M))⁻¹`. -/
lemma chiSmall_contDiff_two {M : ℕ} (hM : 3 ≤ M) : ContDiff ℝ 2 (chiSmall M) := by
  have hbase := chiSmallBase_contDiff_two hM
  have hconst : ContDiff ℝ 2 (fun _ : ℝ³ => (Real.sqrt (chiSmallNormSq M))⁻¹) := contDiff_const
  have heq : chiSmall M = fun z : ℝ³ => chiSmallBase M z * (Real.sqrt (chiSmallNormSq M))⁻¹ := by
    funext z
    dsimp [chiSmall]
    rw [div_eq_mul_inv]
  rw [heq]
  exact hbase.mul hconst

/-- **A2: `chiSmall M` is `C²` with compact support** (`3 ≤ M`) — the
smooth-compact bump needed for the convolution-smoothness stage (A3). -/
lemma chiSmall_contDiff_two_hasCompactSupport {M : ℕ} (hM : 3 ≤ M) :
    ContDiff ℝ 2 (chiSmall M) ∧ HasCompactSupport (chiSmall M) :=
  ⟨chiSmall_contDiff_two hM, chiSmall_hasCompactSupport (by omega)⟩

end BoseGases
end Submission
