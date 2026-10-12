import ChallengeDeps
import Submission.Work.BoseBogFS.BogFSCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.phiC_defs` — the clean bracket as a function of `(τ, c, ‖k‖)`

The scaled clean summand (`Work.BoseBogFS.psiSc`) is

  `psiSc t = 𝒵(τ_s(t) + c_s(t), c_s(t)) − c_s(t)²/(2‖t‖²)`,

and on the honest range (`τ_s ≥ 0`, `c_s ≥ 0`) the algebraic identity
`𝒵(A,B) = B²/(A+√(A²−B²))` turns it into the three-variable function

  `phiC u v r = v²/(u+v+√(u²+2uv)) − v²/(2r²)`,   `(u,v,r) = (τ_s, c_s, ‖t‖)`.

This module only *fixes the vocabulary*: the definition `phiC` and the identity
`psiSc_eq_phiC`.  Its purpose is to isolate the pure real-variable calculus of `phiC`
(`∂/∂u phiC < 0`, `∂/∂r phiC > 0`, the derivative bounds, the per-cell increment bound)
from the measure theory of the cell tiling.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The clean bracket as a function of `(u,v,r)`**: with `u = τ_s`, `v = c_s`,
`r = ‖t‖`,

  `phiC u v r = v²/(u+v+√(u²+2uv)) − v²/(2r²)`.

On `u ≥ 0`, `v ≥ 0` this is `𝒵(u+v,v) − v²/(2r²)` (`Work.BoseBogFS.psiSc` in scaled
variables). -/
def phiC (u v r : ℝ) : ℝ :=
  v ^ 2 / (u + v + Real.sqrt (u ^ 2 + 2 * u * v)) - v ^ 2 / (2 * r ^ 2)

/-- The denominator `S(u,v) = u+v+√(u²+2uv)`. -/
def phiS (u v : ℝ) : ℝ := u + v + Real.sqrt (u ^ 2 + 2 * u * v)

lemma phiC_eq (u v r : ℝ) : phiC u v r = v ^ 2 / phiS u v - v ^ 2 / (2 * r ^ 2) := rfl

/-- **The scaled clean bracket is `phiC`.**  On the honest range (`0 ≤ τ_s`, `0 ≤ c_s`) the
zero point rewrites as `c_s²/S`, so the scaled clean summand is `phiC` at
`(τ_s, c_s, ‖t‖)`. -/
theorem psiSc_eq_phiC {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {ρ μ : ℝ} {t : E3}
    (hP : 0 < ρ * a v)
    (hτ : 0 ≤ tauSc v ρ μ t) (hc : 0 ≤ betaSc v h ρ μ t) :
    psiSc v h ρ μ t = phiC (tauSc v ρ μ t) (betaSc v h ρ μ t) ‖t‖ := by
  set u := tauSc v ρ μ t with hu
  set b := betaSc v h ρ μ t with hb
  have hsq : 0 ≤ u ^ 2 + 2 * u * b := by positivity
  have key : (u + b) - Real.sqrt (u ^ 2 + 2 * u * b)
      = b ^ 2 / ((u + b) + Real.sqrt (u ^ 2 + 2 * u * b)) := by
    by_cases hden : (u + b) + Real.sqrt (u ^ 2 + 2 * u * b) = 0
    · have h1 := Real.sqrt_nonneg (u ^ 2 + 2 * u * b)
      have hub : u + b = 0 := by linarith
      have hs0 : Real.sqrt (u ^ 2 + 2 * u * b) = 0 := by linarith
      have hu0 : u = 0 := by linarith
      have hb0 : b = 0 := by linarith
      rw [hu0, hb0]
      have harg : (0 : ℝ) ^ 2 + 2 * 0 * 0 = 0 := by norm_num
      rw [harg, Real.sqrt_zero]
      norm_num
    · rw [eq_div_iff hden]
      have h3 : Real.sqrt (u ^ 2 + 2 * u * b) ^ 2 = u ^ 2 + 2 * u * b := Real.sq_sqrt hsq
      nlinarith [h3]
  have hmain : tauSc v ρ μ t + betaSc v h ρ μ t
        - Real.sqrt ((tauSc v ρ μ t + betaSc v h ρ μ t) ^ 2 - betaSc v h ρ μ t ^ 2)
      = betaSc v h ρ μ t ^ 2 / (tauSc v ρ μ t + betaSc v h ρ μ t
          + Real.sqrt (tauSc v ρ μ t ^ 2 + 2 * tauSc v ρ μ t * betaSc v h ρ μ t)) := by
    rw [← hu, ← hb]
    rw [show (u + b) ^ 2 - b ^ 2 = u ^ 2 + 2 * u * b by ring]
    exact key
  rw [psiSc, Work.BoseB6.bogZeroPoint, phiC, hmain]

/-! ## The `phiZ` formulation (definitionally the scaled clean bracket) -/

/-- **The clean bracket from the raw pair `(A,B)`**: `A = τ_s + c_s`, `B = c_s`.  This is
`bogZeroPoint A B − B²/(2r²)` *by definition*, so `psiSc = phiZ (τ_s+c_s) c_s ‖t‖` holds by
`rfl` — no sign hypothesis is needed for the identity itself. -/
def phiZ (A B r : ℝ) : ℝ := A - Real.sqrt (A ^ 2 - B ^ 2) - B ^ 2 / (2 * r ^ 2)

lemma phiZ_eq_bogZeroPoint (A B r : ℝ) :
    phiZ A B r = Work.BoseB6.bogZeroPoint A B - B ^ 2 / (2 * r ^ 2) := rfl

/-- **`psiSc` is `phiZ` at the raw pair.** -/
theorem psiSc_eq_phiZ {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {ρ μ : ℝ} {t : E3} :
    psiSc v h ρ μ t
      = phiZ (tauSc v ρ μ t + betaSc v h ρ μ t) (betaSc v h ρ μ t) ‖t‖ := rfl

end Work.BoseBogFS
