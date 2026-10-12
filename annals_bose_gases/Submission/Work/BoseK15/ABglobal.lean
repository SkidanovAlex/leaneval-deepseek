import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.A_ge_and_AB_of_taurad
import Submission.Work.BoseK15.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.ABglobal` — the **global** `|ℬ| ≤ 𝒜` row

FS `eq:BoverA` is proved on the high-momentum region (`|k| ≥ ½K_H⁻¹a⁻¹`), which is
the form `Work.BoseK15.A_ge_and_AB_of_taurad` records.  The §10 chain, however,
consumes the *global* row `|ℬ_k| ≤ 𝒜_k` for all `k`: `Work.BoseB7A.Assembly` uses
it (`hK.AB`) to build `∀ i, 0 ≤ E.D i` and to enlarge the kinetic reserve from
`P_H^q` to `fun _ => True` (`Work.BoseB7.FockData.dNumOpR_mono`).

The global row does hold at the honest instance, and this module proves it from
two honest rows:

* `𝒜 = τ + ρ_zŴ₁`, `ℬ = ρ_zŴ₁` (`eq:BogHamPositive-1`), so on the modes where
  `Ŵ₁ ≥ 0` we have `|ℬ| = ℬ ≤ 𝒜` as soon as `τ ≥ 0`;
* `τ ≥ 0` is `def:tau` (`τ` is a nonnegative combination of squares when
  `0 ≤ ε_T ≤ 1`);
* outside `P_H^q` the momentum is below `¼K_H⁻¹a⁻¹`, which is exactly FS's
  low-momentum region where `Ŵ₁` is positive (FS's `eq:BoverA` proof: on
  `|k| ≤ (2d𝓁)⁻¹` one has `𝒜 + ℬ ≥ 2ρ_zŴ₁(0)(1 − C(μa³)R²/a²)`), recorded here as
  the row `hW1low`.

So the *single* extra honest row `hW1low` restores the global `AB` row that §10
needs, and the guarded kernel interface (`Work.BoseK15.GuardedKernel`) keeps the
design's global `AB`.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The global `|ℬ| ≤ 𝒜`.**  From the `P_H^q` row (FS `eq:BoverA`), the
low-momentum positivity of `Ŵ₁`, `0 ≤ ε_T ≤ 1` and `ρ_z ≥ 0`. -/
theorem AB_global {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {K₀ : ℝ} (h : K15Input K₀ F T E)
    (hABq : ∀ k : Mode, F.PHq E.KH E.aScat k → 2 * |E.B k| ≤ E.A k)
    (hW1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k)
    (heT0 : 0 ≤ E.eT) (heT1 : E.eT ≤ 1) :
    ∀ k : Mode, |E.B k| ≤ E.A k := by
  have hρ : 0 ≤ E.rho := by
    show 0 ≤ E.z ^ 2 / E.ell ^ 3
    have hℓ : 0 < E.ell := h.ell_pos_E
    positivity
  intro k
  by_cases hk : F.PHq E.KH E.aScat k
  · have h2 := hABq k hk
    have h3 : 0 ≤ |E.B k| := abs_nonneg _
    linarith
  · have hk' : ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) := le_of_lt (not_le.mp hk)
    have hW : 0 ≤ E.W1 k := hW1low k hk'
    have hτ : 0 ≤ E.tau k := by
      rw [h.tau_eq k, Work.BoseB4.tauFun]
      have h1 : 0 ≤ 1 - E.eT := by linarith
      have h2 : 0 ≤ max (‖F.kmom k‖ - (2 * E.s * E.ell)⁻¹) 0 := le_max_right _ _
      have h3 : 0 ≤ max (‖F.kmom k‖ - (2 * E.d * E.s * E.ell)⁻¹) 0 := le_max_right _ _
      exact add_nonneg (mul_nonneg h1 (sq_nonneg _)) (mul_nonneg heT0 (sq_nonneg _))
    have hA : E.A k = E.tau k + E.rho * E.W1 k := h.A_eq k
    have hB : E.B k = E.rho * E.W1 k := h.B_eq k
    have hBnn : 0 ≤ E.B k := by rw [hB]; exact mul_nonneg hρ hW
    have h1 : |E.B k| = E.B k := abs_of_nonneg hBnn
    rw [h1, hA, hB]
    linarith

end Work.BoseK15
