import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.Gate
import Submission.Work.BoseBogFS.tauSm_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Numeric` — the two positivity rows of `BogNumeric`

`BogNumeric` (the numeric side conditions of FS `eq:BogIdentity`/`eq:BogIneq`) has two
rows that the §10 gate `Q3KernelFS` does **not** supply:

* `hA : 0 < 𝒜(k) = τ̃(k) + ρŴ₁(k)`,
* `hAB : 0 < 𝒜(k) + ℬ(k) = τ̃(k) + 2ρŴ₁(k)`.

They are strict, while the gate gives only `|ℬ| ≤ 𝒜` (hence `𝒜 ≥ 0`, `𝒜+ℬ ≥ 0`), and the
squeezing parametrisation would degenerate at `𝒜+ℬ = 0`.  At the honest datum they hold
because

* `τ̃ ≥ 0` everywhere (`tauSm_nonneg`) and `τ̃(k) = (1−ε_T)(‖k‖−(sℓ)⁻¹)² + (…)` is
  *large* above the threshold `(sℓ)⁻¹` (`tauSm_ge_sq`), so above
  `c₁ := (sℓ)⁻¹ + √(2ρw₁/(1−ε_T))` the term `τ̃(k)` alone beats `2ρw₁`;
* below `c₁`, `Ŵ₁` is bounded below by `w₀ > 0` (`chat_W1fun_pos_near_zero`-type input at
  the honest datum, i.e. FS's small-ball positivity of `Ŵ₁`), while `−w₁ ≤ Ŵ₁` everywhere
  (`W1hat_abs_le`).

This module carries the **arithmetic** that turns those two inputs into the two rows
(`tauSm_gt_c₁`) and the single entry point `bogNumeric_of_honest` that a consumer calls.
The two `Ŵ₁` inputs are hypotheses in exactly the shape the honest view supplies (see
`README.md` §5.1 and `View.lean`).
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **The high-band row of the positivity input.**  If `τ̃` dominates the square
`(1−ε_T)(‖k‖−(sℓ)⁻¹)²` above the kinetic threshold (the content of `tauSm_ge_sq`), then
above `c₁ := (sℓ)⁻¹ + √(2ρw₁/(1−ε_T))` it dominates the constant `2ρw₁`. -/
theorem tauSm_gt_c₁ (F : FockData Mode) (E : Q3Env Mode) (ρ c₁ w₁ : ℝ)
    (hε1 : E.eT < 1) (hρ : 0 ≤ ρ) (hw₁ : 0 ≤ w₁)
    (hge : ∀ k : Mode, (E.s * E.ell)⁻¹ ≤ ‖F.kmom k‖ →
      (1 - E.eT) * (‖F.kmom k‖ - (E.s * E.ell)⁻¹) ^ 2 ≤ E.tau k)
    (hc₁ : c₁ = (E.s * E.ell)⁻¹ + Real.sqrt (2 * ρ * w₁ / (1 - E.eT))) :
    ∀ k : Mode, c₁ < ‖F.kmom k‖ → 2 * ρ * w₁ < E.tau k := by
  intro k hk
  have h1ε : 0 < 1 - E.eT := by linarith
  set m : ℝ := 2 * ρ * w₁ / (1 - E.eT) with hmdef
  have hm : 0 ≤ m := by
    rw [hmdef]
    exact div_nonneg (mul_nonneg (by linarith) hw₁) h1ε.le
  set s : ℝ := Real.sqrt m with hsdef
  have hs2 : s ^ 2 = m := by rw [hsdef]; exact Real.sq_sqrt hm
  have hsnn : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg m
  set dd : ℝ := ‖F.kmom k‖ - (E.s * E.ell)⁻¹ with hddef
  have hlt : s < dd := by linarith [hk, hc₁, hddef]
  have hdd : 0 < dd := lt_of_le_of_lt hsnn hlt
  have hsq : s * s < dd * dd := by nlinarith [hlt, hsnn, hdd]
  have hmul : (1 - E.eT) * (s * s) < (1 - E.eT) * (dd * dd) :=
    mul_lt_mul_of_pos_left hsq h1ε
  have hs2' : (1 - E.eT) * (s * s) = 2 * ρ * w₁ := by
    rw [show s * s = s ^ 2 by ring, hs2, hmdef]
    field_simp
  have hd2 : (1 - E.eT) * (dd * dd) = (1 - E.eT) * dd ^ 2 := by ring
  have hfin : (1 - E.eT) * dd ^ 2 ≤ E.tau k := by
    have h := hge k (by linarith [hsnn, hc₁, hk])
    rw [← hddef] at h
    exact h
  linarith [hmul, hs2', hd2, hfin]

/-- **The two positivity rows from the honest inputs.**  `τ̃ ≥ 0` and the quantitative
high-band bound `tauSm_gt_c₁` give both rows through `bogA_pos_and_add_pos`, with the two
`Ŵ₁` inputs `−w₁ ≤ Ŵ₁` (everywhere) and `w₀ ≤ Ŵ₁` (below `c₁`). -/
theorem bogA_pos_of_honest (F : FockData Mode) (E : Q3Env Mode) (ρ c₁ w₀ w₁ : ℝ)
    (hε1 : E.eT < 1) (hρ : 0 < ρ) (hw₀ : 0 < w₀) (hw₁ : 0 ≤ w₁)
    (htau0 : ∀ k : Mode, 0 ≤ E.tau k)
    (hge : ∀ k : Mode, (E.s * E.ell)⁻¹ ≤ ‖F.kmom k‖ →
      (1 - E.eT) * (‖F.kmom k‖ - (E.s * E.ell)⁻¹) ^ 2 ≤ E.tau k)
    (hc₁ : c₁ = (E.s * E.ell)⁻¹ + Real.sqrt (2 * ρ * w₁ / (1 - E.eT)))
    (hWlo : ∀ k : Mode, -w₁ ≤ E.W1 k)
    (hW : ∀ k : Mode, ‖F.kmom k‖ ≤ c₁ → w₀ ≤ E.W1 k) :
    (∀ k : Mode, 0 < bogA E ρ k) ∧ (∀ k : Mode, 0 < bogA E ρ k + bogB E ρ k) :=
  bogA_pos_and_add_pos F E ρ c₁ w₀ w₁ hρ hw₀ hw₁ htau0
    (tauSm_gt_c₁ F E ρ c₁ w₁ hε1 hρ.le hw₁ hge hc₁) hWlo hW

/-- **`BogNumeric` at the honest datum.**  The gate supplies every row but the two
positivity rows; those come from `bogA_pos_of_honest`. -/
theorem bogNumeric_of_honest (F : FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Q3Env Mode) (ρ c₁ w₀ w₁ K₀ : ℝ)
    (hgate : Q3KernelFS K₀ F T (Work.BoseFixR.KzEnvAt E ρ))
    (hε1 : E.eT < 1) (hρ : 0 < ρ) (hw₀ : 0 < w₀) (hw₁ : 0 ≤ w₁)
    (htau0 : ∀ k : Mode, 0 ≤ E.tau k)
    (hge : ∀ k : Mode, (E.s * E.ell)⁻¹ ≤ ‖F.kmom k‖ →
      (1 - E.eT) * (‖F.kmom k‖ - (E.s * E.ell)⁻¹) ^ 2 ≤ E.tau k)
    (hc₁ : c₁ = (E.s * E.ell)⁻¹ + Real.sqrt (2 * ρ * w₁ / (1 - E.eT)))
    (hWlo : ∀ k : Mode, -w₁ ≤ E.W1 k)
    (hW : ∀ k : Mode, ‖F.kmom k‖ ≤ c₁ → w₀ ≤ E.W1 k) :
    BogNumeric F E ρ := by
  obtain ⟨hA, hAB⟩ := bogA_pos_of_honest F E ρ c₁ w₀ w₁ hε1 hρ hw₀ hw₁ htau0 hge hc₁ hWlo hW
  exact BogNumeric.of_gate F T E ρ hgate hA hAB

end Work.BoseBogFS
