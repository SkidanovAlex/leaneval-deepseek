import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.BoxCountBand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.diluteAux` — the `τ`-identity in a *minimal* import cone

The dilute band arm (`Submission/Work/BoseB1Cube/cubeDiluteArm.lean`) needs the ledger identity

    `flatScountB / chiMass = flatTau · ‖Φ‖²`   (`flatScountB_div_eq_flatTau_mul_normB`)

which lives in `Submission/Work/BoseB1Cube/flatZeroAux.lean`.  That module's import cone however
contains **both** `Work.BoseFixB1S.boxConstCalibB1` and `Work.BoseFixB1S.boxPairValue`, which
declare `Work.BoseFixB1S.pairMass_eq_setIntegral` twice — a duplicate-declaration landmine that
makes the two modules impossible to import together.  The dilute arm also imports the (large)
`flatFibDeviationB1` family, whose cone already contains `boxConstCalibB1`, so importing
`flatZeroAux` on top breaks the build.

This module re-proves the identity in a cone whose only content is `perBoxF_flat` (the
definitions) and `normB`.  The proofs are copied verbatim from `flatZeroAux.lean` §4.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube.DiluteAux

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A continuous function is integrable on the box `abox n ℓ`. -/
theorem integrableOn_abox_local {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F : Submission.BoseGases.X n → ℝ} (hF : Continuous F) :
    IntegrableOn F (Submission.BoseGases.abox n ℓ) :=
  ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ) hF.continuousOn

/-- `flatMass (sideAt μ (a v)) Φ` **is** the corpus `normB`. -/
theorem flatMass_eq_normB {v : E3 → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseFixB1.flatMass (sideAt μ (a v)) Φ = normB v μ n Φ := rfl

/-- A state of zero mass on the box has zero flat count (the integrand carries `Φ²`). -/
theorem flatScountB_eq_zero_of_flatMass_eq_zero {M : ℕ} {ℓ d : ℝ} {u : E3} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < ℓ) (hΦc : Continuous Φ)
    (hm : Work.BoseFixB1.flatMass ℓ Φ = 0) :
    Work.BoseFixB1.flatScountB M ℓ d u Φ = 0 := by
  have hfint : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    integrableOn_abox_local hℓ (hΦc.pow 2)
  have hz : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) = 0 := by
    rw [Work.BoseFixB1.flatMass] at hm; exact hm
  have hae : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      =ᵐ[(volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (Φ x)) hfint).mp hz
  have hae2 : (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x)
      =ᵐ[(volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)] 0 := by
    filter_upwards [hae] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rw [hx, zero_mul]
  rw [Work.BoseFixB1.flatScountB, MeasureTheory.integral_congr_ae hae2]
  simp

/-- **The `τ`-identity**: `flatScountB/κ = flatTau·flatMass`. -/
theorem flatScountB_div_eq_flatTau_mul {M : ℕ} {ℓ d : ℝ} {u : E3} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < ℓ) (hΦc : Continuous Φ) :
    Work.BoseFixB1.flatScountB M ℓ d u Φ / Work.SmallBoxSliding.chiMass M ℓ d u
      = Work.BoseFixB1.flatTau M ℓ d u Φ * Work.BoseFixB1.flatMass ℓ Φ := by
  by_cases hκ : Work.SmallBoxSliding.chiMass M ℓ d u = 0
  · have hτ0 : Work.BoseFixB1.flatTau M ℓ d u Φ = 0 := by
      rw [Work.BoseFixB1.flatTau, hκ, zero_mul, div_zero]
    rw [hτ0, zero_mul, hκ, div_zero]
  · by_cases hm : Work.BoseFixB1.flatMass ℓ Φ = 0
    · have hS0 := flatScountB_eq_zero_of_flatMass_eq_zero (M := M) (d := d) (u := u) hℓ hΦc hm
      have hτ0 : Work.BoseFixB1.flatTau M ℓ d u Φ = 0 := by
        rw [Work.BoseFixB1.flatTau, hm, mul_zero, div_zero]
      rw [hτ0, zero_mul, hS0, zero_div]
    · rw [Work.BoseFixB1.flatTau]
      field_simp

/-- The same identity in the `normB` vocabulary. -/
theorem flatScountB_div_eq_flatTau_mul_normB {v : E3 → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < sideAt μ (a v))
    (hΦc : Continuous Φ) (u : E3) :
    Work.BoseFixB1.flatScountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ
        / Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
      = Work.BoseFixB1.flatTau (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ
        * normB v μ n Φ := by
  rw [← flatMass_eq_normB (v := v) (μ := μ) (n := n) (Φ := Φ)]
  exact flatScountB_div_eq_flatTau_mul (M := (paramsAt μ (a v)).M)
    (d := (paramsAt μ (a v)).d) (u := u) hℓ hΦc

end Work.BoseB1Cube.DiluteAux
