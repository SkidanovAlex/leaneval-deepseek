import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.BogFSKernel
import Submission.Work.BoseBogFS.gFun_beta_diff_abs_le
import Submission.Work.BoseBogFS.gFun_beta_le
import Submission.Work.BoseBogFS.integrand_reduction
import Submission.Work.BoseFixR.IntegrableChatW1sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.BogFSCompare` — the comparison layer of `integral_cleanFun_le`

The target `Work.BoseBogFS.integral_cleanFun_le` is proved by comparing the honest scaled
clean integrand `psiSc` with FS's `fsI1Integrand` at the affine model kernel
`bogKernel v R ρ μ` and then invoking `Work.BoseB6Est.fsI1_le`.

This module sets up the *interface* of that comparison:

* the radial form `tauScRad` of the honest scaled kinetic symbol (so that the `τ`-part of the
  comparison can be integrated in polar coordinates), with its two quantitative properties
  `tauScRad_le_sq` and `tauScRad_deficit` (`r² − τ_s(r) ≤ 3κr`, `κ = bogKappa`);
* the two constants of the `β`-comparison, `bogDelta` (`χ⋆χ` Taylor deficit, `16πC(R/ℓ)²`)
  and `bogBb` (the `β`-upper bound `8π(1+2C(R/ℓ)²)`), with the pointwise rows
  `betaSc_eq`, `betaSc_close`, `betaSc_le` and `betaSc_nonneg_of_small`.

## Notation (fixed throughout)

`P = ρ·(a v)`, `ℓ = ell v μ`, `c₁ = bogC1 v ρ μ`, `c₂ = bogC2 v ρ μ`,
`ε_T = (paramsAt μ (a v)).eT`, `η = bogEta v R ρ`, `T = bogT v R μ`, `K = bogKernel v R ρ μ`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Two local profile facts

`tauProf` is opaque (`tauProf`), so the two elementary consequences of
the recorded properties (P3) and (P4) used below are re-derived here to keep this module's
import closure small. -/

/-- (P3) of the profile: nonnegativity. -/
private lemma tauProf_nonneg_local (s : ℝ) : 0 ≤ Work.BoseBoxFock.tauProf s := by
  have h := Work.BoseBoxFock.tauProf_spec.2.2.1 s
  have h' : (max 0 (s - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf s := by
    simpa only [Work.BoseBoxFock.tauProf] using h
  linarith [sq_nonneg (max 0 (s - 2))]

/-- (P4) in rescaled form: `c²τ̃(r/c) ≤ r²` for `c > 0`, `r ≥ 0`. -/
private lemma tauProf_div_le_sq_local {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    c ^ 2 * Work.BoseBoxFock.tauProf (r / c) ≤ r ^ 2 := by
  have hrc : 0 ≤ r / c := div_nonneg hr hc.le
  have h := Work.BoseBoxFock.tauProf_le_max_sq (r / c)
  have hmax : max 0 (r / c - 1) ≤ r / c := max_le hrc (by linarith)
  have h2 : (max 0 (r / c - 1)) ^ 2 ≤ (r / c) ^ 2 :=
    pow_le_pow_left₀ (le_max_left _ _) hmax 2
  have h3 : Work.BoseBoxFock.tauProf (r / c) ≤ (r / c) ^ 2 := le_trans h h2
  have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg c)
  have hcsq : c ^ 2 * (r / c) ^ 2 = r ^ 2 := by
    rw [div_pow, mul_div_assoc', mul_div_cancel_left₀ _ (pow_ne_zero 2 hc.ne')]
  rwa [hcsq] at h4

/-! ## 1. The radial honest kinetic symbol -/

/-- **FS's scaled kinetic symbol `τ̃` as a function of the radius**:
`τ̃_rad(r) = (1−ε_T)(2sℓ)⁻²·τ̃(r(2sℓ)) + ε_T(2dsℓ)⁻²·τ̃(r(2dsℓ))`.

It is the radial form of `Work.BoseBoxFock.tauSm`, i.e. `tauSm eT s d ℓ k = tauSmRad … ‖k‖`
definitionally. -/
def tauSmRad (eT s d ℓ r : ℝ) : ℝ :=
  (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (r / (2 * s * ℓ)⁻¹)
    + eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (r / (2 * d * s * ℓ)⁻¹)

lemma tauSm_eq_tauSmRad (eT s d ℓ : ℝ) (k : E3) :
    Work.BoseBoxFock.tauSm eT s d ℓ k = tauSmRad eT s d ℓ ‖k‖ := rfl

/-- **The honest scaled kinetic symbol as a function of the radius**:
`τ_s(r) = P⁻¹τ̃_rad(√P·r)` with `P = ρ·(a v)`.  It is the radial form of `tauSc`. -/
def tauScRad (v : E3 → ℝ) (ρ μ : ℝ) (r : ℝ) : ℝ :=
  (ρ * a v)⁻¹ * tauSmRad (paramsAt μ (a v)).eT (paramsAt μ (a v)).s (paramsAt μ (a v)).d
    (ell v μ) (Real.sqrt (ρ * a v) * r)

/-- `tauSc` is the radial function `tauScRad` evaluated at `‖t‖`. -/
lemma tauSc_eq_tauScRad (v : E3 → ℝ) (ρ μ : ℝ) (t : E3) :
    tauSc v ρ μ t = tauScRad v ρ μ ‖t‖ := by
  rw [tauSc, tauAt, tauScRad, tauSm_eq_tauSmRad, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- **The deficit coefficient** `κ = (1−ε_T)c₁ + ε_T c₂`. -/
def bogKappa (v : E3 → ℝ) (ρ μ : ℝ) : ℝ :=
  (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ + (paramsAt μ (a v)).eT * bogC2 v ρ μ

private lemma sqrt_mul_inv_cancel {P c : ℝ} (hP : 0 < P) :
    Real.sqrt P * (c * Real.sqrt P)⁻¹ = c⁻¹ := by
  have hS : Real.sqrt P ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  calc Real.sqrt P * (c * Real.sqrt P)⁻¹
      = Real.sqrt P * (c⁻¹ * (Real.sqrt P)⁻¹) := by rw [mul_inv]
    _ = (Real.sqrt P * c⁻¹) * (Real.sqrt P)⁻¹ := (mul_assoc _ _ _).symm
    _ = (c⁻¹ * Real.sqrt P) * (Real.sqrt P)⁻¹ := by rw [mul_comm (Real.sqrt P) c⁻¹]
    _ = c⁻¹ * (Real.sqrt P * (Real.sqrt P)⁻¹) := mul_assoc _ _ _
    _ = c⁻¹ := by rw [mul_inv_cancel₀ hS, mul_one]

/-- **The threshold identities**: `√P·c₁ = (2sℓ)⁻¹`, `√P·c₂ = (2dsℓ)⁻¹`. -/
lemma sqrt_mul_bogC1 {v : E3 → ℝ} {ρ μ : ℝ} (hP : 0 < ρ * a v) :
    Real.sqrt (ρ * a v) * bogC1 v ρ μ = (2 * (paramsAt μ (a v)).s * ell v μ)⁻¹ := by
  rw [bogC1]; exact sqrt_mul_inv_cancel hP

lemma sqrt_mul_bogC2 {v : E3 → ℝ} {ρ μ : ℝ} (hP : 0 < ρ * a v) :
    Real.sqrt (ρ * a v) * bogC2 v ρ μ
      = (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ)⁻¹ := by
  rw [bogC2]; exact sqrt_mul_inv_cancel hP

/-- **The `τ_s,r` identity**: the scaled symbol is the standard two-term combination of the
rescaled profiles, `τ_s(r) = (1−ε_T)c₁²τ̃(r/c₁) + ε_Tc₂²τ̃(r/c₂)`. -/
lemma tauScRad_eq (v : E3 → ℝ) {ρ μ : ℝ} (hP : 0 < ρ * a v) (r : ℝ) :
    tauScRad v ρ μ r
      = (1 - (paramsAt μ (a v)).eT) * (bogC1 v ρ μ) ^ 2
          * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)
        + (paramsAt μ (a v)).eT * (bogC2 v ρ μ) ^ 2
          * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ) := by
  have hPinv : (Real.sqrt (ρ * a v))⁻¹ ^ 2 = (ρ * a v)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hP.le]
  have hsq1 : (bogC1 v ρ μ) ^ 2
      = (ρ * a v)⁻¹ * ((2 * (paramsAt μ (a v)).s * ell v μ)⁻¹) ^ 2 := by
    have h1 : (2 * (paramsAt μ (a v)).s * ell v μ * Real.sqrt (ρ * a v))⁻¹
        = (Real.sqrt (ρ * a v))⁻¹ * (2 * (paramsAt μ (a v)).s * ell v μ)⁻¹ := by
      rw [mul_inv]; ring
    rw [bogC1, h1, mul_pow, hPinv]
  have hsq2 : (bogC2 v ρ μ) ^ 2
      = (ρ * a v)⁻¹
        * ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ)⁻¹) ^ 2 := by
    have h1 : (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ
          * Real.sqrt (ρ * a v))⁻¹
        = (Real.sqrt (ρ * a v))⁻¹
          * (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ)⁻¹ := by
      rw [mul_inv]; ring
    rw [bogC2, h1, mul_pow, hPinv]
  have hsqrt : Real.sqrt (ρ * a v) ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  have harg1 : Real.sqrt (ρ * a v) * r / (2 * (paramsAt μ (a v)).s * ell v μ)⁻¹
      = r / bogC1 v ρ μ := by
    rw [← sqrt_mul_bogC1 (v := v) (ρ := ρ) (μ := μ) hP]
    field_simp
  have harg2 : Real.sqrt (ρ * a v) * r
        / (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ)⁻¹
      = r / bogC2 v ρ μ := by
    rw [← sqrt_mul_bogC2 (v := v) (ρ := ρ) (μ := μ) hP]
    field_simp
  rw [tauScRad, tauSmRad, harg1, harg2, hsq1, hsq2]
  ring

/-- `τ_s,r ≥ 0` (both weights nonnegative and `τ̃ ≥ 0`). -/
lemma tauScRad_nonneg (v : E3 → ℝ) {ρ μ : ℝ} (hP : 0 < ρ * a v)
    (heT0 : 0 ≤ (paramsAt μ (a v)).eT) (heT1 : (paramsAt μ (a v)).eT ≤ 1) (r : ℝ) :
    0 ≤ tauScRad v ρ μ r := by
  rw [tauScRad_eq v hP r]
  have h1 : 0 ≤ (1 - (paramsAt μ (a v)).eT) * (bogC1 v ρ μ) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ (paramsAt μ (a v)).eT * (bogC2 v ρ μ) ^ 2 :=
    mul_nonneg heT0 (sq_nonneg _)
  have h3 : 0 ≤ Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ) := tauProf_nonneg_local _
  have h4 : 0 ≤ Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ) := tauProf_nonneg_local _
  nlinarith [h1, h2, h3, h4]

/-- `τ_s,r ≤ r²` (from `τ̃(u) ≤ (max 0 (u−1))²`). -/
lemma tauScRad_le_sq (v : E3 → ℝ) {ρ μ : ℝ} (hP : 0 < ρ * a v)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (heT0 : 0 ≤ (paramsAt μ (a v)).eT) (heT1 : (paramsAt μ (a v)).eT ≤ 1) {r : ℝ}
    (hr : 0 ≤ r) :
    tauScRad v ρ μ r ≤ r ^ 2 := by
  rw [tauScRad_eq v hP r]
  have hA := tauProf_div_le_sq_local (c := bogC1 v ρ μ) (r := r) hc1 hr
  have hB := tauProf_div_le_sq_local (c := bogC2 v ρ μ) (r := r) hc2 hr
  have h1 : (1 - (paramsAt μ (a v)).eT) * ((bogC1 v ρ μ) ^ 2
      * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)) ≤ (1 - (paramsAt μ (a v)).eT) * r ^ 2 :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  have h2 : (paramsAt μ (a v)).eT * ((bogC2 v ρ μ) ^ 2
      * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ)) ≤ (paramsAt μ (a v)).eT * r ^ 2 :=
    mul_le_mul_of_nonneg_left hB heT0
  have e1 : (1 - (paramsAt μ (a v)).eT) * (bogC1 v ρ μ) ^ 2
      * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)
      = (1 - (paramsAt μ (a v)).eT) * ((bogC1 v ρ μ) ^ 2
        * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)) := by ring
  have e2 : (paramsAt μ (a v)).eT * (bogC2 v ρ μ) ^ 2
      * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ)
      = (paramsAt μ (a v)).eT * ((bogC2 v ρ μ) ^ 2
        * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ)) := by ring
  rw [e1, e2]
  nlinarith [h1, h2]

/-- `r² − c²τ̃(r/c) ≤ 3cr` for `c > 0`, `r ≥ 0`: the *only* profile input of the `τ`-estimate.
For `r ≤ c` the profile vanishes; for `c ≤ r ≤ 2c` we use `τ̃ ≥ 0`; beyond `2c` the exact
quadratic tail `(r−3c/2)² + c₀c²` gives the bound with room `(9/4+c₀)c²`. -/
lemma sq_sub_c_sq_tauProf_le {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    r ^ 2 - c ^ 2 * Work.BoseBoxFock.tauProf (r / c) ≤ 3 * c * r := by
  rcases le_or_gt r c with h | h
  · have h1 : Work.BoseBoxFock.tauProf (r / c) = 0 :=
      Work.BoseBoxFock.tauProf_eq_zero_of_le_one (by rw [div_le_one hc]; exact h)
    rw [h1, mul_zero, sub_zero]
    nlinarith
  · rcases le_or_gt r (2 * c) with h2 | h2
    · have h3 : 0 ≤ c ^ 2 * Work.BoseBoxFock.tauProf (r / c) :=
        mul_nonneg (sq_nonneg c) (tauProf_nonneg_local _)
      nlinarith
    · have h4 : Work.BoseBoxFock.tauProf (r / c)
          = (r / c - 3 / 2) ^ 2 + Work.BoseBoxFock.tauC0 :=
        Work.BoseBoxFock.tauProf_quad (by rw [le_div_iff₀ hc]; linarith)
      have h6 : c ^ 2 * ((r / c - 3 / 2) ^ 2 + Work.BoseBoxFock.tauC0)
          = (r - 3 * c / 2) ^ 2 + c ^ 2 * Work.BoseBoxFock.tauC0 := by
        field_simp
      rw [h4, h6]
      nlinarith [sq_nonneg (r - 3 * c / 2), sq_nonneg c, hc, Work.BoseBoxFock.tauC0_nonneg]

/-- **The `τ`-deficit of the scaled symbol**: `r² − τ_s,r ≤ 3κr` with `κ = bogKappa`. -/
lemma tauScRad_deficit (v : E3 → ℝ) {ρ μ : ℝ} (hP : 0 < ρ * a v)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (heT0 : 0 ≤ (paramsAt μ (a v)).eT) (heT1 : (paramsAt μ (a v)).eT ≤ 1) {r : ℝ}
    (hr : 0 ≤ r) :
    r ^ 2 - tauScRad v ρ μ r ≤ 3 * bogKappa v ρ μ * r := by
  rw [tauScRad_eq v hP r]
  have hA := sq_sub_c_sq_tauProf_le (c := bogC1 v ρ μ) (r := r) hc1 hr
  have hB := sq_sub_c_sq_tauProf_le (c := bogC2 v ρ μ) (r := r) hc2 hr
  have h1 : (1 - (paramsAt μ (a v)).eT) * (r ^ 2 - (bogC1 v ρ μ) ^ 2
      * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ))
      ≤ (1 - (paramsAt μ (a v)).eT) * (3 * bogC1 v ρ μ * r) :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  have h2 : (paramsAt μ (a v)).eT * (r ^ 2 - (bogC2 v ρ μ) ^ 2
      * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ))
      ≤ (paramsAt μ (a v)).eT * (3 * bogC2 v ρ μ * r) :=
    mul_le_mul_of_nonneg_left hB heT0
  have hsplit : r ^ 2 - ((1 - (paramsAt μ (a v)).eT) * (bogC1 v ρ μ) ^ 2
        * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)
      + (paramsAt μ (a v)).eT * (bogC2 v ρ μ) ^ 2
        * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ))
      = (1 - (paramsAt μ (a v)).eT) * (r ^ 2 - (bogC1 v ρ μ) ^ 2
          * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ))
        + (paramsAt μ (a v)).eT * (r ^ 2 - (bogC2 v ρ μ) ^ 2
          * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ)) := by
    ring
  rw [hsplit, bogKappa]
  nlinarith [h1, h2]

/-! ## 2. The constants of the `β`-comparison -/

/-- The `χ⋆χ` Taylor deficit at the box scale: `δ = 16π·C·(R/ℓ)²`. -/
def bogDelta (R ℓ C : ℝ) : ℝ := 16 * Real.pi * C * (R / ℓ) ^ 2

/-- The `β`-upper bound on the bulk: `B_β = 8π(1 + 2C(R/ℓ)²)`. -/
def bogBb (R ℓ C : ℝ) : ℝ := 8 * Real.pi * (1 + 2 * C * (R / ℓ) ^ 2)

/-- **The honest `β` in terms of `Ŵ₁`**: `β(t) = a⁻¹Ŵ₁(√P·t)` with `P = ρ·(a v)`. -/
lemma betaSc_eq (v : E3 → ℝ) {h : ScatSol v} {ρ μ : ℝ} (hρ : ρ ≠ 0) (hav : a v ≠ 0) (t : E3) :
    betaSc v h ρ μ t
      = (a v)⁻¹ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ))
          (Real.sqrt (ρ * a v) • t) := by
  rw [betaSc, cAt, W1At]
  have hρa : ρ * a v ≠ 0 := mul_ne_zero hρ hav
  field_simp

/-- **The `β`-closeness row on `[0,T]`**: with `η = bogEta v R ρ = 16πR√(ρa)` and
`δ = bogDelta R ℓ C = 16πC(R/ℓ)²`,
`|β(t) − (8π + η‖t‖)| ≤ δ + 2η‖t‖`.

It combines the Lipschitz bound `chat_W1fun_lipschitz` with the mass bound `W1_mass_bounds`
(`Ŵ₁(0) ∈ [8πa, 8πa(1+2C(R/ℓ)²)]`). -/
lemma betaSc_close {v : E3 → ℝ} {h : ScatSol v} {R C r₁ ρ μ : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁) (hℓ : 0 < (ell v μ))
    (hT : ∀ x : E3, ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hreg : R / (ell v μ) ≤ r₁) (hcond : C * (R / (ell v μ)) ^ 2 ≤ 1 / 2)
    (hρ : 0 < ρ) (hav : 0 < a v) (hrl : R ≤ (ell v μ) * Submission.BoseGases.chiR0) (t : E3) :
    |betaSc v h ρ μ t - (8 * Real.pi + bogEta v R ρ * ‖t‖)|
      ≤ bogDelta R (ell v μ) C + 2 * bogEta v R ρ * ‖t‖ := by
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have hInt : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (ell v μ)) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hrl
  have hmass := W1_mass_bounds (h := h) hR hv hvrad hv_supp hC hr₁ hℓ hT hreg hcond
  have hzero : Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0
      = ∫ y : E3, Work.BoseFixR.W1fun v h (ell v μ) y := chat_zero_eq_integral _ hInt
  have hup : Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0
      ≤ 8 * Real.pi * a v * (1 + 2 * C * (R / (ell v μ)) ^ 2) := by
    rw [hzero]; exact hmass.2
  have hlow : 8 * Real.pi * a v ≤ Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0 := by
    rw [hzero]; exact hmass.1
  have hpn : ‖Real.sqrt (ρ * a v) • t‖ = Real.sqrt (ρ * a v) * ‖t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hlip : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (Real.sqrt (ρ * a v) • t)
      - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0|
      ≤ 16 * Real.pi * R * a v * (Real.sqrt (ρ * a v) * ‖t‖) := by
    have h1 := Work.BoseGateFS.chat_W1fun_lipschitz (h := h) hR hℓ hv hvrad hv_supp hrl
      (Real.sqrt (ρ * a v) • t) 0
    rw [sub_zero, hpn] at h1
    exact h1
  have h0 : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0 - 8 * Real.pi * a v|
      ≤ 8 * Real.pi * a v * (2 * C * (R / (ell v μ)) ^ 2) := by
    rw [abs_of_nonneg (by linarith)]
    nlinarith [hlow, hup]
  have hb : |betaSc v h ρ μ t - 8 * Real.pi|
      = (a v)⁻¹ * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (Real.sqrt (ρ * a v) • t)
          - 8 * Real.pi * a v| := by
    rw [betaSc_eq v hρ.ne' hav.ne' t,
      show (a v)⁻¹ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (Real.sqrt (ρ * a v) • t)
          - 8 * Real.pi
          = (a v)⁻¹ * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ))
              (Real.sqrt (ρ * a v) • t) - 8 * Real.pi * a v) by
        field_simp,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr hav.le)]
  have hmain : |betaSc v h ρ μ t - 8 * Real.pi| ≤ bogDelta R (ell v μ) C + bogEta v R ρ * ‖t‖ := by
    rw [hb]
    have hsplit : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (Real.sqrt (ρ * a v) • t)
          - 8 * Real.pi * a v|
        ≤ |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (Real.sqrt (ρ * a v) • t)
              - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0|
            + |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0 - 8 * Real.pi * a v| := by
      have hab := abs_add_le
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (Real.sqrt (ρ * a v) • t)
          - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0)
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0 - 8 * Real.pi * a v)
      have heq : (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ))
              (Real.sqrt (ρ * a v) • t)
            - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0)
          + (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0 - 8 * Real.pi * a v)
          = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (Real.sqrt (ρ * a v) • t)
            - 8 * Real.pi * a v := by ring
      rwa [heq] at hab
    have hstep := mul_le_mul_of_nonneg_left (le_trans hsplit (add_le_add hlip h0))
      (inv_nonneg.mpr hav.le)
    have hval : (a v)⁻¹ * (16 * Real.pi * R * a v * (Real.sqrt (ρ * a v) * ‖t‖)
          + 8 * Real.pi * a v * (2 * C * (R / (ell v μ)) ^ 2))
        = bogEta v R ρ * ‖t‖ + bogDelta R (ell v μ) C := by
      rw [bogEta, bogDelta, div_pow]
      field_simp
      ring
    linarith [hstep, hval.le, hval.ge]
  have htri : |betaSc v h ρ μ t - (8 * Real.pi + bogEta v R ρ * ‖t‖)|
      ≤ |betaSc v h ρ μ t - 8 * Real.pi| + bogEta v R ρ * ‖t‖ := by
    have key : betaSc v h ρ μ t - (8 * Real.pi + bogEta v R ρ * ‖t‖)
        = (betaSc v h ρ μ t - 8 * Real.pi) + (-(bogEta v R ρ * ‖t‖)) := by ring
    rw [key]
    refine le_trans (abs_add_le _ _) (le_of_eq ?_)
    rw [abs_neg,
      abs_of_nonneg (mul_nonneg (bogEta_nonneg (v := v) hR.le hρ.le) (norm_nonneg t))]
  linarith [hmain, htri]

/-- `β ≤ B_β + η‖t‖` (from `Ŵ₁(p) ≤ Ŵ₁(0) + |Ŵ₁(p) − Ŵ₁(0)|`). -/
lemma betaSc_le {v : E3 → ℝ} {h : ScatSol v} {R C r₁ ρ μ : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁) (hℓ : 0 < (ell v μ))
    (hT : ∀ x : E3, ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hreg : R / (ell v μ) ≤ r₁) (hcond : C * (R / (ell v μ)) ^ 2 ≤ 1 / 2)
    (hρ : 0 < ρ) (hav : 0 < a v) (hrl : R ≤ (ell v μ) * Submission.BoseGases.chiR0) (t : E3) :
    betaSc v h ρ μ t ≤ bogBb R (ell v μ) C + bogEta v R ρ * ‖t‖ := by
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have hInt : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (ell v μ)) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hrl
  have hmass := W1_mass_bounds (h := h) hR hv hvrad hv_supp hC hr₁ hℓ hT hreg hcond
  have hzero : Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0
      = ∫ y : E3, Work.BoseFixR.W1fun v h (ell v μ) y := chat_zero_eq_integral _ hInt
  have hup : Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0
      ≤ 8 * Real.pi * a v * (1 + 2 * C * (R / (ell v μ)) ^ 2) := by
    rw [hzero]; exact hmass.2
  have hpn : ‖Real.sqrt (ρ * a v) • t‖ = Real.sqrt (ρ * a v) * ‖t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hlip : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (Real.sqrt (ρ * a v) • t)
      - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0|
      ≤ 16 * Real.pi * R * a v * (Real.sqrt (ρ * a v) * ‖t‖) := by
    have h1 := Work.BoseGateFS.chat_W1fun_lipschitz (h := h) hR hℓ hv hvrad hv_supp hrl
      (Real.sqrt (ρ * a v) • t) 0
    rw [sub_zero, hpn] at h1
    exact h1
  have hle : Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (Real.sqrt (ρ * a v) • t)
      ≤ Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) 0
        + 16 * Real.pi * R * a v * (Real.sqrt (ρ * a v) * ‖t‖) := by
    have h := (abs_le.mp hlip).2
    linarith
  rw [betaSc_eq v hρ.ne' hav.ne' t]
  have hle' : Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (Real.sqrt (ρ * a v) • t)
      ≤ 8 * Real.pi * a v * (1 + 2 * C * (R / (ell v μ)) ^ 2)
        + 16 * Real.pi * R * a v * (Real.sqrt (ρ * a v) * ‖t‖) := by
    linarith [hle, hup]
  have hfin := mul_le_mul_of_nonneg_left hle' (inv_nonneg.mpr hav.le)
  have hval : (a v)⁻¹ * (8 * Real.pi * a v * (1 + 2 * C * (R / (ell v μ)) ^ 2)
        + 16 * Real.pi * R * a v * (Real.sqrt (ρ * a v) * ‖t‖))
      = bogBb R (ell v μ) C + bogEta v R ρ * ‖t‖ := by
    rw [bogBb, bogEta, div_pow]
    field_simp
  linarith [hfin, hval.le, hval.ge]

/-- **Positivity of `β` on the bulk**: `0 ≤ Ŵ₁(√P·t)` as soon as `R·√P·‖t‖ ≤ 1`
(`Work.BoseBogFS.chat_W1fun_nonneg_small`). -/
lemma betaSc_nonneg_of_small {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hρ : 0 < ρ) (hrl : R ≤ (ell v μ) * Submission.BoseGases.chiR0) (hℓ : 0 < (ell v μ))
    {t : E3} (ht : R * Real.sqrt (ρ * a v) * ‖t‖ ≤ 1) :
    0 ≤ betaSc v h ρ μ t := by
  rw [betaSc, cAt, W1At]
  have h1 : 0 ≤ Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ))
      (Real.sqrt (ρ * a v) • t) := by
    refine Work.BoseBogFS.chat_W1fun_nonneg_small (v := v) (h := h) (R := R) hR hv hvrad
      hv_supp hav hrl hℓ (Real.sqrt (ρ * a v) • t) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    linarith [ht]
  exact mul_nonneg (inv_nonneg.mpr (mul_pos hρ hav).le) (mul_nonneg hρ.le h1)

/-! ## 0b. The `χ⋆χ` Taylor constants (fixed once and for all)

The `β`-rows need the *specific* constant of `conv3chi_second_order_bound`, **not** a free one:
with a free constant `C` and only `C(R/ℓ)² ≤ 1/2` the row `δT³ ≲ lhyEps` is false
(take `C = ℓ²/(2R²)`).  We therefore fix the choice here. -/

/-- The Taylor constant of `χ⋆χ` at the origin. -/
noncomputable def chiTC : ℝ :=
  Classical.choose Submission.BoseGases.conv3chi_second_order_bound

/-- The radius of validity of the Taylor bound. -/
noncomputable def chiTR1 : ℝ :=
  Classical.choose ((Classical.choose_spec
    Submission.BoseGases.conv3chi_second_order_bound).2)

lemma chiTC_nonneg : 0 ≤ chiTC :=
  (Classical.choose_spec Submission.BoseGases.conv3chi_second_order_bound).1

lemma chiTR1_pos : 0 < chiTR1 :=
  (Classical.choose_spec ((Classical.choose_spec
    Submission.BoseGases.conv3chi_second_order_bound).2)).1

lemma chiT_bound (x : E3) (hx : ‖x‖ ≤ chiTR1) :
    |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
      ≤ chiTC * ‖x‖ ^ 2 :=
  (Classical.choose_spec ((Classical.choose_spec
    Submission.BoseGases.conv3chi_second_order_bound).2)).2 x hx

end Work.BoseBogFS
