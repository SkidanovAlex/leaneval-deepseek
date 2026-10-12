import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.chAslotAux
import Submission.Work.BoseBoxFock.PCFU.integrableOn_abox_W1_shift
import Submission.Work.BoseBoxFock.PCFU.windowedDirichlet_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## The arithmetic of the assembly -/

/-- The square root of the Dirichlet budget `D = Cd·μ²·a·ℓ³·‖Φ‖²` contracts. -/
lemma chAslot_sqrtD {Cd μ A ℓ nb : ℝ} (hCd : 0 ≤ Cd) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (hℓ : 0 ≤ ℓ) (hnb : 0 ≤ nb) :
    Real.sqrt (Cd * μ ^ 2 * A * ℓ ^ 3 * nb) * Real.sqrt nb
      = Real.sqrt Cd * μ * Real.sqrt A * ℓ * Real.sqrt ℓ * nb := by
  have hℓ3 : Real.sqrt (ℓ ^ 3) = ℓ * Real.sqrt ℓ := by
    rw [show ℓ ^ 3 = ℓ ^ 2 * ℓ by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hℓ]
  have e1 : Cd * μ ^ 2 * A * ℓ ^ 3 * nb = (Cd * μ ^ 2 * A * ℓ ^ 3) * nb := by ring
  rw [e1, Real.sqrt_mul (show (0 : ℝ) ≤ Cd * μ ^ 2 * A * ℓ ^ 3 by positivity)]
  have e2 : Cd * μ ^ 2 * A * ℓ ^ 3 = (Cd * μ ^ 2 * A) * ℓ ^ 3 := by ring
  rw [e2, Real.sqrt_mul (show (0 : ℝ) ≤ Cd * μ ^ 2 * A by positivity)]
  have e3 : Cd * μ ^ 2 * A = (Cd * μ ^ 2) * A := by ring
  rw [e3, Real.sqrt_mul (show (0 : ℝ) ≤ Cd * μ ^ 2 by positivity),
    Real.sqrt_mul hCd, Real.sqrt_sq hμ, hℓ3]
  have hsq : Real.sqrt nb * Real.sqrt nb = nb := Real.mul_self_sqrt hnb
  rw [show Real.sqrt Cd * μ * Real.sqrt A * (ℓ * Real.sqrt ℓ) * Real.sqrt nb * Real.sqrt nb
      = Real.sqrt Cd * μ * Real.sqrt A * (ℓ * Real.sqrt ℓ)
        * (Real.sqrt nb * Real.sqrt nb) by ring, hsq]
  ring

/-- The taper arithmetic: the `1/√N` decay of the taper bound, at the threshold `Y`. -/
lemma chAslot_taper_arith {Ct chiSup R ℓ Cd μ A nb Y K0 a N : ℝ}
    (hCt : 0 ≤ Ct) (hchiSup : 0 ≤ chiSup) (hR : 0 < R)
    (hμ : 0 < μ) (hA : 0 < A) (hℓ : 0 < ℓ) (hnb : 0 ≤ nb) (hK0 : 0 < K0) (ha : 0 < a)
    (hN : 0 < N)
    (hY : Y = 16 * Ct * Real.sqrt Cd * Real.sqrt chiSup * (1 + R) ^ 3 * μ ^ 2 * Real.sqrt A
      * ℓ ^ 5 * (ℓ ^ 3 + 1) / (K0 * a))
    (hY0 : 0 ≤ Y) (hYle : Y ≤ Real.sqrt N) :
    Ct * Real.sqrt chiSup * (1 + R) ^ 3 * ℓ ^ 5 * Real.sqrt Cd * μ * Real.sqrt A * nb
      / Real.sqrt N
      ≤ (1 / 2) * (K0 * a / (8 * μ * (ℓ ^ 3 + 1)) * nb) := by
  have hNpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hIdentity : Ct * Real.sqrt chiSup * (1 + R) ^ 3 * ℓ ^ 5 * Real.sqrt Cd * μ
      * Real.sqrt A * nb
      = (1 / 2) * (K0 * a / (8 * μ * (ℓ ^ 3 + 1)) * nb) * Y := by
    rw [hY]
    field_simp
    ring
  rw [hIdentity]
  have hratio : Y / Real.sqrt N ≤ 1 := (div_le_one hNpos).mpr hYle
  have hb : (0 : ℝ) ≤ (1 / 2) * (K0 * a / (8 * μ * (ℓ ^ 3 + 1)) * nb) := by positivity
  calc (1 / 2) * (K0 * a / (8 * μ * (ℓ ^ 3 + 1)) * nb) * Y / Real.sqrt N
      = (1 / 2) * (K0 * a / (8 * μ * (ℓ ^ 3 + 1)) * nb) * (Y / Real.sqrt N) := by ring
    _ ≤ (1 / 2) * (K0 * a / (8 * μ * (ℓ ^ 3 + 1)) * nb) * 1 :=
        mul_le_mul_of_nonneg_left hratio hb
    _ = (1 / 2) * (K0 * a / (8 * μ * (ℓ ^ 3 + 1)) * nb) := by ring

/-- The images arithmetic: the face-layer decay `(R/ℓ)^8` against the `μ²ℓ^5(ℓ³+1)` supply,
with the diluteness `μa³ ≤ ε₀` and the regime `2R ≤ ℓ` absorbing the `μ` and `ℓ` dependence. -/
lemma chAslot_images_arith {Ci Cd chiSup R ℓ μ A ε₀ K0 : ℝ}
    (hCi : 0 ≤ Ci) (hCd : 0 ≤ Cd) (hchiSup : 0 ≤ chiSup) (hR : 0 < R)
    (hμ : 0 < μ) (hA : 0 < A) (hℓ : 0 < ℓ) (h2R : 2 * R ≤ ℓ)
    (hdil : μ * A ^ 3 ≤ ε₀)
    (hK0 : 16 * Ci * Real.sqrt Cd * Real.sqrt chiSup * R ^ 8 * (ε₀ / A ^ 3) ^ 2
      * (1 + ((2 * R) ^ 3)⁻¹) ≤ K0) :
    Ci * (R / ℓ) ^ 8 * Real.sqrt chiSup * Real.sqrt Cd * μ ^ 2 * ℓ ^ 5 * (ℓ ^ 3 + 1)
      ≤ K0 / 16 := by
  have hA3 : (0 : ℝ) < A ^ 3 := by positivity
  have hμle : μ ≤ ε₀ / A ^ 3 := (le_div_iff₀ hA3).mpr (by linarith [hdil])
  have hε₀ : 0 ≤ ε₀ := le_trans (by positivity : (0 : ℝ) ≤ μ * A ^ 3) hdil
  have hμ2 : μ ^ 2 ≤ (ε₀ / A ^ 3) ^ 2 := by
    have h1 : (0 : ℝ) ≤ ε₀ / A ^ 3 := div_nonneg hε₀ hA3.le
    nlinarith [hμ.le, hμle, h1]
  have hkey : (R / ℓ) ^ 8 * ℓ ^ 5 * (ℓ ^ 3 + 1) = R ^ 8 * (1 + (ℓ ^ 3)⁻¹) := by
    field_simp
  have hmono : (R / ℓ) ^ 8 * μ ^ 2 * ℓ ^ 5 * (ℓ ^ 3 + 1)
      ≤ R ^ 8 * (ε₀ / A ^ 3) ^ 2 * (1 + ((2 * R) ^ 3)⁻¹) := by
    rw [show (R / ℓ) ^ 8 * μ ^ 2 * ℓ ^ 5 * (ℓ ^ 3 + 1)
        = ((R / ℓ) ^ 8 * ℓ ^ 5 * (ℓ ^ 3 + 1)) * μ ^ 2 by ring, hkey]
    have hR8 : (0 : ℝ) ≤ R ^ 8 := by positivity
    have hinv : (1 + (ℓ ^ 3)⁻¹) ≤ (1 + ((2 * R) ^ 3)⁻¹) := by
      have hpos : (0 : ℝ) < (2 * R) ^ 3 := by positivity
      have h : (ℓ ^ 3)⁻¹ ≤ ((2 * R) ^ 3)⁻¹ :=
        (inv_le_inv₀ (by positivity) hpos).mpr (pow_le_pow_left₀ (by positivity) h2R 3)
      linarith
    calc R ^ 8 * (1 + (ℓ ^ 3)⁻¹) * μ ^ 2
        ≤ R ^ 8 * (1 + ((2 * R) ^ 3)⁻¹) * (ε₀ / A ^ 3) ^ 2 := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hinv hR8) hμ2 (sq_nonneg _)
            (mul_nonneg hR8 (by positivity))
      _ = R ^ 8 * (ε₀ / A ^ 3) ^ 2 * (1 + ((2 * R) ^ 3)⁻¹) := by ring
  have hCnn : (0 : ℝ) ≤ Ci * Real.sqrt chiSup * Real.sqrt Cd :=
    mul_nonneg (mul_nonneg hCi (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hstep : Ci * Real.sqrt chiSup * Real.sqrt Cd
      * ((R / ℓ) ^ 8 * μ ^ 2 * ℓ ^ 5 * (ℓ ^ 3 + 1))
      ≤ Ci * Real.sqrt chiSup * Real.sqrt Cd
        * (R ^ 8 * (ε₀ / A ^ 3) ^ 2 * (1 + ((2 * R) ^ 3)⁻¹)) :=
    mul_le_mul_of_nonneg_left hmono hCnn
  have hstep2 : Ci * (R / ℓ) ^ 8 * Real.sqrt chiSup * Real.sqrt Cd * μ ^ 2 * ℓ ^ 5
      * (ℓ ^ 3 + 1)
      = Ci * Real.sqrt chiSup * Real.sqrt Cd
        * ((R / ℓ) ^ 8 * μ ^ 2 * ℓ ^ 5 * (ℓ ^ 3 + 1)) := by ring
  rw [hstep2]
  refine le_trans hstep ?_
  have h16 : (0 : ℝ) < 16 := by norm_num
  rw [le_div_iff₀ h16]
  have hcomm : Ci * Real.sqrt chiSup * Real.sqrt Cd
      * (R ^ 8 * (ε₀ / A ^ 3) ^ 2 * (1 + ((2 * R) ^ 3)⁻¹)) * 16
      = 16 * Ci * Real.sqrt Cd * Real.sqrt chiSup * R ^ 8 * (ε₀ / A ^ 3) ^ 2
        * (1 + ((2 * R) ^ 3)⁻¹) := by ring
  rw [hcomm]
  exact hK0

end Work.BoseBoxFock.PCFU
