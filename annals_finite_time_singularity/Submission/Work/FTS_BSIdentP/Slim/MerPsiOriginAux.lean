import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS_BSIdentP.Slim.Dev5
import Submission.Work.FTS_BSIdentP.Slim.Dev6
import Submission.Work.FTS_BSIdentP.Slim.Dev11
import Submission.Work.FTS_BSIdentP.Slim.RhoMulRpowWeightLeTwo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliaries for the vanishing of `ψ`, `∂_zψ`, `∂_rψ` at the origin

Part 1: the generic squeeze against `rhoP r z → 0`, the boundedness of the odd extension
against `cos θ`, the arithmetic core of the first-order bounds, and the pointwise bound for
`ψ/r`.  Consumed by `Work.FTS.BSIdentP.Levels.merPsiT_origin_profiles`.
-/

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

set_option maxHeartbeats 2000000

/-- If `|f r z| ≤ K·ρ(r,z)` on the half-plane `r > 0`, then `f → 0` at the origin along that
half-plane. -/
theorem tendsto_zero_of_rhoP_bound {f : ℝ × ℝ → ℝ} {K : ℝ}
    (h : ∀ r z : ℝ, 0 < r → |f (r, z)| ≤ K * Work.Cyl.rhoP r z) :
    Filter.Tendsto f (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hb : Filter.Tendsto (fun p : ℝ × ℝ => K * Work.Cyl.rhoP p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 0) := by
    have hc : Continuous fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 := by
      change Continuous (fun p : ℝ × ℝ => Real.sqrt (p.1 ^ 2 + p.2 ^ 2))
      fun_prop
    have h00 : Work.Cyl.rhoP 0 0 = 0 := by simp [Work.Cyl.rhoP]
    have h1 : Filter.Tendsto (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2)
        (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 (Work.Cyl.rhoP 0 0)) :=
      (hc.tendsto ((0:ℝ), 0)).mono_left nhdsWithin_le_nhds
    rw [h00] at h1
    simpa using h1.const_mul K
  refine squeeze_zero' (Eventually.of_forall fun p => abs_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with p hp
  simpa [Real.norm_eq_abs] using h p.1 p.2 hp

/-- The odd extension loses one power of `π/2 - |θ|`; Jordan's inequality compares that with
`(π/2) cos θ`, which is the form needed to divide by `cos θ`. -/
theorem abs_GG_le_cos {Φ : Work.FTS.BSIdent.Fam} {τ C₀ lam : ℝ}
    (hC₀ : 0 ≤ C₀) (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2) :
    |Work.FTS.BSIdentP.Dev5.GG Φ τ w θ|
      ≤ C₀ * (Real.pi / 2) * Real.cos θ * (1 + w) ^ (-lam) := by
  have h1 := Work.FTS.BSIdent.Cyl.DecayAux.abs_PhiOdd_le (Φ := Φ) (τ := τ) (C₀ := C₀) (q := 1)
    (lam := lam) hC₀ h0
    (fun w θ hw hθ0 hθ1 => by
      simpa [Real.rpow_one] using hrate w θ hw.le hθ0.le hθ1) hw hθ
  rw [Real.rpow_one] at h1
  have hJ := Work.FTS.BSIdent.Cyl.DecayAux.pi_div_two_sub_abs_le_cos (le_of_lt hθ)
  have hrpow : 0 ≤ (1 + w) ^ (-lam) := Real.rpow_nonneg (by linarith) _
  calc |Work.FTS.BSIdentP.Dev5.GG Φ τ w θ|
      = |Work.FTS.BSIdent.PhiOdd Φ w θ τ| := rfl
    _ ≤ C₀ * (Real.pi / 2 - |θ|) * (1 + w) ^ (-lam) := h1
    _ ≤ C₀ * (Real.pi / 2 * Real.cos θ) * (1 + w) ^ (-lam) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ hC₀) hrpow
    _ = C₀ * (Real.pi / 2) * Real.cos θ * (1 + w) ^ (-lam) := by ring

/-- The abstract combination `2 Z c Gv + c (p Z w Gw + R Gt)` is `O(ρ)` when all the
coefficients are `O(ρ)`, the three profile quantities are bounded by the rate hypothesis, and
`(1+w)^{-lam} ≤ 1`. -/
theorem abs_chain_le {c p C₀ lam ρ θ w Z R Gv Gw Gt : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 ≤ p) (hθ0 : 0 ≤ θ)
    (hρ : 0 ≤ ρ) (hw : 0 ≤ w)
    (hZ : |Z| ≤ ρ) (hR : |R| ≤ ρ)
    (hval : |Gv| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam))
    (hwd : |Gw| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1))
    (hth : |Gt| ≤ C₀ * (1 + w) ^ (-lam)) :
    |2 * Z * c * Gv + c * (p * Z * w * Gw + R * Gt)|
      ≤ |c| * C₀ * (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1) * ρ := by
  have h1w : (0:ℝ) < 1 + w := by linarith
  have hS : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith
  have hrpow1 : 0 ≤ (1 + w) ^ (-lam) := Real.rpow_nonneg h1w.le _
  have hrpow2 : 0 ≤ (1 + w) ^ (-lam - 1) := Real.rpow_nonneg h1w.le _
  have hpow1 : (1 + w) ^ (-lam) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hpow2 : w * (1 + w) ^ (-lam - 1) ≤ 1 := by
    have e : (1 + w) ^ (-lam - 1) = (1 + w) ^ (-1 : ℝ) * (1 + w) ^ (-lam) := by
      rw [show -lam - 1 = -1 + -lam by ring, Real.rpow_add h1w]
    have e2 : (1 + w) ^ (-1 : ℝ) = (1 + w)⁻¹ := Real.rpow_neg_one _
    have hw1 : w * (1 + w)⁻¹ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (show w ≤ 1 + w by linarith)
        (inv_nonneg.mpr h1w.le)
      rwa [mul_inv_cancel₀ (ne_of_gt h1w)] at h
    calc w * (1 + w) ^ (-lam - 1)
        = (w * (1 + w)⁻¹) * (1 + w) ^ (-lam) := by rw [e, e2]; ring
      _ ≤ 1 * 1 := mul_le_mul hw1 hpow1 hrpow1 (by norm_num)
      _ = 1 := one_mul 1
  have hv : |Gv| ≤ C₀ * (Real.pi / 2) * (1 + w) ^ (-lam) :=
    hval.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hC₀) hrpow1)
  have hwv : |Gw| ≤ C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1) :=
    hwd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hC₀) hrpow2)
  have hA : |2 * Z * c * Gv| ≤ 2 * |c| * C₀ * (Real.pi / 2) * ρ := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc 2 * |Z| * |c| * |Gv|
        ≤ 2 * ρ * |c| * (C₀ * (Real.pi / 2) * (1 + w) ^ (-lam)) := by
          gcongr
      _ = 2 * |c| * C₀ * (Real.pi / 2) * (ρ * (1 + w) ^ (-lam)) := by ring
      _ ≤ 2 * |c| * C₀ * (Real.pi / 2) * ρ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [hpow1, hρ, hrpow1]
  have hB : |c * (p * Z * w * Gw + R * Gt)| ≤ |c| * (p * C₀ * (Real.pi / 2) + C₀) * ρ := by
    have hsum : |p * Z * w * Gw + R * Gt| ≤ (p * C₀ * (Real.pi / 2) + C₀) * ρ := by
      calc |p * Z * w * Gw + R * Gt| ≤ |p * Z * w * Gw| + |R * Gt| := abs_add_le _ _
        _ ≤ p * C₀ * (Real.pi / 2) * ρ + C₀ * ρ := by
            refine add_le_add ?_ ?_
            · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hw]
              calc p * |Z| * w * |Gw|
                  ≤ p * ρ * w * (C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1)) := by gcongr
                _ = p * C₀ * (Real.pi / 2) * (ρ * (w * (1 + w) ^ (-lam - 1))) := by ring
                _ ≤ p * C₀ * (Real.pi / 2) * (ρ * 1) := by
                    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow2 hρ) ?_
                    positivity
                _ = p * C₀ * (Real.pi / 2) * ρ := by ring
            · rw [abs_mul]
              calc |R| * |Gt| ≤ ρ * (C₀ * (1 + w) ^ (-lam)) := by gcongr
                _ = C₀ * (ρ * (1 + w) ^ (-lam)) := by ring
                _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left (by nlinarith [hpow1, hρ, hrpow1]) hC₀
        _ = (p * C₀ * (Real.pi / 2) + C₀) * ρ := by ring
    calc |c * (p * Z * w * Gw + R * Gt)| = |c| * |p * Z * w * Gw + R * Gt| := by rw [abs_mul]
      _ ≤ |c| * ((p * C₀ * (Real.pi / 2) + C₀) * ρ) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg c)
      _ = |c| * (p * C₀ * (Real.pi / 2) + C₀) * ρ := by ring
  calc |2 * Z * c * Gv + c * (p * Z * w * Gw + R * Gt)|
      ≤ |2 * Z * c * Gv| + |c * (p * Z * w * Gw + R * Gt)| := abs_add_le _ _
    _ ≤ 2 * |c| * C₀ * (Real.pi / 2) * ρ + |c| * (p * C₀ * (Real.pi / 2) + C₀) * ρ :=
        add_le_add hA hB
    _ = |c| * C₀ * (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1) * ρ := by ring

/-- The pointwise bound `|ψ/r| ≤ |c| C₀ (π/2) ρ` for `r > 0`. -/
theorem abs_div_merPsiT_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} {C₀ lam : ℝ}
    (hB : 0 < B (Physical.clockInv C t)) (hlam : 0 < lam) (hC₀ : 0 ≤ C₀)
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam)) :
    ∀ r z : ℝ, 0 < r →
      |Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z / r|
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) * Work.Cyl.rhoP r z := by
  intro r z hr
  rw [Work.FTS.BSIdentP.Dev5.merPsiT_div_fst (τ := Physical.clockInv C t) (α := α)
    (A := A) (B := B) (Φ := Φ) (C := C) (t := t) rfl hr]
  have hρnn : 0 ≤ Work.Cyl.rhoP r z := Work.Cyl.rhoP_nonneg r z
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
      / B (Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos hρpos _) hB
  have hθ : |Work.Cyl.thetaP r z| < Real.pi / 2 :=
    Work.FTS.BSIdent.Cyl.abs_thetaP_lt r z
  have hcos : 0 < Real.cos (Work.Cyl.thetaP r z) := Work.Cyl.cos_thetaP_pos hr z
  have hG := abs_GG_le_cos (Φ := Φ) (τ := Physical.clockInv C t) (C₀ := C₀) (lam := lam)
    hC₀ h0 hrate hw hθ
  have hdiv : |Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z) / Real.cos (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2)
        * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
            / B (Physical.clockInv C t)) ^ (-lam) := by
    rw [abs_div, abs_of_pos hcos, div_le_iff₀ hcos]
    calc |Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t)
          (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
          (Work.Cyl.thetaP r z)|
        ≤ C₀ * (Real.pi / 2) * Real.cos (Work.Cyl.thetaP r z)
            * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
                / B (Physical.clockInv C t)) ^ (-lam) := hG
      _ = (C₀ * (Real.pi / 2)
            * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
                / B (Physical.clockInv C t)) ^ (-lam)) * Real.cos (Work.Cyl.thetaP r z) := by
          ring
  have hle1 : (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
      / B (Physical.clockInv C t)) ^ (-lam) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hw]) (by linarith)
  calc |Work.Cyl.rhoP r z * (A (Physical.clockInv C t))⁻¹
        * (Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t)
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
            (Work.Cyl.thetaP r z) / Real.cos (Work.Cyl.thetaP r z))|
      = Work.Cyl.rhoP r z * |(A (Physical.clockInv C t))⁻¹|
        * |Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t)
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
            (Work.Cyl.thetaP r z) / Real.cos (Work.Cyl.thetaP r z)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hρnn]
    _ ≤ Work.Cyl.rhoP r z * |(A (Physical.clockInv C t))⁻¹|
        * (C₀ * (Real.pi / 2)
            * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
                / B (Physical.clockInv C t)) ^ (-lam)) :=
        mul_le_mul_of_nonneg_left hdiv (mul_nonneg hρnn (abs_nonneg _))
    _ ≤ Work.Cyl.rhoP r z * |(A (Physical.clockInv C t))⁻¹| * (C₀ * (Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left
          (by
            have h := mul_le_mul_of_nonneg_left hle1
              (by positivity : (0:ℝ) ≤ C₀ * (Real.pi / 2))
            simpa using h)
          (mul_nonneg hρnn (abs_nonneg _))
    _ = |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) * Work.Cyl.rhoP r z := by ring

end Work.FTS.BSIdentP.Levels
