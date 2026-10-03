import Mathlib
import Submission.Work.FIArea2.R6.Inputs6
import Submission.Work.FIArea2.R6.Area6eDefs
import Submission.Work.FIArea2.R6.Assembly6
import Submission.Work.FIArea2.R6.sec9ErrSum6_arith
import Submission.Work.FIArea2.R6.BFun29

/-!
# `FIArea2/R6/KCap` — the §9 lacunarity input with the exponent cap raised to `2^27`

The cap `K ≤ 2^10` of `R6/Inputs6.LacProp` is not intrinsic to the §9 estimate: the only place it
enters is the logarithmic conversion `R6/sec9ErrSum6_arith.sec9log`, which needs
`1 + 2(8 + K + 4) ≤ bFun η`.  Since `bFun η ≥ 2^28` for `0 < η < 3/32` (`R6/BFun29`), the cap
`K ≤ 2^26 + 200` is affordable, and that is exactly what the cube-cutoff box estimate
(`R6/uboxSum_le_dsum3` → `R6/ubox_bound3`) produces.

This module is the parallel chain required by the lead's decision of 2026-09-30: `LacProp` and
every file below it stay untouched; `LacPropK` and the re-proved §9 arithmetic live here.
-/

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The lacunarity input of §9 with the exponent cap `Kmax`.**  This is verbatim
`R6/Inputs6.LacProp` with `2 ^ 10` replaced by `Kmax`. -/
def LacPropK (Kmax : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, K ≤ Kmax ∧
    ∀ (H : ℝ), 1 ≤ H → ∀ (R : ℕ), 1 ≤ R →
      (∑' h : ℤ × ℤ, (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
        * (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
            (Nat.gcd u1.natAbs u2.natAbs : ℝ)
              * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
        ≤ C * (H ^ 2 + 1) * ((((2 * R + 1 : ℕ)) : ℝ) ^ 2)
            * (Real.log (H + R + 2)) ^ K

/-- The cap is monotone. -/
theorem LacPropK_mono {Kmax Kmax' : ℕ} (h : Kmax ≤ Kmax')
    (hL : Work.FIArea2.R6.LacPropK Kmax) : Work.FIArea2.R6.LacPropK Kmax' := by
  obtain ⟨C, hC, K, hK, hb⟩ := hL
  exact ⟨C, hC, K, le_trans hK h, hb⟩

/-- `LacProp` is the case `Kmax = 2^10`. -/
theorem LacPropK_of_LacProp (h : Work.FIArea2.R6.LacProp) :
    Work.FIArea2.R6.LacPropK (2 ^ 10) := h

/-- The case `Kmax = 2^10` is `LacProp`. -/
theorem LacProp_of_LacPropK (h : Work.FIArea2.R6.LacPropK (2 ^ 10)) :
    Work.FIArea2.R6.LacProp := h

/-- **The logarithmic conversion**, at the raised cap `KL ≤ 2^26 + 200`:
`(log N + 2)·(log(H+R+2))^{8+KL+4} ≤ 2·(log N)^{bFun η}`,
using `N ≥ 8`, `0 < η < 3/32`, `bFun η ≥ 2^28` and `1 + 2(8+KL+4) ≤ 2^27 + 425 ≤ 2^28`. -/
lemma sec9logK (Pa : Work.FITop.Params) (KL : ℕ) (hKL : KL ≤ 2 ^ 26 + 200) (hN8 : 8 ≤ Pa.N)
    (hη0 : 0 < Pa.η) (hη32 : Pa.η < 3 / 32) :
    (Real.log Pa.N + 2) * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)
      ≤ 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log Pa.N := log_N_ge_two Pa hN8
  have hL1 : (1 : ℝ) ≤ Real.log Pa.N := by linarith
  have hLpos : (0 : ℝ) < Real.log Pa.N := by linarith
  have harg1 : (1 : ℝ) ≤ Work.FIPlan.Hscale Pa.M Pa.N
      + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2 := by
    have hHpos : (0 : ℝ) < Work.FIPlan.Hscale Pa.M Pa.N := by
      rw [Work.FIPlan.Hscale]
      exact mul_pos (Real.rpow_pos_of_pos (by linarith [Pa.hM1]) _) (Real.rpow_pos_of_pos hNpos _)
    have hR : (0 : ℝ) ≤ (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) := by positivity
    linarith
  have hXnn : (0 : ℝ) ≤ (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
      + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4) :=
    pow_nonneg (Real.log_nonneg harg1) _
  have hX : (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
      + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)
      ≤ (Real.log Pa.N) ^ (2 * (8 + KL + 4)) :=
    Work.FIArea2.R6.log_pow_le_six Pa hN8 (8 + KL + 4)
  have hE' : 2 * (8 + KL + 4) ≤ 2 ^ 27 + 424 := by omega
  have hb : 1 + ((2 * (8 + KL + 4) : ℕ) : ℝ) ≤ Work.FITop4.bFun Pa.η := by
    have h28 := Work.FIArea2.R6.bFun_ge_two_pow_28 Pa.η hη0 hη32
    have hcast : ((2 * (8 + KL + 4) : ℕ) : ℝ) ≤ (2 : ℝ) ^ 27 + 424 := by exact_mod_cast hE'
    have hnum : (1 : ℝ) + ((2 : ℝ) ^ 27 + 424) ≤ (2 : ℝ) ^ 28 := by norm_num
    linarith
  have key : (2 * Real.log Pa.N) * (Real.log Pa.N) ^ (2 * (8 + KL + 4))
      = 2 * (Real.log Pa.N) ^ (1 + ((2 * (8 + KL + 4) : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (Real.log Pa.N) (2 * (8 + KL + 4))]
    have h2 : (2 : ℝ) * Real.log Pa.N = 2 * (Real.log Pa.N) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [h2, mul_assoc, ← Real.rpow_add hLpos]
  calc (Real.log Pa.N + 2) * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)
      ≤ (2 * Real.log Pa.N) * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4) := by
        apply mul_le_mul_of_nonneg_right _ hXnn
        linarith
    _ ≤ (2 * Real.log Pa.N) * (Real.log Pa.N) ^ (2 * (8 + KL + 4)) :=
        mul_le_mul_of_nonneg_left hX (by linarith)
    _ = 2 * (Real.log Pa.N) ^ (1 + ((2 * (8 + KL + 4) : ℕ) : ℝ)) := key
    _ ≤ 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_le hL1 hb

/-- **The §9 arithmetic at the raised cap.**  Same as `R6/sec9ErrSum6_arith.sec9ErrSum6_arith`
except that the lacunarity exponent is only bounded by `2^26 + 200`. -/
theorem sec9ErrSum6_arithK (Pa : Work.FITop.Params) (CZ CL C : ℝ) (KL : ℕ)
    (hCZ : 0 < CZ) (hCL : 0 < CL) (hC : 0 < C) (hKL : KL ≤ 2 ^ 26 + 200) (hN8 : 8 ≤ Pa.N)
    (hη0 : 0 < Pa.η) (hη32 : Pa.η < 3 / 32) {β : GaussianInt → ℂ}
    (hErr : Work.FIArea2.R6.sec9ErrSum6 Pa β
      ≤ Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
          * Work.FIArea2.R6.sec9Psum6 Pa β)
    (hPsum : Work.FIArea2.R6.sec9Psum6 Pa β
      ≤ C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
          * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
              * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
          * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
              + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)) :
    Work.FIArea2.R6.sec9ErrSum6 Pa β
      ≤ 256 * 128 * 2 * C * CZ * CL * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log Pa.N := log_N_ge_two Pa hN8
  have hK1nn : 0 ≤ Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2)) := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.rpow_nonneg hNpos.le _)
  have hstep1 : Work.FIArea2.R6.sec9ErrSum6 Pa β ≤
      Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
        * (C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
            * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
                * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)) :=
    le_trans hErr (mul_le_mul_of_nonneg_left hPsum hK1nn)
  have hstep2 : Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
        * (C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
            * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
                * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4))
      ≤ 256 * 128 * 2 * C * CZ * CL * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
    have hG := sec9geom Pa hN8
    have hLb : 256 * (Real.log Pa.N + 2)
        * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
            + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)
        ≤ 256 * 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
      have hinner := sec9logK Pa KL hKL hN8 hη0 hη32
      have hmul := mul_le_mul_of_nonneg_left hinner (by norm_num : (0 : ℝ) ≤ 256)
      calc 256 * (Real.log Pa.N + 2)
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)
          = 256 * ((Real.log Pa.N + 2)
              * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                  + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)) := by ring
        _ ≤ 256 * (2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)) := hmul
        _ = 256 * 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by ring
    have hP3nn : 0 ≤ C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) := by
      have h1 : 0 < C * (CZ * CL) := mul_pos hC (mul_pos hCZ hCL)
      have h2 : 0 < Pa.ϑ⁻¹ := inv_pos.mpr Pa.hϑ0
      have h3 : 0 ≤ Pa.τ ^ (2 : ℕ) := by rw [pow_two]; exact mul_self_nonneg Pa.τ
      exact mul_nonneg (mul_nonneg h1.le h2.le) h3
    have hGnn : 0 ≤ 128 * Pa.N ^ 2 := by positivity
    have hcnn : 0 ≤ 256 * (Real.log Pa.N + 2)
        * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
            + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4) := by
      apply mul_nonneg
      · exact mul_nonneg (by norm_num) (by linarith)
      · exact pow_nonneg (Real.log_nonneg (by
          have hHpos : (0 : ℝ) < Work.FIPlan.Hscale Pa.M Pa.N := by
            rw [Work.FIPlan.Hscale]
            exact mul_pos (Real.rpow_pos_of_pos (by linarith [Pa.hM1]) _)
              (Real.rpow_pos_of_pos hNpos _)
          have hR : (0 : ℝ) ≤ (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) := by positivity
          linarith)) _
    have hAB : (Real.sqrt Pa.M * Pa.N ^ (-(1 : ℝ) / 2)
          * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
              * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2))
        * (256 * (Real.log Pa.N + 2)
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4))
        ≤ (128 * Pa.N ^ 2)
          * (256 * 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)) :=
      mul_le_mul hG hLb hcnn hGnn
    have hab2 := mul_le_mul_of_nonneg_right hAB hP3nn
    calc Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
          * (C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
              * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
                  * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
              * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                  + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4))
        = (Real.sqrt Pa.M * Pa.N ^ (-(1 : ℝ) / 2)
              * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
                  * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2))
            * (256 * (Real.log Pa.N + 2)
                * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                    + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4))
            * (C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)) := by ring
      _ ≤ (128 * Pa.N ^ 2)
            * (256 * 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η))
            * (C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)) := hab2
      _ = 256 * 128 * 2 * C * CZ * CL * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
            * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by ring
  exact le_trans hstep1 hstep2

end

end Work.FIArea2.R6
