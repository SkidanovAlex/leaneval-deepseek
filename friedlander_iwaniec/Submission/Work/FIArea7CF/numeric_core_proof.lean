/-
# `Submission.Work.FIArea7.numeric_core_proof`

The proof of `Work.FIArea7.NumericCore`, the pure real-variable core of the assembly
`Work.FIArea7.Area7Uni6_of_pieces` (*FI* (17.19)).

`NumericCore` says: with the two mass caps, `X⁸ ≤ N^δ₁` (`δ₁ < 3/32`), `K ≍ X³(log(N+2))²⁰`,
`UB ≤ 4θN+2` and `θ ≤ 1`, the sum of the four error terms of the (17.10) assembly is
`≤ c(Pz⁻¹+X⁻¹)N²log N` for `N ≥ N₀`.  Each of the four terms is bounded separately, on the
region where the *power* `N^{3δ₁/8}` dominates every power of a logarithm that occurs:

* the low term `C_L` (delegated as `nc_termL`), bounded by `M·X⁻¹N²log N`;
* the high term `C_H` (delegated as `nc_termH`), likewise;
* the mollifier term `C_E` (delegated as `nc_termE`), likewise;
* the elementary guard term `C_G`, using `log(N+2) ≤ 2 log N`.

The threshold `N₀` produced here is (necessarily) astronomically large: `δ₁` may be arbitrarily
small, and the absorption of the polylogarithmic factors `(log N)^{25}` requires
`N^{3δ₁/16} ≥ (log N)^{25}`.  This is harmless: `N₀` only has to *exist*, and the consumer
`Area7Uni6_of_pieces` takes `(max N₀ 1)⁴ ≤ Pa.x ≤ Pa.N`.
-/
import Mathlib
import Submission.Work.FIArea7CF.Area7Assembly6
import Submission.Work.FIArea7.NCBasic
import Submission.Work.FIArea7.nc_termL
import Submission.Work.FIArea7.nc_termH
import Submission.Work.FIArea7.nc_termE

set_option autoImplicit false

namespace Work.FIArea7

open scoped BigOperators

theorem numeric_core_proof : Work.FIArea7.NumericCore := by
  intro C_L C_H C_E C_G c₁ Clat δ₁ hCL hCH hCE hCG hc₁ hCl hδ0 hδ32
  obtain ⟨NL, ML, hML, htermL⟩ := nc_termL C_L c₁ δ₁ hCL hc₁ hδ0 hδ32
  obtain ⟨NH, MH, hMH, htermH⟩ := nc_termH C_H Clat δ₁ hCH hCl hδ0 hδ32
  obtain ⟨NE, ME, hME, htermE⟩ := nc_termE C_E hCE
  refine ⟨ML + MH + ME + 2 * C_G, max (max NL NH) (max NE 0), by positivity, ?_⟩
  intro N X K θ Pz UB E2v hN0 hN3 hX1 hθ0 hθ1 hX8 hPz0 hK1 hKg hKu hUB0 hUB hE2nn hE2'
  -- ### the thresholds
  have hNL' : NL ≤ N :=
    le_trans (le_trans (le_max_left NL NH) (le_max_left _ _)) hN0
  have hNH' : NH ≤ N :=
    le_trans (le_trans (le_max_right NL NH) (le_max_left _ _)) hN0
  have hNE' : NE ≤ N :=
    le_trans (le_trans (le_max_left NE 0) (le_max_right _ _)) hN0
  -- ### the four estimates, in the shape `≤ M · X⁻¹N²log N`
  have hA : C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
      * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
          + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
      ≤ ML * X⁻¹ * N ^ 2 * Real.log N :=
    htermL hN3 hNL' hX1 hX8 hK1 hKg hKu
  have hB : C_H * (1 + Clat)
      * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3)
      * (Real.log ((K : ℝ) + 2)) ^ 2
      * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
      ≤ MH * X⁻¹ * N ^ 2 * Real.log N :=
    htermH hN3 hNH' hX1 hθ0 hθ1 hX8 hK1 hKg hKu hUB0 hUB
  have hC : C_E * (X + 1) * (N + 1) * (Real.log (N + 2)) ^ 4 * E2v / (K : ℝ)
      ≤ ME * X⁻¹ * N ^ 2 * Real.log N :=
    htermE hN3 hNE' hX1 hθ0 hθ1 hK1 hKg hE2nn hE2'
  -- ### replace the factor `X⁻¹` by the larger factor `Pz⁻¹ + X⁻¹`
  have hcore : X⁻¹ * (N ^ 2 * Real.log N) ≤ (Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N) := by
    have hle : X⁻¹ ≤ Pz⁻¹ + X⁻¹ := by
      have := inv_pos.mpr hPz0
      linarith
    have hnn : (0 : ℝ) ≤ N ^ 2 * Real.log N := by
      have h1 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
      positivity
    exact mul_le_mul_of_nonneg_right hle hnn
  have hA' : C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
      * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
          + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
      ≤ ML * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := by
    calc C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
              + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
        ≤ ML * X⁻¹ * N ^ 2 * Real.log N := hA
      _ = ML * (X⁻¹ * (N ^ 2 * Real.log N)) := by ring
      _ ≤ ML * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) :=
          mul_le_mul_of_nonneg_left hcore hML.le
  have hB' : C_H * (1 + Clat)
      * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3)
      * (Real.log ((K : ℝ) + 2)) ^ 2
      * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
      ≤ MH * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := by
    calc C_H * (1 + Clat)
          * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
        ≤ MH * X⁻¹ * N ^ 2 * Real.log N := hB
      _ = MH * (X⁻¹ * (N ^ 2 * Real.log N)) := by ring
      _ ≤ MH * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) :=
          mul_le_mul_of_nonneg_left hcore hMH.le
  have hC' : C_E * (X + 1) * (N + 1) * (Real.log (N + 2)) ^ 4 * E2v / (K : ℝ)
      ≤ ME * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := by
    calc C_E * (X + 1) * (N + 1) * (Real.log (N + 2)) ^ 4 * E2v / (K : ℝ)
        ≤ ME * X⁻¹ * N ^ 2 * Real.log N := hC
      _ = ME * (X⁻¹ * (N ^ 2 * Real.log N)) := by ring
      _ ≤ ME * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) :=
          mul_le_mul_of_nonneg_left hcore hME.le
  -- ### the elementary guard term
  have hD' : C_G * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log (N + 2)
      ≤ (2 * C_G) * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := by
    have hlog : Real.log (N + 2) ≤ 2 * Real.log N := log_add_two_le_two_mul_log (by linarith)
    have hnn : (0 : ℝ) ≤ C_G * (Pz⁻¹ + X⁻¹) * N ^ 2 := by
      have := inv_pos.mpr hPz0
      positivity
    calc C_G * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log (N + 2)
        = (C_G * (Pz⁻¹ + X⁻¹) * N ^ 2) * Real.log (N + 2) := by ring
      _ ≤ (C_G * (Pz⁻¹ + X⁻¹) * N ^ 2) * (2 * Real.log N) :=
          mul_le_mul_of_nonneg_left hlog hnn
      _ = (2 * C_G) * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := by ring
  have hsum :
      C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
              + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
      + C_H * (1 + Clat)
          * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
      + C_E * (X + 1) * (N + 1) * (Real.log (N + 2)) ^ 4 * E2v / (K : ℝ)
      + C_G * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log (N + 2)
      ≤ ML * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N))
        + MH * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N))
        + ME * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N))
        + (2 * C_G) * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := by
    linarith [hA', hB', hC', hD']
  calc
    C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
            + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
    + C_H * (1 + Clat)
        * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
    + C_E * (X + 1) * (N + 1) * (Real.log (N + 2)) ^ 4 * E2v / (K : ℝ)
    + C_G * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log (N + 2)
      ≤ ML * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N))
        + MH * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N))
        + ME * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N))
        + (2 * C_G) * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := hsum
    _ = (ML + MH + ME + 2 * C_G) * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log N := by ring

end Work.FIArea7
