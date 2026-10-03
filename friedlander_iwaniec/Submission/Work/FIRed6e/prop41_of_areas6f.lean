/- **The amended round-6 composition against the stronger area-4 contract.**

This is the composition of `Submission/Work/FIRed6e/prop41_of_areas6e.lean` — `Area7_6b` in place of
`Area7_6`, the *clean* area 6 `Work.FITop4.Area6_6e` (FI (5.7)+(5.8) only) in place of the
τ-carrying `Area6_6c`, and the τ-removal `Work.FITop4.TauRemoval6` (FI (10.4)) paying the (5.9)
truncation inside the `N²(log N)^{-σ}` (5.25) budget — with area 4 consumed at the strengthened
hypotheses `Work.FITop4.Area4_6c` instead of `Work.FITop4.Area4_6`.

`Area4_6c` (`Submission/Work/FITop4/Areas6f.lean`, design
`Submission/Work/FIArea4/AREA4_ENGINES_LEAD.md` §3.1) adds three hypotheses to area 4, all of them
available at the single call site of the composition:

1. the pins `Pa.θ = thetaOf Pa.x Asave` and `Pa.τ = tauOf Pa.x Asave` (the reduction's `hPiece`
   supplies both);
2. the polar box is axis-free (`Work.FIRed6Axis.FarPiece_isAxisFree`, from the far-piece
   hypothesis of `ReductionAxis`);
3. `(log N)² ≤ X`, which holds at `X = Xcut Pa σ = ⌈(log N)^{3σ+3}⌉` by
   `log_sq_le_Xcut` below.

Nothing else is changed: `ReductionAxis`, `ClassSplit6`, `Area1Sieve6`, `Area2_6b`, `Area3_6`,
`Area6_6e`, `TauRemoval6` and `Area7_6b` are consumed exactly as in the area-4-`Area4_6`
composition, together with the per-piece bundle `AreaBounds6e` of
`Submission.Work.FIRed6e.Bundle6e` and the per-piece budget `budget6e` copied verbatim from that
file.
-/
import Mathlib
import Submission.Work.FIRed6e.Bundle6e
import Submission.Work.FIRed6e.isBetaCoeff6_eq_tauCut_clean
import Submission.Work.FIRed6e.prop102_of_UVW6e
import Submission.Work.FIRed6Axis.Statement
import Submission.Work.FIRed6Axis.Assembly
import Submission.Work.FIRed6Axis.prop41of.Bundle
import Submission.Work.FITop4.Red6.Dform_le_budget6
import Submission.Work.FITop4.Red6.eventually_Xcut_cube_le
import Submission.Work.FITop4.Areas6b
import Submission.Work.FITop4.Areas6c
import Submission.Work.FITop4.Areas6e
import Submission.Work.FITop4.Areas6f
import Submission.Work.FITop4.Areas6
import Submission.Work.FITop4.Red5.BformPi_tau_truncation
import Submission.Work.FITop4.Red5.numHyp_proof_save
import Submission.Work.FITop4.Red5.pieceFacts_proof_save
import Submission.Work.FITop3.Majorant.fhat_upper
import Submission.Work.FITop.SingleDvdTauSqLe

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.FIRed6e

open Finset
open Work.FITop4
open Work.FIRed6Axis
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. The cut dominates `(log N)²` -/

/-- At the composition's cut `Xcut Pa σ = ⌈(log N)^{3σ+3}⌉`, one has `(log N)² ≤ Xcut` as soon as
`log N ≥ 1`: the cut is `⌈·⌉₊` of a power of `log N` whose exponent `3σ + 3` exceeds `2`
(`σ = sigmaChoice Asave > 0`), and `a^·` is monotone on the exponent for a base `a ≥ 1`.  This is
the third of the three extra hypotheses of `Work.FITop4.Area4_6c`, and it is the only fact the
composition needs to supply for them beyond `hPiece`'s pins and `FarPiece_isAxisFree`. -/
lemma log_sq_le_Xcut (Pa : Work.FITop.Params) (h : 1 ≤ Real.log Pa.N) :
    (Real.log Pa.N) ^ (2 : ℕ) ≤ (Xcut Pa (sigmaChoice Asave) : ℝ) := by
  have hσ : 0 < sigmaChoice Asave := by
    unfold sigmaChoice
    have hA' : 0 < Aprime Asave := by
      unfold Aprime; have h := Asave_pos; positivity
    linarith [Asave_pos, hA']
  have h2 : (((2 : ℕ)) : ℝ) ≤ 3 * sigmaChoice Asave + 3 := by
    push_cast
    linarith
  calc (Real.log Pa.N) ^ (2 : ℕ) = (Real.log Pa.N) ^ (((2 : ℕ)) : ℝ) :=
        (Real.rpow_natCast (Real.log Pa.N) 2).symm
    _ ≤ (Real.log Pa.N) ^ (3 * sigmaChoice Asave + 3) :=
        Real.rpow_le_rpow_of_exponent_le h h2
    _ ≤ (Xcut Pa (sigmaChoice Asave) : ℝ) := by
        unfold Xcut
        exact Nat.le_ceil _

/-- `D ≤ log x` eventually. -/
private lemma eventually_log_ge_of (D : ℝ) : ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → D ≤ Real.log (x : ℝ) := by
  rcases le_or_gt 0 D with h | h
  · exact Work.FITop4.Numeric4.log_dominance.2.2.2.1 D h
  · obtain ⟨x₀, hx₀⟩ := Work.FITop4.Numeric4.log_dominance.2.2.2.1 0 le_rfl
    exact ⟨x₀, fun x hx => le_trans (le_of_lt h) (hx₀ x hx)⟩

/-! ## 1. The per-piece Cauchy endpoint -/

/-- The square root of the (5.20) budget in closed form. -/
private lemma sqrt_Tbudget_of (Pa : Work.FITop.Params) :
    Real.sqrt (Tbudget Pa)
      = Pa.ϑ * Pa.θ ^ (2 : ℕ) * Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
          * (Real.log (Pa.M * Pa.N)) ^ (4 : ℕ) := by
  have hMpos : (0:ℝ) < Pa.M := lt_of_lt_of_le zero_lt_one Pa.hM1
  have hNpos : (0:ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  have hlognn : (0:ℝ) ≤ Real.log (Pa.M * Pa.N) :=
    Real.log_nonneg (by nlinarith [Pa.hM1, Pa.hN1])
  have hBnn : (0:ℝ) ≤ Pa.ϑ * Pa.θ ^ (2:ℕ) * Pa.M ^ ((1:ℝ)/4) * Pa.N ^ ((3:ℝ)/4)
      * (Real.log (Pa.M * Pa.N)) ^ (4:ℕ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt Pa.hϑ0)
      (pow_nonneg (le_of_lt Pa.hθ0) 2)) (Real.rpow_nonneg (le_of_lt hMpos) _))
      (Real.rpow_nonneg (le_of_lt hNpos) _)) (pow_nonneg hlognn _)
  have hM2 : (Pa.M ^ ((1:ℝ)/4))^2 = Pa.M ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_natCast (Pa.M ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul (le_of_lt hMpos)]
    norm_num
  have hN2 : (Pa.N ^ ((3:ℝ)/4))^2 = Pa.N ^ ((3:ℝ)/2) := by
    rw [← Real.rpow_natCast (Pa.N ^ ((3:ℝ)/4)) 2, ← Real.rpow_mul (le_of_lt hNpos)]
    norm_num
  have hT2 : (Pa.θ^(2:ℕ))^2 = Pa.θ^(4:ℕ) := by rw [← pow_mul]
  have hG2 : ((Real.log (Pa.M*Pa.N))^(4:ℕ))^2 = (Real.log (Pa.M*Pa.N))^(8:ℕ) := by
    rw [← pow_mul]
  have hsq : (Pa.ϑ * Pa.θ ^ (2:ℕ) * Pa.M ^ ((1:ℝ)/4) * Pa.N ^ ((3:ℝ)/4)
      * (Real.log (Pa.M * Pa.N)) ^ (4:ℕ))^2
      = Pa.ϑ^(2:ℕ) * Pa.θ^(4:ℕ) * Pa.M^((1:ℝ)/2) * Pa.N^((3:ℝ)/2)
          * (Real.log (Pa.M*Pa.N))^(8:ℕ) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hT2, hM2, hN2, hG2]
  rw [show Tbudget Pa = (Pa.ϑ * Pa.θ ^ (2:ℕ) * Pa.M ^ ((1:ℝ)/4) * Pa.N ^ ((3:ℝ)/4)
      * (Real.log (Pa.M * Pa.N)) ^ (4:ℕ))^2 by rw [hsq]; unfold Tbudget; ring]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hBnn]

/-- The per-piece Cauchy bound: `Dform ≤ (1+s)·Tbudget` gives
`√(100·M·Dform) ≤ 10√(1+s)·ϑθ²(MN)^{3/4}·X^4` for any `X ≥ log(MN)`. -/
private lemma sqrt_piece_le_of (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ)
    (s X : ℝ) (hD : Dform Pa f β ≤ (1+s) * Tbudget Pa) (hs : 0 ≤ 1+s)
    (hX : Real.log (Pa.M * Pa.N) ≤ X) :
    Real.sqrt (100 * Pa.M * Dform Pa f β)
      ≤ 10 * Real.sqrt (1+s) * Pa.ϑ * Pa.θ^(2:ℕ) * ((Pa.M * Pa.N)^((3:ℝ)/4)) * X^(4:ℕ) := by
  have hMpos : (0:ℝ) < Pa.M := lt_of_lt_of_le zero_lt_one Pa.hM1
  have hNpos : (0:ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  have hlognn : (0:ℝ) ≤ Real.log (Pa.M * Pa.N) :=
    Real.log_nonneg (by nlinarith [Pa.hM1, Pa.hN1])
  have hMNpos : (0:ℝ) < Pa.M * Pa.N := mul_pos hMpos hNpos
  have hTnn : (0:ℝ) ≤ Tbudget Pa := by
    unfold Tbudget
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt Pa.hϑ0) 2)
      (pow_nonneg (le_of_lt Pa.hθ0) 4)) (Real.rpow_nonneg (le_of_lt hMpos) _))
      (Real.rpow_nonneg (le_of_lt hNpos) _)) (pow_nonneg hlognn _)
  have hMN34 : Pa.M ^ ((3:ℝ)/4) * Pa.N ^ ((3:ℝ)/4) = (Pa.M * Pa.N) ^ ((3:ℝ)/4) :=
    (Real.mul_rpow (le_of_lt hMpos) (le_of_lt hNpos)).symm
  have hlog4 : (Real.log (Pa.M * Pa.N))^(4:ℕ) ≤ X^(4:ℕ) :=
    pow_le_pow_left₀ hlognn hX 4
  have hkey : Pa.M ^ ((1:ℝ)/2) * Real.sqrt (Tbudget Pa)
      = Pa.ϑ * Pa.θ^(2:ℕ) * Pa.M^((3:ℝ)/4) * Pa.N^((3:ℝ)/4)
          * (Real.log (Pa.M*Pa.N))^(4:ℕ) := by
    rw [sqrt_Tbudget_of Pa]
    have h : Pa.M ^ ((1:ℝ)/2) * Pa.M ^ ((1:ℝ)/4) = Pa.M ^ ((3:ℝ)/4) := by
      rw [← Real.rpow_add hMpos, show (1:ℝ)/2 + ((1:ℝ)/4) = (3:ℝ)/4 by norm_num]
    rw [show Pa.M ^ ((1:ℝ)/2) * (Pa.ϑ * Pa.θ^(2:ℕ) * Pa.M ^ ((1:ℝ)/4) * Pa.N ^ ((3:ℝ)/4)
          * (Real.log (Pa.M*Pa.N))^(4:ℕ))
        = (Pa.M ^ ((1:ℝ)/2) * Pa.M ^ ((1:ℝ)/4)) * (Pa.ϑ * Pa.θ^(2:ℕ) * Pa.N ^ ((3:ℝ)/4)
            * (Real.log (Pa.M*Pa.N))^(4:ℕ)) by ring]
    rw [h]; ring
  have hstep : Real.sqrt (100 * Pa.M * Dform Pa f β)
      ≤ Real.sqrt (100 * Pa.M * ((1+s) * Tbudget Pa)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [hD, hMpos]
  have hsplit : Real.sqrt (100 * Pa.M * ((1+s) * Tbudget Pa))
      = 10 * Real.sqrt (1+s) * (Pa.M^((1:ℝ)/2) * Real.sqrt (Tbudget Pa)) := by
    rw [show (100:ℝ) * Pa.M * ((1+s) * Tbudget Pa)
        = 100 * (Pa.M * ((1+s) * Tbudget Pa)) by ring]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 100)]
    rw [show Real.sqrt (100:ℝ) = 10 by norm_num]
    rw [show Pa.M * ((1+s) * Tbudget Pa) = (1+s) * (Pa.M * Tbudget Pa) by ring]
    rw [Real.sqrt_mul hs]
    rw [Real.sqrt_mul (le_of_lt hMpos)]
    rw [Real.sqrt_eq_rpow Pa.M]
    ring
  have hbase : (0:ℝ) ≤ 10 * Real.sqrt (1+s) * Pa.ϑ * Pa.θ^(2:ℕ) * (Pa.M * Pa.N)^((3:ℝ)/4) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Real.sqrt_nonneg _)) (le_of_lt Pa.hϑ0)) (pow_nonneg (le_of_lt Pa.hθ0) 2))
      (Real.rpow_nonneg hMNpos.le _)
  have hstep2 : 10 * Real.sqrt (1+s) * (Pa.M^((1:ℝ)/2) * Real.sqrt (Tbudget Pa))
      ≤ 10 * Real.sqrt (1+s) * Pa.ϑ * Pa.θ^(2:ℕ) * (Pa.M * Pa.N)^((3:ℝ)/4) * X^(4:ℕ) := by
    rw [hkey]
    rw [show 10 * Real.sqrt (1+s) * (Pa.ϑ * Pa.θ^(2:ℕ) * Pa.M^((3:ℝ)/4) * Pa.N^((3:ℝ)/4)
            * (Real.log (Pa.M*Pa.N))^(4:ℕ))
        = 10 * Real.sqrt (1+s) * Pa.ϑ * Pa.θ^(2:ℕ) * (Pa.M^((3:ℝ)/4) * Pa.N^((3:ℝ)/4))
            * (Real.log (Pa.M*Pa.N))^(4:ℕ) by ring]
    rw [hMN34]
    exact mul_le_mul_of_nonneg_left hlog4 hbase
  exact le_trans (le_trans hstep (le_of_eq hsplit)) hstep2


/-! ## 2. The per-piece budget at the amended bundle `AreaBounds6e` -/

private lemma budget6b_fhat_nonneg (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (h : Work.FITop3.IsMajorant Pa (f)) :
    0 ≤ Work.FITop3.Fhat Pa f := by
  show 0 ≤ Work.FITop3.Fhat Pa (f)
  rw [Work.FITop3.Fhat]
  exact Finset.sum_nonneg fun u _ => div_nonneg (h.1 u) (Real.sqrt_nonneg _)

/-- `N^{-1/2}·N² = N^{3/2}` for `N > 0`. -/
private lemma budget6b_rpow_neg_half_mul_sq (N : ℝ) (hN : 0 < N) :
    N ^ (-(1 : ℝ) / 2) * N ^ 2 = N ^ ((3 : ℝ) / 2) := by
  rw [show N ^ 2 = N ^ (((2 : ℕ)) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_add hN,
    show -(1 : ℝ) / 2 + ((2 : ℕ) : ℝ) = (3 : ℝ) / 2 by norm_num]

private theorem budget6e (Pa : Work.FITop.Params) (f : ℤ → ℝ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (X : ℕ) (σ : ℝ) (c1 Cb C3b C3 cU cV cW cE C3max : ℝ)
    (hMaj : Work.FITop4.IsMajorant6 Pa f) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    (hσ : 0 < σ) (hN3 : 3 ≤ Pa.N) (hM16 : 16 ≤ Pa.M)
    (hcU : 0 ≤ cU) (hcV : 0 ≤ cV) (hcW : 0 ≤ cW) (hcE : 0 ≤ cE)
    (hAB : Work.FIRed6e.AreaBounds6e Pa f φ z0 β X σ c1 Cb C3b C3 cU cV cW cE)
    (hX : (Real.log Pa.N) ^ (3 * σ + 3) ≤ (X : ℝ))
    (hFh : Work.FITop3.Fhat Pa f ≤ 4 * Real.sqrt Pa.M)
    (hnum : Work.FITop4.NumHyp Pa.η Pa.x Pa σ c1 Cb C3max 1)
    (hC3le : C3 ≤ C3max) (hC3ble : C3b ≤ C3max) :
    Work.FITop3.Dform Pa (f) β
      ≤ (1 + cU + cV + cW + cE) * Work.FITop4.Tbudget Pa := by
  have hMpos : (0 : ℝ) < Pa.M := by linarith [Pa.hM1]
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hlogN : 0 ≤ Real.log Pa.N := by
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr Real.exp_one_lt_three
    have hle : Real.log 3 ≤ Real.log Pa.N :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hN3)
    linarith
  have hlogMN : 0 ≤ Real.log (Pa.M * Pa.N) := Real.log_nonneg (by nlinarith [Pa.hM1, Pa.hN1])
  obtain ⟨hAB1, hAB2, hAB3, hABV, hABU, hABW⟩ := hAB
  set s : ℝ := cU + cV + cW + cE with hs
  set T : ℝ := Work.FITop4.Tbudget Pa with hT
  have hsnn : 0 ≤ s := by rw [hs]; linarith
  have hTnn : 0 ≤ T := by
    rw [hT, Work.FITop4.Tbudget]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt Pa.hϑ0) 2)
      (pow_nonneg (le_of_lt Pa.hθ0) 4)) (Real.rpow_nonneg hMpos.le _))
      (Real.rpow_nonneg hNpos.le _)) (pow_nonneg hlogMN 8)
  set Wv : ℝ := (Real.log Pa.N) ^ (-σ) + (Pa.Pz : ℝ)⁻¹ * Real.log Pa.N with hW
  have hWnn : 0 ≤ Wv := by
    rw [hW]
    exact add_nonneg (Real.rpow_nonneg hlogN _) (mul_nonneg (by positivity) hlogN)
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hnum
  rw [← hT] at hn1 hn2 hn3 hn4
  rw [← hW] at hn4
  -- ## the three error terms of the areas are at most `T/8`
  have hA0 : c1 * Pa.τ ^ (2 : ℕ) * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
      + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
      * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) ≤ T / 8 := by linarith [hn3]
  have hB0 : Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2 * (Real.log Pa.N) ^ (bFun Pa.η)
      ≤ T / 8 := by linarith [hn2]
  have hτpos : 0 < Pa.τ := by
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have hlogpos : 0 < Real.log (Pa.x : ℝ) := Real.log_pos (by linarith)
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hlogpos _) Pa.hτ1
  have hEnn : 0 ≤ (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
      * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (add_nonneg (inv_nonneg.mpr (le_of_lt hτpos)) (le_of_lt Pa.hθ0))
      (pow_nonneg (le_of_lt Pa.hθ0) 4)) (Real.rpow_nonneg hMpos.le _))
      (Real.rpow_nonneg hNpos.le _)) (pow_nonneg hlogN _)
  have hC0mono : C3 * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
      * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)))
      ≤ C3max * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
      * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))) :=
    mul_le_mul_of_nonneg_right hC3le hEnn
  have hC0bmono : C3b * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
      * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)))
      ≤ C3max * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
      * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))) :=
    mul_le_mul_of_nonneg_right hC3ble hEnn
  have hC0 : C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
      * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) ≤ T / 8 := by
    linarith [hn1, hC0mono]
  have hC0b : C3b * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
      * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) ≤ T / 8 := by
    linarith [hn1, hC0bmono]
  -- ## the chain `Dform ≤ Dstar ≤ (D₀).re`
  have hDform1 : Work.FITop3.Dform Pa (f) β
      ≤ Work.FITop3.Dstar Pa (f) β + T / 8 := by
    have h := (hAB1 f φ z0 β hMaj hβ).2
    linarith [hA0]
  have hDstar1 : Work.FITop3.Dstar Pa (f) β
      ≤ (Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re + T / 4 := by
    have h := hAB2 f φ z0 β hMaj hβ
    have hre := Complex.re_le_norm
      ((Work.FITop3.Dstar Pa (f) β : ℂ)
        - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β)
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    linarith [h, hB0, hC0b]
  have hD0re : (Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re
      ≤ (Work.FITop3.Fhat Pa f * Pa.N ^ (-(1 : ℝ) / 2))
          * (Work.FITop4.Tbeta (Work.FITop.radN Pa) β).re + T / 8 := by
    have h := hAB3 f φ z0 β hMaj hβ
    have hre := Complex.re_le_norm
      (Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β
        - Work.FITop4.cMain6 (Work.FITop3.Fhat Pa f) Pa.N
            * Work.FITop4.Tbeta (Work.FITop.radN Pa) β)
    rw [Complex.sub_re] at hre
    have hcm : (Work.FITop4.cMain6 (Work.FITop3.Fhat Pa f) Pa.N
          * Work.FITop4.Tbeta (Work.FITop.radN Pa) β).re
        = (Work.FITop3.Fhat Pa f * Pa.N ^ (-(1 : ℝ) / 2))
          * (Work.FITop4.Tbeta (Work.FITop.radN Pa) β).re := by
      unfold Work.FITop4.cMain6
      rw [Complex.re_ofReal_mul]
    linarith [h, hC0, hcm]
  -- ## Proposition 10.2 for `T(β)` (the partition is `Red6.Tbeta_partition`)
  have hTB := prop102_of_UVW6e Pa X σ β hσ hN3 hX
    (Work.FITop4.Red6.Tbeta_partition (Pa := Pa) X (φ := φ) (z0 := z0) (β := β) hβ)
    cU cV cW cE hcU hcV hcW hcE hABU hABV hABW
  have hre : (Work.FITop4.Tbeta (Work.FITop.radN Pa) β).re ≤ s * (Pa.N ^ 2 * Wv) := by
    have h2 : Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ) + (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N
        = Pa.N ^ 2 * Wv := by rw [hW]; ring
    rw [h2] at hTB
    have h3 := Complex.re_le_norm (Work.FITop4.Tbeta (Work.FITop.radN Pa) β)
    rw [hs]
    linarith [h3, hTB]
  -- ## the main term: `Fhat6·N^{-1/2}·‖T(β)‖ ≤ s·T/2`
  have hFh' : Work.FITop3.Fhat Pa f ≤ 4 * Pa.M ^ ((1 : ℝ) / 2) := by
    have hs1 : Real.sqrt Pa.M = Pa.M ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow Pa.M
    linarith [hFh]
  have hcoe : 0 ≤ Work.FITop3.Fhat Pa f * Pa.N ^ (-(1 : ℝ) / 2) :=
    mul_nonneg (budget6b_fhat_nonneg Pa f (Work.FITop4.IsMajorant6.toMajorant hMaj))
      (Real.rpow_nonneg hNpos.le _)
  have hmain : (Work.FITop3.Fhat Pa f * Pa.N ^ (-(1 : ℝ) / 2))
      * (Work.FITop4.Tbeta (Work.FITop.radN Pa) β).re ≤ s * (T / 2) := by
    have hstep2 : (Work.FITop3.Fhat Pa f * Pa.N ^ (-(1 : ℝ) / 2)) * (s * (Pa.N ^ 2 * Wv))
        = Work.FITop3.Fhat Pa f * (s * (Pa.N ^ ((3 : ℝ) / 2) * Wv)) := by
      calc (Work.FITop3.Fhat Pa f * Pa.N ^ (-(1 : ℝ) / 2)) * (s * (Pa.N ^ 2 * Wv))
          = Work.FITop3.Fhat Pa f * (s * ((Pa.N ^ (-(1 : ℝ) / 2) * Pa.N ^ 2) * Wv)) := by ring
        _ = Work.FITop3.Fhat Pa f * (s * (Pa.N ^ ((3 : ℝ) / 2) * Wv)) := by
              rw [budget6b_rpow_neg_half_mul_sq Pa.N hNpos]
    have hnn : 0 ≤ s * (Pa.N ^ ((3 : ℝ) / 2) * Wv) :=
      mul_nonneg hsnn (mul_nonneg (Real.rpow_nonneg hNpos.le _) hWnn)
    have hkey8 : 16 * (Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) * Wv) ≤ T := by
      linarith [hn4]
    have hkey : 4 * (Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) * Wv) ≤ T / 2 := by
      have hxnn : 0 ≤ Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) * Wv :=
        mul_nonneg (mul_nonneg (Real.rpow_nonneg hMpos.le _) (Real.rpow_nonneg hNpos.le _)) hWnn
      linarith [hkey8, hxnn]
    calc (Work.FITop3.Fhat Pa f * Pa.N ^ (-(1 : ℝ) / 2))
          * (Work.FITop4.Tbeta (Work.FITop.radN Pa) β).re
        ≤ (Work.FITop3.Fhat Pa f * Pa.N ^ (-(1 : ℝ) / 2)) * (s * (Pa.N ^ 2 * Wv)) :=
          mul_le_mul_of_nonneg_left hre hcoe
      _ = Work.FITop3.Fhat Pa f * (s * (Pa.N ^ ((3 : ℝ) / 2) * Wv)) := hstep2
      _ ≤ (4 * Pa.M ^ ((1 : ℝ) / 2)) * (s * (Pa.N ^ ((3 : ℝ) / 2) * Wv)) :=
          mul_le_mul_of_nonneg_right hFh' hnn
      _ = s * (4 * (Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) * Wv)) := by ring
      _ ≤ s * (T / 2) := mul_le_mul_of_nonneg_left hkey hsnn
  have hD0final : (Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re
      ≤ s * (T / 2) + T / 8 := by linarith [hD0re, hmain]
  -- ## the final bookkeeping
  have hDform_final : Work.FITop3.Dform Pa (f) β ≤ (1 + s) * T := by
    have h1 : Work.FITop3.Dform Pa (f) β ≤ s * (T / 2) + T / 2 := by
      linarith [hDform1, hDstar1, hD0final]
    have h2 : s * (T / 2) + T / 2 ≤ (1 + s) * T := by
      have : (1 + s) * T - (s * (T / 2) + T / 2) = T * (1 / 2 + s / 2) := by ring
      nlinarith [hTnn, hsnn, this]
    linarith [h1, h2]
  have hc : (1 : ℝ) + cU + cV + cW + cE = 1 + s := by rw [hs]; ring
  rw [hc]
  exact hDform_final



/-! ## 3. The composition -/

/-- **The amended composition against the axis-aware reduction**: from the axis-aware reduction
`ReductionAxis` and the far-piece class split `ClassSplit6`, the areas 1–3 as before, the *stronger*
area 4 `Area4_6c`, the *clean* area 6 `Area6_6e` (no τ pin) and the amended area 7 `Area7_6b`
imply the frozen-exponent, `Π`-restricted target, once the (5.9) τ-removal `TauRemoval6` is paid
inside the `N²(log N)^{-σ}` budget. -/
theorem prop41_of_areas6f_of (hred : Work.FIRed6Axis.ReductionAxis)
    (hsplit : Work.FIRed6Axis.ClassSplit6) (hτ : Work.FITop4.TauRemoval6) :
    Work.FITop4.Area1Sieve6 → Work.FITop4.Area2_6b → Work.FITop4.Area3_6 →
      Work.FITop4.Area4_6c → Work.FITop4.Area6_6e → Work.FITop4.Area7_6b →
      Work.FITop4.Prop41StatementPiBig := by
  intro h1 h2 h3 h4 h5 h6
  intro η hη0 hη1
  obtain ⟨c1, x₀1, hc1, hA1⟩ := h1
  obtain ⟨Cb, C3b, x₀2, hCb, hC3b, hA2⟩ := h2 η hη0 hη1
  obtain ⟨C3, x₀3, hC3, hA3⟩ := h3 η hη0 hη1
  obtain ⟨cV, x₀4, hcV, hA4⟩ := h4 η hη0 hη1
  obtain ⟨cU, x₀6, hcU, hA6⟩ := h5 η hη0 hη1
  obtain ⟨δ7, cW, x₀7, hδ7, hcW, hA7⟩ := h6 η hη0 hη1
  obtain ⟨Cτ, x₀τr, hCτ, hTR⟩ := hτ
  have hC3maxpos : (0 : ℝ) < max C3b C3 := lt_of_lt_of_le hC3b (le_max_left _ _)
  have hσpos : 0 < sigmaChoice Asave := by
    unfold sigmaChoice
    have hA' : 0 < Aprime Asave := by
      unfold Aprime; have h := Asave_pos; positivity
    linarith [Asave_pos, hA']
  obtain ⟨x₀N, hNumAll⟩ := Work.FITop4.Red5.numHyp_proof_save η hη0 hη1 c1 Cb (max C3b C3) 1
    hc1 hCb hC3maxpos (by norm_num)
  obtain ⟨x₀F, hFacts⟩ := Work.FITop4.Red5.pieceFacts_proof_save η hη0 hη1 δ7 hδ7
  obtain ⟨x₀T, hThr⟩ := Work.FITop4.Red5.numHyp_threshold_save η c1 Cb (max C3b C3)
    hη0 hc1 hCb hC3maxpos
  obtain ⟨x₀τ, hτdom⟩ := Work.FITop4.Numeric4.log_dominance.1
    (2 * Asave + (2:ℝ)^(20:ℕ)) (η/3) (by have h := Asave_pos; positivity) (by positivity)
  obtain ⟨x₀L, hLthr⟩ := eventually_log_ge_of ((16:ℝ) * (((1:ℝ)/4 + η) ^ (-(sigmaChoice Asave))))
  obtain ⟨x₀cube, hcube⟩ := Work.FITop4.Red6.eventually_Xcut_cube_le
  obtain ⟨ct, x₀t, hct, ht⟩ := Work.FITop4.Red5.BformPi_tau_truncation
  have hctR : (0:ℝ) < (ct:ℝ) := by exact_mod_cast hct
  obtain ⟨cr, hcr, x₀r, hRed⟩ := hred
  obtain ⟨cA, hcA, XA, hAseq⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Aseq_ge_const_mul_rpow
  obtain ⟨Xatil, hAtil⟩ := Work.FITop.Aseq_le_const_mul_AcountAtil
  set G : ℝ := 2 / Submission.ASP.Gprod Submission.ASP.FIg + 1 with hGdef
  have hGpos : 0 < G := by
    rw [hGdef]
    have h := Submission.ASP.Gprod_FIg_pos
    have h2 : 0 < 2 / Submission.ASP.Gprod Submission.ASP.FIg := div_pos (by norm_num) h
    linarith
  set s : ℝ := cU + cV + cW + Cτ with hsdef
  have hs1 : 0 ≤ 1 + s := by rw [hsdef]; linarith
  have hBmaxpos : 0 < BmaxBig η := by
    unfold BmaxBig
    have h1 := Work.FITop4.bFun_pos η
    have h2 : (0:ℝ) < (2:ℝ)^(31:ℕ) := by positivity
    linarith
  have hKpos : 0 < (64 * (10 * cr * Real.sqrt (1+s)) + 3*cr) * (G/cA) + ct + 1 := by
    have h1 : 0 ≤ 64 * (10 * cr * Real.sqrt (1+s)) + 3*cr := by
      have hcr0 : 0 ≤ cr := le_of_lt hcr
      nlinarith [Real.sqrt_nonneg (1+s)]
    have h2 : 0 ≤ (G/cA) := div_nonneg (le_of_lt hGpos) (le_of_lt hcA)
    nlinarith [mul_nonneg h1 h2, hctR]
  set X₀ : ℝ := ({x₀1, x₀2, x₀3, x₀4, x₀6, x₀τr, x₀7, (x₀cube : ℝ), (0:ℝ)} : Finset ℝ).max'
    (by simp) with hX₀def
  refine ⟨BmaxBig η, (64 * (10 * cr * Real.sqrt (1+s)) + 3*cr) * (G/cA) + ct + 1,
    max ⌈X₀⌉₊ (x₀N + x₀F + x₀T + x₀t + x₀r + XA + Xatil + x₀L + x₀τ + x₀cube + 3),
    hBmaxpos, le_rfl, hKpos, ?_⟩
  intro x hx N hNlo hNhi hll C hC1 hC2 Pz hP2 hPlo hPhi
  have hxbase : x₀N + x₀F + x₀T + x₀t + x₀r + XA + Xatil + x₀L + x₀τ + x₀cube + 3 ≤ x :=
    le_trans (le_max_right _ _) hx
  have hceil_le : (⌈X₀⌉₊ : ℝ) ≤ (x : ℝ) := by
    have h1 : (⌈X₀⌉₊ : ℕ) ≤ x := le_trans (le_max_left _ _) hx
    exact_mod_cast h1
  have hX₀le : X₀ ≤ (x : ℝ) := le_trans (Nat.le_ceil X₀) hceil_le
  have hX₀le' : ({x₀1, x₀2, x₀3, x₀4, x₀6, x₀τr, x₀7, (x₀cube : ℝ), (0:ℝ)} : Finset ℝ).max'
      (by simp) ≤ (x : ℝ) := by rw [hX₀def] at hX₀le; exact hX₀le
  have harea : ∀ y ∈ ({x₀1, x₀2, x₀3, x₀4, x₀6, x₀τr, x₀7, (x₀cube : ℝ), (0:ℝ)} : Finset ℝ),
      y ≤ (x : ℝ) := by
    intro y hy
    exact le_trans (Finset.le_max' _ y hy) hX₀le'
  have hx1 : x₀1 ≤ (x : ℝ) := harea x₀1 (by simp)
  have hx2 : x₀2 ≤ (x : ℝ) := harea x₀2 (by simp)
  have hx3 : x₀3 ≤ (x : ℝ) := harea x₀3 (by simp)
  have hx4 : x₀4 ≤ (x : ℝ) := harea x₀4 (by simp)
  have hx6 : x₀6 ≤ (x : ℝ) := harea x₀6 (by simp)
  have hx7 : x₀7 ≤ (x : ℝ) := harea x₀7 (by simp)
  have hxτr : x₀τr ≤ (x : ℝ) := harea x₀τr (by simp)
  have hxcb : (x₀cube : ℝ) ≤ (x : ℝ) := harea _ (by simp)
  have hxco : x₀cube ≤ x := by exact_mod_cast hxcb
  have hxN : x₀N ≤ x := by omega
  have hxF : x₀F ≤ x := by omega
  have hxt : x₀t ≤ x := by omega
  have hxr : x₀r ≤ x := by omega
  have hxXA : XA ≤ x := by omega
  have hxAt : Xatil ≤ x := by omega
  have hxL : x₀L ≤ x := by omega
  have hxτ : x₀τ ≤ x := by omega
  obtain ⟨hx1r, hL4, hLA, _, _, _, _, _⟩ := hThr x (by omega)
  have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hLpos : 0 < Real.log (x:ℝ) := by linarith
  have hLnn : 0 ≤ Real.log (x:ℝ) := le_of_lt hLpos
  have hL1 : (1:ℝ) ≤ Real.log (x:ℝ) := by linarith
  have hL2 : (2:ℝ) ≤ Real.log (x:ℝ) := by linarith
  have hcpos : (0:ℝ) < (1:ℝ)/4 + η := by linarith
  have hN1r : (1:ℝ) < (N:ℝ) :=
    lt_of_le_of_lt (Real.one_le_rpow hx1r (le_of_lt hcpos)) hNlo
  have hN1 : 1 ≤ N := by exact_mod_cast le_of_lt hN1r
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le zero_lt_one (le_of_lt hN1r)
  have hXnn : 0 < (x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-(BmaxBig η)) :=
    mul_pos (Real.rpow_pos_of_pos hxpos _) (Real.rpow_pos_of_pos hLpos _)
  have hNhi' : 2 * (N:ℝ) < (x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-(BmaxBig η - 1)) := by
    have h2 : (2:ℝ) * (N:ℝ)
        < 2 * ((x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-(BmaxBig η))) := by linarith [hNhi]
    have key : 2 * ((x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-(BmaxBig η)))
        ≤ (x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-(BmaxBig η - 1)) := by
      rw [show -(BmaxBig η - 1) = -(BmaxBig η) + 1 by ring, Real.rpow_add hLpos, Real.rpow_one]
      have hPnn : 0 ≤ (x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-(BmaxBig η)) := le_of_lt hXnn
      nlinarith [hL2, hPnn]
    linarith [h2, key]
  have hLAx : (Real.log (x:ℝ))^Asave ≤ (x:ℝ) := by
    refine le_trans hLA ?_
    calc (x:ℝ)^((1:ℝ)/4) ≤ (x:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx1r (by norm_num)
      _ = (x:ℝ) := Real.rpow_one _
  have hϑx1 : 1 ≤ varthetaOf x Asave * (x:ℝ) := by
    have hLApos : 0 < (Real.log (x:ℝ))^Asave := Real.rpow_pos_of_pos hLpos _
    unfold varthetaOf
    rw [Real.rpow_neg hLnn, ← div_eq_inv_mul, le_div_iff₀ hLApos]
    simpa using hLAx
  have hτlow : (Real.log (x:ℝ))^(Asave+124) ≤ tauOf x Asave := by
    unfold tauOf
    apply Real.rpow_le_rpow_of_exponent_le hL1
    nlinarith [Asave_pos]
  have hτ124 : (Real.log (x:ℝ))^(124:ℕ) ≤ tauOf x Asave := by
    rw [← Real.rpow_natCast (Real.log (x:ℝ)) 124]
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hL1 ?_) hτlow
    push_cast
    linarith [Asave_pos]
  have hτle : tauOf x Asave ≤ (x:ℝ)^(η/3) := by
    have h := hτdom x hxτ
    simpa [tauOf] using h
  have ht' := ht x N Pz C (tauOf x Asave) hxt hN1 hC1 hτ124
  have hred' := hRed x N Pz C (tauOf x Asave) η hxr hN1 hC1 hP2 hη0 hη1 hll
    hNlo hNhi hNhi' hC2 hPlo hPhi hτlow hτle hϑx1
  obtain ⟨ι, hιF, Pa, f, φ, β, hPiece, hMaj, hβ, hFar, hcount, hBform⟩ := hred'
  letI := hιF
  have hAseqx : cA * (x:ℝ)^((3:ℝ)/4) ≤ (Submission.Aseq x : ℝ) := hAseq x hxXA
  have hAtilx : (Submission.Aseq x : ℝ) ≤ G * AcountAtil x := by
    rw [hGdef]; exact hAtil x hxAt
  -- ## the per-piece step: bound the `64` classes mod `8` separately, then reassemble
  have hper : ∀ i : ι, Real.sqrt (100 * (Pa i).M * Dform (Pa i) (f i) (β i))
      ≤ 64 * (10 * Real.sqrt (1+s)) * (varthetaOf x Asave) * (thetaOf x Asave)^(2:ℕ)
          * (((Pa i).M * (Pa i).N)^((3:ℝ)/4)) * (Real.log (x:ℝ))^(4:ℕ) := by
    intro i
    obtain ⟨hx_eq, hη_eq, hA_eq, hA'_eq, hϑ_eq, hθ_eq, hτ_eq, hPz_eq, hC_eq, hNle_i, hNle_i'⟩
      := hPiece i
    have hMpos_i : (0:ℝ) < (Pa i).M := lt_of_lt_of_le zero_lt_one (Pa i).hM1
    have hNpos_i : (0:ℝ) < (Pa i).N := lt_of_lt_of_le zero_lt_one (Pa i).hN1
    have hNlo_i : (x:ℝ)^((1:ℝ)/4+η) < (Pa i).N := by
      have h := (Pa i).hNlo; rw [hx_eq, hη_eq] at h; exact h
    have hMNx_i : (Pa i).M * (Pa i).N ≤ (x:ℝ) := by
      have h := (Pa i).hMNx; rw [hx_eq] at h; exact h
    have hlogMNle_i : Real.log ((Pa i).M * (Pa i).N) ≤ Real.log (x:ℝ) :=
      Real.log_le_log (by positivity) hMNx_i
    have hNpiece : (Pa i).N < 2 * ((x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-(BmaxBig η))) := by
      have h := hNle_i'; linarith [hNhi]
    have hFacts_i := hFacts x ((Pa i).N) (Pa i) hxF hx_eq hη_eq hA_eq hA'_eq hθ_eq hϑ_eq hτ_eq
      le_rfl (by linarith [hNpos_i]) hNpiece
    obtain ⟨hS1, hB1, hC9, hD6, hE7, hM16, hN3⟩ := hFacts_i
    have hL1 : (1 : ℝ) ≤ Real.log (Pa i).N := by
      have h3 : (0 : ℝ) < 3 := by norm_num
      have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt h3).mpr Real.exp_one_lt_three
      have hle : Real.log 3 ≤ Real.log (Pa i).N := Real.log_le_log h3 hN3
      linarith
    have h4 : 16 * (Real.log ((Pa i).M * (Pa i).N))^(8:ℕ)
        * (Real.log (x:ℝ))^(2*Asave + 4*Aprime Asave)
        ≤ (Real.log (Pa i).N)^(sigmaChoice Asave) := by
      have hσeq : 2*Asave + 4*Aprime Asave = sigmaChoice Asave - 9 := by
        unfold sigmaChoice; ring
      have hlogMNnn : 0 ≤ Real.log ((Pa i).M*(Pa i).N) :=
        Real.log_nonneg (by nlinarith [(Pa i).hM1, (Pa i).hN1])
      have hℓgt : ((1:ℝ)/4 + η) * Real.log (x:ℝ) < Real.log (Pa i).N := by
        have h := Real.log_lt_log (Real.rpow_pos_of_pos hxpos _) hNlo_i
        rwa [Real.log_rpow hxpos] at h
      have hYL : 16 ≤ ((1:ℝ)/4 + η)^(sigmaChoice Asave) * Real.log (x:ℝ) := by
        have h := hLthr x hxL
        have hpow : 0 < ((1:ℝ)/4+η)^(sigmaChoice Asave) := Real.rpow_pos_of_pos hcpos _
        rw [Real.rpow_neg (le_of_lt hcpos)] at h
        rw [← div_eq_mul_inv, div_le_iff₀ hpow] at h
        linarith [h]
      calc 16 * (Real.log ((Pa i).M*(Pa i).N))^(8:ℕ) * (Real.log (x:ℝ))^(2*Asave+4*Aprime Asave)
          = 16 * (Real.log ((Pa i).M*(Pa i).N))^(8:ℕ)
              * (Real.log (x:ℝ))^(sigmaChoice Asave - 9) := by rw [hσeq]
        _ ≤ 16 * (Real.log (x:ℝ))^8 * (Real.log (x:ℝ))^(sigmaChoice Asave - 9) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLnn _)
              exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogMNnn hlogMNle_i 8)
                (by norm_num)
        _ = 16 * (Real.log (x:ℝ))^(sigmaChoice Asave - 1) := by
              have hexp : ((8:ℕ):ℝ) + (sigmaChoice Asave - 9) = sigmaChoice Asave - 1 := by
                push_cast; ring
              rw [← Real.rpow_natCast (Real.log (x:ℝ)) 8, mul_assoc,
                  ← Real.rpow_add hLpos ((8:ℕ):ℝ) (sigmaChoice Asave - 9), hexp]
        _ ≤ (((1:ℝ)/4 + η) * Real.log (x:ℝ))^(sigmaChoice Asave) := by
              rw [Real.mul_rpow (le_of_lt hcpos) hLnn]
              have hXpos : 0 < (Real.log (x:ℝ))^(sigmaChoice Asave - 1) :=
                Real.rpow_pos_of_pos hLpos _
              have he : (Real.log (x:ℝ))^(sigmaChoice Asave)
                  = (Real.log (x:ℝ))^(sigmaChoice Asave - 1) * Real.log (x:ℝ) := by
                calc (Real.log (x:ℝ))^(sigmaChoice Asave)
                    = (Real.log (x:ℝ))^((sigmaChoice Asave - 1) + 1) := by congr 1; ring
                  _ = (Real.log (x:ℝ))^(sigmaChoice Asave - 1)
                        * (Real.log (x:ℝ))^(1:ℝ) := Real.rpow_add hLpos _ _
                  _ = (Real.log (x:ℝ))^(sigmaChoice Asave - 1) * Real.log (x:ℝ) := by
                        rw [Real.rpow_one]
              rw [he]
              nlinarith [hYL, hXpos]
        _ ≤ (Real.log (Pa i).N)^(sigmaChoice Asave) :=
              Real.rpow_le_rpow (mul_nonneg (le_of_lt hcpos) hLnn) (le_of_lt hℓgt)
                (le_of_lt hσpos)
    have hnumi : NumHyp (Pa i).η (Pa i).x (Pa i) (sigmaChoice Asave) c1 Cb (max C3b C3) 1 := by
      have h := hNumAll x (Pa i) ((Pa i).N/2) (sigmaChoice Asave) hxN hx_eq hη_eq hA_eq hA'_eq
        hθ_eq hϑ_eq hτ_eq (by linarith [hNpos_i]) (by linarith [hNpos_i])
        (by linarith [hNhi, hNle_i', hXnn, hNpos_i]) h4
      rwa [← hη_eq, ← hx_eq] at h
    have hxi1 : x₀1 ≤ ((Pa i).x : ℝ) := by rw [hx_eq]; exact hx1
    have hxi2 : x₀2 ≤ ((Pa i).x : ℝ) := by rw [hx_eq]; exact hx2
    have hxi3 : x₀3 ≤ ((Pa i).x : ℝ) := by rw [hx_eq]; exact hx3
    have hxi4 : x₀4 ≤ ((Pa i).x : ℝ) := by rw [hx_eq]; exact hx4
    have hxi6 : x₀6 ≤ ((Pa i).x : ℝ) := by rw [hx_eq]; exact hx6
    have hxiτr : x₀τr ≤ ((Pa i).x : ℝ) := by rw [hx_eq]; exact hxτr
    have hxi7 : x₀7 ≤ ((Pa i).x : ℝ) := by rw [hx_eq]; exact hx7
    have hcube_i : (((Xcut (Pa i) (sigmaChoice Asave) : ℕ)) : ℝ) ^ 3
        ≤ Real.exp (Real.sqrt (Real.log ((Pa i).N : ℝ))) :=
      hcube (Pa i) (by rw [hx_eq]; exact hxco)
    -- the per-class bound: (5.18) against (5.20) for each of the `64` classes mod `8`
    have hperclass : ∀ c : ZMod 8 × ZMod 8,
        Real.sqrt (100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)))
          ≤ 10 * Real.sqrt (1+s) * (varthetaOf x Asave) * (thetaOf x Asave)^(2:ℕ)
              * (((Pa i).M * (Pa i).N)^((3:ℝ)/4)) * (Real.log (x:ℝ))^(4:ℕ) := by
      intro c
      have hβ_ic : IsBetaCoeff6 (Pa i) (φ i) (rep8 c) (clsRestrict (rep8 c) (β i)) :=
        hsplit (Pa i) (φ i) (rep8 c) (β i) (hβ i) (hFar i)
      have hAB : AreaBounds6e (Pa i) (f i) (φ i) (rep8 c) (clsRestrict (rep8 c) (β i))
          (Xcut (Pa i) (sigmaChoice Asave)) (sigmaChoice Asave) c1 Cb C3b C3 cU cV cW Cτ :=
        ⟨(fun f' φ' z0' β' hF' hb => hA1 (Pa i) hxi1 f' φ' z0' β' hF' hb),
         (fun f' φ' z0' β' hF' hb => hA2 (Pa i) hxi2 hη_eq f' φ' z0' β' hF' hb),
         (fun f' φ' z0' β' hF' hb => hA3 (Pa i) hxi3 hη_eq f' φ' z0' β' hF' hb),
         hA4 (Pa i) hxi4 hη_eq (by rw [hx_eq]; exact hθ_eq) (by rw [hx_eq]; exact hτ_eq)
           (Xcut (Pa i) (sigmaChoice Asave)) (φ i) (rep8 c)
           (clsRestrict (rep8 c) (β i)) (hβ_ic)
           (fun z hz => FarPiece_isAxisFree (hFar i) hz) hB1 (log_sq_le_Xcut (Pa i) hL1)
           hC9 (by rw [nuU]; exact hD6),
         (by
           obtain ⟨βc, hβc, hβeq⟩ := isBetaCoeff6_eq_tauCut_clean hβ_ic
             (fun z hz => FarPiece_isAxisFree (hFar i) hz)
           have hU6 := hA6 (Pa i) hxi6 hη_eq (Xcut (Pa i) (sigmaChoice Asave)) (φ i) (rep8 c) βc
             hβc (fun z hz => FarPiece_isAxisFree (hFar i) hz) hB1 (by rw [nuU]; exact hD6) hcube_i
           have hUτ := hTR (Pa i) hxiτr (by rw [hx_eq]; exact hτ_eq)
             (cutU (Xcut (Pa i) (sigmaChoice Asave))) (cutU_abs_le _) (φ i) (rep8 c) βc hβc
           rw [hβeq]
           exact Ucut_tauCut_le (Pa i) (Xcut (Pa i) (sigmaChoice Asave)) βc cU Cτ
             (le_of_lt hcU) (le_of_lt hCτ) hL1 hU6
             (by simpa only [← Ucut_eq_Tcut_cutU] using hUτ)),
         hA7 (Pa i) hxi7 hη_eq (by rw [hx_eq]; exact hτ_eq)
           (Xcut (Pa i) (sigmaChoice Asave)) (φ i) (rep8 c)
           (clsRestrict (rep8 c) (β i)) (hβ_ic)
           (fun z hz => FarPiece_isAxisFree (hFar i) hz)
           hB1 hE7 (by rw [nuU]; exact hD6)⟩
      have hFh : Work.FITop3.Fhat (Pa i) (f i) ≤ 4 * Real.sqrt (Pa i).M :=
        Work.FITop3.Majorant.fhat_upper (Pa i) (f i)
          (Work.FITop4.IsMajorant6.toMajorant (hMaj i)) hM16
      have hXc : (Real.log (Pa i).N) ^ (3 * sigmaChoice Asave + 3)
          ≤ ((Xcut (Pa i) (sigmaChoice Asave) : ℕ) : ℝ) := Nat.le_ceil _
      have hDB := budget6e (Pa i) (f i) (φ i) (rep8 c) (clsRestrict (rep8 c) (β i))
        (Xcut (Pa i) (sigmaChoice Asave)) (sigmaChoice Asave) c1 Cb C3b C3 cU cV cW Cτ (max C3b C3)
        (hMaj i) hβ_ic hσpos hN3 hM16 (le_of_lt hcU) (le_of_lt hcV) (le_of_lt hcW) (le_of_lt hCτ)
        hAB hXc hFh hnumi (le_max_right _ _) (le_max_left _ _)
      have hD' : Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)) ≤ (1+s) * Tbudget (Pa i) := by
        rw [hsdef]; linarith [hDB]
      have hpiece := sqrt_piece_le_of (Pa i) (f i) (clsRestrict (rep8 c) (β i)) s
        (Real.log (x:ℝ)) hD' hs1 hlogMNle_i
      rw [hϑ_eq, hθ_eq] at hpiece
      exact hpiece
    -- the class split of `Dform` and the reassembly of the `64` per-class bounds
    have hDcnn : ∀ c : ZMod 8 × ZMod 8,
        0 ≤ Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)) := by
      intro c
      have hDf : Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i))
          = ∑ w ∈ Work.FITop.boxM (Pa i), (f i) (Work.FIPlan.gnorm w)
              * Complex.normSq (∑ z ∈ Work.FITop.boxN (Pa i),
                  clsRestrict (rep8 c) (β i) z * Work.FITop3.Zc w z) := rfl
      rw [hDf]
      exact Finset.sum_nonneg fun w _ =>
        mul_nonneg ((hMaj i).2.1 _) (Complex.normSq_nonneg _)
    set K : ℝ := 10 * Real.sqrt (1+s) * (varthetaOf x Asave) * (thetaOf x Asave)^(2:ℕ)
        * (((Pa i).M * (Pa i).N)^((3:ℝ)/4)) * (Real.log (x:ℝ))^(4:ℕ) with hKdef
    have hKnn : 0 ≤ K := by
      rw [hKdef]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (Real.sqrt_nonneg _)) (Real.rpow_nonneg hLnn _))
        (pow_nonneg (Real.rpow_nonneg hLnn _) 2)) (Real.rpow_nonneg (by positivity) _))
        (pow_nonneg hLnn 4)
    have hKc : ∀ c : ZMod 8 × ZMod 8,
        Real.sqrt (100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i))) ≤ K := by
      intro c
      have h := hperclass c
      rw [hKdef]
      exact h
    have hsqc : ∀ c : ZMod 8 × ZMod 8,
        100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)) ≤ K ^ 2 := by
      intro c
      have hnn : 0 ≤ 100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)) :=
        mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hMpos_i)) (hDcnn c)
      calc 100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i))
          = (Real.sqrt (100 * (Pa i).M
              * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)))) ^ 2 :=
            (Real.sq_sqrt hnn).symm
        _ ≤ K ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hKc c) 2
    have hsumle : (∑ c : ZMod 8 × ZMod 8,
          100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i))) ≤ 64 * K ^ 2 := by
      calc (∑ c : ZMod 8 × ZMod 8,
            100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)))
          ≤ ∑ c : ZMod 8 × ZMod 8, K ^ 2 := Finset.sum_le_sum (fun c _ => hsqc c)
        _ = 64 * K ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
            norm_num
    have hsplit_i : Real.sqrt (100 * (Pa i).M * Dform (Pa i) (f i) (β i))
        ≤ 8 * Real.sqrt (∑ c : ZMod 8 × ZMod 8,
            100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i))) := by
      have h64 := Dform_classSplit (Pa i) (f i) (β i) (hMaj i).2.1
      have hrew : (∑ c : ZMod 8 × ZMod 8,
            Dform (Pa i) (f i) (fun z => if cls8 z = c then β i z else 0))
          = ∑ c : ZMod 8 × ZMod 8,
              Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [clsRestrict_rep8_eq c (β i)]
      rw [hrew] at h64
      have hstep : 100 * (Pa i).M * Dform (Pa i) (f i) (β i)
          ≤ 64 * (∑ c : ZMod 8 × ZMod 8,
              100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i))) := by
        have hfactor : (∑ c : ZMod 8 × ZMod 8,
              100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)))
            = 100 * (Pa i).M * (∑ c : ZMod 8 × ZMod 8,
                Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i))) := by
          rw [Finset.mul_sum]
        have h3 : 100 * (Pa i).M * Dform (Pa i) (f i) (β i)
            ≤ 100 * (Pa i).M * (64 * (∑ c : ZMod 8 × ZMod 8,
                Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)))) :=
          mul_le_mul_of_nonneg_left h64 (le_of_lt (mul_pos (by norm_num) hMpos_i))
        rw [hfactor]
        linarith [h3]
      calc Real.sqrt (100 * (Pa i).M * Dform (Pa i) (f i) (β i))
          ≤ Real.sqrt (64 * (∑ c : ZMod 8 × ZMod 8,
              100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i)))) :=
            Real.sqrt_le_sqrt hstep
        _ = 8 * Real.sqrt (∑ c : ZMod 8 × ZMod 8,
              100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i))) := by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64), show Real.sqrt (64:ℝ) = 8 by norm_num]
    calc Real.sqrt (100 * (Pa i).M * Dform (Pa i) (f i) (β i))
        ≤ 8 * Real.sqrt (∑ c : ZMod 8 × ZMod 8,
            100 * (Pa i).M * Dform (Pa i) (f i) (clsRestrict (rep8 c) (β i))) := hsplit_i
      _ ≤ 8 * Real.sqrt (64 * K ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsumle) (by norm_num)
      _ = 64 * (10 * Real.sqrt (1+s)) * (varthetaOf x Asave) * (thetaOf x Asave)^(2:ℕ)
            * (((Pa i).M * (Pa i).N)^((3:ℝ)/4)) * (Real.log (x:ℝ))^(4:ℕ) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64), show Real.sqrt (64:ℝ) = 8 by norm_num,
            Real.sqrt_sq hKnn, hKdef]
          ring
  have hsum : (∑ i : ι, Real.sqrt (100 * (Pa i).M * Dform (Pa i) (f i) (β i)))
      ≤ 64 * (10 * Real.sqrt (1+s)) * (varthetaOf x Asave) * (thetaOf x Asave)^(2:ℕ)
          * (Real.log (x:ℝ))^(4:ℕ)
          * (cr * (thetaOf x Asave)^(-(2:ℝ)) * (x:ℝ)^((3:ℝ)/4)) := by
    have hstep1 : (∑ i : ι, Real.sqrt (100 * (Pa i).M * Dform (Pa i) (f i) (β i)))
        ≤ ∑ i : ι, 64 * (10 * Real.sqrt (1+s)) * (varthetaOf x Asave)
            * (thetaOf x Asave)^(2:ℕ)
            * (((Pa i).M * (Pa i).N)^((3:ℝ)/4)) * (Real.log (x:ℝ))^(4:ℕ) :=
      Finset.sum_le_sum (fun i _ => hper i)
    have hstep2 : (∑ i : ι, 64 * (10 * Real.sqrt (1+s)) * (varthetaOf x Asave)
            * (thetaOf x Asave)^(2:ℕ)
            * (((Pa i).M * (Pa i).N)^((3:ℝ)/4)) * (Real.log (x:ℝ))^(4:ℕ))
        = 64 * (10 * Real.sqrt (1+s)) * (varthetaOf x Asave) * (thetaOf x Asave)^(2:ℕ)
            * (Real.log (x:ℝ))^(4:ℕ)
            * (∑ i : ι, (((Pa i).M * (Pa i).N)^((3:ℝ)/4))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring
    have hAnn : 0 ≤ 64 * (10 * Real.sqrt (1+s)) * (varthetaOf x Asave) * (thetaOf x Asave)^(2:ℕ)
        * (Real.log (x:ℝ))^(4:ℕ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
        (Real.rpow_nonneg hLnn _)) (pow_nonneg (Real.rpow_nonneg hLnn _) 2))
        (pow_nonneg hLnn 4)
    have hcnt := mul_le_mul_of_nonneg_left hcount hAnn
    rw [hstep2] at hstep1
    exact le_trans hstep1 hcnt
  have hsum' : (∑ i : ι, Real.sqrt (100 * (Pa i).M * Dform (Pa i) (f i) (β i)))
      ≤ 64 * (10 * Real.sqrt (1+s)) * cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4)
          * (Real.log (x:ℝ))^(4:ℕ) := by
    have hθpos : 0 < thetaOf x Asave := Real.rpow_pos_of_pos hLpos _
    have hcancel : (thetaOf x Asave)^(2:ℕ) * (thetaOf x Asave)^(-(2:ℝ)) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hθpos]
      norm_num
    calc (∑ i : ι, Real.sqrt (100 * (Pa i).M * Dform (Pa i) (f i) (β i)))
        ≤ 64 * (10 * Real.sqrt (1+s)) * (varthetaOf x Asave) * (thetaOf x Asave)^(2:ℕ)
            * (Real.log (x:ℝ))^(4:ℕ)
            * (cr * (thetaOf x Asave)^(-(2:ℝ)) * (x:ℝ)^((3:ℝ)/4)) := hsum
      _ = (64 * (10 * Real.sqrt (1+s)) * cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4)
            * (Real.log (x:ℝ))^(4:ℕ))
            * ((thetaOf x Asave)^(2:ℕ) * (thetaOf x Asave)^(-(2:ℝ))) := by ring
      _ = 64 * (10 * Real.sqrt (1+s)) * cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4)
            * (Real.log (x:ℝ))^(4:ℕ) := by rw [hcancel, mul_one]
  have hmain : Work.FITop.BformPi x N C Pz
      ≤ 64 * (10 * Real.sqrt (1+s)) * cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4)
          * (Real.log (x:ℝ))^(4:ℕ)
        + cr * ((thetaOf x Asave) * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^(100:ℕ)
                + (varthetaOf x Asave)^((3:ℝ)/4) * (x:ℝ)^((3:ℝ)/4)
                  * (Real.log (x:ℝ))^(65536:ℕ))
        + cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^(Kaxis)
        + ct * (tauOf x Asave)⁻¹ * AcountAtil x * (Real.log (x:ℝ))^(131072:ℕ) := by
    linarith [ht', hBform, hsum']
  -- ## exponential absorption
  have hAnn : 0 ≤ AcountAtil x := Work.FITop.AcountAtil_nonneg' x
  have hPpos : 0 < (Real.log (x:ℝ))^(4 - Astar) := Real.rpow_pos_of_pos hLpos _
  have hPnn : 0 ≤ (Real.log (x:ℝ))^(4 - Astar) := le_of_lt hPpos
  have hC0nn : 0 ≤ G/cA := div_nonneg (le_of_lt hGpos) (le_of_lt hcA)
  have hx34nn : 0 ≤ (x:ℝ)^((3:ℝ)/4) := Real.rpow_nonneg (le_of_lt hxpos) _
  have hx34le : (x:ℝ)^((3:ℝ)/4) ≤ (G/cA) * AcountAtil x := by
    have h1 : cA * (x:ℝ)^((3:ℝ)/4) ≤ G * AcountAtil x := le_trans hAseqx hAtilx
    have h2 : (x:ℝ)^((3:ℝ)/4) ≤ (G * AcountAtil x)/cA := by
      rw [le_div_iff₀ hcA]; linarith [h1]
    calc (x:ℝ)^((3:ℝ)/4) ≤ (G*AcountAtil x)/cA := h2
      _ = (G/cA)*AcountAtil x := by ring
  have hC0Ann : 0 ≤ (G/cA) * AcountAtil x := mul_nonneg hC0nn hAnn
  have he1 : (varthetaOf x Asave) * (Real.log (x:ℝ))^(4:ℕ) ≤ (Real.log (x:ℝ))^(4 - Astar) := by
    rw [show varthetaOf x Asave = (Real.log (x:ℝ))^(-Asave) from rfl,
        ← Real.rpow_natCast (Real.log (x:ℝ)) 4, ← Real.rpow_add hLpos]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    push_cast
    linarith [Astar_le_Asave]
  have he2 : (thetaOf x Asave) * (Real.log (x:ℝ))^(100:ℕ) ≤ (Real.log (x:ℝ))^(4 - Astar) := by
    rw [show thetaOf x Asave = (Real.log (x:ℝ))^(-(Aprime Asave)) from rfl,
        ← Real.rpow_natCast (Real.log (x:ℝ)) 100, ← Real.rpow_add hLpos]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    norm_num [Aprime, Asave, Astar]
  have he3 : (varthetaOf x Asave)^((3:ℝ)/4) * (Real.log (x:ℝ))^(65536:ℕ)
      ≤ (Real.log (x:ℝ))^(4 - Astar) := by
    have hϑ : (varthetaOf x Asave)^((3:ℝ)/4) = (Real.log (x:ℝ))^((-Asave)*((3:ℝ)/4)) := by
      rw [show varthetaOf x Asave = (Real.log (x:ℝ))^(-Asave) from rfl, ← Real.rpow_mul hLnn]
    rw [hϑ, ← Real.rpow_natCast (Real.log (x:ℝ)) 65536, ← Real.rpow_add hLpos]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    norm_num [Asave, Astar]
  have he5 : (tauOf x Asave)⁻¹ * (Real.log (x:ℝ))^(131072:ℕ)
      ≤ (Real.log (x:ℝ))^(4 - Astar) := by
    rw [show tauOf x Asave = (Real.log (x:ℝ))^(2*Asave + (2:ℝ)^(20:ℕ)) from rfl,
        ← Real.rpow_neg hLnn (2*Asave + (2:ℝ)^(20:ℕ)),
        ← Real.rpow_natCast (Real.log (x:ℝ)) 131072,
        ← Real.rpow_add hLpos]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    norm_num [Asave, Astar]
  have heK : (varthetaOf x Asave) * (Real.log (x:ℝ))^(Kaxis) ≤ (Real.log (x:ℝ))^(4 - Astar) := by
    rw [show varthetaOf x Asave = (Real.log (x:ℝ))^(-Asave) from rfl,
        ← Real.rpow_natCast (Real.log (x:ℝ)) Kaxis, ← Real.rpow_add hLpos]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    norm_num [Kaxis, Asave, Astar]
  have hsq0 : 0 ≤ 64 * (10 * Real.sqrt (1+s)) * cr := by
    have hcr0 : 0 ≤ cr := le_of_lt hcr
    nlinarith [Real.sqrt_nonneg (1+s)]
  have hϑL4nn : 0 ≤ (varthetaOf x Asave) * (Real.log (x:ℝ))^(4:ℕ) :=
    mul_nonneg (Real.rpow_nonneg hLnn _) (pow_nonneg hLnn 4)
  have hϑPLnn : 0 ≤ (varthetaOf x Asave)^((3:ℝ)/4) * (Real.log (x:ℝ))^(65536:ℕ) :=
    mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hLnn _) _) (pow_nonneg hLnn 65536)
  have hθPLnn : 0 ≤ (thetaOf x Asave) * (Real.log (x:ℝ))^(100:ℕ) :=
    mul_nonneg (Real.rpow_nonneg hLnn _) (pow_nonneg hLnn 100)
  have hϑKnn : 0 ≤ (varthetaOf x Asave) * (Real.log (x:ℝ))^(Kaxis) :=
    mul_nonneg (Real.rpow_nonneg hLnn _) (pow_nonneg hLnn Kaxis)
  have hE1 : 64 * (10 * Real.sqrt (1+s)) * cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4)
        * (Real.log (x:ℝ))^(4:ℕ)
      ≤ 64 * (10 * Real.sqrt (1+s)) * cr * ((G/cA) * AcountAtil x)
        * (Real.log (x:ℝ))^(4 - Astar) := by
    have h2 : (x:ℝ)^((3:ℝ)/4) * ((varthetaOf x Asave) * (Real.log (x:ℝ))^(4:ℕ))
        ≤ ((G/cA) * AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) :=
      mul_le_mul hx34le he1 hϑL4nn hC0Ann
    calc 64 * (10 * Real.sqrt (1+s)) * cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4)
          * (Real.log (x:ℝ))^(4:ℕ)
        = (64 * (10 * Real.sqrt (1+s)) * cr)
            * ((x:ℝ)^((3:ℝ)/4) * ((varthetaOf x Asave) * (Real.log (x:ℝ))^(4:ℕ))) := by ring
      _ ≤ (64 * (10 * Real.sqrt (1+s)) * cr)
            * (((G/cA) * AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar)) :=
          mul_le_mul_of_nonneg_left h2 hsq0
      _ = 64 * (10 * Real.sqrt (1+s)) * cr * ((G/cA) * AcountAtil x)
            * (Real.log (x:ℝ))^(4 - Astar) := by ring
  have hE2a : cr * (thetaOf x Asave) * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^(100:ℕ)
      ≤ cr * ((G/cA)*AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) := by
    have h2 : (x:ℝ)^((3:ℝ)/4) * ((thetaOf x Asave) * (Real.log (x:ℝ))^(100:ℕ))
        ≤ ((G/cA) * AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) :=
      mul_le_mul hx34le he2 hθPLnn hC0Ann
    have hcr0 : 0 ≤ cr := le_of_lt hcr
    calc cr * (thetaOf x Asave) * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^(100:ℕ)
        = cr * ((x:ℝ)^((3:ℝ)/4) * ((thetaOf x Asave) * (Real.log (x:ℝ))^(100:ℕ))) := by ring
      _ ≤ cr * (((G/cA) * AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar)) :=
          mul_le_mul_of_nonneg_left h2 hcr0
      _ = cr * ((G/cA)*AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) := by ring
  have hE2b : cr * ((varthetaOf x Asave)^((3:ℝ)/4)) * (x:ℝ)^((3:ℝ)/4)
        * (Real.log (x:ℝ))^(65536:ℕ)
      ≤ cr * ((G/cA)*AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) := by
    have h2 : (x:ℝ)^((3:ℝ)/4)
          * ((varthetaOf x Asave)^((3:ℝ)/4) * (Real.log (x:ℝ))^(65536:ℕ))
        ≤ ((G/cA) * AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) :=
      mul_le_mul hx34le he3 hϑPLnn hC0Ann
    have hcr0 : 0 ≤ cr := le_of_lt hcr
    calc cr * ((varthetaOf x Asave)^((3:ℝ)/4)) * (x:ℝ)^((3:ℝ)/4)
          * (Real.log (x:ℝ))^(65536:ℕ)
        = cr * ((x:ℝ)^((3:ℝ)/4)
            * ((varthetaOf x Asave)^((3:ℝ)/4) * (Real.log (x:ℝ))^(65536:ℕ))) := by ring
      _ ≤ cr * (((G/cA) * AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar)) :=
          mul_le_mul_of_nonneg_left h2 hcr0
      _ = cr * ((G/cA)*AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) := by ring
  have hE2 : cr * ((thetaOf x Asave) * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^(100:ℕ)
        + (varthetaOf x Asave)^((3:ℝ)/4) * (x:ℝ)^((3:ℝ)/4)
          * (Real.log (x:ℝ))^(65536:ℕ))
      ≤ 2 * cr * ((G/cA)*AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) := by
    have h := add_le_add hE2a hE2b
    linarith [h]
  have hE3 : ct * (tauOf x Asave)⁻¹ * AcountAtil x * (Real.log (x:ℝ))^(131072:ℕ)
      ≤ ct * AcountAtil x * (Real.log (x:ℝ))^(4 - Astar) := by
    calc ct * (tauOf x Asave)⁻¹ * AcountAtil x * (Real.log (x:ℝ))^(131072:ℕ)
        = ct * AcountAtil x * ((tauOf x Asave)⁻¹ * (Real.log (x:ℝ))^(131072:ℕ)) := by ring
      _ ≤ ct * AcountAtil x * (Real.log (x:ℝ))^(4 - Astar) :=
          mul_le_mul_of_nonneg_left he5 (mul_nonneg (le_of_lt hctR) hAnn)
  have hE4 : cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^(Kaxis)
      ≤ cr * ((G/cA)*AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) := by
    have h2 : (x:ℝ)^((3:ℝ)/4) * ((varthetaOf x Asave) * (Real.log (x:ℝ))^(Kaxis))
        ≤ ((G/cA) * AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) :=
      mul_le_mul hx34le heK hϑKnn hC0Ann
    have hcr0 : 0 ≤ cr := le_of_lt hcr
    calc cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^(Kaxis)
        = cr * ((x:ℝ)^((3:ℝ)/4) * ((varthetaOf x Asave) * (Real.log (x:ℝ))^(Kaxis))) := by ring
      _ ≤ cr * (((G/cA) * AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar)) :=
          mul_le_mul_of_nonneg_left h2 hcr0
      _ = cr * ((G/cA)*AcountAtil x) * (Real.log (x:ℝ))^(4 - Astar) := by ring
  have hfinal : Work.FITop.BformPi x N C Pz
      ≤ ((64 * (10 * cr * Real.sqrt (1+s)) + 3*cr) * (G/cA) + ct + 1)
          * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)) := by
    have hÃP : 0 ≤ AcountAtil x * (Real.log (x:ℝ))^(4 - Astar) := mul_nonneg hAnn hPnn
    have hZ : 0 ≤ (G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)) :=
      mul_nonneg hC0nn hÃP
    have hA1'' : 64 * (10 * Real.sqrt (1+s)) * cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4)
          * (Real.log (x:ℝ))^(4:ℕ)
        ≤ (64 * (10 * cr * Real.sqrt (1+s)))
            * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar))) :=
      le_trans hE1 (le_of_eq (by ring))
    have hA2'' : cr * ((thetaOf x Asave) * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^(100:ℕ)
                + (varthetaOf x Asave)^((3:ℝ)/4) * (x:ℝ)^((3:ℝ)/4)
                  * (Real.log (x:ℝ))^(65536:ℕ))
        ≤ 2 * cr * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar))) :=
      le_trans hE2 (le_of_eq (by ring))
    have hA4'' : cr * (varthetaOf x Asave) * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^(Kaxis)
        ≤ cr * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar))) :=
      le_trans hE4 (le_of_eq (by ring))
    have hA3'' : ct * (tauOf x Asave)⁻¹ * AcountAtil x * (Real.log (x:ℝ))^(131072:ℕ)
        ≤ ct * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)) :=
      le_trans hE3 (le_of_eq (by ring))
    have hsum4 := add_le_add (add_le_add (add_le_add hA1'' hA2'') hA4'') hA3''
    have hkey : (64 * (10 * cr * Real.sqrt (1+s)))
            * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)))
          + 2 * cr * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)))
          + cr * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)))
          + ct * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar))
        ≤ (64 * (10 * cr * Real.sqrt (1+s)))
            * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)))
          + 3 * cr * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)))
          + ct * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar))
          + (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)) := by
      have hm : 0 ≤ cr * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar))) :=
        mul_nonneg (le_of_lt hcr) hZ
      linarith [hm, hÃP]
    have hkey2 : (64 * (10 * cr * Real.sqrt (1+s)))
            * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)))
          + 3 * cr * ((G/cA) * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)))
          + ct * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar))
          + (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar))
        = ((64 * (10 * cr * Real.sqrt (1+s)) + 3*cr) * (G/cA) + ct + 1)
          * (AcountAtil x * (Real.log (x:ℝ))^(4 - Astar)) := by ring
    exact le_trans hmain (le_trans (le_trans hsum4 hkey) (le_of_eq hkey2))
  refine hfinal.trans_eq ?_
  ring


end

/-- **The amended composition at the strengthened area 4**: the corrected areas 1–3, the stronger
area 4 `Work.FITop4.Area4_6c`, the *clean* area 6 (`Work.FITop4.Area6_6e`) and the τ-removal
`Work.FITop4.TauRemoval6`, together with the amended area 7, take the frozen-exponent,
`Π`-restricted target. -/
theorem prop41_of_areas6f (h1 : Work.FITop4.Area1Sieve6) (h2 : Work.FITop4.Area2_6b)
    (h3 : Work.FITop4.Area3_6) (h4 : Work.FITop4.Area4_6c)
    (h6 : Work.FITop4.Area6_6e) (hτ : Work.FITop4.TauRemoval6) (h7 : Work.FITop4.Area7_6b) :
    Work.FITop4.Prop41StatementPiBig :=
  prop41_of_areas6f_of Work.FIRed6Axis.reduction_save6_axis Work.FIRed6Axis.classSplit6 hτ
    h1 h2 h3 h4 h6 h7

end Work.FIRed6e
