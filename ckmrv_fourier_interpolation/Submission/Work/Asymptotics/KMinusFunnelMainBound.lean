/-
# The core bound for the `d = 24` funnel tail

This file proves `Work.Asymptotics.KMinusFunnelMainBound`.

The bracket `Q = brMinus 24 + Sh · br0 24` factorizes as `Q = Sh · ((Sh)⁻¹ · Q)`, and
`Compact.decomp24_sum` writes `(Sh)⁻¹ · Q = Tref24 + Dev24Sum` with the reference part `Tref24`
and the seven deviations `Dev1, …, Dev7` of `Compact`.  On the funnel contour `z = i t`,
`t ≥ Im τ + 1`:

* `‖Sh τ z · Tref24‖ ≤ C (scale τ)^N (1+t)` (`ShTref_bound`);
* `‖Sh τ z · Devᵢ‖ ≤ C (scale τ)^N (1+t)` for `i = 1, …, 7` (`Dev1_bound`, …, `Dev7_bound`),
  the two `dSinv`-terms being handled through `Sh · dSinv = 1 - Sh · Sinvref` together with
  `‖Sh τ z · Sinvref τ z - 1‖ ≤ C (‖Ept z‖²/‖Ept τ‖²)²`
  (`Funnel24Tail.ShSinvrefFunnelBound`).

The atom bounds are collected in `Submission/Work/Asymptotics/KMinusFunnelAtoms.lean`.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_bounds
import Submission.Work.Asymptotics.Compact.kminus_tail_main
import Submission.Work.Asymptotics.KMinusFunnelAtoms
import Submission.Work.Asymptotics.Funnel24Tail.Tref24FunnelBound
import Submission.Work.Asymptotics.Funnel24Tail.ShSinvrefFunnelBound
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.FunnelNumerics.Lamb_funnel_bound
import Submission.Work.Residues.KMinusCuspDefs

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels
open Work.Residues (Ept)
open Work.Asymptotics.Funnel24

noncomputable section

/-! ## Elementary helpers -/

/-- `0 ≤ a * b * c`. -/
theorem nn3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 0 ≤ a * b * c :=
  mul_nonneg (mul_nonneg ha hb) hc

/-- `0 ≤ a * b * c * d`. -/
theorem nn4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ a * b * c * d := mul_nonneg (nn3 ha hb hc) hd

/-- `0 ≤ a * b * c * d * e`. -/
theorem nn5 {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ a * b * c * d * e := mul_nonneg (nn4 ha hb hc hd) he

/-- `0 ≤ a * b * c * d * e * f`. -/
theorem nn6 {a b c d e f : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hf : 0 ≤ f) : 0 ≤ a * b * c * d * e * f := mul_nonneg (nn5 ha hb hc hd he) hf

/-- `((a²)⁻¹ + K) a³ ≤ 1 + K` for `0 < a ≤ 1`, `K ≥ 0`. -/
theorem inv_sq_add_cube {a K : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hK : 0 ≤ K) :
    ((a ^ 2)⁻¹ + K) * a ^ 3 ≤ 1 + K := by
  have h1 : (a ^ 2)⁻¹ * a ^ 3 = a := by field_simp; try ring
  have h3 : a ^ 3 ≤ 1 := pow_le_one₀ (le_of_lt ha0) ha1
  have h2 : K * a ^ 3 ≤ K := by nlinarith [h3, hK]
  have h4 : ((a ^ 2)⁻¹ + K) * a ^ 3 = (a ^ 2)⁻¹ * a ^ 3 + K * a ^ 3 := by ring
  rw [h4, h1]; linarith

/-- `(a²/V)² ((a²)⁻¹ + K) V ≤ 1 + K` for `0 < a`, `a²/V ≤ 1`, `a ≤ 1`, `K ≥ 0`. -/
theorem dSinv_key {a V K : ℝ} (ha0 : 0 < a) (h1 : a ^ 2 * V⁻¹ ≤ 1) (h2 : a ≤ 1)
    (hK : 0 ≤ K) : (a ^ 2 * V⁻¹) ^ 2 * ((a ^ 2)⁻¹ + K) * V ≤ 1 + K := by
  rcases lt_trichotomy V 0 with hV | hV | hV
  · have h1' : a ^ 2 * V⁻¹ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (le_of_lt ha0) 2) (inv_nonpos.mpr hV.le)
    have hsq : (0 : ℝ) ≤ (a ^ 2 * V⁻¹) ^ 2 := sq_nonneg _
    have hfac : (0 : ℝ) ≤ (a ^ 2)⁻¹ + K :=
      add_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt ha0) 2)) hK
    have hle0 : (a ^ 2 * V⁻¹) ^ 2 * ((a ^ 2)⁻¹ + K) * V ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hsq hfac) hV.le
    linarith
  · rw [hV, mul_zero]; linarith
  · have hkey1 : (a ^ 2 * V⁻¹) ^ 2 * (a ^ 2)⁻¹ * V = a ^ 2 * V⁻¹ := by
      field_simp; try ring
    have hkey2 : (a ^ 2 * V⁻¹) ^ 2 * K * V ≤ K := by
      have hid : (a ^ 2 * V⁻¹) ^ 2 * V = (a ^ 2 * V⁻¹) * a ^ 2 := by field_simp; try ring
      have hred : (a ^ 2 * V⁻¹) * a ^ 2 ≤ 1 := by
        have h3 : a ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt ha0) h2
        calc (a ^ 2 * V⁻¹) * a ^ 2 ≤ 1 * 1 :=
              mul_le_mul h1 h3 (pow_nonneg (le_of_lt ha0) 2) (by norm_num)
          _ = 1 := by norm_num
      calc (a ^ 2 * V⁻¹) ^ 2 * K * V = K * ((a ^ 2 * V⁻¹) ^ 2 * V) := by ring
        _ = K * ((a ^ 2 * V⁻¹) * a ^ 2) := by rw [hid]
        _ ≤ K * 1 := mul_le_mul_of_nonneg_left hred hK
        _ = K := by ring
    have hdist : (a ^ 2 * V⁻¹) ^ 2 * ((a ^ 2)⁻¹ + K) * V
        = (a ^ 2 * V⁻¹) ^ 2 * (a ^ 2)⁻¹ * V + (a ^ 2 * V⁻¹) ^ 2 * K * V := by ring
    rw [hdist, hkey1]; linarith [hkey2]

/-- Combining two bounds of the shape `C (scale τ)^N (1+t)`. -/
theorem add_bound {X Y : ℂ} {C1 N1 C2 N2 : ℝ} {τ : ℍ} {t : ℝ}
    (h1 : ‖X‖ ≤ C1 * (scale τ) ^ N1 * (1 + t)) (h2 : ‖Y‖ ≤ C2 * (scale τ) ^ N2 * (1 + t))
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (ht : 0 ≤ t) :
    ‖X + Y‖ ≤ (C1 + C2) * (scale τ) ^ (N1 + N2) * (1 + t) := by
  have hs : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have h1' : (scale τ) ^ N1 ≤ (scale τ) ^ (N1 + N2) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have h2' : (scale τ) ^ N2 ≤ (scale τ) ^ (N1 + N2) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have ht1 : (0 : ℝ) ≤ 1 + t := by linarith
  have hA : C1 * (scale τ) ^ N1 * (1 + t) ≤ C1 * (scale τ) ^ (N1 + N2) * (1 + t) := by
    refine mul_le_mul_of_nonneg_right ?_ ht1
    exact mul_le_mul_of_nonneg_left h1' hC1
  have hB : C2 * (scale τ) ^ N2 * (1 + t) ≤ C2 * (scale τ) ^ (N1 + N2) * (1 + t) := by
    refine mul_le_mul_of_nonneg_right ?_ ht1
    exact mul_le_mul_of_nonneg_left h2' hC2
  refine le_trans (norm_add_le X Y) ?_
  calc ‖X‖ + ‖Y‖ ≤ C1 * (scale τ) ^ (N1 + N2) * (1 + t) + C2 * (scale τ) ^ (N1 + N2) * (1 + t) :=
        add_le_add (le_trans h1 hA) (le_trans h2 hB)
    _ = (C1 + C2) * (scale τ) ^ (N1 + N2) * (1 + t) := by ring

/-! ## `Sh` is bounded on the funnel contour -/

/-- `‖Sh τ z‖ ≤ 135/8` on the funnel contour. -/
theorem ShFunnelBound : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
    (z : ℂ) = (t : ℂ) * Complex.I → ‖Compact.Sh τ z‖ ≤ C := by
  refine ⟨135 / 8, by norm_num, fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hz2 : (2 : ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  have hE4z : ‖E4Fun z ^ 3‖ ≤ 27 / 8 := by
    rw [norm_pow]
    have h := Funnel24.norm_E4_le hz2
    have h' := pow_le_pow_left₀ (norm_nonneg (E4Fun z)) h 3
    norm_num at h'
    exact h'
  have hjz : ‖DeltaFun z * jInvariantFun z‖ ≤ 27 / 8 := by
    rw [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
    exact hE4z
  have hEptz : ‖Ept z‖ ^ 2 = Real.exp (-(2 * Real.pi * z.im)) := by
    rw [Work.Residues.norm_Ept, sq, ← Real.exp_add]
    congr 1; ring
  have hDz : ‖DeltaFun z‖ ≤ 2 * ‖Ept z‖ ^ 2 := by
    have h := DeltaFun_le_two_exp z hz1
    rwa [hEptz]
  have hexp : Real.exp (2 * Real.pi * τ.im) * ‖Ept z‖ ^ 2 ≤ Real.exp (-(2 * Real.pi)) :=
    exp_im_mul_Ept_sq_le τ z t hτ ht hzim
  have hexp' : ‖Ept z‖ ^ 2 * Real.exp (2 * Real.pi * τ.im) ≤ Real.exp (-(2 * Real.pi)) := by
    rw [mul_comm]; exact hexp
  have h3 : Real.exp (-(2 * Real.pi)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith [Real.pi_pos]
  have hDj : ‖DeltaFun z * jInvariantFun τ‖ ≤ 27 / 2 := by
    rw [norm_mul]
    have hj := norm_j_funnel τ hτ
    have hD0 : (0 : ℝ) ≤ ‖DeltaFun z‖ := norm_nonneg _
    have h1 : ‖DeltaFun z‖ * ‖jInvariantFun τ‖
        ≤ (2 * ‖Ept z‖ ^ 2) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) :=
      mul_le_mul hDz hj (norm_nonneg _) (by linarith [pow_nonneg (norm_nonneg (Ept z)) 2])
    have h2 : (2 * ‖Ept z‖ ^ 2) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im))
        = (27 / 2) * (‖Ept z‖ ^ 2 * Real.exp (2 * Real.pi * τ.im)) := by ring
    rw [h2] at h1
    refine le_trans h1 ?_
    calc (27 / 2) * (‖Ept z‖ ^ 2 * Real.exp (2 * Real.pi * τ.im))
        ≤ (27 / 2) * Real.exp (-(2 * Real.pi)) := mul_le_mul_of_nonneg_left hexp' (by norm_num)
      _ ≤ (27 / 2) * 1 := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 27 / 2 := by ring
  rw [show Compact.Sh τ z
      = -(DeltaFun z * (jInvariantFun τ - jInvariantFun z)) from Compact.Sh_eq τ z]
  calc ‖-(DeltaFun z * (jInvariantFun τ - jInvariantFun z))‖
      = ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := norm_neg _
    _ ≤ ‖DeltaFun z * jInvariantFun τ‖ + ‖DeltaFun z * jInvariantFun z‖ := by
        rw [show DeltaFun z * (jInvariantFun τ - jInvariantFun z)
            = DeltaFun z * jInvariantFun τ - DeltaFun z * jInvariantFun z from by ring]
        exact norm_sub_le _ _
    _ ≤ 27 / 2 + 27 / 8 := add_le_add hDj hjz
    _ = 135 / 8 := by norm_num

/-! ## The `Sh`-multiplied reference part -/

/-- `‖Sh τ z · Tref24 ℓ τ z‖ ≤ C (scale τ)^N (1+t)` on the funnel contour. -/
theorem ShTref_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Tref24 ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨CSh, hCSh, hShb⟩ := ShFunnelBound
  obtain ⟨Ct, Nt, hCt, hNt, hTref⟩ := Funnel24Tail.Tref24FunnelBound ℓ
  refine ⟨CSh * Ct, Nt, mul_pos hCSh hCt, hNt, fun τ z t hτ ht hz => ?_⟩
  calc ‖Compact.Sh τ z * Compact.Tref24 ℓ τ z‖
      = ‖Compact.Sh τ z‖ * ‖Compact.Tref24 ℓ τ z‖ := norm_mul _ _
    _ ≤ CSh * (Ct * (scale τ) ^ Nt * (1 + t)) :=
        mul_le_mul (hShb τ z t hτ ht hz) (hTref τ z t hτ ht hz) (norm_nonneg _) hCSh.le
    _ = CSh * Ct * (scale τ) ^ Nt * (1 + t) := by ring

/-! ## The seven deviation terms -/

/-- `‖c * X‖ ≤ A * B` when `‖c‖ ≤ A` and `‖X‖ ≤ B` and `0 ≤ A`. -/
theorem norm_mul_le_of {c X : ℂ} {A B : ℝ} (h1 : ‖c‖ ≤ A) (h2 : ‖X‖ ≤ B) (hA : 0 ≤ A) :
    ‖c * X‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) hA

/-- `‖Sh τ z · Dev1 ℓ τ z‖ ≤ C (scale τ)^N (1+t)`. -/
theorem Dev1_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Dev1 ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨CSh, hCSh, hShb⟩ := ShFunnelBound
  obtain ⟨Csi, hCsi, hSib⟩ := Sinvref_funnel
  obtain ⟨CD, ND, hCD, hND, hD⟩ := A24diff_funnel ℓ
  refine ⟨CSh * Csi * CD * 25, ND, mul_pos (mul_pos (mul_pos hCSh hCsi) hCD) (by norm_num),
    hND, fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have hu : ‖Ept z‖ ≤ 1 := norm_Ept_le_one' hz1
  have hu0 : (0 : ℝ) < ‖Ept z‖ := norm_pos_iff.mpr (Work.Residues.Ept_ne_zero z)
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have hsN0 : (0 : ℝ) ≤ (scale τ) ^ ND := scale_rpow_nonneg' τ ND
  have hDref0 : (0 : ℝ) ≤ (‖Ept z‖ ^ 2)⁻¹ + 24 :=
    add_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 2)) (by norm_num)
  have hDref : ‖Compact.Dref z‖ ≤ (‖Ept z‖ ^ 2)⁻¹ + 24 := Funnel24.norm_Dref_le hz1
  have hsplit : Compact.Sh τ z * Compact.Dev1 ℓ τ z
      = (Compact.Sh τ z * Compact.Sinvref τ z) * Compact.Dref z
        * (Compact.A24 ℓ τ z - Compact.A24ref ℓ τ z) := by
    simp only [Compact.Dev1]; ring
  rw [hsplit]
  have hkey := inv_sq_add_cube (a := ‖Ept z‖) (K := 24) hu0 hu (by norm_num)
  have he1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have hb2 : ‖(Compact.Sh τ z * Compact.Sinvref τ z) * Compact.Dref z‖
      ≤ (CSh * Csi) * ((‖Ept z‖ ^ 2)⁻¹ + 24) := by
    have h1 : ‖Compact.Sh τ z * Compact.Sinvref τ z‖ ≤ CSh * Csi := by
      rw [norm_mul]
      exact mul_le_mul (hShb τ z t hτ ht hz) (hSib τ z t hτ ht hz) (norm_nonneg _) hCSh.le
    exact norm_mul_le_of h1 hDref (mul_nonneg hCSh.le hCsi.le)
  have hb3 : ‖(Compact.Sh τ z * Compact.Sinvref τ z) * Compact.Dref z
        * (Compact.A24 ℓ τ z - Compact.A24ref ℓ τ z)‖
      ≤ ((CSh * Csi) * ((‖Ept z‖ ^ 2)⁻¹ + 24))
        * (CD * (scale τ) ^ ND * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t)
          * ‖Ept z‖ ^ 3) :=
    norm_mul_le_of hb2 (hD τ z t hτ ht hz) (mul_nonneg (mul_nonneg hCSh.le hCsi.le) hDref0)
  calc ‖(Compact.Sh τ z * Compact.Sinvref τ z) * Compact.Dref z
        * (Compact.A24 ℓ τ z - Compact.A24ref ℓ τ z)‖
      ≤ ((CSh * Csi) * ((‖Ept z‖ ^ 2)⁻¹ + 24))
        * (CD * (scale τ) ^ ND * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t)
          * ‖Ept z‖ ^ 3) := hb3
    _ = ((CSh * Csi * CD * (scale τ) ^ ND * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im)))) * (((‖Ept z‖ ^ 2)⁻¹ + 24) * ‖Ept z‖ ^ 3) := by
          ring
    _ ≤ ((CSh * Csi * CD * (scale τ) ^ ND * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im)))) * (1 + 24) :=
          mul_le_mul_of_nonneg_left hkey
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCsi.le) hCD.le) hsN0) (by linarith)) hE0)
    _ ≤ ((CSh * Csi * CD * (scale τ) ^ ND * (1 + t) * 1)) * (1 + 24) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCsi.le) hCD.le) hsN0) (by linarith))) (by norm_num)
    _ = CSh * Csi * CD * 25 * (scale τ) ^ ND * (1 + t) := by ring

/-- `‖Sh τ z · Dev2 ℓ τ z‖ ≤ C (scale τ)^N (1+t)`. -/
theorem Dev2_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Dev2 ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨CSh, hCSh, hShb⟩ := ShFunnelBound
  obtain ⟨Csi, hCsi, hSib⟩ := Sinvref_funnel
  obtain ⟨Cdd, hCdd, hdd⟩ := norm_dDelta_le
  obtain ⟨CA, NA, hCA, hNA, hA⟩ := A24_funnel ℓ
  refine ⟨CSh * Csi * Cdd * CA, NA, mul_pos (mul_pos (mul_pos hCSh hCsi) hCdd) hCA,
    hNA, fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have hu : ‖Ept z‖ ≤ 1 := norm_Ept_le_one' hz1
  have hu0 : (0 : ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have hsN0 : (0 : ℝ) ≤ (scale τ) ^ NA := scale_rpow_nonneg' τ NA
  have hsplit : Compact.Sh τ z * Compact.Dev2 ℓ τ z
      = (Compact.Sh τ z * Compact.Sinvref τ z) * Compact.dDelta z * Compact.A24 ℓ τ z := by
    simp only [Compact.Dev2]; ring
  rw [hsplit]
  have he1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have hu2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ hu0 hu
  have hb2 : ‖(Compact.Sh τ z * Compact.Sinvref τ z) * Compact.dDelta z‖
      ≤ (CSh * Csi) * (Cdd * ‖Ept z‖ ^ 2) := by
    have h1 : ‖Compact.Sh τ z * Compact.Sinvref τ z‖ ≤ CSh * Csi := by
      rw [norm_mul]
      exact mul_le_mul (hShb τ z t hτ ht hz) (hSib τ z t hτ ht hz) (norm_nonneg _) hCSh.le
    exact norm_mul_le_of h1 (hdd z hz1) (mul_nonneg hCSh.le hCsi.le)
  have hb3 : ‖(Compact.Sh τ z * Compact.Sinvref τ z) * Compact.dDelta z * Compact.A24 ℓ τ z‖
      ≤ ((CSh * Csi) * (Cdd * ‖Ept z‖ ^ 2))
        * (CA * (scale τ) ^ NA * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t)) :=
    norm_mul_le_of hb2 (hA τ z t hτ ht hz)
      (mul_nonneg (mul_nonneg hCSh.le hCsi.le) (mul_nonneg hCdd.le (pow_nonneg hu0 2)))
  calc ‖(Compact.Sh τ z * Compact.Sinvref τ z) * Compact.dDelta z * Compact.A24 ℓ τ z‖
      ≤ ((CSh * Csi) * (Cdd * ‖Ept z‖ ^ 2))
        * (CA * (scale τ) ^ NA * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t)) := hb3
    _ = (CSh * Csi * Cdd * CA * (scale τ) ^ NA * (1 + t))
        * (Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 2) := by ring
    _ ≤ (CSh * Csi * Cdd * CA * (scale τ) ^ NA * (1 + t)) * 1 :=
          mul_le_mul_of_nonneg_left
            (by have h := mul_le_mul he1 hu2 (pow_nonneg hu0 2) (by norm_num); simpa using h)
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCsi.le) hCdd.le) hCA.le) hsN0) (by linarith))
    _ = CSh * Csi * Cdd * CA * (scale τ) ^ NA * (1 + t) := by ring

/-- `Sh · dSinv = 1 - Sh · Sinvref`. -/
theorem Sh_mul_dSinv {τ z : ℍ} (hshne : Compact.Sh τ z ≠ 0) :
    Compact.Sh τ z * ((Compact.Sh τ z)⁻¹ - Compact.Sinvref τ z)
      = 1 - Compact.Sh τ z * Compact.Sinvref τ z := by
  rw [mul_sub, mul_inv_cancel₀ hshne]

/-- `‖Sh τ z · Dev3 ℓ τ z‖ ≤ C (scale τ)^N (1+t)`. -/
theorem Dev3_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Dev3 ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨Chm, hChm, hhmm⟩ := Funnel24Tail.ShSinvrefFunnelBound
  obtain ⟨CK, hCK, hK⟩ := norm_invDelta_bound
  obtain ⟨CA, NA, hCA, hNA, hA⟩ := A24_funnel ℓ
  refine ⟨Chm * CA * (CK + 1), NA, mul_pos (mul_pos hChm hCA) (by linarith), hNA,
    fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have hu : ‖Ept z‖ ≤ 1 := norm_Ept_le_one' hz1
  have hu0 : (0 : ℝ) < ‖Ept z‖ := norm_pos_iff.mpr (Work.Residues.Ept_ne_zero z)
  have hdiv : ‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹ ≤ Real.exp (-(2 * Real.pi)) :=
    Funnel24Tail.Ept_sq_div_le hτ ht hz
  have hdiv1 : ‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹ ≤ 1 :=
    le_trans hdiv (by rw [Real.exp_le_one_iff]; linarith [Real.pi_pos])
  have hq0 : (0 : ℝ) ≤ ‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹ :=
    mul_nonneg (pow_nonneg (norm_nonneg _) 2) (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 2))
  have hshne : Compact.Sh τ z ≠ 0 := by
    have h16 := funnel_Sh_ge τ z t hτ ht hz
    intro h0
    rw [h0, norm_zero] at h16
    norm_num at h16
  have hsplit : Compact.Sh τ z * Compact.Dev3 ℓ τ z
      = (1 - Compact.Sh τ z * Compact.Sinvref τ z) * (DeltaFun z)⁻¹ * Compact.A24 ℓ τ z := by
    simp only [Compact.Dev3, Compact.dSinv]
    rw [show Compact.Sh τ z * (((Compact.Sh τ z)⁻¹ - Compact.Sinvref τ z) * (DeltaFun z)⁻¹
          * Compact.A24 ℓ τ z)
        = (Compact.Sh τ z * ((Compact.Sh τ z)⁻¹ - Compact.Sinvref τ z))
          * ((DeltaFun z)⁻¹ * Compact.A24 ℓ τ z) from by ring,
      Sh_mul_dSinv hshne]
    ring
  rw [hsplit]
  have hfirst : ‖(1 - Compact.Sh τ z * Compact.Sinvref τ z)‖
      ≤ Chm * (‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2 := by
    have h := hhmm τ z t hτ ht hz
    rw [show (1 : ℂ) - Compact.Sh τ z * Compact.Sinvref τ z
        = -(Compact.Sh τ z * Compact.Sinvref τ z - 1) from by ring, norm_neg]
    exact h
  have hinv : ‖(DeltaFun z)⁻¹‖ ≤ (‖Ept z‖ ^ 2)⁻¹ + CK := hK z hz1
  have hinv0 : (0 : ℝ) ≤ (‖Ept z‖ ^ 2)⁻¹ + CK :=
    add_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 2)) hCK
  have hb2 : ‖(1 - Compact.Sh τ z * Compact.Sinvref τ z) * (DeltaFun z)⁻¹‖
      ≤ (Chm * (‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2) * ((‖Ept z‖ ^ 2)⁻¹ + CK) :=
    norm_mul_le_of hfirst hinv (mul_nonneg hChm.le (pow_nonneg hq0 2))
  have hb3 : ‖(1 - Compact.Sh τ z * Compact.Sinvref τ z) * (DeltaFun z)⁻¹
        * Compact.A24 ℓ τ z‖
      ≤ ((Chm * (‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2) * ((‖Ept z‖ ^ 2)⁻¹ + CK))
        * (CA * (scale τ) ^ NA * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t)) :=
    norm_mul_le_of hb2 (hA τ z t hτ ht hz) (mul_nonneg (mul_nonneg hChm.le (pow_nonneg hq0 2)) hinv0)
  have hVeq : Real.exp (-(2 * Real.pi * τ.im)) = ‖Ept τ‖ ^ 2 := by
    rw [Work.Residues.norm_Ept, sq, ← Real.exp_add]
    congr 1; ring
  have hkey := dSinv_key (a := ‖Ept z‖) (V := ‖Ept τ‖ ^ 2) (K := CK) hu0 hdiv1 hu hCK
  calc ‖(1 - Compact.Sh τ z * Compact.Sinvref τ z) * (DeltaFun z)⁻¹ * Compact.A24 ℓ τ z‖
      ≤ ((Chm * (‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2) * ((‖Ept z‖ ^ 2)⁻¹ + CK))
        * (CA * (scale τ) ^ NA * Real.exp (-(2 * Real.pi * τ.im)) * (1 + t)) := hb3
    _ = (Chm * CA * (scale τ) ^ NA * (1 + t))
        * ((‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2 * ((‖Ept z‖ ^ 2)⁻¹ + CK)
          * Real.exp (-(2 * Real.pi * τ.im))) := by ring
    _ = (Chm * CA * (scale τ) ^ NA * (1 + t))
        * ((‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2 * ((‖Ept z‖ ^ 2)⁻¹ + CK)
          * ‖Ept τ‖ ^ 2) := by rw [hVeq]
    _ ≤ (Chm * CA * (scale τ) ^ NA * (1 + t)) * (1 + CK) :=
          mul_le_mul_of_nonneg_left hkey
            (mul_nonneg (mul_nonneg (mul_nonneg hChm.le hCA.le) (scale_rpow_nonneg' τ NA)) (by linarith))
    _ = Chm * CA * (CK + 1) * (scale τ) ^ NA * (1 + t) := by ring

/-- `‖Sh τ z · Dev4 ℓ τ z‖ ≤ C (scale τ)^N (1+t)`. -/
theorem Dev4_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Dev4 ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨CSh, hCSh, hShb⟩ := ShFunnelBound
  obtain ⟨Csi, hCsi, hSib⟩ := Sinvref_funnel
  obtain ⟨CC, NC, hCC, hNC, hC⟩ := C24_funnel ℓ
  obtain ⟨Cdw, hCdw, hdw⟩ := norm_dW_le
  refine ⟨CSh * Csi * CC * Cdw, NC, mul_pos (mul_pos (mul_pos hCSh hCsi) hCC) hCdw,
    hNC, fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have hu : ‖Ept z‖ ≤ 1 := norm_Ept_le_one' hz1
  have hu0 : (0 : ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have hsN0 : (0 : ℝ) ≤ (scale τ) ^ NC := scale_rpow_nonneg' τ NC
  have hsplit : Compact.Sh τ z * Compact.Dev4 ℓ τ z
      = (Compact.Sh τ z * Compact.Sinvref τ z) * Compact.C24 ℓ τ * Compact.dW z := by
    simp only [Compact.Dev4]; ring
  rw [hsplit]
  have hu3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ hu0 hu
  have hb2 : ‖(Compact.Sh τ z * Compact.Sinvref τ z) * Compact.C24 ℓ τ‖
      ≤ (CSh * Csi) * (CC * (scale τ) ^ NC) := by
    have h1 : ‖Compact.Sh τ z * Compact.Sinvref τ z‖ ≤ CSh * Csi := by
      rw [norm_mul]
      exact mul_le_mul (hShb τ z t hτ ht hz) (hSib τ z t hτ ht hz) (norm_nonneg _) hCSh.le
    exact norm_mul_le_of h1 (hC τ hτ) (mul_nonneg hCSh.le hCsi.le)
  have hb3 : ‖(Compact.Sh τ z * Compact.Sinvref τ z) * Compact.C24 ℓ τ * Compact.dW z‖
      ≤ ((CSh * Csi) * (CC * (scale τ) ^ NC)) * (Cdw * ‖Ept z‖ ^ 3) :=
    norm_mul_le_of hb2 (hdw z hz1)
      (mul_nonneg (mul_nonneg hCSh.le hCsi.le) (mul_nonneg hCC.le hsN0))
  calc ‖(Compact.Sh τ z * Compact.Sinvref τ z) * Compact.C24 ℓ τ * Compact.dW z‖
      ≤ ((CSh * Csi) * (CC * (scale τ) ^ NC)) * (Cdw * ‖Ept z‖ ^ 3) := hb3
    _ = (CSh * Csi * CC * Cdw * (scale τ) ^ NC) * ‖Ept z‖ ^ 3 := by ring
    _ ≤ (CSh * Csi * CC * Cdw * (scale τ) ^ NC) * 1 :=
          mul_le_mul_of_nonneg_left hu3 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCsi.le) hCC.le) hCdw.le) hsN0)
    _ ≤ (CSh * Csi * CC * Cdw * (scale τ) ^ NC) * (1 + t) :=
          mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + t)
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCsi.le) hCC.le) hCdw.le) hsN0)

/-- `‖Sh τ z · Dev5 ℓ τ z‖ ≤ C (scale τ)^N (1+t)`. -/
theorem Dev5_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Dev5 ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨Chm, hChm, hhmm⟩ := Funnel24Tail.ShSinvrefFunnelBound
  obtain ⟨CC, NC, hCC, hNC, hC⟩ := C24_funnel ℓ
  obtain ⟨CW, hCW, hW⟩ := norm_W_le
  refine ⟨Chm * CC * CW, NC, mul_pos (mul_pos hChm hCC) hCW, hNC, fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have hsN0 : (0 : ℝ) ≤ (scale τ) ^ NC := scale_rpow_nonneg' τ NC
  have hdiv : ‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹ ≤ Real.exp (-(2 * Real.pi)) :=
    Funnel24Tail.Ept_sq_div_le hτ ht hz
  have hdiv1 : ‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹ ≤ 1 :=
    le_trans hdiv (by rw [Real.exp_le_one_iff]; linarith [Real.pi_pos])
  have hq0 : (0 : ℝ) ≤ ‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹ :=
    mul_nonneg (pow_nonneg (norm_nonneg _) 2) (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 2))
  have hshne : Compact.Sh τ z ≠ 0 := by
    have h16 := funnel_Sh_ge τ z t hτ ht hz
    intro h0
    rw [h0, norm_zero] at h16
    norm_num at h16
  have hsplit : Compact.Sh τ z * Compact.Dev5 ℓ τ z
      = (1 - Compact.Sh τ z * Compact.Sinvref τ z) * Compact.C24 ℓ τ * WFun z := by
    simp only [Compact.Dev5, Compact.dSinv]
    rw [show Compact.Sh τ z * (((Compact.Sh τ z)⁻¹ - Compact.Sinvref τ z) * Compact.C24 ℓ τ
          * WFun z)
        = (Compact.Sh τ z * ((Compact.Sh τ z)⁻¹ - Compact.Sinvref τ z))
          * (Compact.C24 ℓ τ * WFun z) from by ring,
      Sh_mul_dSinv hshne]
    ring
  rw [hsplit]
  have hfirst : ‖(1 - Compact.Sh τ z * Compact.Sinvref τ z)‖
      ≤ Chm * (‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2 := by
    have h := hhmm τ z t hτ ht hz
    rw [show (1 : ℂ) - Compact.Sh τ z * Compact.Sinvref τ z
        = -(Compact.Sh τ z * Compact.Sinvref τ z - 1) from by ring, norm_neg]
    exact h
  have hkey : (‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2 ≤ 1 := pow_le_one₀ hq0 hdiv1
  have hb2 : ‖(1 - Compact.Sh τ z * Compact.Sinvref τ z) * Compact.C24 ℓ τ‖
      ≤ (Chm * (‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2) * (CC * (scale τ) ^ NC) :=
    norm_mul_le_of hfirst (hC τ hτ) (mul_nonneg hChm.le (pow_nonneg hq0 2))
  have hb3 : ‖(1 - Compact.Sh τ z * Compact.Sinvref τ z) * Compact.C24 ℓ τ * WFun z‖
      ≤ ((Chm * (‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2) * (CC * (scale τ) ^ NC)) * CW :=
    norm_mul_le_of hb2 (hW z hz1)
      (mul_nonneg (mul_nonneg hChm.le (pow_nonneg hq0 2)) (mul_nonneg hCC.le hsN0))
  calc ‖(1 - Compact.Sh τ z * Compact.Sinvref τ z) * Compact.C24 ℓ τ * WFun z‖
      ≤ ((Chm * (‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2) * (CC * (scale τ) ^ NC)) * CW := hb3
    _ = (Chm * CC * CW * (scale τ) ^ NC) * ((‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2) := by ring
    _ ≤ (Chm * CC * CW * (scale τ) ^ NC) * 1 :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg (mul_nonneg (mul_nonneg hChm.le hCC.le) hCW.le) (scale_rpow_nonneg' τ NC))
    _ ≤ (Chm * CC * CW * (scale τ) ^ NC) * (1 + t) :=
          mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + t)
            (mul_nonneg (mul_nonneg (mul_nonneg hChm.le hCC.le) hCW.le) (scale_rpow_nonneg' τ NC))

/-- `‖Sh τ z · Dev6 ℓ τ z‖ ≤ C (scale τ)^N (1+t)`. -/
theorem Dev6_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Dev6 ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨CSh, hCSh, hShb⟩ := ShFunnelBound
  obtain ⟨Cdw, hCdw, hdw⟩ := norm_dW_le
  obtain ⟨CB, NB, hCB, hNB, hB⟩ := B24_funnel ℓ
  refine ⟨CSh * Cdw * CB * 25, NB, mul_pos (mul_pos (mul_pos hCSh hCdw) hCB) (by norm_num),
    hNB, fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have hu : ‖Ept z‖ ≤ 1 := norm_Ept_le_one' hz1
  have hu0 : (0 : ℝ) < ‖Ept z‖ := norm_pos_iff.mpr (Work.Residues.Ept_ne_zero z)
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have hsN0 : (0 : ℝ) ≤ (scale τ) ^ NB := scale_rpow_nonneg' τ NB
  have hDref0 : (0 : ℝ) ≤ (‖Ept z‖ ^ 2)⁻¹ + 24 :=
    add_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 2)) (by norm_num)
  have hDref : ‖Compact.Dref z‖ ≤ (‖Ept z‖ ^ 2)⁻¹ + 24 := Funnel24.norm_Dref_le hz1
  have hsplit : Compact.Sh τ z * Compact.Dev6 ℓ τ z
      = -(Compact.Sh τ z * Compact.Dref z * Compact.dW z * Compact.B24 ℓ τ) := by
    simp only [Compact.Dev6]; ring
  rw [hsplit, norm_neg]
  have he1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have hkey := inv_sq_add_cube (a := ‖Ept z‖) (K := 24) hu0 hu (by norm_num)
  have hb2 : ‖Compact.Sh τ z * Compact.Dref z * Compact.dW z‖
      ≤ (CSh * ((‖Ept z‖ ^ 2)⁻¹ + 24)) * (Cdw * ‖Ept z‖ ^ 3) := by
    have h1 : ‖Compact.Sh τ z * Compact.Dref z‖ ≤ CSh * ((‖Ept z‖ ^ 2)⁻¹ + 24) := by
      rw [norm_mul]
      exact mul_le_mul (hShb τ z t hτ ht hz) hDref (norm_nonneg _) hCSh.le
    calc ‖Compact.Sh τ z * Compact.Dref z * Compact.dW z‖
        = ‖Compact.Sh τ z * Compact.Dref z‖ * ‖Compact.dW z‖ := norm_mul _ _
      _ ≤ (CSh * ((‖Ept z‖ ^ 2)⁻¹ + 24)) * (Cdw * ‖Ept z‖ ^ 3) :=
          mul_le_mul h1 (hdw z hz1) (norm_nonneg _) (mul_nonneg hCSh.le hDref0)
  have hb3 : ‖Compact.Sh τ z * Compact.Dref z * Compact.dW z * Compact.B24 ℓ τ‖
      ≤ ((CSh * ((‖Ept z‖ ^ 2)⁻¹ + 24)) * (Cdw * ‖Ept z‖ ^ 3))
        * (CB * (scale τ) ^ NB * Real.exp (-(2 * Real.pi * τ.im))) :=
    norm_mul_le_of hb2 (hB τ hτ)
      (mul_nonneg (mul_nonneg hCSh.le hDref0) (mul_nonneg hCdw.le (pow_nonneg (norm_nonneg _) 3)))
  calc ‖Compact.Sh τ z * Compact.Dref z * Compact.dW z * Compact.B24 ℓ τ‖
      ≤ ((CSh * ((‖Ept z‖ ^ 2)⁻¹ + 24)) * (Cdw * ‖Ept z‖ ^ 3))
        * (CB * (scale τ) ^ NB * Real.exp (-(2 * Real.pi * τ.im))) := hb3
    _ = ((CSh * Cdw * CB * (scale τ) ^ NB) * Real.exp (-(2 * Real.pi * τ.im)))
        * (((‖Ept z‖ ^ 2)⁻¹ + 24) * ‖Ept z‖ ^ 3) := by ring
    _ ≤ ((CSh * Cdw * CB * (scale τ) ^ NB) * Real.exp (-(2 * Real.pi * τ.im))) * (1 + 24) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCdw.le) hCB.le) hsN0) hE0)
    _ ≤ ((CSh * Cdw * CB * (scale τ) ^ NB) * 1) * (1 + 24) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1
            (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCdw.le) hCB.le) hsN0)) (by norm_num)
    _ = CSh * Cdw * CB * 25 * (scale τ) ^ NB := by ring
    _ ≤ CSh * Cdw * CB * 25 * (scale τ) ^ NB * (1 + t) :=
          le_mul_of_one_le_right (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCdw.le) hCB.le) (by norm_num)) hsN0)
            (by linarith : (1 : ℝ) ≤ 1 + t)

/-- `‖Sh τ z · Dev7 ℓ τ z‖ ≤ C (scale τ)^N (1+t)`. -/
theorem Dev7_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Dev7 ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨CSh, hCSh, hShb⟩ := ShFunnelBound
  obtain ⟨Cdd, hCdd, hdd⟩ := norm_dDelta_le
  obtain ⟨CW, hCW, hW⟩ := norm_W_le
  obtain ⟨CB, NB, hCB, hNB, hB⟩ := B24_funnel ℓ
  refine ⟨CSh * Cdd * CW * CB, NB, mul_pos (mul_pos (mul_pos hCSh hCdd) hCW) hCB,
    hNB, fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have hu : ‖Ept z‖ ≤ 1 := norm_Ept_le_one' hz1
  have hu0 : (0 : ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have hsN0 : (0 : ℝ) ≤ (scale τ) ^ NB := scale_rpow_nonneg' τ NB
  have hsplit : Compact.Sh τ z * Compact.Dev7 ℓ τ z
      = -(Compact.Sh τ z * Compact.dDelta z * WFun z * Compact.B24 ℓ τ) := by
    simp only [Compact.Dev7]; ring
  rw [hsplit, norm_neg]
  have he1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have hu2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ hu0 hu
  have hb2 : ‖Compact.Sh τ z * Compact.dDelta z * WFun z‖
      ≤ (CSh * (Cdd * ‖Ept z‖ ^ 2)) * CW := by
    have h1 : ‖Compact.Sh τ z * Compact.dDelta z‖ ≤ CSh * (Cdd * ‖Ept z‖ ^ 2) := by
      rw [norm_mul]
      exact mul_le_mul (hShb τ z t hτ ht hz) (hdd z hz1) (norm_nonneg _) hCSh.le
    calc ‖Compact.Sh τ z * Compact.dDelta z * WFun z‖
        = ‖Compact.Sh τ z * Compact.dDelta z‖ * ‖WFun z‖ := norm_mul _ _
      _ ≤ (CSh * (Cdd * ‖Ept z‖ ^ 2)) * CW :=
          mul_le_mul h1 (hW z hz1) (norm_nonneg _)
            (mul_nonneg hCSh.le (mul_nonneg hCdd.le (pow_nonneg hu0 2)))
  have hb3 : ‖Compact.Sh τ z * Compact.dDelta z * WFun z * Compact.B24 ℓ τ‖
      ≤ ((CSh * (Cdd * ‖Ept z‖ ^ 2)) * CW)
        * (CB * (scale τ) ^ NB * Real.exp (-(2 * Real.pi * τ.im))) :=
    norm_mul_le_of hb2 (hB τ hτ)
      (mul_nonneg (mul_nonneg hCSh.le (mul_nonneg hCdd.le (pow_nonneg hu0 2))) hCW.le)
  calc ‖Compact.Sh τ z * Compact.dDelta z * WFun z * Compact.B24 ℓ τ‖
      ≤ ((CSh * (Cdd * ‖Ept z‖ ^ 2)) * CW)
        * (CB * (scale τ) ^ NB * Real.exp (-(2 * Real.pi * τ.im))) := hb3
    _ = ((CSh * Cdd * CW * CB * (scale τ) ^ NB) * Real.exp (-(2 * Real.pi * τ.im)))
        * ‖Ept z‖ ^ 2 := by ring
    _ ≤ ((CSh * Cdd * CW * CB * (scale τ) ^ NB) * Real.exp (-(2 * Real.pi * τ.im))) * 1 :=
          mul_le_mul_of_nonneg_left hu2 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCdd.le) hCW.le) hCB.le) hsN0) hE0)
    _ ≤ ((CSh * Cdd * CW * CB * (scale τ) ^ NB) * 1) * 1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCdd.le) hCW.le) hCB.le) hsN0)) (by norm_num)
    _ = CSh * Cdd * CW * CB * (scale τ) ^ NB := by ring
    _ ≤ CSh * Cdd * CW * CB * (scale τ) ^ NB * (1 + t) :=
          le_mul_of_one_le_right (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCSh.le hCdd.le) hCW.le) hCB.le) hsN0)
            (by linarith : (1 : ℝ) ≤ 1 + t)

/-! ## Assembly -/

/-- `‖Sh τ z · Σ Devᵢ‖ ≤ C (scale τ)^N (1+t)`. -/
theorem DevSum_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Dev24Sum ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := Dev1_bound ℓ
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := Dev2_bound ℓ
  obtain ⟨C3, N3, hC3, hN3, h3⟩ := Dev3_bound ℓ
  obtain ⟨C4, N4, hC4, hN4, h4⟩ := Dev4_bound ℓ
  obtain ⟨C5, N5, hC5, hN5, h5⟩ := Dev5_bound ℓ
  obtain ⟨C6, N6, hC6, hN6, h6⟩ := Dev6_bound ℓ
  obtain ⟨C7, N7, hC7, hN7, h7⟩ := Dev7_bound ℓ
  refine ⟨C1 + (C2 + (C3 + (C4 + (C5 + (C6 + C7))))),
    N1 + (N2 + (N3 + (N4 + (N5 + (N6 + N7))))), by positivity, by positivity,
    fun τ z t hτ ht hz => ?_⟩
  have hsplit : Compact.Sh τ z * Compact.Dev24Sum ℓ τ z
      = Compact.Sh τ z * Compact.Dev1 ℓ τ z
        + (Compact.Sh τ z * Compact.Dev2 ℓ τ z
          + (Compact.Sh τ z * Compact.Dev3 ℓ τ z
            + (Compact.Sh τ z * Compact.Dev4 ℓ τ z
              + (Compact.Sh τ z * Compact.Dev5 ℓ τ z
                + (Compact.Sh τ z * Compact.Dev6 ℓ τ z
                  + Compact.Sh τ z * Compact.Dev7 ℓ τ z))))) := by
    simp only [Compact.Dev24Sum]; ring
  rw [hsplit]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have b67 := add_bound (h6 τ z t hτ ht hz) (h7 τ z t hτ ht hz) hC6.le hC7.le hN6 hN7 ht0
  have b567 := add_bound (h5 τ z t hτ ht hz) b67 hC5.le (by positivity) hN5 (by positivity) ht0
  have b4567 := add_bound (h4 τ z t hτ ht hz) b567 hC4.le (by positivity) hN4 (by positivity) ht0
  have b34567 := add_bound (h3 τ z t hτ ht hz) b4567 hC3.le (by positivity) hN3 (by positivity) ht0
  have b234567 := add_bound (h2 τ z t hτ ht hz) b34567 hC2.le (by positivity) hN2 (by positivity) ht0
  exact add_bound (h1 τ z t hτ ht hz) b234567 hC1.le (by positivity) hN1 (by positivity) ht0

/-- `‖Sh τ z · (Tref24 ℓ τ z + Σ Devᵢ)‖ ≤ C (scale τ)^N (1+t)`. -/
theorem ShTrefDev_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * (Compact.Tref24 ℓ τ z + Compact.Dev24Sum ℓ τ z)‖
        ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := ShTref_bound ℓ
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := DevSum_bound ℓ
  refine ⟨C1 + C2, N1 + N2, by positivity, by positivity, fun τ z t hτ ht hz => ?_⟩
  have hsplit : Compact.Sh τ z * (Compact.Tref24 ℓ τ z + Compact.Dev24Sum ℓ τ z)
      = Compact.Sh τ z * Compact.Tref24 ℓ τ z + Compact.Sh τ z * Compact.Dev24Sum ℓ τ z := by
    ring
  rw [hsplit]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  exact add_bound (h1 τ z t hτ ht hz) (h2 τ z t hτ ht hz) hC1.le hC2.le hN1 hN2 ht0

/-- **The core bound for the `d = 24` funnel tail.**

For `τ` in the funnel and `z = i t`, `t ≥ Im τ + 1`, the bracket
`brMinus 24 τ z + Sh τ z · br0 24 ℓ τ z` (which is `3456π·Sh·(K₋^{(24)} - 𝒢₋^{(24)})`) is bounded
by `C (scale τ)^N (1+t)^M`.  (The caller only needs this *non-decaying* form: combined with
`‖Sh⁻¹‖ ≤ 16` and `e^{-π(t-Im τ)} ≥ e^{-π}` it yields the decaying tail bound.) -/
theorem KMinusFunnelMainBound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Asymptotics.Compact.brMinus ℓ 24 τ z
            + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C, N, hC, hN, hb⟩ := ShTrefDev_bound ℓ
  refine ⟨C, N, 1, hC, hN, by norm_num, fun τ z t hτ ht hz => ?_⟩
  have hSh16 := funnel_Sh_ge τ z t hτ ht hz
  have hshne : Compact.Sh τ z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hSh16
    norm_num at hSh16
  have hdec := Compact.decomp24_sum ℓ τ z hshne
  have hQ : Compact.brMinus ℓ 24 τ z + Compact.Sh τ z * Compact.br0 24 ℓ τ z
      = Compact.Sh τ z * (Compact.Tref24 ℓ τ z + Compact.Dev24Sum ℓ τ z) := by
    have h2 : Compact.Sh τ z * ((Compact.Sh τ z)⁻¹
        * (Compact.brMinus ℓ 24 τ z + Compact.Sh τ z * Compact.br0 24 ℓ τ z))
        = Compact.brMinus ℓ 24 τ z + Compact.Sh τ z * Compact.br0 24 ℓ τ z := by
      rw [← mul_assoc, mul_inv_cancel₀ hshne, one_mul]
    rw [← h2, hdec]
  rw [hQ]
  simpa using hb τ z t hτ ht hz

end

end Work.Asymptotics
