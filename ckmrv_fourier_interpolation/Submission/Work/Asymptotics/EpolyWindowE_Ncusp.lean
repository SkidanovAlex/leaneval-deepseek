/-
# The polynomial bound for the cleared `K_-`-numerator `Ncusp` at `z = i s`, `s ≤ 1`

`Ncusp ℓ d τ z` (`Work.Asymptotics.KMinusCuspBallDefs`) is the cleared cusp numerator of
CKMRV's `K_-`:

  `Ncusp ℓ d τ z = Δ(z)(j τ - j z) z^{-(2-d/2)} K_-^{(d)}(τ, S·z)`   (`Ncusp_ident`).

This file proves `Work.Asymptotics.EpolyWindowE_ncusp_low_bound`, the "below the pole" bound
that the far-window brick `Work.Asymptotics.EWindow_far` consumes:

for `w ∈ E = KEpsilon` and `0 < s ≤ 1` with `s⁻¹ ≤ Im (S • w) - 1`,

  `‖Ncusp ℓ d w (i s)‖ ≤ C (scale w)^N (1 + s⁻¹)^M`.

The proof expands the two explicit formulas

* `Ncusp ℓ 8 τ z = (2·1728·π)⁻¹ · T8 ℓ τ z`   (`Ncusp_eight_expansion`),
* `Ncusp ℓ 24 τ z = (2·1728·π)⁻¹ · T24 ℓ τ z` (`Ncusp_twentyfour_expansion`),

and bounds each factor.  The `z`-side atoms at `z = i s` are transported by the `S`-laws to the
funnel point `i/s` (`Im = 1/s ≥ 1`) where the theta quartics and `E₄, E₆` are bounded, the two
exponentials `e^{2π/s}` (`‖j(i s)‖`, `‖Δ(i s)‖⁻¹`) being cancelled against `e^{-2π Im (S•w)}`
via the hypothesis `s⁻¹ ≤ Im (S • w) - 1`.  The `τ`-side atoms are bounded on `EReg ⊇ KEpsilon`
by `Work.Asymptotics.EReg_atom_bounds` and the CKMRV `E`-order cancellation identities
`Work.Asymptotics.EReg_identities`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.ERegDefs
import Submission.Work.Asymptotics.EReg_atom_bounds
import Submission.Work.Asymptotics.EReg_alpha8_bound
import Submission.Work.Asymptotics.EReg_alpha24_bound
import Submission.Work.Asymptotics.EReg_identities
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.Xi8_low_bound
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Kernels.All
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

noncomputable section

open Work.Kernels

set_option maxHeartbeats 8000000

/-! ## Elementary geometry -/

lemma KEpsilon_subset_EReg {w : UpperHalfPlane} (hw : w ∈ KEpsilon) : w ∈ EReg := by
  rw [mem_EReg]
  exact le_trans (by norm_num) hw.2

/-- `tS τ = e^{-π Im (S • τ)}`. -/
lemma tS_eq_exp (τ : UpperHalfPlane) :
    tS τ = Real.exp (-(Real.pi * (ModularGroup.S • τ).im)) := rfl

/-- `scale (i s) ≤ 3 (1 + s⁻¹)` for `0 < s ≤ 1`. -/
lemma scale_imagAxis_le (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    scale (imagAxis s hs) ≤ 3 * (1 + s⁻¹) := by
  have hnorm : ‖((imagAxis s hs : UpperHalfPlane) : ℂ)‖ = s := norm_imagAxis_coe' s hs
  have him : (imagAxis s hs).im = s := imagAxis_im' s hs
  have hs0 : 0 ≤ s := hs.le
  have hinv0 : 0 ≤ s⁻¹ := inv_nonneg.mpr hs0
  have hinv1 : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  rw [scale, hnorm, him]
  linarith

/-! ## The `z`-side atoms at `z = i s` -/

lemma E4_imagAxis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖E4Fun (imagAxis s hs)‖ ≤ C * (1 + s⁻¹) ^ (4 : ℕ) := by
  obtain ⟨CΔ, C4, C6, C2, Cd, Ce, hCΔ, hC4, hC6, hC2, hCd, hCe, hat⟩ := imagAxis_atoms_bound
  exact ⟨C4, hC4, fun s hs hs1 => (hat s hs hs1).2.1⟩

lemma E6_imagAxis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖E6Fun (imagAxis s hs)‖ ≤ C * (1 + s⁻¹) ^ (6 : ℕ) := by
  obtain ⟨CΔ, C4, C6, C2, Cd, Ce, hCΔ, hC4, hC6, hC2, hCd, hCe, hat⟩ := imagAxis_atoms_bound
  exact ⟨C6, hC6, fun s hs hs1 => (hat s hs hs1).2.2.1⟩

lemma E8_imagAxis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖E8Fun (imagAxis s hs)‖ ≤ C * (1 + s⁻¹) ^ (8 : ℕ) := by
  obtain ⟨C4, hC4, hb⟩ := E4_imagAxis_bound
  refine ⟨C4 ^ 2, by positivity, fun s hs hs1 => ?_⟩
  have h4 := hb s hs hs1
  have hE8 : E8Fun (imagAxis s hs) = E4Fun (imagAxis s hs) ^ 2 := rfl
  rw [hE8, norm_pow]
  calc ‖E4Fun (imagAxis s hs)‖ ^ 2 ≤ (C4 * (1 + s⁻¹) ^ (4 : ℕ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h4 2
    _ = C4 ^ 2 * (1 + s⁻¹) ^ (8 : ℕ) := by ring

lemma E10_imagAxis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖E10Fun (imagAxis s hs)‖ ≤ C * (1 + s⁻¹) ^ (10 : ℕ) := by
  obtain ⟨C4, hC4, h4b⟩ := E4_imagAxis_bound
  obtain ⟨C6, hC6, h6b⟩ := E6_imagAxis_bound
  refine ⟨C4 * C6, by positivity, fun s hs hs1 => ?_⟩
  have h10 : E10Fun (imagAxis s hs) = E4Fun (imagAxis s hs) * E6Fun (imagAxis s hs) := rfl
  rw [h10, norm_mul]
  calc ‖E4Fun (imagAxis s hs)‖ * ‖E6Fun (imagAxis s hs)‖
      ≤ (C4 * (1 + s⁻¹) ^ (4 : ℕ)) * (C6 * (1 + s⁻¹) ^ (6 : ℕ)) :=
        mul_le_mul (h4b s hs hs1) (h6b s hs hs1) (norm_nonneg _)
          (by positivity)
    _ = (C4 * C6) * (1 + s⁻¹) ^ (10 : ℕ) := by ring

lemma E14_imagAxis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖E14Fun (imagAxis s hs)‖ ≤ C * (1 + s⁻¹) ^ (14 : ℕ) := by
  obtain ⟨C4, hC4, h4b⟩ := E4_imagAxis_bound
  obtain ⟨C6, hC6, h6b⟩ := E6_imagAxis_bound
  refine ⟨C4 ^ 2 * C6, by positivity, fun s hs hs1 => ?_⟩
  have h14 : E14Fun (imagAxis s hs) = E4Fun (imagAxis s hs) ^ 2 * E6Fun (imagAxis s hs) := rfl
  rw [h14, norm_mul, norm_pow]
  calc ‖E4Fun (imagAxis s hs)‖ ^ 2 * ‖E6Fun (imagAxis s hs)‖
      ≤ (C4 * (1 + s⁻¹) ^ (4 : ℕ)) ^ 2 * (C6 * (1 + s⁻¹) ^ (6 : ℕ)) := by
        refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (h4b s hs hs1) 2) (h6b s hs hs1)
          (norm_nonneg _) (by positivity)
    _ = (C4 ^ 2 * C6) * (1 + s⁻¹) ^ (14 : ℕ) := by ring

/-- `‖V (i s)‖ ≤ C (1 + s⁻¹)²`: `V(τ) = -(S•τ)² W(S•τ)` and `W = 1 + O(e^{-π Im})`. -/
lemma V_imagAxis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖VFun (imagAxis s hs)‖ ≤ C * (1 + s⁻¹) ^ (2 : ℕ) := by
  obtain ⟨C2, hC2, h2⟩ := Work.Residues.WFun_decay
  refine ⟨1 + C2, by linarith, fun s hs hs1 => ?_⟩
  have hS : ModularGroup.S • imagAxis s hs = imagAxis s⁻¹ (inv_pos.mpr hs) :=
    imagAxis_smul_S s hs
  have hVS := EReg_V_S (imagAxis s hs)
  rw [hS] at hVS
  have hnorm : ‖((imagAxis s⁻¹ (inv_pos.mpr hs) : UpperHalfPlane) : ℂ)‖ = s⁻¹ :=
    norm_imagAxis_coe' s⁻¹ (inv_pos.mpr hs)
  have him : (imagAxis s⁻¹ (inv_pos.mpr hs)).im = s⁻¹ :=
    imagAxis_im' s⁻¹ (inv_pos.mpr hs)
  have hsinv1 : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  have hsinv0 : (0 : ℝ) ≤ s⁻¹ := le_trans zero_le_one hsinv1
  have hW : ‖WFun (imagAxis s⁻¹ (inv_pos.mpr hs))‖ ≤ 1 + C2 := by
    have h := h2 (imagAxis s⁻¹ (inv_pos.mpr hs)) (by rw [him]; exact hsinv1)
    have h3 : ‖WFun (imagAxis s⁻¹ (inv_pos.mpr hs))
        - 1‖ ≤ C2 * Real.exp (-(Real.pi * s⁻¹)) := by
      simpa [him] using h
    have h4 : Real.exp (-(Real.pi * s⁻¹)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hsinv0])
    have h5 : C2 * Real.exp (-(Real.pi * s⁻¹)) ≤ C2 :=
      by simpa using mul_le_of_le_one_right hC2.le h4
    calc ‖WFun (imagAxis s⁻¹ (inv_pos.mpr hs))‖
        = ‖(WFun (imagAxis s⁻¹ (inv_pos.mpr hs)) - 1) + 1‖ := by ring_nf
      _ ≤ ‖WFun (imagAxis s⁻¹ (inv_pos.mpr hs)) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖WFun (imagAxis s⁻¹ (inv_pos.mpr hs)) - 1‖ + 1 := by rw [norm_one]
      _ ≤ 1 + C2 := by linarith
  rw [hVS, norm_mul, norm_neg, norm_pow, hnorm]
  have hsq : (s⁻¹) ^ 2 ≤ (1 + s⁻¹) ^ 2 := by
    have : s⁻¹ ≤ 1 + s⁻¹ := by linarith
    exact pow_le_pow_left₀ hsinv0 this 2
  calc (s⁻¹) ^ 2 * ‖WFun (imagAxis s⁻¹ (inv_pos.mpr hs))‖
      ≤ (s⁻¹) ^ 2 * (1 + C2) := mul_le_mul_of_nonneg_left hW (by positivity)
    _ ≤ (1 + s⁻¹) ^ 2 * (1 + C2) := mul_le_mul_of_nonneg_right hsq (by linarith)
    _ = (1 + C2) * (1 + s⁻¹) ^ 2 := by ring

/-- `‖U (i s)² - W (i s)²‖ ≤ C (1 + s⁻¹)⁴`. -/
lemma UW2_imagAxis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2‖
        ≤ C * (1 + s⁻¹) ^ (4 : ℕ) := by
  obtain ⟨C1, hC1, h1⟩ := Work.Residues.UFun_decay
  obtain ⟨C3, hC3, h3⟩ := Work.Residues.VFun_decay
  refine ⟨(1 + C1) ^ 2 + C3 ^ 2 + 1, by positivity, fun s hs hs1 => ?_⟩
  have hS : ModularGroup.S • imagAxis s hs = imagAxis s⁻¹ (inv_pos.mpr hs) :=
    imagAxis_smul_S s hs
  have hnorm : ‖((imagAxis s⁻¹ (inv_pos.mpr hs) : UpperHalfPlane) : ℂ)‖ = s⁻¹ :=
    norm_imagAxis_coe' s⁻¹ (inv_pos.mpr hs)
  have him : (imagAxis s⁻¹ (inv_pos.mpr hs)).im = s⁻¹ :=
    imagAxis_im' s⁻¹ (inv_pos.mpr hs)
  have hsinv1 : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  have hsinv0 : (0 : ℝ) ≤ s⁻¹ := le_trans zero_le_one hsinv1
  -- `‖U(i s)‖ ≤ s⁻²(1+C1)`, `‖W(i s)‖ ≤ s⁻² C3`
  have hU : ‖UFun (imagAxis s hs)‖ ≤ s⁻¹ ^ 2 * (1 + C1) := by
    have hUS := EReg_U_S (imagAxis s hs)
    rw [hS] at hUS
    have hb : ‖UFun (imagAxis s⁻¹ (inv_pos.mpr hs))‖ ≤ 1 + C1 := by
      have h := h1 (imagAxis s⁻¹ (inv_pos.mpr hs)) (by rw [him]; exact hsinv1)
      have h4 : Real.exp (-(Real.pi * s⁻¹)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hsinv0])
      have h5 : C1 * Real.exp (-(Real.pi * s⁻¹)) ≤ C1 :=
        by simpa using mul_le_of_le_one_right hC1.le h4
      calc ‖UFun (imagAxis s⁻¹ (inv_pos.mpr hs))‖
          = ‖(UFun (imagAxis s⁻¹ (inv_pos.mpr hs)) - 1) + 1‖ := by ring_nf
        _ ≤ ‖UFun (imagAxis s⁻¹ (inv_pos.mpr hs)) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖UFun (imagAxis s⁻¹ (inv_pos.mpr hs)) - 1‖ + 1 := by rw [norm_one]
        _ ≤ 1 + C1 := by
            have h3' : ‖UFun (imagAxis s⁻¹ (inv_pos.mpr hs)) - 1‖
                ≤ C1 * Real.exp (-(Real.pi * s⁻¹)) := by simpa [him] using h
            linarith
    rw [hUS, norm_mul, norm_neg, norm_pow, hnorm]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hV : ‖WFun (imagAxis s hs)‖ ≤ s⁻¹ ^ 2 * C3 := by
    have hWS := EReg_W_S (imagAxis s hs)
    rw [hS] at hWS
    have hb : ‖VFun (imagAxis s⁻¹ (inv_pos.mpr hs))‖ ≤ C3 := by
      have h := h3 (imagAxis s⁻¹ (inv_pos.mpr hs)) (by rw [him]; exact hsinv1)
      have h4 : Real.exp (-(Real.pi * s⁻¹)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hsinv0])
      have h5 : C3 * Real.exp (-(Real.pi * s⁻¹)) ≤ C3 :=
        by simpa using mul_le_of_le_one_right hC3.le h4
      rw [him] at h
      linarith
    rw [hWS, norm_mul, norm_neg, norm_pow, hnorm]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hsq : ((s⁻¹) ^ 2) ^ 2 ≤ ((1 + s⁻¹) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by
      have : s⁻¹ ≤ 1 + s⁻¹ := by linarith
      exact pow_le_pow_left₀ hsinv0 this 2) 2
  have hkey : ((s⁻¹) ^ 2) ^ 2 = (s⁻¹) ^ 4 := by ring
  have hkey2 : ((1 + s⁻¹) ^ 2) ^ 2 = (1 + s⁻¹) ^ 4 := by ring
  rw [hkey, hkey2] at hsq
  calc ‖UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2‖
      ≤ ‖UFun (imagAxis s hs) ^ 2‖ + ‖WFun (imagAxis s hs) ^ 2‖ := norm_sub_le _ _
    _ = ‖UFun (imagAxis s hs)‖ ^ 2 + ‖WFun (imagAxis s hs)‖ ^ 2 := by
        simp only [norm_pow]
    _ ≤ (s⁻¹ ^ 2 * (1 + C1)) ^ 2 + (s⁻¹ ^ 2 * C3) ^ 2 :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) hU 2)
          (pow_le_pow_left₀ (norm_nonneg _) hV 2)
    _ = (s⁻¹) ^ 4 * ((1 + C1) ^ 2 + C3 ^ 2) := by ring
    _ ≤ (1 + s⁻¹) ^ 4 * ((1 + C1) ^ 2 + C3 ^ 2) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ ≤ ((1 + C1) ^ 2 + C3 ^ 2 + 1) * (1 + s⁻¹) ^ 4 := by
        have h1' : (0 : ℝ) ≤ (1 + s⁻¹) ^ 4 := by positivity
        nlinarith [h1']

/-- `S • (i/t) = i t`. -/
lemma S_smul_imagAxis_invE (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • imagAxis t⁻¹ (inv_pos.mpr ht) = imagAxis t ht := by
  apply UpperHalfPlane.ext
  rw [Work.Kernels.S_smul_coe]
  rw [show ((imagAxis t⁻¹ (inv_pos.mpr ht) : UpperHalfPlane) : ℂ)
        = ((t⁻¹ : ℝ) : ℂ) * Complex.I from rfl,
      show ((imagAxis t ht : UpperHalfPlane) : ℂ) = ((t : ℝ) : ℂ) * Complex.I from rfl]
  rw [Complex.ofReal_inv, mul_inv, Complex.inv_I, inv_inv]
  ring

/-- `1/Δ(i s) = O(s^{12} e^{2π/s})`. -/
lemma DeltaFun_imagAxis_inv_boundE :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖DeltaFun (imagAxis s hs)‖⁻¹ ≤ C * s ^ 12 * Real.exp (2 * Real.pi / s) := by
  refine ⟨2, by norm_num, fun s hs hs1 => ?_⟩
  have hS : ModularGroup.S • imagAxis s⁻¹ (inv_pos.mpr hs) = imagAxis s hs :=
    S_smul_imagAxis_invE s hs
  have h := DeltaFun_S_smul' (imagAxis s⁻¹ (inv_pos.mpr hs))
  rw [hS] at h
  have hnorm : ‖DeltaFun (imagAxis s⁻¹ (inv_pos.mpr hs))‖
      = s ^ 12 * ‖DeltaFun (imagAxis s hs)‖ := by
    rw [h, norm_mul, norm_pow, norm_imagAxis_coe' s hs]
  have hlow := DeltaFun_imagAxis_lower_sharp s⁻¹ (inv_pos.mpr hs) ((one_le_inv₀ hs).mpr hs1)
  have hs12 : (0 : ℝ) < s ^ 12 := by positivity
  have hΔpos : 0 < ‖DeltaFun (imagAxis s hs)‖ :=
    norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
  have h1 : (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * s⁻¹))
      ≤ s ^ 12 * ‖DeltaFun (imagAxis s hs)‖ := by rw [← hnorm]; exact hlow
  have h3 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hs12.le)
  have h4 : (s ^ 12)⁻¹ * (s ^ 12 * ‖DeltaFun (imagAxis s hs)‖)
      = ‖DeltaFun (imagAxis s hs)‖ := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs12), one_mul]
  rw [h4] at h3
  have h5 : ‖DeltaFun (imagAxis s hs)‖⁻¹
      ≤ (((s ^ 12)⁻¹) * ((1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * s⁻¹))))⁻¹ :=
    (inv_le_inv₀ hΔpos (by positivity)).mpr h3
  calc ‖DeltaFun (imagAxis s hs)‖⁻¹
      ≤ (((s ^ 12)⁻¹) * ((1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * s⁻¹))))⁻¹ := h5
    _ = 2 * s ^ 12 * Real.exp (2 * Real.pi / s) := by
        rw [Real.exp_neg]
        have hs12ne : s ^ 12 ≠ 0 := ne_of_gt hs12
        have hene : Real.exp (-(2 * Real.pi * s⁻¹)) ≠ 0 := Real.exp_ne_zero _
        field_simp

/-- `j(i s) = O(e^{2π/s})`. -/
lemma jInvariantFun_imagAxis_boundE :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖jInvariantFun (imagAxis s hs)‖ ≤ C * Real.exp (2 * Real.pi / s) := by
  obtain ⟨C, hC, hb⟩ := jInvariantFun_bound_third
  refine ⟨C, hC, fun s hs hs1 => ?_⟩
  have hs' : 0 < s⁻¹ := inv_pos.mpr hs
  have hle : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  have h13 : (1 : ℝ) / 3 ≤ (imagAxis s⁻¹ hs').im := by
    rw [imagAxis_im' s⁻¹ hs']; linarith
  have h := hb (imagAxis s⁻¹ hs') h13
  have hSm : ModularGroup.S • imagAxis s⁻¹ hs' = imagAxis s hs := S_smul_imagAxis_invE s hs
  have heq : jInvariantFun (imagAxis s⁻¹ hs') = jInvariantFun (imagAxis s hs) := by
    have h2 := (Work.Kernels.KernelFacts.jInvariantFun_S_smul (imagAxis s⁻¹ hs')).symm
    rw [hSm] at h2
    exact h2
  rw [heq, imagAxis_im' s⁻¹ hs'] at h
  refine le_trans h (mul_le_mul_of_nonneg_left ?_ hC.le)
  rw [show (2 : ℝ) * Real.pi * s⁻¹ = 2 * Real.pi / s by rw [div_eq_mul_inv]]

/-- `‖𝓛_S (i s)‖ ≤ C (1 + s⁻¹)^N`. -/
lemma LS_imagAxis_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C NL : ℝ, 0 < C ∧ 0 ≤ NL ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖ℓ.L_S (imagAxis s hs)‖ ≤ C * (1 + s⁻¹) ^ NL := by
  obtain ⟨α, N, hα, hN, hb⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ ℓ.L_S).mp ℓ.memP_S
  refine ⟨max α 1 * 3 ^ N, N, by positivity, hN, fun s hs hs1 => ?_⟩
  have h := hb (imagAxis s hs) (Set.mem_univ _)
  have hsc : scale (imagAxis s hs) ≤ 3 * (1 + s⁻¹) := scale_imagAxis_le s hs hs1
  have hS1 : (1 : ℝ) ≤ scale (imagAxis s hs) := Work.Kernels.one_le_scale _
  have hT1 : (1 : ℝ) ≤ 3 * (1 + s⁻¹) := by
    have : (0 : ℝ) ≤ s⁻¹ := inv_nonneg.mpr hs.le
    nlinarith
  have h1 : (scale (imagAxis s hs)) ^ N ≤ (3 * (1 + s⁻¹)) ^ N :=
    Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hsc hN
  have h2 : (3 * (1 + s⁻¹)) ^ N = 3 ^ N * (1 + s⁻¹) ^ N := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
  have h3 : α * (scale (imagAxis s hs)) ^ N ≤ α * (3 ^ N * (1 + s⁻¹) ^ N) :=
    mul_le_mul_of_nonneg_left (by rw [h2] at h1; exact h1) hα
  have hT0 : (0 : ℝ) ≤ (1 + s⁻¹) ^ N := Real.rpow_nonneg (by positivity) N
  calc ‖ℓ.L_S (imagAxis s hs)‖ ≤ α * (scale (imagAxis s hs)) ^ N := h
    _ ≤ α * (3 ^ N * (1 + s⁻¹) ^ N) := h3
    _ = α * 3 ^ N * (1 + s⁻¹) ^ N := by ring
    _ ≤ max α 1 * 3 ^ N * (1 + s⁻¹) ^ N := by
        have h6 : α * 3 ^ N ≤ max α 1 * 3 ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left α 1) (Real.rpow_nonneg (by norm_num) N)
        calc α * 3 ^ N * (1 + s⁻¹) ^ N = (α * 3 ^ N) * (1 + s⁻¹) ^ N := by ring
          _ ≤ (max α 1 * 3 ^ N) * (1 + s⁻¹) ^ N := mul_le_mul_of_nonneg_right h6 hT0
          _ = max α 1 * 3 ^ N * (1 + s⁻¹) ^ N := by ring


/-! ## Norm helpers -/

private lemma nsub3E (a b c : ℂ) : ‖a - b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  refine le_trans (norm_sub_le (a - b) c) ?_
  have := norm_sub_le a b
  linarith

private lemma nadd3E (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  refine le_trans (norm_add_le (a + b) c) ?_
  have := norm_add_le a b
  linarith

private lemma nadd2E (a b : ℂ) : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _

/-- Norm of a product from bounds on the factors. -/
private lemma nmulE {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hA : 0 ≤ A) :
    ‖a * b‖ ≤ A * B := by
  rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg b) hA

/-- The exponential cancellation: `(tS w)² e^{2π/s} ≤ e^{-2π}` under `s⁻¹ ≤ Im (S • w) - 1`. -/
private lemma tS_sq_mul_exp_le {w : UpperHalfPlane} {s : ℝ} (hs : 0 < s)
    (hfar : s⁻¹ ≤ (ModularGroup.S • w).im - 1) :
    (tS w) ^ 2 * Real.exp (2 * Real.pi / s) ≤ Real.exp (-(2 * Real.pi)) := by
  have hT : tS w = Real.exp (-(Real.pi * (ModularGroup.S • w).im)) := rfl
  have h2 : s⁻¹ + 1 ≤ (ModularGroup.S • w).im := by linarith
  have h3 : 2 * Real.pi * (s⁻¹ + 1) ≤ 2 * Real.pi * (ModularGroup.S • w).im :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have key : -(Real.pi * (ModularGroup.S • w).im) + -(Real.pi * (ModularGroup.S • w).im)
      + 2 * Real.pi / s ≤ -(2 * Real.pi) := by
    rw [div_eq_mul_inv]
    nlinarith [h3]
  calc (tS w) ^ 2 * Real.exp (2 * Real.pi / s)
      = Real.exp (-(Real.pi * (ModularGroup.S • w).im))
          * Real.exp (-(Real.pi * (ModularGroup.S • w).im)) * Real.exp (2 * Real.pi / s) := by
        rw [hT, sq]
    _ = Real.exp (-(Real.pi * (ModularGroup.S • w).im) + -(Real.pi * (ModularGroup.S • w).im)
          + 2 * Real.pi / s) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-(2 * Real.pi)) := Real.exp_le_exp.mpr key

/-- `U^a ≤ U^b` for `U ≥ 1`, `a ≤ b`. -/
private lemma rpowmono {x : ℝ} (hx : 1 ≤ x) {a b : ℝ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le hx h

/-! ## The `τ`-side atoms -/

/-- `Alpha ℓ 24 0 τ = Δ τ`. -/
lemma Alpha24_zeroE (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    Alpha ℓ 24 0 τ = DeltaFun τ := by
  simp [Alpha, Work.Kernels.psiVec, vlen, Work.Kernels.fk]

/-- `‖Δ w‖ ≤ C (scale w)^N (tS w)²` on `E`. -/
lemma Ncusp_delta_tau (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ w : UpperHalfPlane, w ∈ KEpsilon →
      ‖DeltaFun w‖ ≤ C * (scale w) ^ N * (tS w) ^ 2 := by
  obtain ⟨C, N, hC, hN, hb⟩ := EReg_atom_bounds ℓ
  exact ⟨C, N, hC, hN, fun w hw => (hb w (KEpsilon_subset_EReg hw)).2.2.2.2.2.1⟩

/-- `‖j τ‖ (tS τ)² ≤ C (scale τ)^N`. -/
lemma Ncusp_jdelta (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ w : UpperHalfPlane, w ∈ KEpsilon →
      ‖jInvariantFun w‖ * (tS w) ^ 2 ≤ C * (scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := EReg_atom_bounds ℓ
  exact ⟨C, N, hC, hN, fun w hw =>
    (hb w (KEpsilon_subset_EReg hw)).2.2.2.2.2.2.2.2.2.1⟩

/-- `‖j τ (α₁ - α₂)‖ ≤ C (scale τ)^N` for `d = 24`. -/
lemma Ncusp_jbeta (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ w : UpperHalfPlane, w ∈ KEpsilon →
      ‖jInvariantFun w * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w)‖ ≤ C * (scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := EReg_alpha24_bound ℓ
  exact ⟨C, N, hC, hN, fun w hw => (hb w (KEpsilon_subset_EReg hw)).2.2.2⟩

/-- `‖α₂‖ ≤ C (scale τ)^N` for `d = 24`. -/
lemma Ncusp_alpha24_2 (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ w : UpperHalfPlane, w ∈ KEpsilon →
      ‖Alpha ℓ 24 2 w‖ ≤ C * (scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := EReg_alpha24_bound ℓ
  exact ⟨C, N, hC, hN, fun w hw => (hb w (KEpsilon_subset_EReg hw)).2.1⟩

/-- **The CKMRV `E`-order cancellation: `α₁ - α₂` is `O((tS)²)` on `E` (for `d = 24`).** -/
lemma Ncusp_beta_tau (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ w : UpperHalfPlane, w ∈ KEpsilon →
      ‖Alpha ℓ 24 1 w - Alpha ℓ 24 2 w‖ ≤ C * (scale w) ^ N * (tS w) ^ 2 := by
  obtain ⟨C, N, hC, hN, hb⟩ := EReg_atom_bounds ℓ
  obtain ⟨C1, hCC1, hC1ge1⟩ : ∃ C1 : ℝ, C ≤ C1 ∧ 1 ≤ C1 :=
    ⟨max C 1, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, N ≤ (n : ℝ) := ⟨Nat.ceil N, Nat.le_ceil N⟩
  have hC1pos : 0 < C1 := lt_of_lt_of_le zero_lt_one hC1ge1
  have hC1nn : (0 : ℝ) ≤ C1 := hC1pos.le
  refine ⟨9 * C1 ^ 6 + 1, ((6 * n : ℕ) : ℝ), by positivity, by positivity, fun w hw => ?_⟩
  obtain ⟨hU, hV, hW, hE4, hE6, hΔu, hΔl, hL, hLS, hj, hjΔ⟩ := hb w (KEpsilon_subset_EReg hw)
  have hd1 : (1 : ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have hdN : (scale w) ^ N ≤ (scale w) ^ n := by
    rw [← Real.rpow_natCast (scale w) n]
    exact Real.rpow_le_rpow_of_exponent_le hd1 hn
  have hU1 : ‖UFun w‖ ≤ C1 * (scale w) ^ n :=
    le_trans hU (mul_le_mul hCC1 hdN (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N) hC1nn)
  have hV1 : ‖VFun w‖ ≤ C1 * (scale w) ^ n :=
    le_trans hV (mul_le_mul hCC1 hdN (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N) hC1nn)
  have hE41 : ‖E4Fun w‖ ≤ C1 * (scale w) ^ n :=
    le_trans hE4 (mul_le_mul hCC1 hdN (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N) hC1nn)
  have hW1 : ‖WFun w‖ ≤ C1 * (scale w) ^ n * tS w :=
    le_trans hW (mul_le_mul_of_nonneg_right
      (mul_le_mul hCC1 hdN (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N) hC1nn)
      (tS_nonneg w))
  have hL1 : ‖ℓ.L w‖ ≤ C1 * (scale w) ^ n * tS w :=
    le_trans hL (mul_le_mul_of_nonneg_right
      (mul_le_mul hCC1 hdN (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N) hC1nn)
      (tS_nonneg w))
  have hLS1 : ‖ℓ.L_S w‖ ≤ C1 * (scale w) ^ n :=
    le_trans hLS (mul_le_mul hCC1 hdN (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N) hC1nn)
  -- the identity `α₁ - α₂ = -(9/2)E₄(𝓛·UV²W + 𝓛_S·UVW²)`
  have hbeta_eq : Alpha ℓ 24 1 w - Alpha ℓ 24 2 w
      = -((9 / 2 : ℂ) * (E4Fun w * (ℓ.L w * (UFun w * VFun w ^ 2 * WFun w))
          + E4Fun w * (ℓ.L_S w * (UFun w * VFun w * WFun w ^ 2)))) := by
    have h1 : Alpha ℓ 24 1 w = Work.Kernels.psi2 ℓ w * E10Fun w := by
      simp [Alpha, Work.Kernels.psiVec, vlen, Work.Kernels.fk]
    have h2 : Alpha ℓ 24 2 w = Work.Kernels.psi4 ℓ w * E8Fun w := by
      simp [Alpha, Work.Kernels.psiVec, vlen, Work.Kernels.fk]
    obtain ⟨-, -, hX, hY⟩ := EReg_identities w
    have hstep : Alpha ℓ 24 1 w - Alpha ℓ 24 2 w
        = -(Work.Residues.Xfun w * ℓ.L w + Work.Residues.Yfun w * ℓ.L_S w) := by
      rw [h1, h2]
      simp only [Work.Kernels.psi2, Work.Kernels.psi4, Work.Residues.Xfun, Work.Residues.Yfun]
      ring
    rw [hstep, hX, hY]
    ring
  rw [hbeta_eq, norm_neg]
  set A : ℝ := C1 * (scale w) ^ n with hA
  set T : ℝ := tS w with hT
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; positivity
  have hT0 : (0 : ℝ) ≤ T := by rw [hT]; exact tS_nonneg w
  have hV2 : ‖VFun w ^ 2‖ ≤ A ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hV1 2
  have hUV2W : ‖UFun w * VFun w ^ 2 * WFun w‖ ≤ A * A ^ 2 * (A * T) := by
    have h : ‖UFun w * VFun w ^ 2‖ ≤ A * A ^ 2 := nmulE hU1 hV2 hA0
    exact nmulE h hW1 (by positivity)
  have hUVW2 : ‖UFun w * VFun w * WFun w ^ 2‖ ≤ A * A * ((A * T) ^ 2) := by
    have hW2 : ‖WFun w ^ 2‖ ≤ (A * T) ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hW1 2
    have h : ‖UFun w * VFun w‖ ≤ A * A := nmulE hU1 hV1 hA0
    exact nmulE h hW2 (by positivity)
  have hterm1 : ‖E4Fun w * (ℓ.L w * (UFun w * VFun w ^ 2 * WFun w))‖ ≤ A ^ 6 * T ^ 2 := by
    have h1 : ‖ℓ.L w * (UFun w * VFun w ^ 2 * WFun w)‖ ≤ (A * T) * (A * A ^ 2 * (A * T)) :=
      nmulE hL1 hUV2W (by positivity)
    calc ‖E4Fun w * (ℓ.L w * (UFun w * VFun w ^ 2 * WFun w))‖
        ≤ A * ((A * T) * (A * A ^ 2 * (A * T))) := nmulE hE41 h1 hA0
      _ = A ^ 6 * T ^ 2 := by ring
  have hterm2 : ‖E4Fun w * (ℓ.L_S w * (UFun w * VFun w * WFun w ^ 2))‖ ≤ A ^ 6 * T ^ 2 := by
    have h1 : ‖ℓ.L_S w * (UFun w * VFun w * WFun w ^ 2)‖ ≤ A * (A * A * ((A * T) ^ 2)) :=
      nmulE hLS1 hUVW2 hA0
    calc ‖E4Fun w * (ℓ.L_S w * (UFun w * VFun w * WFun w ^ 2))‖
        ≤ A * (A * (A * A * ((A * T) ^ 2))) := nmulE hE41 h1 hA0
      _ = A ^ 6 * T ^ 2 := by ring
  rw [norm_mul]
  have h92 : ‖(9 / 2 : ℂ)‖ = 9 / 2 := by
    rw [show (9 / 2 : ℂ) = (9 : ℂ) / 2 from rfl, norm_div]
    norm_num
  rw [h92]
  have hmain : ‖E4Fun w * (ℓ.L w * (UFun w * VFun w ^ 2 * WFun w))
        + E4Fun w * (ℓ.L_S w * (UFun w * VFun w * WFun w ^ 2))‖
      ≤ A ^ 6 * T ^ 2 + A ^ 6 * T ^ 2 :=
    le_trans (nadd2E _ _) (add_le_add hterm1 hterm2)
  have hA6 : A ^ 6 = C1 ^ 6 * (scale w) ^ (6 * n : ℕ) := by
    rw [hA, mul_pow, ← pow_mul, Nat.mul_comm n 6]
  calc (9 / 2 : ℝ) * ‖E4Fun w * (ℓ.L w * (UFun w * VFun w ^ 2 * WFun w))
        + E4Fun w * (ℓ.L_S w * (UFun w * VFun w * WFun w ^ 2))‖
      ≤ (9 / 2 : ℝ) * (A ^ 6 * T ^ 2 + A ^ 6 * T ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 9 * C1 ^ 6 * ((scale w) ^ (6 * n : ℕ) * (tS w) ^ 2) := by rw [hA6, hT]; ring
    _ ≤ (9 * C1 ^ 6 + 1) * ((scale w) ^ (6 * n : ℕ) * (tS w) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (9 * C1 ^ 6 + 1) * (scale w) ^ ((6 * n : ℕ) : ℝ) * (tS w) ^ 2 := by
        rw [Real.rpow_natCast]; ring

/-- The `d = 8` `τ`-side package: `α₀`, `α₂` and `α₁ - α₂ j` are polynomially bounded. -/
lemma Ncusp_alpha8_pkg (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ w : UpperHalfPlane, w ∈ KEpsilon →
      ‖Alpha ℓ 8 0 w‖ ≤ C * (scale w) ^ N ∧
      ‖Alpha ℓ 8 2 w‖ ≤ C * (scale w) ^ N ∧
      ‖Alpha ℓ 8 1 w - Alpha ℓ 8 2 w * jInvariantFun w‖ ≤ C * (scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := EReg_alpha8_bound ℓ
  exact ⟨C, N, hC, hN, fun w hw => hb w (KEpsilon_subset_EReg hw)⟩

/-! ## The main bound -/

theorem EpolyWindowE_ncusp_low_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (s : ℝ) (hs : 0 < s), w ∈ KEpsilon → s ≤ 1 →
        s⁻¹ ≤ (ModularGroup.S • w).im - 1 →
        ‖Ncusp ℓ d w (imagAxis s hs)‖
          ≤ C * (scale w) ^ N * (1 + s⁻¹) ^ M := by
  rcases hd with rfl | rfl
  · -- d = 8
    obtain ⟨Ca, Na, hCa, hNa, hA⟩ := Ncusp_alpha8_pkg ℓ
    obtain ⟨C6, hC6, hE6⟩ := E6_imagAxis_bound
    obtain ⟨C8, hC8, hE8⟩ := E8_imagAxis_bound
    obtain ⟨C10, hC10, hE10⟩ := E10_imagAxis_bound
    obtain ⟨CV, hCV, hVb⟩ := V_imagAxis_bound
    obtain ⟨CW, hCW, hWb⟩ := UW2_imagAxis_bound
    obtain ⟨CLS, NL, hCLS, hNL, hLSb⟩ := LS_imagAxis_bound ℓ
    refine ⟨‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ *
        (3456 * Ca * C10 * CLS + (Ca + 1728 * Ca) * C8 * CV + Ca * C6 * CW) + 1,
      Na, 10 + NL + 8 + 2, by positivity, hNa, by linarith, ?_⟩
    intro w s hs hw hs1 hfar
    obtain ⟨hA0, hA2, hA12⟩ := hA w hw
    have hS1 : (1 : ℝ) ≤ scale w := Work.Kernels.one_le_scale w
    have hU1 : (1 : ℝ) ≤ 1 + s⁻¹ := by
      have : (0 : ℝ) ≤ s⁻¹ := inv_nonneg.mpr hs.le
      linarith
    have hE6' : ‖E6Fun (imagAxis s hs)‖ ≤ C6 * (1 + s⁻¹) ^ ((6 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; exact hE6 s hs hs1
    have hE8' : ‖E8Fun (imagAxis s hs)‖ ≤ C8 * (1 + s⁻¹) ^ ((8 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; exact hE8 s hs hs1
    have hE10' : ‖E10Fun (imagAxis s hs)‖ ≤ C10 * (1 + s⁻¹) ^ ((10 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; exact hE10 s hs hs1
    have hV' : ‖VFun (imagAxis s hs)‖ ≤ CV * (1 + s⁻¹) ^ ((2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; exact hVb s hs hs1
    have hW' : ‖UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2‖
        ≤ CW * (1 + s⁻¹) ^ ((4 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; exact hWb s hs hs1
    have hLS' := hLSb s hs hs1
    set U : ℝ := 1 + s⁻¹ with hUdef
    set M : ℝ := 10 + NL + 8 + 2 with hMdef
    have hUM : ∀ a : ℝ, a ≤ M → U ^ a ≤ U ^ M := fun a ha => rpowmono hU1 ha
    have hUM10 : U ^ ((10 : ℕ) : ℝ) ≤ U ^ M := hUM _ (by rw [hMdef]; push_cast; linarith)
    have hUM8 : U ^ ((8 : ℕ) : ℝ) ≤ U ^ M := hUM _ (by rw [hMdef]; push_cast; linarith)
    have hUM6 : U ^ ((6 : ℕ) : ℝ) ≤ U ^ M := hUM _ (by rw [hMdef]; push_cast; linarith)
    have hUM2 : U ^ ((2 : ℕ) : ℝ) ≤ U ^ M := hUM _ (by rw [hMdef]; push_cast; linarith)
    have hUM4 : U ^ ((4 : ℕ) : ℝ) ≤ U ^ M := hUM _ (by rw [hMdef]; push_cast; linarith)
    have hUMa : U ^ NL ≤ U ^ M := hUM _ (by rw [hMdef]; push_cast; linarith)
    have hQ0 : (0 : ℝ) ≤ U ^ M := Real.rpow_nonneg (by linarith) M
    rw [Ncusp_eight_expansion ℓ w (imagAxis s hs), norm_mul]
    have hfk10 : fk (ulen 8 0) (imagAxis s hs) = E10Fun (imagAxis s hs) := by
      simp [ulen, Work.Kernels.fk]
    have hfk8 : fk (ulen 8 1) (imagAxis s hs) = E8Fun (imagAxis s hs) := by
      simp [ulen, Work.Kernels.fk]
    have hfk6 : fk (ulen 8 2) (imagAxis s hs) = E6Fun (imagAxis s hs) := by
      simp [ulen, Work.Kernels.fk]
    have hT8 : ‖T8 ℓ w (imagAxis s hs)‖
        ≤ (3456 * Ca * C10 * CLS + (Ca + 1728 * Ca) * C8 * CV + Ca * C6 * CW)
            * (scale w) ^ Na * U ^ M := by
      rw [T8, hfk10, hfk8, hfk6]
      refine le_trans (nadd3E _ _ _) ?_
      have t1 : ‖(-3456 : ℂ) * Alpha ℓ 8 0 w * E10Fun (imagAxis s hs)
          * ℓ.L_S (imagAxis s hs)‖
          ≤ 3456 * Ca * C10 * CLS * (scale w) ^ Na * U ^ M := by
        have h1 : ‖(-3456 : ℂ) * Alpha ℓ 8 0 w‖ ≤ 3456 * (Ca * (scale w) ^ Na) := by
          rw [norm_mul]
          calc ‖(-3456 : ℂ)‖ * ‖Alpha ℓ 8 0 w‖ = 3456 * ‖Alpha ℓ 8 0 w‖ := by norm_num
            _ ≤ 3456 * (Ca * (scale w) ^ Na) := mul_le_mul_of_nonneg_left hA0 (by norm_num)
        have h2 : ‖E10Fun (imagAxis s hs) * ℓ.L_S (imagAxis s hs)‖
            ≤ (C10 * U ^ ((10 : ℕ) : ℝ)) * (CLS * U ^ NL) := nmulE hE10' hLS' (by positivity)
        calc ‖(-3456 : ℂ) * Alpha ℓ 8 0 w * E10Fun (imagAxis s hs) * ℓ.L_S (imagAxis s hs)‖
            = ‖(-3456 : ℂ) * Alpha ℓ 8 0 w‖
                * ‖E10Fun (imagAxis s hs) * ℓ.L_S (imagAxis s hs)‖ := by
              rw [show (-3456 : ℂ) * Alpha ℓ 8 0 w * E10Fun (imagAxis s hs)
                    * ℓ.L_S (imagAxis s hs)
                  = ((-3456 : ℂ) * Alpha ℓ 8 0 w)
                    * (E10Fun (imagAxis s hs) * ℓ.L_S (imagAxis s hs)) from by ring,
                norm_mul]
          _ ≤ (3456 * (Ca * (scale w) ^ Na)) * ((C10 * U ^ ((10 : ℕ) : ℝ)) * (CLS * U ^ NL)) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = 3456 * Ca * C10 * CLS * (scale w) ^ Na * (U ^ ((10 : ℕ) : ℝ) * U ^ NL) := by ring
          _ = 3456 * Ca * C10 * CLS * (scale w) ^ Na * U ^ (((10 : ℕ) : ℝ) + NL) := by
              rw [Real.rpow_add (by linarith)]
          _ ≤ 3456 * Ca * C10 * CLS * (scale w) ^ Na * U ^ M := by
              refine mul_le_mul_of_nonneg_left (hUM _ ?_)
                (by positivity)
              rw [hMdef]; push_cast; linarith
      have h12 : ‖Alpha ℓ 8 1 w + Alpha ℓ 8 2 w * (1728 - jInvariantFun w)‖
          ≤ (Ca + 1728 * Ca) * (scale w) ^ Na := by
        have heq : Alpha ℓ 8 1 w + Alpha ℓ 8 2 w * (1728 - jInvariantFun w)
            = (Alpha ℓ 8 1 w - Alpha ℓ 8 2 w * jInvariantFun w) + 1728 * Alpha ℓ 8 2 w := by
          ring
        rw [heq]
        refine le_trans (nadd2E _ _) ?_
        have h2 : ‖(1728 : ℂ) * Alpha ℓ 8 2 w‖ = 1728 * ‖Alpha ℓ 8 2 w‖ := by
          rw [norm_mul]; norm_num
        rw [h2]
        have h3 : (1728 : ℝ) * ‖Alpha ℓ 8 2 w‖ ≤ 1728 * (Ca * (scale w) ^ Na) :=
          mul_le_mul_of_nonneg_left hA2 (by norm_num)
        linarith [hA12, h3]
      have h2full : ‖(Alpha ℓ 8 1 w + Alpha ℓ 8 2 w * (1728 - jInvariantFun w))
            * E8Fun (imagAxis s hs) * (-(VFun (imagAxis s hs)))‖
          ≤ (Ca + 1728 * Ca) * C8 * CV * (scale w) ^ Na * U ^ M := by
        calc ‖(Alpha ℓ 8 1 w + Alpha ℓ 8 2 w * (1728 - jInvariantFun w))
              * E8Fun (imagAxis s hs) * (-(VFun (imagAxis s hs)))‖
            = (‖Alpha ℓ 8 1 w + Alpha ℓ 8 2 w * (1728 - jInvariantFun w)‖
                * ‖E8Fun (imagAxis s hs)‖) * ‖VFun (imagAxis s hs)‖ := by
              rw [norm_mul, norm_mul, norm_neg]
          _ ≤ (((Ca + 1728 * Ca) * (scale w) ^ Na) * (C8 * U ^ ((8 : ℕ) : ℝ)))
                * (CV * U ^ ((2 : ℕ) : ℝ)) :=
              mul_le_mul (mul_le_mul h12 hE8' (norm_nonneg _) (by positivity)) hV'
                (norm_nonneg _) (by positivity)
          _ = (Ca + 1728 * Ca) * C8 * CV * (scale w) ^ Na
                * (U ^ ((8 : ℕ) : ℝ) * U ^ ((2 : ℕ) : ℝ)) := by ring
          _ = (Ca + 1728 * Ca) * C8 * CV * (scale w) ^ Na
                * U ^ (((8 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) := by rw [Real.rpow_add (by linarith)]
          _ ≤ (Ca + 1728 * Ca) * C8 * CV * (scale w) ^ Na * U ^ M := by
              refine mul_le_mul_of_nonneg_left (hUM _ ?_) (by positivity)
              rw [hMdef]; push_cast; linarith
      have h3full : ‖(-(Alpha ℓ 8 1 w) + Alpha ℓ 8 2 w * jInvariantFun w)
            * E6Fun (imagAxis s hs)
            * (UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2)‖
          ≤ Ca * C6 * CW * (scale w) ^ Na * U ^ M := by
        have hneg : ‖-(Alpha ℓ 8 1 w) + Alpha ℓ 8 2 w * jInvariantFun w‖
            = ‖Alpha ℓ 8 1 w - Alpha ℓ 8 2 w * jInvariantFun w‖ := by
          rw [show -(Alpha ℓ 8 1 w) + Alpha ℓ 8 2 w * jInvariantFun w
              = -(Alpha ℓ 8 1 w - Alpha ℓ 8 2 w * jInvariantFun w) by ring, norm_neg]
        calc ‖(-(Alpha ℓ 8 1 w) + Alpha ℓ 8 2 w * jInvariantFun w)
              * E6Fun (imagAxis s hs)
              * (UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2)‖
            = (‖-(Alpha ℓ 8 1 w) + Alpha ℓ 8 2 w * jInvariantFun w‖
                * ‖E6Fun (imagAxis s hs)‖)
              * ‖UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2‖ := by
              rw [norm_mul, norm_mul]
          _ ≤ ((Ca * (scale w) ^ Na) * (C6 * U ^ ((6 : ℕ) : ℝ)))
                * (CW * U ^ ((4 : ℕ) : ℝ)) := by
              rw [hneg]
              exact mul_le_mul (mul_le_mul hA12 hE6' (norm_nonneg _) (by positivity)) hW'
                (norm_nonneg _) (by positivity)
          _ = Ca * C6 * CW * (scale w) ^ Na * (U ^ ((6 : ℕ) : ℝ) * U ^ ((4 : ℕ) : ℝ)) := by ring
          _ = Ca * C6 * CW * (scale w) ^ Na
                * U ^ (((6 : ℕ) : ℝ) + ((4 : ℕ) : ℝ)) := by rw [Real.rpow_add (by linarith)]
          _ ≤ Ca * C6 * CW * (scale w) ^ Na * U ^ M := by
              refine mul_le_mul_of_nonneg_left (hUM _ ?_) (by positivity)
              rw [hMdef]; push_cast; linarith
      have hsum := add_le_add (add_le_add t1 h2full) h3full
      have hconst : 3456 * Ca * C10 * CLS * (scale w) ^ Na * U ^ M
            + (Ca + 1728 * Ca) * C8 * CV * (scale w) ^ Na * U ^ M
            + Ca * C6 * CW * (scale w) ^ Na * U ^ M
          = (3456 * Ca * C10 * CLS + (Ca + 1728 * Ca) * C8 * CV + Ca * C6 * CW)
              * (scale w) ^ Na * U ^ M := by ring
      rwa [hconst] at hsum
    have hfin : ‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T8 ℓ w (imagAxis s hs)‖
        ≤ (‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ *
            (3456 * Ca * C10 * CLS + (Ca + 1728 * Ca) * C8 * CV + Ca * C6 * CW) + 1)
          * (scale w) ^ Na * U ^ M := by
      have hK0 : (0 : ℝ) ≤ ‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ := norm_nonneg _
      calc ‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T8 ℓ w (imagAxis s hs)‖
          ≤ ‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖
              * ((3456 * Ca * C10 * CLS + (Ca + 1728 * Ca) * C8 * CV + Ca * C6 * CW)
                * (scale w) ^ Na * U ^ M) := mul_le_mul_of_nonneg_left hT8 hK0
        _ ≤ (‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ *
              (3456 * Ca * C10 * CLS + (Ca + 1728 * Ca) * C8 * CV + Ca * C6 * CW) + 1)
              * (scale w) ^ Na * U ^ M := by
            have h0 : (0 : ℝ) ≤ (scale w) ^ Na * U ^ M := by positivity
            nlinarith [h0, hK0]
    rw [hUdef] at hfin
    exact hfin
  · -- d = 24
    obtain ⟨Cd, Nd, hCd, hNd, hDelt⟩ := Ncusp_delta_tau ℓ
    obtain ⟨Cb, Nb, hCb, hNb, hBet⟩ := Ncusp_beta_tau ℓ
    obtain ⟨Cj2, Nj2, hCj2, hNj2, hJb⟩ := Ncusp_jbeta ℓ
    obtain ⟨Ca2, Na2, hCa2, hNa2, hA2b⟩ := Ncusp_alpha24_2 ℓ
    obtain ⟨Cjd, Njd, hCjd, hNjd, hJd⟩ := Ncusp_jdelta ℓ
    obtain ⟨C10, hC10, hE10⟩ := E10_imagAxis_bound
    obtain ⟨C14, hC14, hE14⟩ := E14_imagAxis_bound
    obtain ⟨CV, hCV, hVb⟩ := V_imagAxis_bound
    obtain ⟨CW, hCW, hWb⟩ := UW2_imagAxis_bound
    obtain ⟨CLS, NL, hCLS, hNL, hLSb⟩ := LS_imagAxis_bound ℓ
    obtain ⟨Cinv, hCinv, hinvb⟩ := DeltaFun_imagAxis_inv_boundE
    obtain ⟨Cj, hCj, hjb⟩ := jInvariantFun_imagAxis_boundE
    refine ⟨‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ *
        (3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
          + ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
              + 1728 * Ca2) * CV
          + Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi))) + 1,
      2 * (Nd + Nb + Nj2 + Na2 + Njd), 28 + NL, by positivity, by positivity, by positivity, ?_⟩
    intro w s hs hw hs1 hfar
    have hS1 : (1 : ℝ) ≤ scale w := Work.Kernels.one_le_scale w
    have hU1 : (1 : ℝ) ≤ 1 + s⁻¹ := by
      have : (0 : ℝ) ≤ s⁻¹ := inv_nonneg.mpr hs.le
      linarith
    have hK0 : 0 < Real.exp (-(2 * Real.pi)) := Real.exp_pos _
    have hT2e := tS_sq_mul_exp_le (w := w) hs hfar
    have hs12 : s ^ 12 ≤ 1 := pow_le_one₀ hs.le hs1
    set N0 : ℝ := Nd + Nb + Nj2 + Na2 + Njd with hN0
    set Nf : ℝ := 2 * N0 with hNf
    set Mf : ℝ := 28 + NL with hMf
    have hN00 : (0 : ℝ) ≤ N0 := by rw [hN0]; linarith
    have hMf0 : (0 : ℝ) ≤ Mf := by rw [hMf]; linarith
    have hSsub : ∀ a : ℝ, a ≤ Nf → (scale w) ^ a ≤ (scale w) ^ Nf := fun a ha => rpowmono hS1 ha
    have hS0sub : ∀ a : ℝ, a ≤ N0 → (scale w) ^ a ≤ (scale w) ^ N0 := fun a ha => rpowmono hS1 ha
    have hUsub : ∀ a : ℝ, a ≤ Mf → (1 + s⁻¹) ^ a ≤ (1 + s⁻¹) ^ Mf := fun a ha => rpowmono hU1 ha
    have hNd0 : Nd ≤ N0 := by rw [hN0]; linarith
    have hNb0 : Nb ≤ N0 := by rw [hN0]; linarith
    have hNj20 : Nj2 ≤ N0 := by rw [hN0]; linarith
    have hNa20 : Na2 ≤ N0 := by rw [hN0]; linarith
    have hNjd0 : Njd ≤ N0 := by rw [hN0]; linarith
    have hN0N : N0 ≤ Nf := by rw [hNf]; linarith
    have hSfnn : (0 : ℝ) ≤ (scale w) ^ Nf := Real.rpow_nonneg (by positivity) Nf
    have hS0nn : (0 : ℝ) ≤ (scale w) ^ N0 := Real.rpow_nonneg (by positivity) N0
    have hUfnn : (0 : ℝ) ≤ (1 + s⁻¹) ^ Mf := Real.rpow_nonneg (by linarith) Mf
    -- z-side atom bounds
    have hE10' : ‖E10Fun (imagAxis s hs)‖ ≤ C10 * (1 + s⁻¹) ^ ((10 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; exact hE10 s hs hs1
    have hE14' : ‖E14Fun (imagAxis s hs)‖ ≤ C14 * (1 + s⁻¹) ^ ((14 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; exact hE14 s hs hs1
    have hV' : ‖VFun (imagAxis s hs)‖ ≤ CV * (1 + s⁻¹) ^ ((2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; exact hVb s hs hs1
    have hW' : ‖UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2‖
        ≤ CW * (1 + s⁻¹) ^ ((4 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; exact hWb s hs hs1
    have hLS' := hLSb s hs hs1
    have hInv' := hinvb s hs hs1
    have hJz' := hjb s hs hs1
    have hVb' : ‖VFun (imagAxis s hs)‖ ≤ CV * (1 + s⁻¹) ^ Mf :=
      le_trans hV' (mul_le_mul_of_nonneg_left (hUsub 2 (by rw [hMf]; push_cast; linarith)) hCV.le)
    -- `fk 2` and `fk (-2)` at `i s`
    have hfk2 : fk 2 (imagAxis s hs) = E14Fun (imagAxis s hs) / DeltaFun (imagAxis s hs) := by
      simp [Work.Kernels.fk]
    have hfkm2 : fk (-2) (imagAxis s hs) = E10Fun (imagAxis s hs) / DeltaFun (imagAxis s hs) := by
      simp [Work.Kernels.fk]
    have hfk2b : ‖fk 2 (imagAxis s hs)‖
        ≤ C14 * Cinv * Real.exp (2 * Real.pi / s) * (1 + s⁻¹) ^ ((14 : ℕ) : ℝ) := by
      rw [hfk2, norm_div, div_eq_mul_inv]
      refine le_trans (mul_le_mul hE14' hInv' (by positivity) (by positivity)) ?_
      have he : C14 * (1 + s⁻¹) ^ ((14 : ℕ) : ℝ) * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s))
          = C14 * Cinv * Real.exp (2 * Real.pi / s) * (1 + s⁻¹) ^ ((14 : ℕ) : ℝ)
            * (s ^ 12) := by ring
      rw [he]
      have h1 : s ^ 12 ≤ 1 := hs12
      have h2 : (0 : ℝ) ≤ C14 * Cinv * Real.exp (2 * Real.pi / s) * (1 + s⁻¹) ^ ((14 : ℕ) : ℝ) :=
        by positivity
      exact mul_le_of_le_one_right h2 h1
    have hfkm2b : ‖fk (-2) (imagAxis s hs)‖
        ≤ C10 * Cinv * Real.exp (2 * Real.pi / s) * (1 + s⁻¹) ^ ((10 : ℕ) : ℝ) := by
      rw [hfkm2, norm_div, div_eq_mul_inv]
      refine le_trans (mul_le_mul hE10' hInv' (by positivity) (by positivity)) ?_
      have he : C10 * (1 + s⁻¹) ^ ((10 : ℕ) : ℝ) * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s))
          = C10 * Cinv * Real.exp (2 * Real.pi / s) * (1 + s⁻¹) ^ ((10 : ℕ) : ℝ)
            * (s ^ 12) := by ring
      rw [he]
      have h1 : s ^ 12 ≤ 1 := hs12
      have h2 : (0 : ℝ) ≤ C10 * Cinv * Real.exp (2 * Real.pi / s) * (1 + s⁻¹) ^ ((10 : ℕ) : ℝ) :=
        by positivity
      exact mul_le_of_le_one_right h2 h1
    -- τ-side atoms (all with exponent `N0`)
    have hD0 : ‖Alpha ℓ 24 0 w‖ ≤ Cd * (scale w) ^ N0 * (tS w) ^ 2 := by
      have hbase : ‖DeltaFun w‖ ≤ Cd * (scale w) ^ Nd * (tS w) ^ 2 := hDelt w hw
      rw [Alpha24_zeroE]
      refine le_trans hbase ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hS0sub Nd hNd0) hCd.le) (by positivity)
    have hB0 : ‖Alpha ℓ 24 1 w - Alpha ℓ 24 2 w‖ ≤ Cb * (scale w) ^ N0 * (tS w) ^ 2 :=
      le_trans (hBet w hw) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hS0sub Nb hNb0) hCb.le) (by positivity))
    have hJb0 : ‖jInvariantFun w * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w)‖
        ≤ Cj2 * (scale w) ^ N0 :=
      le_trans (hJb w hw) (mul_le_mul_of_nonneg_left (hS0sub Nj2 hNj20) hCj2.le)
    have hA20 : ‖Alpha ℓ 24 2 w‖ ≤ Ca2 * (scale w) ^ N0 :=
      le_trans (hA2b w hw) (mul_le_mul_of_nonneg_left (hS0sub Na2 hNa20) hCa2.le)
    have hJd0 : ‖jInvariantFun w‖ * (tS w) ^ 2 ≤ Cjd * (scale w) ^ N0 :=
      le_trans (hJd w hw) (mul_le_mul_of_nonneg_left (hS0sub Njd hNjd0) hCjd.le)
    -- the `β₁ = -3456α₀ + 2(α₁-α₂)` bound
    have hb1b : ‖((-3456 : ℂ) * Alpha ℓ 24 0 w
          + 2 * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w))‖
        ≤ (3456 * Cd + 2 * Cb) * (scale w) ^ N0 * (tS w) ^ 2 := by
      have h1 : ‖(-3456 : ℂ) * Alpha ℓ 24 0 w‖ ≤ 3456 * (Cd * (scale w) ^ N0 * (tS w) ^ 2) := by
        rw [norm_mul]
        calc ‖(-3456 : ℂ)‖ * ‖Alpha ℓ 24 0 w‖ = 3456 * ‖Alpha ℓ 24 0 w‖ := by norm_num
          _ ≤ 3456 * (Cd * (scale w) ^ N0 * (tS w) ^ 2) :=
              mul_le_mul_of_nonneg_left hD0 (by norm_num)
      have h2 : ‖(2 : ℂ) * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w)‖
          ≤ 2 * (Cb * (scale w) ^ N0 * (tS w) ^ 2) := by
        rw [norm_mul]
        calc ‖(2 : ℂ)‖ * ‖Alpha ℓ 24 1 w - Alpha ℓ 24 2 w‖
            = 2 * ‖Alpha ℓ 24 1 w - Alpha ℓ 24 2 w‖ := by norm_num
          _ ≤ 2 * (Cb * (scale w) ^ N0 * (tS w) ^ 2) :=
              mul_le_mul_of_nonneg_left hB0 (by norm_num)
      refine le_trans (nadd2E _ _) ?_
      refine le_trans (add_le_add h1 h2) ?_
      have hsum : 3456 * Cd * (scale w) ^ N0 + 2 * Cb * (scale w) ^ N0
          ≤ (3456 * Cd + 2 * Cb) * (scale w) ^ N0 := by
        nlinarith [mul_nonneg hCd.le hS0nn, mul_nonneg hCb.le hS0nn]
      calc 3456 * (Cd * (scale w) ^ N0 * (tS w) ^ 2)
            + 2 * (Cb * (scale w) ^ N0 * (tS w) ^ 2)
          = (3456 * Cd * (scale w) ^ N0 + 2 * Cb * (scale w) ^ N0) * (tS w) ^ 2 := by ring
        _ ≤ ((3456 * Cd + 2 * Cb) * (scale w) ^ N0) * (tS w) ^ 2 :=
            mul_le_mul_of_nonneg_right hsum (by positivity)
        _ = (3456 * Cd + 2 * Cb) * (scale w) ^ N0 * (tS w) ^ 2 := by ring
    -- the `j`-difference bound
    have hJz2 : ‖jInvariantFun (imagAxis s hs)‖ * (tS w) ^ 2
        ≤ Cj * Real.exp (-(2 * Real.pi)) := by
      have h1 : ‖jInvariantFun (imagAxis s hs)‖ * (tS w) ^ 2 * Real.exp (2 * Real.pi / s)
          ≤ Cj * (Real.exp (2 * Real.pi / s) * Real.exp (-(2 * Real.pi))) := by
        calc ‖jInvariantFun (imagAxis s hs)‖ * (tS w) ^ 2 * Real.exp (2 * Real.pi / s)
            = ‖jInvariantFun (imagAxis s hs)‖
                * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s)) := by ring
          _ ≤ (Cj * Real.exp (2 * Real.pi / s)) * Real.exp (-(2 * Real.pi)) :=
              mul_le_mul hJz' hT2e (by positivity) (by positivity)
          _ = Cj * (Real.exp (2 * Real.pi / s) * Real.exp (-(2 * Real.pi))) := by ring
      have hexppos : 0 < Real.exp (2 * Real.pi / s) := Real.exp_pos _
      rw [mul_comm (Real.exp (2 * Real.pi / s))] at h1
      rw [← mul_assoc] at h1
      exact le_of_mul_le_mul_right h1 hexppos
    have hsep : ‖(jInvariantFun w - jInvariantFun (imagAxis s hs))‖ * (tS w) ^ 2
        ≤ Cjd * (scale w) ^ N0 + Cj * Real.exp (-(2 * Real.pi)) := by
      have h1 : ‖(jInvariantFun w - jInvariantFun (imagAxis s hs))‖
          ≤ ‖jInvariantFun w‖ + ‖jInvariantFun (imagAxis s hs)‖ := norm_sub_le _ _
      have h2 : ‖(jInvariantFun w - jInvariantFun (imagAxis s hs))‖ * (tS w) ^ 2
          ≤ (‖jInvariantFun w‖ + ‖jInvariantFun (imagAxis s hs)‖) * (tS w) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : (‖jInvariantFun w‖ + ‖jInvariantFun (imagAxis s hs)‖) * (tS w) ^ 2
          = ‖jInvariantFun w‖ * (tS w) ^ 2 + ‖jInvariantFun (imagAxis s hs)‖ * (tS w) ^ 2 := by
        ring
      rw [h3] at h2
      linarith [h2, hJd0, hJz2]
    have hb1 : ‖((-3456 : ℂ) * Alpha ℓ 24 0 w
          + 2 * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w))
          * (jInvariantFun w - jInvariantFun (imagAxis s hs))‖
        ≤ (3456 * Cd + 2 * Cb) * (scale w) ^ N0
          * (Cjd * (scale w) ^ N0 + Cj * Real.exp (-(2 * Real.pi))) := by
      calc ‖((-3456 : ℂ) * Alpha ℓ 24 0 w
            + 2 * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w))
            * (jInvariantFun w - jInvariantFun (imagAxis s hs))‖
          = ‖((-3456 : ℂ) * Alpha ℓ 24 0 w
              + 2 * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w))‖
              * ‖(jInvariantFun w - jInvariantFun (imagAxis s hs))‖ := norm_mul _ _
        _ ≤ ((3456 * Cd + 2 * Cb) * (scale w) ^ N0 * (tS w) ^ 2)
              * ‖(jInvariantFun w - jInvariantFun (imagAxis s hs))‖ :=
            mul_le_mul_of_nonneg_right hb1b (norm_nonneg _)
        _ = (3456 * Cd + 2 * Cb) * (scale w) ^ N0
              * (‖(jInvariantFun w - jInvariantFun (imagAxis s hs))‖ * (tS w) ^ 2) := by ring
        _ ≤ (3456 * Cd + 2 * Cb) * (scale w) ^ N0
              * (Cjd * (scale w) ^ N0 + Cj * Real.exp (-(2 * Real.pi))) :=
            mul_le_mul_of_nonneg_left hsep (by positivity)
    -- the bracket
    have hpowN : (scale w) ^ N0 * (scale w) ^ N0 = (scale w) ^ Nf := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < scale w), hNf]
      congr 1
      ring
    have hpart1 : (3456 * Cd + 2 * Cb) * (scale w) ^ N0
          * (Cjd * (scale w) ^ N0 + Cj * Real.exp (-(2 * Real.pi)))
        ≤ ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi)))) * (scale w) ^ Nf := by
      have he : (3456 * Cd + 2 * Cb) * (scale w) ^ N0
            * (Cjd * (scale w) ^ N0 + Cj * Real.exp (-(2 * Real.pi)))
          = ((3456 * Cd + 2 * Cb) * Cjd) * ((scale w) ^ N0 * (scale w) ^ N0)
            + ((3456 * Cd + 2 * Cb) * Cj * Real.exp (-(2 * Real.pi))) * (scale w) ^ N0 := by ring
      rw [he, hpowN]
      have h2' : ((3456 * Cd + 2 * Cb) * Cj * Real.exp (-(2 * Real.pi))) * (scale w) ^ N0
          ≤ ((3456 * Cd + 2 * Cb) * Cj * Real.exp (-(2 * Real.pi))) * (scale w) ^ Nf :=
        mul_le_mul_of_nonneg_left (hSsub N0 hN0N) (by positivity)
      have he2 : ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi)))) * (scale w) ^ Nf
          = ((3456 * Cd + 2 * Cb) * Cjd) * (scale w) ^ Nf
            + ((3456 * Cd + 2 * Cb) * Cj * Real.exp (-(2 * Real.pi))) * (scale w) ^ Nf := by ring
      rw [he2]
      linarith [h2']
    have hbr : ‖((((-3456 : ℂ) * Alpha ℓ 24 0 w
              + 2 * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w)))
              * (jInvariantFun w - jInvariantFun (imagAxis s hs)))
            + ((Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * jInvariantFun w
                + 1728 * Alpha ℓ 24 2 w)‖
        ≤ ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2 + 1728 * Ca2)
            * (scale w) ^ Nf := by
      have hAl : ‖(1728 : ℂ) * Alpha ℓ 24 2 w‖ ≤ 1728 * (Ca2 * (scale w) ^ N0) := by
        rw [norm_mul]
        calc ‖(1728 : ℂ)‖ * ‖Alpha ℓ 24 2 w‖ = 1728 * ‖Alpha ℓ 24 2 w‖ := by norm_num
          _ ≤ 1728 * (Ca2 * (scale w) ^ N0) := mul_le_mul_of_nonneg_left hA20 (by norm_num)
      have hJa : ‖(Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * jInvariantFun w‖ ≤ Cj2 * (scale w) ^ N0 := by
        rw [mul_comm]
        exact hJb0
      have hB : ‖(Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * jInvariantFun w
            + 1728 * Alpha ℓ 24 2 w‖
          ≤ Cj2 * (scale w) ^ N0 + 1728 * (Ca2 * (scale w) ^ N0) :=
        le_trans (nadd2E _ _) (add_le_add hJa hAl)
      refine le_trans (nadd2E _ _) ?_
      refine le_trans (add_le_add hb1 hB) ?_
      have h2' : Cj2 * (scale w) ^ N0 ≤ Cj2 * (scale w) ^ Nf :=
        mul_le_mul_of_nonneg_left (hSsub N0 hN0N) hCj2.le
      have h3' : 1728 * (Ca2 * (scale w) ^ N0) ≤ (1728 * Ca2) * (scale w) ^ Nf := by
        rw [show (1728 : ℝ) * (Ca2 * (scale w) ^ N0) = (1728 * Ca2) * (scale w) ^ N0 by ring]
        exact mul_le_mul_of_nonneg_left (hSsub N0 hN0N) (by positivity)
      have he : ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
              + 1728 * Ca2) * (scale w) ^ Nf
          = ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi)))) * (scale w) ^ Nf
            + Cj2 * (scale w) ^ Nf + (1728 * Ca2) * (scale w) ^ Nf := by ring
      rw [he]
      linarith [hpart1, h2', h3']
    have hT24 : T24 ℓ w (imagAxis s hs)
        = ((-3456 : ℂ) * Alpha ℓ 24 0 w) * fk 2 (imagAxis s hs) * ℓ.L_S (imagAxis s hs)
          - (((((-3456 : ℂ) * Alpha ℓ 24 0 w
                + 2 * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w)))
                * (jInvariantFun w - jInvariantFun (imagAxis s hs)))
              + ((Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * jInvariantFun w
                  + 1728 * Alpha ℓ 24 2 w))
            * VFun (imagAxis s hs)
          - (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * fk (-2) (imagAxis s hs)
            * (UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2) := by
      rw [T24]; ring
    -- Term A
    have hTermA : ‖((-3456 : ℂ) * Alpha ℓ 24 0 w) * fk 2 (imagAxis s hs)
          * ℓ.L_S (imagAxis s hs)‖
        ≤ 3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
            * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf := by
      have h1 : ‖((-3456 : ℂ) * Alpha ℓ 24 0 w) * fk 2 (imagAxis s hs)‖
          ≤ (3456 * (Cd * (scale w) ^ N0 * (tS w) ^ 2))
            * (C14 * Cinv * Real.exp (2 * Real.pi / s) * (1 + s⁻¹) ^ ((14 : ℕ) : ℝ)) := by
        refine nmulE ?_ hfk2b (by positivity)
        rw [norm_mul]
        calc ‖(-3456 : ℂ)‖ * ‖Alpha ℓ 24 0 w‖ = 3456 * ‖Alpha ℓ 24 0 w‖ := by norm_num
          _ ≤ 3456 * (Cd * (scale w) ^ N0 * (tS w) ^ 2) :=
              mul_le_mul_of_nonneg_left hD0 (by norm_num)
      have hQ14 : (1 + s⁻¹) ^ ((14 : ℕ) : ℝ) * (1 + s⁻¹) ^ NL
          = (1 + s⁻¹) ^ (((14 : ℕ) : ℝ) + NL) := (Real.rpow_add (by linarith) _ _).symm
      have hQ14M : (1 + s⁻¹) ^ (((14 : ℕ) : ℝ) + NL) ≤ (1 + s⁻¹) ^ Mf :=
        hUsub _ (by rw [hMf]; push_cast; linarith)
      calc ‖((-3456 : ℂ) * Alpha ℓ 24 0 w) * fk 2 (imagAxis s hs) * ℓ.L_S (imagAxis s hs)‖
          = ‖((-3456 : ℂ) * Alpha ℓ 24 0 w) * fk 2 (imagAxis s hs)‖
              * ‖ℓ.L_S (imagAxis s hs)‖ := by rw [norm_mul]
        _ ≤ (3456 * (Cd * (scale w) ^ N0 * (tS w) ^ 2)
              * (C14 * Cinv * Real.exp (2 * Real.pi / s) * (1 + s⁻¹) ^ ((14 : ℕ) : ℝ)))
              * (CLS * (1 + s⁻¹) ^ NL) := mul_le_mul h1 hLS' (norm_nonneg _) (by positivity)
        _ = 3456 * Cd * C14 * Cinv * CLS * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s))
              * (scale w) ^ N0 * ((1 + s⁻¹) ^ ((14 : ℕ) : ℝ) * (1 + s⁻¹) ^ NL) := by ring
        _ ≤ 3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
              * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf := by
            rw [hQ14]
            have hA0 : (0 : ℝ) ≤ 3456 * Cd * C14 * Cinv * CLS := by positivity
            have hstep1 : 3456 * Cd * C14 * Cinv * CLS
                  * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s)) * (scale w) ^ N0
                ≤ 3456 * Cd * C14 * Cinv * CLS
                  * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s)) * (scale w) ^ Nf :=
              mul_le_mul_of_nonneg_left (hSsub N0 hN0N) (by positivity)
            have hstep2 : 3456 * Cd * C14 * Cinv * CLS
                  * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s)) * (scale w) ^ Nf
                ≤ 3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
                  * (scale w) ^ Nf :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT2e hA0) hSfnn
            have h1 : 3456 * Cd * C14 * Cinv * CLS
                  * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s)) * (scale w) ^ N0
                ≤ 3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
                  * (scale w) ^ Nf := le_trans hstep1 hstep2
            exact mul_le_mul h1 hQ14M (Real.rpow_nonneg (by linarith) _)
              (by positivity)
    -- Term B
    have hTermB : ‖((((-3456 : ℂ) * Alpha ℓ 24 0 w
              + 2 * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w)))
              * (jInvariantFun w - jInvariantFun (imagAxis s hs))
            + ((Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * jInvariantFun w
                + 1728 * Alpha ℓ 24 2 w)) * VFun (imagAxis s hs)‖
        ≤ ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2 + 1728 * Ca2)
            * CV * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf := by
      calc ‖((((-3456 : ℂ) * Alpha ℓ 24 0 w
              + 2 * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w)))
              * (jInvariantFun w - jInvariantFun (imagAxis s hs))
            + ((Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * jInvariantFun w
                + 1728 * Alpha ℓ 24 2 w)) * VFun (imagAxis s hs)‖
          = ‖((((-3456 : ℂ) * Alpha ℓ 24 0 w
              + 2 * (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w)))
              * (jInvariantFun w - jInvariantFun (imagAxis s hs))
            + ((Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * jInvariantFun w
                + 1728 * Alpha ℓ 24 2 w))‖ * ‖VFun (imagAxis s hs)‖ := norm_mul _ _
        _ ≤ (((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
                + 1728 * Ca2) * (scale w) ^ Nf) * (CV * (1 + s⁻¹) ^ Mf) :=
            mul_le_mul hbr hVb' (norm_nonneg _) (by positivity)
        _ = ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2 + 1728 * Ca2)
              * CV * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf := by ring
    -- Term D
    have hTermD : ‖(Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * fk (-2) (imagAxis s hs)
          * (UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2)‖
        ≤ Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi)) * (scale w) ^ Nf
            * (1 + s⁻¹) ^ Mf := by
      have h1 : ‖Alpha ℓ 24 1 w - Alpha ℓ 24 2 w‖ ≤ Cb * (scale w) ^ N0 * (tS w) ^ 2 := hB0
      have h2 : ‖fk (-2) (imagAxis s hs)
            * (UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2)‖
          ≤ (C10 * Cinv * Real.exp (2 * Real.pi / s) * (1 + s⁻¹) ^ ((10 : ℕ) : ℝ))
            * (CW * (1 + s⁻¹) ^ ((4 : ℕ) : ℝ)) := nmulE hfkm2b hW' (by positivity)
      have hQm : (1 + s⁻¹) ^ ((10 : ℕ) : ℝ) * (1 + s⁻¹) ^ ((4 : ℕ) : ℝ)
          ≤ (1 + s⁻¹) ^ Mf := by
        rw [(Real.rpow_add (by linarith) _ _).symm]
        exact hUsub _ (by rw [hMf]; push_cast; linarith)
      have hQmnn : (0 : ℝ) ≤ (1 + s⁻¹) ^ ((10 : ℕ) : ℝ) * (1 + s⁻¹) ^ ((4 : ℕ) : ℝ) := by
        positivity
      calc ‖(Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * fk (-2) (imagAxis s hs)
            * (UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2)‖
          = ‖Alpha ℓ 24 1 w - Alpha ℓ 24 2 w‖
              * ‖fk (-2) (imagAxis s hs)
                * (UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2)‖ := by
            rw [show (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w) * fk (-2) (imagAxis s hs)
                  * (UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2)
                = (Alpha ℓ 24 1 w - Alpha ℓ 24 2 w)
                  * (fk (-2) (imagAxis s hs)
                    * (UFun (imagAxis s hs) ^ 2 - WFun (imagAxis s hs) ^ 2)) from by ring,
              norm_mul]
        _ ≤ (Cb * (scale w) ^ N0 * (tS w) ^ 2)
              * ((C10 * Cinv * Real.exp (2 * Real.pi / s) * (1 + s⁻¹) ^ ((10 : ℕ) : ℝ))
                * (CW * (1 + s⁻¹) ^ ((4 : ℕ) : ℝ))) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = Cb * C10 * Cinv * CW * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s)) * (scale w) ^ N0
              * ((1 + s⁻¹) ^ ((10 : ℕ) : ℝ) * (1 + s⁻¹) ^ ((4 : ℕ) : ℝ)) := by ring
        _ ≤ Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi)) * (scale w) ^ Nf
              * (1 + s⁻¹) ^ Mf := by
            have hKc : (0 : ℝ) ≤ Cb * C10 * Cinv * CW := by positivity
            have hstep1 : Cb * C10 * Cinv * CW * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s))
                  * (scale w) ^ N0
                ≤ Cb * C10 * Cinv * CW * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s))
                  * (scale w) ^ Nf :=
              mul_le_mul_of_nonneg_left (hSsub N0 hN0N) (by positivity)
            have hstep2 : Cb * C10 * Cinv * CW * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s))
                  * (scale w) ^ Nf
                ≤ Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi)) * (scale w) ^ Nf :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT2e hKc) hSfnn
            have h1 : Cb * C10 * Cinv * CW * ((tS w) ^ 2 * Real.exp (2 * Real.pi / s))
                  * (scale w) ^ N0
                ≤ Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi)) * (scale w) ^ Nf :=
              le_trans hstep1 hstep2
            exact mul_le_mul h1 hQm hQmnn (by positivity)
    -- final assembly
    rw [Ncusp_twentyfour_expansion ℓ w (imagAxis s hs), norm_mul]
    have hT24b : ‖T24 ℓ w (imagAxis s hs)‖
        ≤ (3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
            + ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
                + 1728 * Ca2) * CV
            + Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi)))
          * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf := by
      rw [hT24]
      refine le_trans (nsub3E _ _ _) ?_
      have he : (3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
              * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf
            + ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
                + 1728 * Ca2) * CV * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf
            + Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi)) * (scale w) ^ Nf
                * (1 + s⁻¹) ^ Mf)
          = (3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
              + ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
                  + 1728 * Ca2) * CV
              + Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi)))
            * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf := by ring
      rw [← he]
      linarith [hTermA, hTermB, hTermD]
    have hfin : ‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T24 ℓ w (imagAxis s hs)‖
        ≤ (‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ *
            (3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
              + ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
                  + 1728 * Ca2) * CV
              + Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi))) + 1)
          * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf := by
      have hK0 : (0 : ℝ) ≤ ‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ := norm_nonneg _
      calc ‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T24 ℓ w (imagAxis s hs)‖
          ≤ ‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖
              * ((3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
                  + ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
                      + 1728 * Ca2) * CV
                  + Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi)))
                * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf) :=
            mul_le_mul_of_nonneg_left hT24b hK0
        _ = (‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ *
              (3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
                + ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
                    + 1728 * Ca2) * CV
                + Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi))))
              * ((scale w) ^ Nf * (1 + s⁻¹) ^ Mf) := by ring
        _ ≤ (‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ *
              (3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
                + ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
                    + 1728 * Ca2) * CV
                + Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi))) + 1)
              * ((scale w) ^ Nf * (1 + s⁻¹) ^ Mf) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (‖((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹‖ *
              (3456 * Cd * C14 * Cinv * CLS * Real.exp (-(2 * Real.pi))
                + ((3456 * Cd + 2 * Cb) * (Cjd + Cj * Real.exp (-(2 * Real.pi))) + Cj2
                    + 1728 * Ca2) * CV
                + Cb * C10 * Cinv * CW * Real.exp (-(2 * Real.pi))) + 1)
              * (scale w) ^ Nf * (1 + s⁻¹) ^ Mf := by ring
    rw [hNf] at hfin
    rw [hN0] at hfin
    rw [hMf] at hfin
    exact hfin

end

end Work.Asymptotics
