/-
# The weighted spike-circle bounds for the `d = 24` `τ`-coefficients

The four coefficients `N0f, N2f, M0f, M2f` of the `d = 24` kernel (defined in
`Work.Residues.KPlusAux`) are evaluated at `e₂ = E₂ τ`, `e₄ = E₄ τ`, `e₆ = E₆ τ` and
`h = kph τ ζ = (Δ τ · (j τ - j ζ))⁻¹`.  On the spike circle with `Im τ` large:

* `‖E₂ τ - 1‖, ‖E₄ τ - 1‖, ‖E₆ τ - 1‖ = O(ε τ)` with `ε τ = exp (-2 π Im τ)`,
* every `h`-dependent term of the four polynomials carries the factor
  `e₄³ - e₆² = 1728 Δ τ = O(ε τ)`, and
* `kph τ ζ` is bounded on the spike circle (this is the divisor lower bound
  `SB_inv_DeltaTauJ`, i.e. `‖Δ τ (j τ - j ζ)‖ ≥ c` there).

Hence all four coefficients are `O(ε τ) = O(tpar τ ^ 2)`, which is precisely the weighted
bound `SBs H 2`.  The file proves this in the form

`∃ H, SBs H 2 (N0f ...) ∧ SBs H 2 (M0f ...) ∧ SBs H 2 (N2f ...) ∧ SBs H 2 (M2f ...)`.
-/
import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SBsAtoms
import Submission.Work.Asymptotics.SpikeCircle.SphereBoundAux
import Submission.Work.Residues.KPlusAux
import Submission.Work.Asymptotics.SpikeCircle.KPlus24_coeff_alg

noncomputable section
open UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.SpikeCircle

open Work.Kernels
open Work.Residues.KPlusAux

set_option maxHeartbeats 1000000

/-! ## `tpar τ ^ 2 = ε τ` and the boundedness of `kph` -/

/-- `tpar τ ^ 2 = exp (-2 π Im τ) = ε τ`. -/
lemma tpar_sq_eq_eps (τ : ℍ) :
    (Work.Residues.tpar τ) ^ (2 : ℝ) = Work.Residues.KPlusAux.eps τ := by
  simp only [Work.Residues.tpar, Work.Residues.KPlusAux.eps, Real.rpow_ofNat]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- On the spike circle, `kph τ ζ = (Δ τ · (j τ - j ζ))⁻¹` is bounded by a power of `S τ`. -/
lemma exists_kph_scale_bound : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
    ∀ τ ζ : ℍ, Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → 3 ≤ τ.im →
      ‖Work.Residues.KPlusAux.kph τ ζ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := SB_inv_DeltaTauJ
  refine ⟨C, N, hC, hN, fun τ ζ hτ hζ h3 => ?_⟩
  simpa only [Work.Residues.KPlusAux.kph, Work.Residues.KPlusAux.kpJ] using hb τ ζ hτ hζ h3

/-! ## Assembly -/

/-- **Assembly.**  If a coefficient `P` satisfies the algebraic bound
`‖P e₂ e₄ e₆ h‖ ≤ (600 + 400 Hh) m` whenever `‖eᵢ - 1‖ ≤ m ≤ 1` and `‖h‖ ≤ Hh`, then on the
spike circle the coefficient `P (E₂ τ) (E₄ τ) (E₆ τ) (kph τ ζ)` decays like `tpar τ ^ 2`. -/
lemma SBs.of_coeff_bound (P : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hP : ∀ (e2 e4 e6 h : ℂ) (m Hh : ℝ), 0 ≤ m → m ≤ 1 →
      ‖e2 - 1‖ ≤ m → ‖e4 - 1‖ ≤ m → ‖e6 - 1‖ ≤ m → ‖h‖ ≤ Hh → 0 ≤ Hh →
      ‖P e2 e4 e6 h‖ ≤ (600 + 400 * Hh) * m)
    {H2 H4 H6 H : ℝ} {K2 K4 K6 Ch Nh : ℝ}
    (hK2 : 0 ≤ K2) (hK4 : 0 ≤ K4) (hK6 : 0 ≤ K6) (hCh : 0 < Ch) (hNh : 0 ≤ Nh)
    (hb2 : ∀ τ : ℍ, H2 ≤ τ.im → ‖E2Fun τ - 1‖ ≤ K2 * Work.Residues.KPlusAux.eps τ)
    (hb4 : ∀ τ : ℍ, H4 ≤ τ.im → ‖E4Fun τ - 1‖ ≤ K4 * Work.Residues.KPlusAux.eps τ)
    (hb6 : ∀ τ : ℍ, H6 ≤ τ.im → ‖E6Fun τ - 1‖ ≤ K6 * Work.Residues.KPlusAux.eps τ)
    (hkph : ∀ τ ζ : ℍ, Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → 3 ≤ τ.im →
      ‖Work.Residues.KPlusAux.kph τ ζ‖ ≤ Ch * (scale τ) ^ Nh)
    (hH3 : 3 ≤ H) (hH2 : H2 ≤ H) (hH4 : H4 ≤ H) (hH6 : H6 ≤ H)
    (hHlog : Real.log (max (max K2 K4) K6 + 1) ≤ 2 * Real.pi * H) :
    SBs H 2
      (fun τ ζ => P (E2Fun τ) (E4Fun τ) (E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ)) := by
  set K0 : ℝ := max (max K2 K4) K6 + 1 with hK0
  have hK0pos : 0 < K0 := by rw [hK0]; positivity
  have hK2' : K2 ≤ K0 := by
    rw [hK0]; linarith [le_max_left (max K2 K4) K6, le_max_left K2 K4]
  have hK4' : K4 ≤ K0 := by
    rw [hK0]; linarith [le_max_left (max K2 K4) K6, le_max_right K2 K4]
  have hK6' : K6 ≤ K0 := by rw [hK0]; linarith [le_max_right (max K2 K4) K6]
  refine ⟨(600 + 400 * Ch) * K0, Nh, by positivity, hNh, fun τ ζ hτ hζ hH => ?_⟩
  have hlogτ : Real.log K0 ≤ 2 * Real.pi * τ.im := by
    have h2 : 2 * Real.pi * H ≤ 2 * Real.pi * τ.im := by nlinarith [Real.pi_pos, hH]
    linarith
  have heps_le : Work.Residues.KPlusAux.eps τ ≤ K0⁻¹ := by
    rw [Work.Residues.KPlusAux.eps]
    calc Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(Real.log K0)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = K0⁻¹ := by rw [Real.exp_neg, Real.exp_log hK0pos]
  have hm1 : K0 * Work.Residues.KPlusAux.eps τ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left heps_le hK0pos.le
    rwa [mul_inv_cancel₀ (ne_of_gt hK0pos)] at h
  have heps0 : 0 ≤ Work.Residues.KPlusAux.eps τ := (Work.Residues.KPlusAux.eps_pos τ).le
  have hm0 : 0 ≤ K0 * Work.Residues.KPlusAux.eps τ := mul_nonneg hK0pos.le heps0
  have hd2 : ‖E2Fun τ - 1‖ ≤ K0 * Work.Residues.KPlusAux.eps τ :=
    le_trans (hb2 τ (le_trans hH2 hH)) (mul_le_mul_of_nonneg_right hK2' heps0)
  have hd4 : ‖E4Fun τ - 1‖ ≤ K0 * Work.Residues.KPlusAux.eps τ :=
    le_trans (hb4 τ (le_trans hH4 hH)) (mul_le_mul_of_nonneg_right hK4' heps0)
  have hd6 : ‖E6Fun τ - 1‖ ≤ K0 * Work.Residues.KPlusAux.eps τ :=
    le_trans (hb6 τ (le_trans hH6 hH)) (mul_le_mul_of_nonneg_right hK6' heps0)
  have hHh0 : 0 ≤ Ch * (scale τ) ^ Nh := by
    have := Real.rpow_nonneg (scale_pos τ).le Nh
    positivity
  have hkh : ‖Work.Residues.KPlusAux.kph τ ζ‖ ≤ Ch * (scale τ) ^ Nh :=
    hkph τ ζ hτ hζ (le_trans hH3 hH)
  have hmain := hP _ _ _ _ (K0 * Work.Residues.KPlusAux.eps τ) (Ch * (scale τ) ^ Nh)
    hm0 hm1 hd2 hd4 hd6 hkh hHh0
  have hs1 : 1 ≤ (scale τ) ^ Nh := Real.one_le_rpow (one_le_scale τ) hNh
  have hs0 : 0 ≤ (scale τ) ^ Nh := Real.rpow_nonneg (scale_pos τ).le Nh
  have hkey : 600 + 400 * (Ch * (scale τ) ^ Nh) ≤ (600 + 400 * Ch) * (scale τ) ^ Nh := by
    nlinarith [hCh.le, hs1, hs0]
  have hstep : (600 + 400 * (Ch * (scale τ) ^ Nh)) * (K0 * Work.Residues.KPlusAux.eps τ)
      ≤ (600 + 400 * Ch) * (scale τ) ^ Nh * (K0 * Work.Residues.KPlusAux.eps τ) :=
    mul_le_mul_of_nonneg_right hkey hm0
  refine le_trans (le_trans hmain hstep) (le_of_eq ?_)
  rw [tpar_sq_eq_eps τ]
  ring

/-! ## The four coefficients -/


theorem SBs_KPlus24_coeffs : ∃ H : ℝ,
    Work.Asymptotics.SpikeCircle.SBs H 2 (fun τ ζ => Work.Residues.KPlusAux.N0f (Work.Kernels.E2Fun τ) (Work.Kernels.E4Fun τ) (Work.Kernels.E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ)) ∧
    Work.Asymptotics.SpikeCircle.SBs H 2 (fun τ ζ => Work.Residues.KPlusAux.M0f (Work.Kernels.E2Fun τ) (Work.Kernels.E4Fun τ) (Work.Kernels.E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ)) ∧
    Work.Asymptotics.SpikeCircle.SBs H 2 (fun τ ζ => Work.Residues.KPlusAux.N2f (Work.Kernels.E2Fun τ) (Work.Kernels.E4Fun τ) (Work.Kernels.E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ)) ∧
    Work.Asymptotics.SpikeCircle.SBs H 2 (fun τ ζ => Work.Residues.KPlusAux.M2f (Work.Kernels.E2Fun τ) (Work.Kernels.E4Fun τ) (Work.Kernels.E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ)) := by
  obtain ⟨H2, K2, hK2, hb2⟩ := E2_decay_bound
  obtain ⟨H4, K4, hK4, hb4⟩ := E4_decay_bound
  obtain ⟨H6, K6, hK6, hb6⟩ := E6_decay_bound
  obtain ⟨Ch, Nh, hCh, hNh, hkph⟩ := exists_kph_scale_bound
  set K0 : ℝ := max (max K2 K4) K6 + 1 with hK0
  set H : ℝ := max 3 (max H2 (max H4 (max H6 (Real.log K0 / (2 * Real.pi))))) with hHdef
  have hK0pos : 0 < K0 := by rw [hK0]; positivity
  have hH3 : 3 ≤ H := by
    rw [hHdef]; exact le_max_left _ _
  have hH2 : H2 ≤ H := by
    rw [hHdef]
    exact le_trans (le_max_left H2 (max H4 (max H6 (Real.log K0 / (2 * Real.pi)))))
      (le_max_right 3 (max H2 (max H4 (max H6 (Real.log K0 / (2 * Real.pi))))))
  have hH4 : H4 ≤ H := by
    rw [hHdef]
    exact le_trans
      (le_trans (le_max_left H4 (max H6 (Real.log K0 / (2 * Real.pi))))
        (le_max_right H2 (max H4 (max H6 (Real.log K0 / (2 * Real.pi))))))
      (le_max_right 3 (max H2 (max H4 (max H6 (Real.log K0 / (2 * Real.pi))))))
  have hH6 : H6 ≤ H := by
    rw [hHdef]
    exact le_trans
      (le_trans
        (le_trans (le_max_left H6 (Real.log K0 / (2 * Real.pi)))
          (le_max_right H4 (max H6 (Real.log K0 / (2 * Real.pi)))))
        (le_max_right H2 (max H4 (max H6 (Real.log K0 / (2 * Real.pi))))))
      (le_max_right 3 (max H2 (max H4 (max H6 (Real.log K0 / (2 * Real.pi))))))
  have hL : Real.log K0 / (2 * Real.pi) ≤ H := by
    rw [hHdef]
    exact le_trans
      (le_trans
        (le_trans (le_max_right H6 (Real.log K0 / (2 * Real.pi)))
          (le_max_right H4 (max H6 (Real.log K0 / (2 * Real.pi)))))
        (le_max_right H2 (max H4 (max H6 (Real.log K0 / (2 * Real.pi))))))
      (le_max_right 3 (max H2 (max H4 (max H6 (Real.log K0 / (2 * Real.pi))))))
  have hHlog : Real.log K0 ≤ 2 * Real.pi * H := by
    have h1 : 2 * Real.pi * (Real.log K0 / (2 * Real.pi)) = Real.log K0 := by
      field_simp
    have h2 : 2 * Real.pi * (Real.log K0 / (2 * Real.pi)) ≤ 2 * Real.pi * H :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith [h1, h2]
  have hN0 : SBs H 2 (fun τ ζ => N0f (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ ζ)) :=
    SBs.of_coeff_bound (P := fun e2 e4 e6 h => N0f e2 e4 e6 h)
      (fun e2 e4 e6 h m Hh hm hm1 h2 h4 h6 hh hHh =>
        (KPlus24_coeff_alg (m := m) (Hh := Hh) hm hm1 h2 h4 h6 hh hHh).1)
      (H2 := H2) (H4 := H4) (H6 := H6) (H := H) (K2 := K2) (K4 := K4) (K6 := K6)
      (Ch := Ch) (Nh := Nh) hK2 hK4 hK6 hCh hNh hb2 hb4 hb6 hkph hH3 hH2 hH4 hH6 hHlog
  have hM0 : SBs H 2 (fun τ ζ => M0f (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ ζ)) :=
    SBs.of_coeff_bound (P := fun e2 e4 e6 h => M0f e2 e4 e6 h)
      (fun e2 e4 e6 h m Hh hm hm1 h2 h4 h6 hh hHh =>
        (KPlus24_coeff_alg (m := m) (Hh := Hh) hm hm1 h2 h4 h6 hh hHh).2.2.1)
      (H2 := H2) (H4 := H4) (H6 := H6) (H := H) (K2 := K2) (K4 := K4) (K6 := K6)
      (Ch := Ch) (Nh := Nh) hK2 hK4 hK6 hCh hNh hb2 hb4 hb6 hkph hH3 hH2 hH4 hH6 hHlog
  have hN2 : SBs H 2 (fun τ ζ => N2f (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ ζ)) :=
    SBs.of_coeff_bound (P := fun e2 e4 e6 h => N2f e2 e4 e6 h)
      (fun e2 e4 e6 h m Hh hm hm1 h2 h4 h6 hh hHh =>
        (KPlus24_coeff_alg (m := m) (Hh := Hh) hm hm1 h2 h4 h6 hh hHh).2.1)
      (H2 := H2) (H4 := H4) (H6 := H6) (H := H) (K2 := K2) (K4 := K4) (K6 := K6)
      (Ch := Ch) (Nh := Nh) hK2 hK4 hK6 hCh hNh hb2 hb4 hb6 hkph hH3 hH2 hH4 hH6 hHlog
  have hM2 : SBs H 2 (fun τ ζ => M2f (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ ζ)) :=
    SBs.of_coeff_bound (P := fun e2 e4 e6 h => M2f e2 e4 e6 h)
      (fun e2 e4 e6 h m Hh hm hm1 h2 h4 h6 hh hHh =>
        (KPlus24_coeff_alg (m := m) (Hh := Hh) hm hm1 h2 h4 h6 hh hHh).2.2.2)
      (H2 := H2) (H4 := H4) (H6 := H6) (H := H) (K2 := K2) (K4 := K4) (K6 := K6)
      (Ch := Ch) (Nh := Nh) hK2 hK4 hK6 hCh hNh hb2 hb4 hb6 hkph hH3 hH2 hH4 hH6 hHlog
  exact ⟨H, hN0, hM0, hN2, hM2⟩

end Work.Asymptotics.SpikeCircle
