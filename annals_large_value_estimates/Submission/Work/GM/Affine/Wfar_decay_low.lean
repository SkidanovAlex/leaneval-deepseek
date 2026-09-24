import Mathlib
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.far_wsum_lattice_bound
import Submission.Work.GM.Affine.ghatFar_eq_sum_Wfar
import Submission.Work.GM.Affine.tsum_norm_psi1hat_shift_decay
import Submission.Work.GM.Affine.window_abs_le_half

/-!
# GM §9, region II: decay in `T` of the far resonance weight `Wfar`

The far weight is

`Wfar K M₃ y = M₃ Σ_{ℓ : |ℓ - y| > 2/M₃} ψ̂₁(M₃ (ℓ - y))`,

and the statement proved here is that, *inside the relevant window* for `y`,

`T^η/(2M₃) ≤ |y| ≤ a^η T^η/M₃`,   `η = min δ 1 / 2`,   `M₃ ≥ T^4`,

it decays like `M₃ T^{-(δ+4)}`.

The mechanism is the super-polynomial decay of `ψ̂₁` (`psi1hat_decay`) together with the fact
that the window forces `y` to be *near the origin*: `|y| ≤ a^η T^η/M₃ ≤ a T /T^4 = a/T³`, so once
`T ≥ 4a + 4` we have `|y| ≤ 1/2` and every lattice point `ℓ ∈ ℤ` satisfies

* `ℓ = 0`:  `M₃|ℓ - y| = M₃|y| ≥ T^η/2`,
* `ℓ ≠ 0`:  `|ℓ - y| ≥ |ℓ| - 1/2 ≥ |ℓ|/2`, so `M₃|ℓ - y| ≥ M₃|ℓ|/2 ≥ T^4|ℓ|/2`.

Choosing the decay exponent `N` with `η N ≥ δ + 4` (and then automatically `4N ≥ δ + 4`) gives a
summable majorant whose total mass is `≲ T^{-(δ+4)}` (lemma `tsum_norm_psi1hat_shift_decay`).

For `T` in the bounded range `[T₀, max (max T₀ 1) (4a+4)]` the crude lattice bound
`far_wsum_lattice_bound` (`O(M₃ (1+|y|)²)`) suffices; the threshold `T₁ = max (max T₀ 1) (4a+4)`
depends only on `T₀` and `a`, so both regimes are covered by a single constant.
-/

namespace Work.GM.Affine

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

noncomputable section

/-- The far weight is dominated by `M₃` times the full (untruncated) shifted lattice sum of
`‖ψ̂₁‖`: forgetting the truncation `|ℓ - y| > 2/M₃` can only increase the sum. -/
lemma norm_Wfar_le_tsum (K M₃ y : ℝ) (hK : 0 < K) (hM₃ : 1 ≤ M₃) :
    ‖Wfar K M₃ y‖ ≤ M₃ * ∑' ℓ : ℤ, ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖ := by
  have hM₃nn : (0:ℝ) ≤ M₃ := by linarith
  obtain ⟨C', -, hbound⟩ := tsum_norm_psi1hat_shift_le K hK
  obtain ⟨hsumm, -⟩ := hbound M₃ y hM₃
  have hsumm' : Summable (fun ℓ : ℤ =>
      ‖(if |(ℓ:ℝ) - y| > 2/M₃ then psi1hat K (M₃ * ((ℓ:ℝ) - y)) else 0 : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun ℓ => norm_nonneg _) (fun ℓ => ?_) hsumm
    split_ifs with h
    · exact le_refl _
    · simp
  have hnorm : ‖∑' ℓ : ℤ,
        (if |(ℓ:ℝ) - y| > 2/M₃ then psi1hat K (M₃ * ((ℓ:ℝ) - y)) else 0 : ℂ)‖
      ≤ ∑' ℓ : ℤ,
        ‖(if |(ℓ:ℝ) - y| > 2/M₃ then psi1hat K (M₃ * ((ℓ:ℝ) - y)) else 0 : ℂ)‖ :=
    norm_tsum_le_tsum_norm hsumm'
  have hle : (∑' ℓ : ℤ,
        ‖(if |(ℓ:ℝ) - y| > 2/M₃ then psi1hat K (M₃ * ((ℓ:ℝ) - y)) else 0 : ℂ)‖)
      ≤ ∑' ℓ : ℤ, ‖psi1hat K (M₃ * ((ℓ:ℝ) - y))‖ :=
    Summable.tsum_le_tsum (fun ℓ => by split_ifs with h <;> simp) hsumm' hsumm
  unfold Wfar
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM₃nn]
  exact mul_le_mul_of_nonneg_left (le_trans hnorm hle) hM₃nn

/-- **Decay in `T` of the far resonance weight.**  Inside the window
`T^η/(2M₃) ≤ |y| ≤ a^η T^η/M₃` (with `η = min δ 1 / 2`) and for `M₃ ≥ T^4` the far weight is
`≲ M₃ T^{-(δ+4)}`. -/
theorem Wfar_decay_low {K T₀ a : ℝ} (hK : 0 < K) (ha : 1 ≤ a) (hT₀ : 1 ≤ T₀) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ M₃ y : ℝ, T ^ 4 ≤ M₃ →
      T ^ (min δ 1 / 2) / (2 * M₃) ≤ |y| →
      |y| ≤ a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) / M₃ →
      ‖Wfar K M₃ y‖ ≤ C * M₃ * T ^ (-(δ + 4)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := tsum_norm_psi1hat_shift_decay K hK hδ
  obtain ⟨C₂, hC₂pos, hC₂⟩ := far_wsum_lattice_bound K hK
  -- The threshold between the two regimes: only `T₀` and `a` enter, so one constant suffices.
  set T₁ : ℝ := max (max T₀ 1) (4 * a + 4) with hT₁
  have hT₁1 : 1 ≤ T₁ := le_trans (le_max_right T₀ 1) (le_max_left _ _)
  have hT₁a : 4 * a + 4 ≤ T₁ := le_max_right _ _
  have hT₁pos : 0 < T₁ := lt_of_lt_of_le zero_lt_one hT₁1
  set Cmax : ℝ := max C₁ (C₂ * (1 + a * T₁) ^ 2 * T₁ ^ (δ + 4)) with hCmax
  have hCmaxpos : 0 < Cmax := lt_max_of_lt_left hC₁pos
  have hηle1 : min δ 1 / 2 ≤ 1 := by
    have h : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  refine ⟨Cmax, hCmaxpos, ?_⟩
  intro T hT₀T M₃ y hM₃ hylow hyhigh
  have hT1 : 1 ≤ T := le_trans hT₀ hT₀T
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hM₃1 : 1 ≤ M₃ := le_trans (one_le_pow₀ hT1 (n := 4)) hM₃
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃1
  have hδ4 : 0 < δ + 4 := by linarith
  by_cases hcase : T₁ ≤ T
  · -- Large `T`: the window forces `|y| ≤ 1/2` and the lattice sum decays.
    have hyabs : |y| ≤ 1 / 2 := window_abs_le_half hδ ha (le_trans hT₁a hcase) hM₃ hyhigh
    have hsum := hC₁ T M₃ y hT1 hM₃ hyabs hylow
    have hW := norm_Wfar_le_tsum K M₃ y hK hM₃1
    have hTpownn : 0 ≤ T ^ (-(δ + 4)) := Real.rpow_nonneg hTpos.le _
    calc ‖Wfar K M₃ y‖ ≤ M₃ * (∑' ℓ : ℤ, ‖psi1hat K (M₃ * ((ℓ:ℝ) - y))‖) := hW
      _ ≤ M₃ * (C₁ * T ^ (-(δ + 4))) := mul_le_mul_of_nonneg_left hsum (by linarith)
      _ = C₁ * M₃ * T ^ (-(δ + 4)) := by ring
      _ ≤ Cmax * M₃ * T ^ (-(δ + 4)) := by
            apply mul_le_mul_of_nonneg_right _ hTpownn
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · -- Small `T`: the crude lattice bound, with the constant absorbing `T₁^{δ+4}`.
    push Not at hcase
    have hW := (hC₂ M₃ 2 y hM₃1 (by norm_num)).2.2
    have h1 : a ^ (min δ 1 / 2) ≤ a := by
      have h := Real.rpow_le_rpow_of_exponent_le ha hηle1
      rwa [Real.rpow_one] at h
    have h2 : T ^ (min δ 1 / 2) ≤ T := by
      have h := Real.rpow_le_rpow_of_exponent_le hT1 hηle1
      rwa [Real.rpow_one] at h
    have h3 : 0 ≤ a ^ (min δ 1 / 2) := Real.rpow_nonneg (by linarith) _
    have h4 : 0 ≤ T ^ (min δ 1 / 2) := Real.rpow_nonneg hTpos.le _
    have hy_le : |y| ≤ a * T₁ := by
      calc |y| ≤ a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) / M₃ := hyhigh
        _ ≤ a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) / 1 :=
              div_le_div_of_nonneg_left (mul_nonneg h3 h4) zero_lt_one hM₃1
        _ = a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) := by ring
        _ ≤ a * T := mul_le_mul h1 h2 h4 (by linarith)
        _ ≤ a * T₁ := mul_le_mul_of_nonneg_left (le_of_lt hcase) (by linarith)
    have h1y : 1 + |y| ≤ 1 + a * T₁ := by linarith
    have hsq : (1 + |y|) ^ 2 ≤ (1 + a * T₁) ^ 2 := pow_le_pow_left₀ (by positivity) h1y 2
    have htin : T ^ (δ + 4) * T ^ (-(δ + 4)) = 1 := by
      rw [← Real.rpow_add hTpos, show δ + 4 + (-(δ + 4)) = 0 by ring, Real.rpow_zero]
    have hkey : C₂ * (1 + a * T₁) ^ 2 ≤ Cmax * T ^ (-(δ + 4)) := by
      have hT₁pow : T ^ (δ + 4) ≤ T₁ ^ (δ + 4) :=
        Real.rpow_le_rpow hTpos.le (le_of_lt hcase) hδ4.le
      have hc : C₂ * (1 + a * T₁) ^ 2 * T ^ (δ + 4) ≤ Cmax := by
        calc C₂ * (1 + a * T₁) ^ 2 * T ^ (δ + 4)
            ≤ C₂ * (1 + a * T₁) ^ 2 * T₁ ^ (δ + 4) :=
              mul_le_mul_of_nonneg_left hT₁pow (by positivity)
          _ ≤ Cmax := le_max_right _ _
      have hstep := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hTpos.le (-(δ + 4)))
      rwa [mul_assoc, htin, mul_one] at hstep
    calc ‖Wfar K M₃ y‖ ≤ C₂ * M₃ * (1 + |y|) ^ 2 := hW
      _ ≤ C₂ * M₃ * (1 + a * T₁) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg (le_of_lt hC₂pos) (le_of_lt hM₃pos))
      _ = M₃ * (C₂ * (1 + a * T₁) ^ 2) := by ring
      _ ≤ M₃ * (Cmax * T ^ (-(δ + 4))) := mul_le_mul_of_nonneg_left hkey (by linarith)
      _ = Cmax * M₃ * T ^ (-(δ + 4)) := by ring

end

end Work.GM.Affine
