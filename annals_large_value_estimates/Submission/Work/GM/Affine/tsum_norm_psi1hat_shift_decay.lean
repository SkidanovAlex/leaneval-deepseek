import Mathlib
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.tsum_norm_psi1hat_shift_pow_le
import Submission.Work.GM.Affine.pow_bound_aux

namespace Work.GM.Affine

open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-!
# Decay in `T` of the shifted lattice sum of `‖ψ̂₁‖` (GM §9, region II)

`ψ̂₁ = 𝓕 ψ₁` is the Fourier transform of a `C^∞` bump of compact support, hence decays faster
than any polynomial (`psi1hat_decay`).  On the lattice shifted by `y` with `|y| ≤ 1/2` this
yields the estimate

`∑_{ℓ ∈ ℤ} ‖ψ̂₁(M₃(ℓ - y))‖ ≤ C · (1/β)^N + 4·2^N·C / M₃^N`

whenever `β ≤ M₃|y|` (`tsum_norm_psi1hat_shift_pow_le`): the term `ℓ = 0` is the only one whose
argument can be small, and it is controlled by `M₃|y| ≥ β`; all other lattice points satisfy
`|ℓ - y| ≥ |ℓ|/2`, giving a `ζ(N)`-summable geometric tail.

Choosing the decay exponent `N` with `N·(min δ 1 / 2) ≥ δ + 4` (which also forces
`4N ≥ δ + 4`) and inserting `β = T^(min δ 1/2)/2`, `M₃ ≥ T^4` turns this into the statement
below: the whole sum is `≲ T^{-(δ+4)}` uniformly in `y` with `|y| ≤ 1/2` and in
`M₃ ≥ T^4`, on the range `|y| ≥ T^(min δ 1/2)/(2M₃)`.

This is the input used by `FarMass`/`Wfar` estimates in `Wfar_decay_low`.
-/

/-- **Decay of the shifted lattice sum of `‖ψ̂₁‖`.** -/
theorem tsum_norm_psi1hat_shift_decay (K : ℝ) (hK : 0 < K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T M₃ y : ℝ), 1 ≤ T → T ^ 4 ≤ M₃ → |y| ≤ 1 / 2 →
      T ^ (min δ 1 / 2) / (2 * M₃) ≤ |y| →
      (∑' ℓ : ℤ, ‖Work.GM.Affine.psi1hat K (M₃ * ((ℓ : ℝ) - y))‖) ≤ C * T ^ (-(δ + 4)) := by
  set η : ℝ := min δ 1 / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    have h1 : 0 < min δ 1 := lt_min hδ one_pos
    linarith
  have hηhalf : η ≤ 1 / 2 := by
    rw [hηdef]
    have h1 : min δ 1 ≤ 1 := min_le_right δ 1
    linarith
  -- The decay exponent `N` is chosen so that `N·η ≥ δ + 4`; this is the only place where `δ`
  -- enters the constant.
  set N : ℕ := Nat.ceil ((δ + 4) / η) + 2 with hNdef
  have hNge : (δ + 4) / η ≤ (N : ℝ) := by
    have h1 : ((Nat.ceil ((δ + 4) / η) : ℕ) : ℝ) ≤ (N : ℝ) := by
      rw [hNdef]; push_cast; linarith
    exact le_trans (Nat.le_ceil _) h1
  have hNα : δ + 4 ≤ (N : ℝ) * η := by
    have h2 := mul_le_mul_of_nonneg_right hNge hηpos.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hηpos)] at h2
  have hN2 : 2 ≤ N := by omega
  have hN4 : δ + 4 ≤ 4 * (N : ℝ) := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h2 : (N : ℝ) * η ≤ (N : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_left hηhalf h1
    have h3 : δ + 4 ≤ (N : ℝ) / 2 := by linarith [hNα, h2]
    linarith
  obtain ⟨C₀, hC₀pos, hdec⟩ := psi1hat_decay K hK N
  have hC₀nn : 0 ≤ C₀ := hC₀pos.le
  refine ⟨5 * 2 ^ N * C₀, by positivity, ?_⟩
  intro T M₃ y hT hM₃ hhy hylow
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hM₃1 : 1 ≤ M₃ := le_trans (one_le_pow₀ hT) hM₃
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃1
  have hβpos : 0 < T ^ η / 2 := by
    have h : 0 < T ^ η := Real.rpow_pos_of_pos hTpos η
    linarith
  have hyβ : T ^ η / 2 ≤ M₃ * |y| := by
    have h1 : T ^ η / (2 * M₃) * M₃ ≤ |y| * M₃ :=
      mul_le_mul_of_nonneg_right hylow hM₃pos.le
    have h2 : T ^ η / (2 * M₃) * M₃ = T ^ η / 2 := by
      have hMne : M₃ ≠ 0 := ne_of_gt hM₃pos
      field_simp
    rw [h2] at h1
    linarith
  have hsum := tsum_norm_psi1hat_shift_pow_le (K := K) (N := N) hN2 hC₀nn hdec
      (M₃ := M₃) (y := y) (β := T ^ η / 2) hM₃1 hhy hβpos hyβ
  have harith := pow_bound_aux (T := T) (α := η) (δ := δ) (M₃ := M₃) (N := N)
      hT hηpos hM₃ hNα hN4
  calc (∑' ℓ : ℤ, ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖)
      ≤ C₀ * ((1 / (T ^ η / 2)) ^ N + 4 * 2 ^ N / M₃ ^ N) := hsum
    _ ≤ C₀ * (5 * 2 ^ N * T ^ (-(δ + 4))) := mul_le_mul_of_nonneg_left harith hC₀nn
    _ = 5 * 2 ^ N * C₀ * T ^ (-(δ + 4)) := by ring

end

end Work.GM.Affine
