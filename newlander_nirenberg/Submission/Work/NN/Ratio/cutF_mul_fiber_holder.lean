import Mathlib
import Submission.Work.NN.Ratio.Defs

namespace Work.NN.Ratio

theorem cutF_mul_fiber_holder {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {χ : ℂ → ℂ} {L b T : ℝ} (hbT : b < T) (hL0 : 0 ≤ L)
    (hχ_le : ∀ ζ : ℂ, ‖χ ζ‖ ≤ 1)
    (hχ_zero : ∀ ζ : ℂ, b ≤ ‖ζ‖ → χ ζ = 0)
    (hL : ∀ ζ ζ' : ℂ, ‖χ ζ - χ ζ'‖ ≤ L * ‖ζ - ζ'‖)
    {j : Fin n} {F : (Fin n → ℂ) → ℂ} {A : ℝ} (hA0 : 0 ≤ A)
    (hF : ∀ z : Fin n → ℂ, (∀ l, ‖z l‖ < T) → ‖F z‖ ≤ A)
    (hFh : ∀ x y : Fin n → ℂ, (∀ l, ‖x l‖ < T) → (∀ l, ‖y l‖ < T) →
      ‖F x - F y‖ ≤ A * ‖x - y‖ ^ α) :
    ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < T) → (∀ l, l ≠ j → ‖a' l‖ < T) →
      ‖χ (a j) * F a - χ (a' j) * F a'‖ ≤ 64 * (1 + L) * A * ‖a - a'‖ ^ α := by
  intro a a' ha ha'
  set d : ℝ := ‖a - a'‖ with hd
  have hd_nonneg : 0 ≤ d := by rw [hd]; exact norm_nonneg _
  have hdα_nonneg : 0 ≤ d ^ α := Real.rpow_nonneg hd_nonneg α
  -- The j-th coordinate projection is 1-Lipschitz.
  have coord_le : ∀ z z' : Fin n → ℂ, ‖z j - z' j‖ ≤ ‖z - z'‖ := by
    intro z z'
    have h := norm_le_pi_norm (z - z') j
    rwa [Pi.sub_apply] at h
  -- χ ∘ (· j) is L-Lipschitz.
  have chi_lip : ∀ z z' : Fin n → ℂ, ‖χ (z j) - χ (z' j)‖ ≤ L * ‖z - z'‖ := by
    intro z z'
    have h1 := hL (z j) (z' j)
    have h2 : L * ‖z j - z' j‖ ≤ L * ‖z - z'‖ :=
      mul_le_mul_of_nonneg_left (coord_le z z') hL0
    linarith
  -- A nonzero cutoff value forces the j-th coordinate into the small ball, hence
  -- the whole point into the box where `F` is controlled.
  have box_of : ∀ z : Fin n → ℂ, χ (z j) ≠ 0 → (∀ l, l ≠ j → ‖z l‖ < T) →
      ∀ l, ‖z l‖ < T := by
    intro z hz h l
    by_cases hl : l = j
    · rw [hl]
      have hb : ‖z j‖ < b := by
        by_contra hcon
        rw [not_lt] at hcon
        exact hz (hχ_zero (z j) hcon)
      linarith
    · exact h l hl
  -- On the slab, `χ (· j) * F` is bounded by `A`.
  have bnd : ∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < T) → ‖χ (z j) * F z‖ ≤ A := by
    intro z hz
    by_cases h : χ (z j) = 0
    · rw [h, zero_mul, norm_zero]; exact hA0
    · have hbox := box_of z h hz
      calc ‖χ (z j) * F z‖ = ‖χ (z j)‖ * ‖F z‖ := norm_mul _ _
        _ ≤ 1 * A := mul_le_mul (hχ_le (z j)) (hF z hbox) (norm_nonneg _) (by norm_num)
        _ = A := one_mul A
  by_cases hd1 : 1 ≤ d
  · -- Case `d ≥ 1`: the universal bound `2 A` suffices.
    have hdα1 : 1 ≤ d ^ α := Real.one_le_rpow hd1 (le_of_lt hα)
    have hAd : A ≤ A * d ^ α := by
      have := mul_le_mul_of_nonneg_left hdα1 hA0
      rwa [mul_one] at this
    have hAd2 : 64 * (1 + L) * A ≤ 64 * (1 + L) * A * d ^ α := by
      have hnn : (0:ℝ) ≤ 64 * (1 + L) := by nlinarith [hL0]
      have h := mul_le_mul_of_nonneg_left hAd hnn
      have heq : 64 * (1 + L) * (A * d ^ α) = 64 * (1 + L) * A * d ^ α := by ring
      rwa [heq] at h
    have h2 : 2 * A ≤ 64 * (1 + L) * A := by
      have h64 : (2:ℝ) ≤ 64 * (1 + L) := by nlinarith [hL0]
      exact mul_le_mul_of_nonneg_right h64 hA0
    calc ‖χ (a j) * F a - χ (a' j) * F a'‖
        ≤ ‖χ (a j) * F a‖ + ‖χ (a' j) * F a'‖ := norm_sub_le _ _
      _ ≤ A + A := add_le_add (bnd a ha) (bnd a' ha')
      _ = 2 * A := by ring
      _ ≤ 64 * (1 + L) * A * d ^ α := by linarith [h2, hAd2]
  · -- Case `d ≤ 1`.
    have hdle1 : d ≤ 1 := le_of_lt (not_le.mp hd1)
    have hd_le : d ≤ d ^ α := by
      rcases eq_or_lt_of_le hd_nonneg with h0 | hpos
      · rw [← h0, Real.zero_rpow (ne_of_gt hα)]
      · have h := Real.rpow_le_rpow_of_exponent_ge hpos hdle1 (le_of_lt hα1)
        rwa [Real.rpow_one] at h
    have hLdA_le : L * d * A ≤ 64 * (1 + L) * A * d ^ α := by
      have h1a : L * d ≤ L * d ^ α := mul_le_mul_of_nonneg_left hd_le hL0
      have h1 : L * d * A ≤ L * d ^ α * A := mul_le_mul_of_nonneg_right h1a hA0
      have hnn : (0:ℝ) ≤ A * d ^ α := mul_nonneg hA0 hdα_nonneg
      have h2 : L * d ^ α * A ≤ 64 * (1 + L) * A * d ^ α := by
        have hLle : L ≤ 64 * (1 + L) := by nlinarith [hL0]
        calc L * d ^ α * A = L * (A * d ^ α) := by ring
          _ ≤ 64 * (1 + L) * (A * d ^ α) := mul_le_mul_of_nonneg_right hLle hnn
          _ = 64 * (1 + L) * A * d ^ α := by ring
      linarith
    by_cases hboth : χ (a j) ≠ 0 ∧ χ (a' j) ≠ 0
    · -- Both cutoff values nonzero: both points lie in the box, decompose.
      have hboxa := box_of a hboth.1 ha
      have hboxa' := box_of a' hboth.2 ha'
      have hFa : ‖F a - F a'‖ ≤ A * d ^ α := by
        have := hFh a a' hboxa hboxa'
        rw [hd]; exact this
      have hFa' : ‖F a'‖ ≤ A := hF a' hboxa'
      have hlip : ‖χ (a j) - χ (a' j)‖ ≤ L * d := by
        have h := chi_lip a a'
        rw [← hd] at h; exact h
      have hdecomp : χ (a j) * F a - χ (a' j) * F a'
          = χ (a j) * (F a - F a') + (χ (a j) - χ (a' j)) * F a' := by ring
      rw [hdecomp]
      calc ‖χ (a j) * (F a - F a') + (χ (a j) - χ (a' j)) * F a'‖
          ≤ ‖χ (a j) * (F a - F a')‖ + ‖(χ (a j) - χ (a' j)) * F a'‖ := norm_add_le _ _
        _ = ‖χ (a j)‖ * ‖F a - F a'‖ + ‖χ (a j) - χ (a' j)‖ * ‖F a'‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ 1 * (A * d ^ α) + (L * d) * A := by
              apply add_le_add
              · exact mul_le_mul (hχ_le (a j)) hFa (norm_nonneg _) (by norm_num)
              · exact mul_le_mul hlip hFa' (norm_nonneg _) (mul_nonneg hL0 hd_nonneg)
        _ ≤ 64 * (1 + L) * A * d ^ α := by
              have hLdA : (L * d) * A ≤ (L * d ^ α) * A :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd_le hL0) hA0
              have e1 : 1 * (A * d ^ α) + (L * d ^ α) * A = (1 + L) * A * d ^ α := by ring
              have hle : 1 * (A * d ^ α) + (L * d) * A
                  ≤ 1 * (A * d ^ α) + (L * d ^ α) * A := by linarith [hLdA]
              have hle2 : (1 + L) * A * d ^ α ≤ 64 * (1 + L) * A * d ^ α := by
                have hnn : (0:ℝ) ≤ (1 + L) * A * d ^ α :=
                  mul_nonneg (mul_nonneg (by linarith [hL0]) hA0) hdα_nonneg
                nlinarith [hnn]
              calc 1 * (A * d ^ α) + (L * d) * A
                  ≤ 1 * (A * d ^ α) + (L * d ^ α) * A := hle
                _ = (1 + L) * A * d ^ α := e1
                _ ≤ 64 * (1 + L) * A * d ^ α := hle2
    · -- At least one cutoff value vanishes.
      have hd0 : χ (a j) = 0 ∨ χ (a' j) = 0 := by
        rcases not_and_or.mp hboth with h | h
        · exact Or.inl (not_not.mp h)
        · exact Or.inr (not_not.mp h)
      rcases hd0 with hzj | hzj
      · have hgoal : ‖χ (a j) * F a - χ (a' j) * F a'‖ = ‖χ (a' j) * F a'‖ := by
          rw [hzj]; simp
        rw [hgoal]
        have hkey : ‖χ (a' j) * F a'‖ ≤ L * d * A := by
          by_cases hz' : χ (a' j) = 0
          · rw [hz', zero_mul, norm_zero]
            exact mul_nonneg (mul_nonneg hL0 hd_nonneg) hA0
          · have hbox' := box_of a' hz' ha'
            have hFat : ‖F a'‖ ≤ A := hF a' hbox'
            have hchi : ‖χ (a' j)‖ ≤ L * d := by
              have h1 := hL (a j) (a' j)
              rw [hzj, zero_sub, norm_neg] at h1
              have hcoord : ‖a j - a' j‖ ≤ d := by
                have h := coord_le a a'; rw [← hd] at h; exact h
              have h2 : L * ‖a j - a' j‖ ≤ L * d :=
                mul_le_mul_of_nonneg_left hcoord hL0
              linarith
            calc ‖χ (a' j) * F a'‖ = ‖χ (a' j)‖ * ‖F a'‖ := norm_mul _ _
              _ ≤ (L * d) * A := mul_le_mul hchi hFat (norm_nonneg _) (mul_nonneg hL0 hd_nonneg)
        linarith [hkey, hLdA_le]
      · have hgoal : ‖χ (a j) * F a - χ (a' j) * F a'‖ = ‖χ (a j) * F a‖ := by
          rw [hzj]; simp
        rw [hgoal]
        have hkey : ‖χ (a j) * F a‖ ≤ L * d * A := by
          by_cases hz : χ (a j) = 0
          · rw [hz, zero_mul, norm_zero]
            exact mul_nonneg (mul_nonneg hL0 hd_nonneg) hA0
          · have hbox := box_of a hz ha
            have hFa : ‖F a‖ ≤ A := hF a hbox
            have hchi : ‖χ (a j)‖ ≤ L * d := by
              have h1 := hL (a j) (a' j)
              rw [hzj, sub_zero] at h1
              have hcoord : ‖a j - a' j‖ ≤ d := by
                have h := coord_le a a'; rw [← hd] at h; exact h
              have h2 : L * ‖a j - a' j‖ ≤ L * d :=
                mul_le_mul_of_nonneg_left hcoord hL0
              linarith
            calc ‖χ (a j) * F a‖ = ‖χ (a j)‖ * ‖F a‖ := norm_mul _ _
              _ ≤ (L * d) * A := mul_le_mul hchi hFa (norm_nonneg _) (mul_nonneg hL0 hd_nonneg)
        linarith [hkey, hLdA_le]

end Work.NN.Ratio
