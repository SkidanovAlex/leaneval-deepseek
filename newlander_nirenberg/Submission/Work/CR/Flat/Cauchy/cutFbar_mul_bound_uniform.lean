import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolDefs

namespace Work.CR.Flat.Cauchy

/-- For `0 ≤ x ≤ 1` and `0 < α ≤ 1` one has `x ≤ x ^ α`. -/
private lemma rpow_self_le {x α : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hα0 : 0 < α) (hα1 : α ≤ 1) : x ≤ x ^ α := by
  rcases eq_or_lt_of_le hx0 with h | h
  · subst h
    rw [Real.zero_rpow (ne_of_gt hα0)]
  · have hle : x ^ (1:ℝ) ≤ x ^ α := Real.rpow_le_rpow_of_exponent_ge h hx1 hα1
    rwa [Real.rpow_one] at hle

theorem cutFbar_mul_bound_uniform {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {j : Fin n}
    {cχ cχ' : ℝ}
    (hcχ : ∀ ζ : ℂ, ‖dbarC openCut ζ‖ ≤ cχ)
    (hcχ0 : ∀ ζ : ℂ, cutOut ≤ ‖ζ‖ → dbarC openCut ζ = 0)
    (hcχ' : ∀ ζ ζ' : ℂ, ‖dbarC openCut ζ - dbarC openCut ζ'‖ ≤ cχ' * ‖ζ - ζ'‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : (Fin n → ℂ) → ℂ} {A H : ℝ}, 0 ≤ A → 0 ≤ H →
      (∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A) →
      (∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet →
        ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) →
      (∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < trTrack) → ‖z j‖ ≤ cutOut →
        ‖dbarC openCut (z j) * F z‖ ≤ C * A) ∧
      (∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
        (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
        ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖ ≤ C * (A + H) * ‖a - a'‖ ^ α) := by
  refine ⟨65 * (|cχ| + |cχ'| + 1), ?_, ?_⟩
  · have h : (0 : ℝ) < |cχ| + |cχ'| + 1 := by positivity
    positivity
  · intro F A H hA0 hH0 hA hH
    have hcutOut_lt : cutOut < trTrack := by rw [cutOut, trTrack]; norm_num
    have hCpos : 0 < 65 * (|cχ| + |cχ'| + 1) := by
      have h : (0 : ℝ) < |cχ| + |cχ'| + 1 := by positivity
      positivity
    have hcχC : |cχ| ≤ 65 * (|cχ| + |cχ'| + 1) := by
      nlinarith [abs_nonneg cχ, abs_nonneg cχ']
    have hcχ'C : |cχ'| ≤ 65 * (|cχ| + |cχ'| + 1) := by
      nlinarith [abs_nonneg cχ, abs_nonneg cχ']
    have mem_track : ∀ {u : Fin n → ℂ}, (∀ l, l ≠ j → ‖u l‖ < trTrack) →
        ‖u j‖ < cutOut → u ∈ trackSet := by
      intro u hu huj l
      by_cases hl : l = j
      · subst hl; exact lt_trans huj hcutOut_lt
      · exact hu l hl
    have singleTerm : ∀ {u : Fin n → ℂ}, (∀ l, l ≠ j → ‖u l‖ < trTrack) →
        ‖dbarC openCut (u j) * F u‖ ≤ |cχ| * A := by
      intro u hu
      by_cases h : ‖u j‖ < cutOut
      · have hut : u ∈ trackSet := mem_track hu h
        have hFu : ‖F u‖ ≤ A := hA u hut
        calc ‖dbarC openCut (u j) * F u‖ = ‖dbarC openCut (u j)‖ * ‖F u‖ := norm_mul _ _
          _ ≤ |cχ| * A :=
              mul_le_mul (le_trans (hcχ (u j)) (le_abs_self cχ)) hFu (norm_nonneg _) (abs_nonneg _)
      · have hge : cutOut ≤ ‖u j‖ := not_lt.mp h
        rw [hcχ0 (u j) hge, zero_mul, norm_zero]
        exact mul_nonneg (abs_nonneg _) hA0
    constructor
    · -- Part 1
      intro z hz hzj
      have hzt : z ∈ trackSet := by
        intro l
        by_cases hl : l = j
        · subst hl; exact lt_of_le_of_lt hzj hcutOut_lt
        · exact hz l hl
      calc ‖dbarC openCut (z j) * F z‖ = ‖dbarC openCut (z j)‖ * ‖F z‖ := norm_mul _ _
        _ ≤ |cχ| * A :=
            mul_le_mul (le_trans (hcχ (z j)) (le_abs_self cχ)) (hA z hzt) (norm_nonneg _) (abs_nonneg _)
        _ ≤ 65 * (|cχ| + |cχ'| + 1) * A := mul_le_mul_of_nonneg_right hcχC hA0
    · -- Part 2
      intro a a' ha ha'
      have ht0 : 0 ≤ ‖a - a'‖ := norm_nonneg _
      have hab : ‖a j - a' j‖ ≤ ‖a - a'‖ := by
        have h := norm_le_pi_norm (a - a') j
        simpa using h
      by_cases hbig : (1 / 32 : ℝ) ≤ ‖a - a'‖
      · -- large distance
        have h1 := singleTerm ha
        have h2 := singleTerm ha'
        have hAH : 0 ≤ A + H := by linarith
        have htp : (1 / 32 : ℝ) ≤ ‖a - a'‖ ^ α := by
          have haux : (1 / 32 : ℝ) ^ α ≤ ‖a - a'‖ ^ α :=
            Real.rpow_le_rpow (by norm_num) hbig (le_of_lt hα)
          have hbase : (1 / 32 : ℝ) ≤ (1 / 32 : ℝ) ^ α :=
            rpow_self_le (by norm_num) (by norm_num) hα (le_of_lt hα1)
          linarith
        have hCt : 65 * (|cχ| + |cχ'| + 1) * (1 / 32 : ℝ)
            ≤ 65 * (|cχ| + |cχ'| + 1) * ‖a - a'‖ ^ α :=
          mul_le_mul_of_nonneg_left htp (by positivity)
        have h2c : 2 * |cχ| ≤ 65 * (|cχ| + |cχ'| + 1) * (1 / 32 : ℝ) := by
          nlinarith [abs_nonneg cχ, abs_nonneg cχ']
        have hmain : 2 * |cχ| ≤ 65 * (|cχ| + |cχ'| + 1) * ‖a - a'‖ ^ α := le_trans h2c hCt
        calc ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
            ≤ ‖dbarC openCut (a j) * F a‖ + ‖dbarC openCut (a' j) * F a'‖ := norm_sub_le _ _
          _ ≤ |cχ| * A + |cχ| * A := add_le_add h1 h2
          _ = 2 * |cχ| * A := by ring
          _ ≤ 2 * |cχ| * (A + H) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ ≤ 65 * (|cχ| + |cχ'| + 1) * (A + H) * ‖a - a'‖ ^ α := by
              have hstep := mul_le_mul_of_nonneg_right hmain hAH
              calc 2 * |cχ| * (A + H)
                  ≤ (65 * (|cχ| + |cχ'| + 1) * ‖a - a'‖ ^ α) * (A + H) := hstep
                _ = 65 * (|cχ| + |cχ'| + 1) * (A + H) * ‖a - a'‖ ^ α := by ring
      · -- small distance
        replace hbig : ‖a - a'‖ < 1 / 32 := not_le.mp hbig
        have ht1 : ‖a - a'‖ ≤ 1 := by linarith
        have htα : ‖a - a'‖ ≤ ‖a - a'‖ ^ α := rpow_self_le ht0 ht1 hα (le_of_lt hα1)
        have hrpow : 0 ≤ ‖a - a'‖ ^ α := Real.rpow_nonneg ht0 α
        by_cases haj : ‖a j‖ < cutOut
        · have hat : a ∈ trackSet := mem_track ha haj
          by_cases ha'j : ‖a' j‖ < cutOut
          · -- both below cutOut
            have ha't : a' ∈ trackSet := mem_track ha' ha'j
            have hFa : ‖F a‖ ≤ A := hA a hat
            have hFa' : ‖F a'‖ ≤ A := hA a' ha't
            have hHol : ‖F a - F a'‖ ≤ H * ‖a - a'‖ ^ α := hH a a' hat ha't
            have hsplit : dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'
                = dbarC openCut (a j) * (F a - F a')
                  + (dbarC openCut (a j) - dbarC openCut (a' j)) * F a' := by ring
            have hT1 : ‖dbarC openCut (a j) * (F a - F a')‖ ≤ |cχ| * (H * ‖a - a'‖ ^ α) := by
              rw [norm_mul]
              exact mul_le_mul (le_trans (hcχ (a j)) (le_abs_self cχ)) hHol (norm_nonneg _) (abs_nonneg _)
            have hc : ‖dbarC openCut (a j) - dbarC openCut (a' j)‖ ≤ |cχ'| * ‖a - a'‖ := by
              refine le_trans (hcχ' (a j) (a' j)) ?_
              calc cχ' * ‖a j - a' j‖ ≤ |cχ'| * ‖a j - a' j‖ :=
                    mul_le_mul_of_nonneg_right (le_abs_self cχ') (norm_nonneg _)
                _ ≤ |cχ'| * ‖a - a'‖ := mul_le_mul_of_nonneg_left hab (abs_nonneg cχ')
            have hT2 : ‖(dbarC openCut (a j) - dbarC openCut (a' j)) * F a'‖
                ≤ |cχ'| * ‖a - a'‖ * A := by
              rw [norm_mul]
              calc ‖dbarC openCut (a j) - dbarC openCut (a' j)‖ * ‖F a'‖
                  ≤ (|cχ'| * ‖a - a'‖) * A := mul_le_mul hc hFa' (norm_nonneg _) (by positivity)
                _ = |cχ'| * ‖a - a'‖ * A := by ring
            rw [hsplit]
            calc ‖dbarC openCut (a j) * (F a - F a')
                  + (dbarC openCut (a j) - dbarC openCut (a' j)) * F a'‖
                ≤ ‖dbarC openCut (a j) * (F a - F a')‖
                  + ‖(dbarC openCut (a j) - dbarC openCut (a' j)) * F a'‖ := norm_add_le _ _
              _ ≤ |cχ| * (H * ‖a - a'‖ ^ α) + |cχ'| * ‖a - a'‖ * A := add_le_add hT1 hT2
              _ ≤ |cχ| * (H * ‖a - a'‖ ^ α) + |cχ'| * A * ‖a - a'‖ ^ α := by
                  have hstep : |cχ'| * ‖a - a'‖ * A ≤ |cχ'| * A * ‖a - a'‖ ^ α := by
                    calc |cχ'| * ‖a - a'‖ * A = (|cχ'| * A) * ‖a - a'‖ := by ring
                      _ ≤ (|cχ'| * A) * ‖a - a'‖ ^ α :=
                          mul_le_mul_of_nonneg_left htα (by positivity)
                  linarith
              _ ≤ 65 * (|cχ| + |cχ'| + 1) * (A + H) * ‖a - a'‖ ^ α := by
                  have hcoef1 : |cχ| * H ≤ 65 * (|cχ| + |cχ'| + 1) * H :=
                    mul_le_mul_of_nonneg_right hcχC hH0
                  have hcoef2 : |cχ'| * A ≤ 65 * (|cχ| + |cχ'| + 1) * A :=
                    mul_le_mul_of_nonneg_right hcχ'C hA0
                  have hcoef : |cχ| * H + |cχ'| * A
                      ≤ 65 * (|cχ| + |cχ'| + 1) * (A + H) := by nlinarith [hcoef1, hcoef2]
                  calc |cχ| * (H * ‖a - a'‖ ^ α) + |cχ'| * A * ‖a - a'‖ ^ α
                      = (|cχ| * H + |cχ'| * A) * ‖a - a'‖ ^ α := by ring
                    _ ≤ (65 * (|cχ| + |cχ'| + 1) * (A + H)) * ‖a - a'‖ ^ α :=
                        mul_le_mul_of_nonneg_right hcoef hrpow
                    _ = 65 * (|cχ| + |cχ'| + 1) * (A + H) * ‖a - a'‖ ^ α := by ring
          · -- `a` below, `a'` at least cutOut
            have ha'ge : cutOut ≤ ‖a' j‖ := not_lt.mp ha'j
            have hFa : ‖F a‖ ≤ A := hA a hat
            have hzero : dbarC openCut (a' j) = 0 := hcχ0 (a' j) ha'ge
            have hcoef : ‖dbarC openCut (a j)‖ ≤ |cχ'| * ‖a - a'‖ := by
              have hh := hcχ' (a j) (a' j)
              rw [hzero, sub_zero] at hh
              refine le_trans hh ?_
              calc cχ' * ‖a j - a' j‖ ≤ |cχ'| * ‖a j - a' j‖ :=
                    mul_le_mul_of_nonneg_right (le_abs_self cχ') (norm_nonneg _)
                _ ≤ |cχ'| * ‖a - a'‖ := mul_le_mul_of_nonneg_left hab (abs_nonneg cχ')
            calc ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
                = ‖dbarC openCut (a j) * F a‖ := by rw [hzero, zero_mul, sub_zero]
              _ = ‖dbarC openCut (a j)‖ * ‖F a‖ := norm_mul _ _
              _ ≤ (|cχ'| * ‖a - a'‖) * A := mul_le_mul hcoef hFa (norm_nonneg _) (by positivity)
              _ = |cχ'| * A * ‖a - a'‖ := by ring
              _ ≤ |cχ'| * A * ‖a - a'‖ ^ α := mul_le_mul_of_nonneg_left htα (by positivity)
              _ ≤ 65 * (|cχ| + |cχ'| + 1) * (A + H) * ‖a - a'‖ ^ α := by
                  have hcoef2 : |cχ'| * A ≤ 65 * (|cχ| + |cχ'| + 1) * (A + H) := by
                    nlinarith [hcχ'C, hA0, hH0]
                  calc |cχ'| * A * ‖a - a'‖ ^ α
                      ≤ (65 * (|cχ| + |cχ'| + 1) * (A + H)) * ‖a - a'‖ ^ α :=
                        mul_le_mul_of_nonneg_right hcoef2 hrpow
                    _ = 65 * (|cχ| + |cχ'| + 1) * (A + H) * ‖a - a'‖ ^ α := by ring
        · have hage : cutOut ≤ ‖a j‖ := not_lt.mp haj
          by_cases ha'j : ‖a' j‖ < cutOut
          · -- `a'` below, `a` at least cutOut
            have ha't : a' ∈ trackSet := mem_track ha' ha'j
            have hFa' : ‖F a'‖ ≤ A := hA a' ha't
            have hzero : dbarC openCut (a j) = 0 := hcχ0 (a j) hage
            have hcoef : ‖dbarC openCut (a' j)‖ ≤ |cχ'| * ‖a - a'‖ := by
              have hh := hcχ' (a' j) (a j)
              rw [hzero, sub_zero] at hh
              refine le_trans hh ?_
              calc cχ' * ‖a' j - a j‖ ≤ |cχ'| * ‖a' j - a j‖ :=
                    mul_le_mul_of_nonneg_right (le_abs_self cχ') (norm_nonneg _)
                _ ≤ |cχ'| * ‖a - a'‖ := by
                    apply mul_le_mul_of_nonneg_left _ (abs_nonneg cχ')
                    have h2 := norm_le_pi_norm (a - a') j
                    have : ‖a' j - a j‖ = ‖a j - a' j‖ := by rw [← norm_neg]; congr 1; ring
                    rw [this]; simpa using h2
            calc ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
                = ‖dbarC openCut (a' j) * F a'‖ := by
                    rw [hzero, zero_mul, zero_sub, norm_neg]
              _ = ‖dbarC openCut (a' j)‖ * ‖F a'‖ := norm_mul _ _
              _ ≤ (|cχ'| * ‖a - a'‖) * A := mul_le_mul hcoef hFa' (norm_nonneg _) (by positivity)
              _ = |cχ'| * A * ‖a - a'‖ := by ring
              _ ≤ |cχ'| * A * ‖a - a'‖ ^ α := mul_le_mul_of_nonneg_left htα (by positivity)
              _ ≤ 65 * (|cχ| + |cχ'| + 1) * (A + H) * ‖a - a'‖ ^ α := by
                  have hcoef2 : |cχ'| * A ≤ 65 * (|cχ| + |cχ'| + 1) * (A + H) := by
                    nlinarith [hcχ'C, hA0, hH0]
                  calc |cχ'| * A * ‖a - a'‖ ^ α
                      ≤ (65 * (|cχ| + |cχ'| + 1) * (A + H)) * ‖a - a'‖ ^ α :=
                        mul_le_mul_of_nonneg_right hcoef2 hrpow
                    _ = 65 * (|cχ| + |cχ'| + 1) * (A + H) * ‖a - a'‖ ^ α := by ring
          · -- both at least cutOut
            have ha'ge : cutOut ≤ ‖a' j‖ := not_lt.mp ha'j
            have hz : dbarC openCut (a j) = 0 := hcχ0 (a j) hage
            have hz' : dbarC openCut (a' j) = 0 := hcχ0 (a' j) ha'ge
            calc ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
                = 0 := by rw [hz, hz']; simp
              _ ≤ 65 * (|cχ| + |cχ'| + 1) * (A + H) * ‖a - a'‖ ^ α :=
                  mul_nonneg (mul_nonneg (le_of_lt hCpos) (by linarith)) hrpow

end Work.CR.Flat.Cauchy
