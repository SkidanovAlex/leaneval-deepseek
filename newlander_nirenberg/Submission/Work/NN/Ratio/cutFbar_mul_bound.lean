import Mathlib
import Submission.Work.NN.Ratio.Defs

namespace Work.NN.Ratio

/-- For `0 ≤ d`, `1 ≤ M` and `0 < α < 1` one has `min d M ≤ M * d ^ α`: this is the
elementary interpolation that lets a Lipschitz bound in a coordinate be converted into the
Hölder exponent `α` used in the tracking estimate. -/
lemma min_le_mul_rpow {d M α : ℝ} (hd : 0 ≤ d) (hα : 0 < α) (hα1 : α < 1)
    (hM : 1 ≤ M) : min d M ≤ M * d ^ α := by
  rcases le_total d 1 with h | h
  · have h1 : d ≤ d ^ α := Real.self_le_rpow_of_le_one hd h hα1.le
    calc min d M ≤ d := min_le_left _ _
      _ ≤ d ^ α := h1
      _ = 1 * d ^ α := (one_mul _).symm
      _ ≤ M * d ^ α := mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hd α)
  · have h1 : (1 : ℝ) ≤ d ^ α := Real.one_le_rpow h hα.le
    calc min d M ≤ M := min_le_right _ _
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * d ^ α := mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one hM)

/-- For nonnegative `c`, `c'`, `d` and `0 < α < 1` one has
`min c (c' * d) ≤ max c c' * d ^ α`.  This handles the "one of the two points has left the
support of the cutoff" cases. -/
lemma min_le_max_mul_rpow {c c' d α : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hd : 0 ≤ d)
    (hα0 : 0 < α) (hα1 : α < 1) :
    min c (c' * d) ≤ max c c' * d ^ α := by
  have hdα : 0 ≤ d ^ α := Real.rpow_nonneg hd α
  rcases le_total d 1 with h | h
  · have h1 : d ≤ d ^ α := Real.self_le_rpow_of_le_one hd h hα1.le
    calc min c (c' * d) ≤ c' * d := min_le_right _ _
      _ ≤ c' * d ^ α := mul_le_mul_of_nonneg_left h1 hc'
      _ ≤ max c c' * d ^ α := mul_le_mul_of_nonneg_right (le_max_right _ _) hdα
  · have h1 : (1 : ℝ) ≤ d ^ α := Real.one_le_rpow h hα0.le
    calc min c (c' * d) ≤ c := min_le_left _ _
      _ = c * 1 := (mul_one c).symm
      _ ≤ c * d ^ α := mul_le_mul_of_nonneg_left h1 hc
      _ ≤ max c c' * d ^ α := mul_le_mul_of_nonneg_right (le_max_left _ _) hdα

theorem cutFbar_mul_bound {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {χ : ℂ → ℂ} {b T : ℝ} (hbT : b < T) {cχ cχ' : ℝ}
    (hcχ : ∀ ζ : ℂ, ‖Work.CR.Flat.dbarC χ ζ‖ ≤ cχ)
    (hcχ0 : ∀ ζ : ℂ, b ≤ ‖ζ‖ → Work.CR.Flat.dbarC χ ζ = 0)
    (hcχ' : ∀ ζ ζ' : ℂ, ‖Work.CR.Flat.dbarC χ ζ - Work.CR.Flat.dbarC χ ζ'‖ ≤ cχ' * ‖ζ - ζ'‖) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (j : Fin n) {F : (Fin n → ℂ) → ℂ} {A H : ℝ}, 0 ≤ A → 0 ≤ H →
        (∀ z : Fin n → ℂ, (∀ l, ‖z l‖ < T) → ‖F z‖ ≤ A) →
        (∀ x y : Fin n → ℂ, (∀ l, ‖x l‖ < T) → (∀ l, ‖y l‖ < T) →
          ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) →
        (∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < T) → ‖z j‖ ≤ b →
          ‖Work.CR.Flat.dbarC χ (z j) * F z‖ ≤ C * A) ∧
        (∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < T) → (∀ l, l ≠ j → ‖a' l‖ < T) →
          ‖Work.CR.Flat.dbarC χ (a j) * F a - Work.CR.Flat.dbarC χ (a' j) * F a'‖
            ≤ C * (A + H) * ‖a - a'‖ ^ α) := by
  -- nonnegativity of the two constants, extracted from the hypotheses
  have hcχ_nn : 0 ≤ cχ := by
    have h := hcχ (0 : ℂ)
    have h2 := norm_nonneg (Work.CR.Flat.dbarC χ (0 : ℂ))
    linarith
  have hcχ'_nn : 0 ≤ cχ' := by
    have h := hcχ' (0 : ℂ) (1 : ℂ)
    have h01 : ‖(0 : ℂ) - 1‖ = 1 := by norm_num
    rw [h01, mul_one] at h
    have h2 := norm_nonneg (Work.CR.Flat.dbarC χ (0 : ℂ) - Work.CR.Flat.dbarC χ (1 : ℂ))
    linarith
  set C0 : ℝ := max 1 (cχ + cχ' + cχ' * max 1 (2 * T)) with hC0
  have hM1 : (1 : ℝ) ≤ max 1 (2 * T) := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ max 1 (2 * T) := le_trans zero_le_one hM1
  have hC0pos : 0 < C0 := by
    rw [hC0]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  have hC0χ : cχ ≤ C0 := by
    rw [hC0]
    have hprod : 0 ≤ cχ' * max 1 (2 * T) := mul_nonneg hcχ'_nn hM0
    exact le_trans (by linarith) (le_max_right _ _)
  have hC0M : cχ' * max 1 (2 * T) ≤ C0 := by
    rw [hC0]
    exact le_trans (by linarith) (le_max_right _ _)
  have hC0χ' : cχ' ≤ C0 := by
    rw [hC0]
    have hstep : cχ' ≤ cχ' * max 1 (2 * T) := by
      calc cχ' = cχ' * 1 := (mul_one cχ').symm
        _ ≤ cχ' * max 1 (2 * T) := mul_le_mul_of_nonneg_left hM1 hcχ'_nn
    exact le_trans (by linarith) (le_max_right _ _)
  refine ⟨C0, hC0pos, ?_⟩
  intro j F A H hA hH hFA hFH
  constructor
  · -- first estimate: the point is inside the support of the cutoff
    intro z hzj hzj'
    have hzall : ∀ l, ‖z l‖ < T := by
      intro l
      by_cases hl : l = j
      · rw [hl]; exact lt_of_le_of_lt hzj' hbT
      · exact hzj l hl
    have hFz : ‖F z‖ ≤ A := hFA z hzall
    calc ‖Work.CR.Flat.dbarC χ (z j) * F z‖
        = ‖Work.CR.Flat.dbarC χ (z j)‖ * ‖F z‖ := norm_mul _ _
      _ ≤ cχ * A := mul_le_mul (hcχ (z j)) hFz (norm_nonneg _) hcχ_nn
      _ ≤ C0 * A := mul_le_mul_of_nonneg_right hC0χ hA
  · -- second estimate: the difference of the two products
    intro a a' ha ha'
    set d : ℝ := ‖a - a'‖ with hd
    have hdnn : 0 ≤ d := by rw [hd]; exact norm_nonneg _
    have hcoord : ‖a j - a' j‖ ≤ d := by
      rw [hd]
      simpa using norm_le_pi_norm (a - a') j
    have hcoord' : ‖a' j - a j‖ ≤ d := by
      rw [hd]
      calc ‖a' j - a j‖ = ‖(a' - a) j‖ := by simp
        _ ≤ ‖a' - a‖ := norm_le_pi_norm _ j
        _ = ‖a - a'‖ := norm_sub_rev _ _
    rcases lt_or_ge (‖a j‖) T with haT | haT
    · rcases lt_or_ge (‖a' j‖) T with ha'T | ha'T
      · -- both coordinates inside the tracking region
        have hxa : ∀ l, ‖a l‖ < T := fun l => by
          by_cases hl : l = j
          · rw [hl]; exact haT
          · exact ha l hl
        have hxa' : ∀ l, ‖a' l‖ < T := fun l => by
          by_cases hl : l = j
          · rw [hl]; exact ha'T
          · exact ha' l hl
        have hFa : ‖F a‖ ≤ A := hFA a hxa
        have hFa' : ‖F a'‖ ≤ A := hFA a' hxa'
        have hdiff : ‖F a - F a'‖ ≤ H * d ^ α := by
          have h := hFH a a' hxa hxa'
          simpa only [hd] using h
        have hsub : ‖a j - a' j‖ ≤ min d (2 * T) := by
          refine le_min hcoord ?_
          have h := norm_sub_le (a j) (a' j)
          linarith
        have hmin : min d (2 * T) ≤ max 1 (2 * T) * d ^ α :=
          le_trans (le_min (min_le_left _ _)
            (le_trans (min_le_right _ _) (le_max_right (1 : ℝ) (2 * T))))
            (min_le_mul_rpow hdnn hα hα1 (le_max_left (1 : ℝ) (2 * T)))
        have hgl : ‖Work.CR.Flat.dbarC χ (a j) - Work.CR.Flat.dbarC χ (a' j)‖ ≤
            cχ' * (max 1 (2 * T) * d ^ α) := by
          calc ‖Work.CR.Flat.dbarC χ (a j) - Work.CR.Flat.dbarC χ (a' j)‖
              ≤ cχ' * ‖a j - a' j‖ := hcχ' _ _
            _ ≤ cχ' * (min d (2 * T)) := mul_le_mul_of_nonneg_left hsub hcχ'_nn
            _ ≤ cχ' * (max 1 (2 * T) * d ^ α) :=
                mul_le_mul_of_nonneg_left hmin hcχ'_nn
        have hdecomp : Work.CR.Flat.dbarC χ (a j) * F a - Work.CR.Flat.dbarC χ (a' j) * F a'
            = Work.CR.Flat.dbarC χ (a j) * (F a - F a')
              + (Work.CR.Flat.dbarC χ (a j) - Work.CR.Flat.dbarC χ (a' j)) * F a' := by
          ring
        rw [hdecomp]
        calc ‖Work.CR.Flat.dbarC χ (a j) * (F a - F a')
                + (Work.CR.Flat.dbarC χ (a j) - Work.CR.Flat.dbarC χ (a' j)) * F a'‖
            ≤ ‖Work.CR.Flat.dbarC χ (a j) * (F a - F a')‖
              + ‖(Work.CR.Flat.dbarC χ (a j) - Work.CR.Flat.dbarC χ (a' j)) * F a'‖ :=
                norm_add_le _ _
          _ = ‖Work.CR.Flat.dbarC χ (a j)‖ * ‖F a - F a'‖
              + ‖Work.CR.Flat.dbarC χ (a j) - Work.CR.Flat.dbarC χ (a' j)‖ * ‖F a'‖ := by
                rw [norm_mul, norm_mul]
          _ ≤ cχ * (H * d ^ α) + cχ' * (max 1 (2 * T) * d ^ α) * A := by
              apply add_le_add
              · exact mul_le_mul (hcχ (a j)) hdiff (norm_nonneg _) hcχ_nn
              · exact mul_le_mul hgl hFa' (norm_nonneg _)
                  (mul_nonneg hcχ'_nn (mul_nonneg hM0 (Real.rpow_nonneg hdnn α)))
          _ = (cχ * H + cχ' * max 1 (2 * T) * A) * d ^ α := by ring
          _ ≤ (C0 * H + C0 * A) * d ^ α := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hdnn α)
              exact add_le_add (mul_le_mul_of_nonneg_right hC0χ hH)
                (mul_le_mul_of_nonneg_right hC0M hA)
          _ = C0 * (A + H) * d ^ α := by ring
      · -- the `j`-coordinate of `a'` has left the support
        have hg0' : Work.CR.Flat.dbarC χ (a' j) = 0 :=
          hcχ0 (a' j) (le_trans (le_of_lt hbT) ha'T)
        have hxa : ∀ l, ‖a l‖ < T := fun l => by
          by_cases hl : l = j
          · rw [hl]; exact haT
          · exact ha l hl
        have hFa : ‖F a‖ ≤ A := hFA a hxa
        have hgle : ‖Work.CR.Flat.dbarC χ (a j)‖ ≤ min cχ (cχ' * d) := by
          refine le_min (hcχ (a j)) ?_
          calc ‖Work.CR.Flat.dbarC χ (a j)‖
              = ‖Work.CR.Flat.dbarC χ (a j) - Work.CR.Flat.dbarC χ (a' j)‖ := by
                rw [hg0', sub_zero]
            _ ≤ cχ' * ‖a j - a' j‖ := hcχ' _ _
            _ ≤ cχ' * d := mul_le_mul_of_nonneg_left hcoord hcχ'_nn
        have hmin := min_le_max_mul_rpow hcχ_nn hcχ'_nn hdnn hα hα1
        have hE : ‖Work.CR.Flat.dbarC χ (a j) * F a - Work.CR.Flat.dbarC χ (a' j) * F a'‖
            = ‖Work.CR.Flat.dbarC χ (a j) * F a‖ := by
          rw [hg0', zero_mul, sub_zero]
        rw [hE]
        have hmaxC : max cχ cχ' ≤ C0 := max_le hC0χ hC0χ'
        have hstep : max cχ cχ' * A ≤ C0 * (A + H) := by
          calc max cχ cχ' * A ≤ C0 * A := mul_le_mul_of_nonneg_right hmaxC hA
            _ ≤ C0 * (A + H) := mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hC0pos)
        calc ‖Work.CR.Flat.dbarC χ (a j) * F a‖
            = ‖Work.CR.Flat.dbarC χ (a j)‖ * ‖F a‖ := norm_mul _ _
          _ ≤ min cχ (cχ' * d) * A :=
              mul_le_mul hgle hFa (norm_nonneg _) (le_min hcχ_nn (mul_nonneg hcχ'_nn hdnn))
          _ ≤ max cχ cχ' * d ^ α * A := mul_le_mul_of_nonneg_right hmin hA
          _ = (max cχ cχ' * A) * d ^ α := by ring
          _ ≤ C0 * (A + H) * d ^ α := mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg hdnn α)
    · -- the `j`-coordinate of `a` has left the support
      have hg0 : Work.CR.Flat.dbarC χ (a j) = 0 :=
        hcχ0 (a j) (le_trans (le_of_lt hbT) haT)
      rcases lt_or_ge (‖a' j‖) T with ha'T | ha'T
      · have hxa' : ∀ l, ‖a' l‖ < T := fun l => by
          by_cases hl : l = j
          · rw [hl]; exact ha'T
          · exact ha' l hl
        have hFa' : ‖F a'‖ ≤ A := hFA a' hxa'
        have hgle : ‖Work.CR.Flat.dbarC χ (a' j)‖ ≤ min cχ (cχ' * d) := by
          refine le_min (hcχ (a' j)) ?_
          calc ‖Work.CR.Flat.dbarC χ (a' j)‖
              = ‖Work.CR.Flat.dbarC χ (a' j) - Work.CR.Flat.dbarC χ (a j)‖ := by
                rw [hg0, sub_zero]
            _ ≤ cχ' * ‖a' j - a j‖ := hcχ' _ _
            _ ≤ cχ' * d := mul_le_mul_of_nonneg_left hcoord' hcχ'_nn
        have hmin := min_le_max_mul_rpow hcχ_nn hcχ'_nn hdnn hα hα1
        have hE : ‖Work.CR.Flat.dbarC χ (a j) * F a - Work.CR.Flat.dbarC χ (a' j) * F a'‖
            = ‖Work.CR.Flat.dbarC χ (a' j) * F a'‖ := by
          rw [hg0, zero_mul, zero_sub, norm_neg]
        rw [hE]
        have hmaxC : max cχ cχ' ≤ C0 := max_le hC0χ hC0χ'
        have hstep : max cχ cχ' * A ≤ C0 * (A + H) := by
          calc max cχ cχ' * A ≤ C0 * A := mul_le_mul_of_nonneg_right hmaxC hA
            _ ≤ C0 * (A + H) := mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hC0pos)
        calc ‖Work.CR.Flat.dbarC χ (a' j) * F a'‖
            = ‖Work.CR.Flat.dbarC χ (a' j)‖ * ‖F a'‖ := norm_mul _ _
          _ ≤ min cχ (cχ' * d) * A :=
              mul_le_mul hgle hFa' (norm_nonneg _) (le_min hcχ_nn (mul_nonneg hcχ'_nn hdnn))
          _ ≤ max cχ cχ' * d ^ α * A := mul_le_mul_of_nonneg_right hmin hA
          _ = (max cχ cχ' * A) * d ^ α := by ring
          _ ≤ C0 * (A + H) * d ^ α := mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg hdnn α)
      · have hg0' : Work.CR.Flat.dbarC χ (a' j) = 0 :=
          hcχ0 (a' j) (le_trans (le_of_lt hbT) ha'T)
        have hE : ‖Work.CR.Flat.dbarC χ (a j) * F a - Work.CR.Flat.dbarC χ (a' j) * F a'‖ = 0 := by
          simp [hg0, hg0']
        rw [hE]
        exact mul_nonneg (mul_nonneg (le_of_lt hC0pos) (by linarith)) (Real.rpow_nonneg hdnn α)

end Work.NN.Ratio
