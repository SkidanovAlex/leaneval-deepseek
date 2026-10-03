import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxAux

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-! ## Elementary growth lemmas

The bookkeeping of the weight `modelWeight A ρ l₁ l₂ k₁ k₂ = ⟨L⟩^A · 2^{A·2^{ρL}}`: on the
scales `N = 2^{L/C₀ - 2}` of the §6 regime the doubly exponential factor `2^{-2^{L/C₀-2}}`
beats the weight as soon as `ρ` is small compared with `1/C₀`, with an exponential gain
`2^{-cL}` to spare.  All the estimates are elementary; the only non-trivial input is the
quadratic lower bound `t²/16 ≤ 2^t` for the exponential. -/

/-- **The quadratic lower bound for `2^t`.**  For `t ≥ 0`, `t^2/16 ≤ 2^t`.

(Indeed `2^t = exp(t log 2)` and `exp u ≥ 1 + u`, so `2^t ≥ (t log 2/2)^2 ≥ t^2/16`
because `log 2 ≥ 1/2`.) -/
lemma sq_div_16_le_two_rpow (t : ℝ) (ht : 0 ≤ t) : t^2/16 ≤ (2:ℝ)^t := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm (Real.log 2) t]
  have hlog : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogsq : (1:ℝ)/4 ≤ (Real.log 2)^2 := by nlinarith
  have hmain : (t * Real.log 2 / 2)^2 ≤ Real.exp (t * Real.log 2) := by
    have h1 : t * Real.log 2 / 2 + 1 ≤ Real.exp (t * Real.log 2 / 2) := Real.add_one_le_exp _
    have h2 : 0 ≤ t * Real.log 2 / 2 := by positivity
    have h3 : (t * Real.log 2 / 2)^2 ≤ (Real.exp (t * Real.log 2 / 2))^2 := by nlinarith
    have hexp : (Real.exp (t * Real.log 2 / 2))^2 = Real.exp (t * Real.log 2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    exact h3
  have h4 : t^2/16 ≤ (t * Real.log 2 / 2)^2 := by
    nlinarith [hlogsq, sq_nonneg t]
  linarith

/-- `1 + L ≤ 4^L`. -/
lemma one_add_le_four_pow (L : ℕ) : (1 + (L:ℝ)) ≤ (4:ℝ)^L := by
  induction L with
  | zero => norm_num
  | succ n ih =>
    have h4n : (0:ℝ) < (4:ℝ)^n := pow_pos (by norm_num) n
    rw [pow_succ]
    push_cast
    nlinarith [ih]

/-- `4^L = 2^{2L}` as a real power. -/
lemma four_pow_eq (L : ℕ) : (4:ℝ)^L = (2:ℝ)^(2*(L:ℝ)) := by
  have hcast : (2:ℝ)*(L:ℝ) = ((2*L : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, Real.rpow_natCast, pow_mul]
  norm_num

/-- **The polynomial factor is negligible.**  If `8 ≤ αL` and `128A ≤ α²L`, then
`(1+L)^A ≤ 2^{2^{αL-4}}`. -/
lemma poly_le_rpow (A α : ℝ) (L : ℕ) (hA : 0 ≤ A) (hL1 : 1 ≤ (L:ℝ))
    (h1 : 8 ≤ α*(L:ℝ)) (h2 : 128*A ≤ α^2*(L:ℝ)) :
    (1 + (L:ℝ))^A ≤ (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-4)) := by
  have hL0 : (0:ℝ) ≤ (L:ℝ) := by linarith
  have h4 : (1 + (L:ℝ)) ≤ (4:ℝ)^L := one_add_le_four_pow L
  have h2L : (4:ℝ)^L = (2:ℝ)^(2*(L:ℝ)) := four_pow_eq L
  have hpoly : (1 + (L:ℝ))^A ≤ (2:ℝ)^(2*(L:ℝ)*A) := by
    have h1' : (1 + (L:ℝ)) ≤ (2:ℝ)^(2*(L:ℝ)) := by rw [← h2L]; exact h4
    calc (1 + (L:ℝ))^A ≤ ((2:ℝ)^(2*(L:ℝ)))^A :=
          Real.rpow_le_rpow (by positivity) h1' hA
      _ = (2:ℝ)^(2*(L:ℝ)*A) := by rw [← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num)]
  have ht : 0 ≤ α*(L:ℝ) - 4 := by linarith
  have hquad := sq_div_16_le_two_rpow (α*(L:ℝ) - 4) ht
  have hmain : 2*(L:ℝ)*A ≤ (2:ℝ)^(α*(L:ℝ)-4) := by
    have haux : 2*(L:ℝ)*A ≤ (α*(L:ℝ)-4)^2/16 := by
      have hhalf : α*(L:ℝ)/2 ≤ α*(L:ℝ) - 4 := by linarith
      have hsq : (α*(L:ℝ)/2)^2 ≤ (α*(L:ℝ)-4)^2 := by nlinarith
      nlinarith [hsq]
    linarith
  calc (1 + (L:ℝ))^A ≤ (2:ℝ)^(2*(L:ℝ)*A) := hpoly
    _ ≤ (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-4)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hmain

/-- **The exponential factor `2^{A·2^{ρL}}` is dominated by `2^{2^{αL-4}}`**
whenever `ρ ≤ α/8`, `8 ≤ αL` and `16A + 5 ≤ 7αL/8`. -/
lemma exp2_le_rpow (A ρ α : ℝ) (L : ℕ) (hA : 0 ≤ A) (hρα : ρ ≤ α/8) (hL1 : 1 ≤ (L:ℝ))
    (h1 : 8 ≤ α*(L:ℝ)) (h2 : 16*A + 5 ≤ 7*(α*(L:ℝ))/8) :
    (2:ℝ)^(A * (2:ℝ)^(ρ*(L:ℝ))) ≤ (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-4)) := by
  have hL0 : (0:ℝ) ≤ (L:ℝ) := by linarith
  have hρL : ρ*(L:ℝ) ≤ α*(L:ℝ)/8 := by nlinarith
  have hpow : (2:ℝ)^(ρ*(L:ℝ)) ≤ (2:ℝ)^(α*(L:ℝ)/8) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hρL
  have ht : 0 ≤ 7*(α*(L:ℝ))/8 - 4 := by linarith
  have hquad := sq_div_16_le_two_rpow (7*(α*(L:ℝ))/8 - 4) ht
  have hAle : A ≤ (2:ℝ)^(7*(α*(L:ℝ))/8 - 4) := by
    have ht1 : 1 ≤ 7*(α*(L:ℝ))/8 - 4 := by linarith
    have ht2 : 7*(α*(L:ℝ))/8 - 4 ≤ (7*(α*(L:ℝ))/8 - 4)^2 := by nlinarith
    have h16 : 16*A ≤ (7*(α*(L:ℝ))/8 - 4)^2 := by nlinarith
    linarith
  have hmul : A * (2:ℝ)^(ρ*(L:ℝ)) ≤ (2:ℝ)^(7*(α*(L:ℝ))/8-4) * (2:ℝ)^(α*(L:ℝ)/8) :=
    mul_le_mul hAle hpow (by positivity) (by positivity)
  have hcomb : (2:ℝ)^(7*(α*(L:ℝ))/8-4) * (2:ℝ)^(α*(L:ℝ)/8) = (2:ℝ)^(α*(L:ℝ)-4) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hfinal : A * (2:ℝ)^(ρ*(L:ℝ)) ≤ (2:ℝ)^(α*(L:ℝ)-4) := by rw [← hcomb]; exact hmul
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hfinal

/-- **The linear factor `cL` is negligible.**  If `8 ≤ αL` and `64c ≤ α²L`, then
`cL ≤ 2^{αL-3}`. -/
lemma lin_le_rpow (c α : ℝ) (L : ℕ) (hL1 : 1 ≤ (L:ℝ))
    (h1 : 8 ≤ α*(L:ℝ)) (h2 : 64*c ≤ α^2*(L:ℝ)) :
    c*(L:ℝ) ≤ (2:ℝ)^(α*(L:ℝ)-3) := by
  have hL0 : (0:ℝ) ≤ (L:ℝ) := by linarith
  have ht : 0 ≤ α*(L:ℝ) - 3 := by linarith
  have hquad := sq_div_16_le_two_rpow (α*(L:ℝ) - 3) ht
  have haux : c*(L:ℝ) ≤ (α*(L:ℝ)-3)^2/16 := by
    have hhalf : α*(L:ℝ)/2 ≤ α*(L:ℝ) - 3 := by linarith
    have hnn : 0 ≤ α*(L:ℝ)/2 := by linarith
    have hsq : (α*(L:ℝ)/2)^2 ≤ (α*(L:ℝ)-3)^2 := by nlinarith
    nlinarith [hsq]
  linarith

/-- **The weight `modelWeight A ρ L L L L` loses to the doubly exponential factor
`2^{-2^{L/C₀-2}}` with an exponential gain `2^{-cL}`,** for all large `L`.

This is the bookkeeping of the §6 regime: the admissible scales of `mod-approx` are the
`N ≥ 2^{2^{L/C₀}} = 2^{2^{L/C₀ - 2}·4}`, so the error factor `N^{-1}` of the proposition beats
the weight `⟨L⟩^A 2^{A·2^{ρL}}` as soon as `2ρC₀ ≤ 1/4`, leaving an exponential gain. -/
theorem modelWeightInvLeGain (A c ρ : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (hρ : 0 < ρ)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (hρC : 2 * ρ * C₀ ≤ 1 / 4) :
    ∃ B : ℕ, ∀ L : ℕ, B ≤ L →
      (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / C₀ - 2)) * Work.KMTAreas.A7.modelWeight A ρ L L L L
        ≤ (2 : ℝ) ^ (-(c * (L : ℝ))) := by
  set α : ℝ := 1/C₀ with hαdef
  have hC₀pos : (0:ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hαpos : 0 < α := by rw [hαdef]; positivity
  -- `ρ ≤ α/8` from `2ρC₀ ≤ 1/4`
  have hρle : ρ ≤ α/8 := by
    have h8C₀ : (0:ℝ) < 8*C₀ := by linarith
    have h1 : ρ ≤ 1/(8*C₀) := by
      rw [le_div_iff₀ h8C₀]
      nlinarith
    have h2 : 1/(8*C₀) = α/8 := by rw [hαdef]; ring
    linarith
  -- the threshold
  obtain ⟨B, hB⟩ := exists_nat_ge
    (max 1 (max (128*A/α^2) (max (8*(16*A+5)/(7*α)) (max (8/α) (64*c/α^2)))))
  refine ⟨B, ?_⟩
  intro L hBL
  set M : ℝ := max 1 (max (128*A/α^2) (max (8*(16*A+5)/(7*α)) (max (8/α) (64*c/α^2))))
    with hMdef
  have hB' : M ≤ (B:ℝ) := by rw [hMdef]; exact hB
  have hLM : M ≤ (L:ℝ) := le_trans hB' (by exact_mod_cast hBL)
  -- the four consequences of `L ≥ M`
  have hL1 : (1:ℝ) ≤ (L:ℝ) := le_trans (le_max_left _ _) hLM
  have hαL8 : 8 ≤ α*(L:ℝ) := by
    have hd : 8/α ≤ M := by
      rw [hMdef]
      exact le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have hdL : 8/α ≤ (L:ℝ) := le_trans hd hLM
    have := (div_le_iff₀ hαpos).mp hdL
    linarith
  have h128 : 128*A ≤ α^2*(L:ℝ) := by
    have ha : 128*A/α^2 ≤ M := by
      rw [hMdef]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have haL : 128*A/α^2 ≤ (L:ℝ) := le_trans ha hLM
    have := (div_le_iff₀ (by positivity : (0:ℝ) < α^2)).mp haL
    linarith
  have h16A5 : 16*A + 5 ≤ 7*(α*(L:ℝ))/8 := by
    have hb : 8*(16*A+5)/(7*α) ≤ M := by
      rw [hMdef]
      exact le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    have hbL : 8*(16*A+5)/(7*α) ≤ (L:ℝ) := le_trans hb hLM
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 7*α)).mp hbL
    nlinarith
  have h64c : 64*c ≤ α^2*(L:ℝ) := by
    have he : 64*c/α^2 ≤ M := by
      rw [hMdef]
      exact le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have heL : 64*c/α^2 ≤ (L:ℝ) := le_trans he hLM
    have := (div_le_iff₀ (by positivity : (0:ℝ) < α^2)).mp heL
    linarith
  -- the three factors
  have hpoly := poly_le_rpow A α L hA hL1 hαL8 h128
  have hexp2 := exp2_le_rpow A ρ α L hA hρle hL1 hαL8 h16A5
  have hlin := lin_le_rpow c α L hL1 hαL8 h64c
  -- the weight
  have hWle : (1 + (L:ℝ))^A * (2:ℝ)^(A * (2:ℝ)^(ρ*(L:ℝ)))
      ≤ (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-2) - c*(L:ℝ)) := by
    -- first bound the weight by `2^{2^{αL-3}}`
    have hW : (1 + (L:ℝ))^A * (2:ℝ)^(A * (2:ℝ)^(ρ*(L:ℝ)))
        ≤ (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-3)) := by
      have hfour : (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-4)) * (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-4))
          = (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-3)) := by
        rw [← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
        congr 1
        rw [show α*(L:ℝ)-3 = (α*(L:ℝ)-4) + 1 by ring,
          Real.rpow_add (show (0:ℝ) < 2 by norm_num),
          show (2:ℝ)^(1:ℝ) = 2 by norm_num]
        ring
      calc (1 + (L:ℝ))^A * (2:ℝ)^(A * (2:ℝ)^(ρ*(L:ℝ)))
          ≤ (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-4)) * (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-4)) :=
            mul_le_mul hpoly hexp2 (by positivity) (by positivity)
        _ = (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-3)) := hfour
    -- and `2^{αL-3}` is at most `2^{αL-2} - cL`
    have hgap : (2:ℝ)^(α*(L:ℝ)-3) ≤ (2:ℝ)^(α*(L:ℝ)-2) - c*(L:ℝ) := by
      have hsplit : (2:ℝ)^(α*(L:ℝ)-2) = (2:ℝ)^(α*(L:ℝ)-3) + (2:ℝ)^(α*(L:ℝ)-3) := by
        rw [show α*(L:ℝ)-2 = (α*(L:ℝ)-3) + 1 by ring,
          Real.rpow_add (show (0:ℝ) < 2 by norm_num),
          show (2:ℝ)^(1:ℝ) = 2 by norm_num]
        ring
      linarith [hlin]
    exact le_trans hW (Real.rpow_le_rpow_of_exponent_le (by norm_num) hgap)
  -- the exponent identity
  have hExpEq : (2:ℝ)^((L:ℝ)/C₀ - 2) = (2:ℝ)^(α*(L:ℝ)-2) := by
    congr 1
    rw [hαdef]
    ring
  have hlmax : Work.KMTAreas.A7.lmaxR L L L L = (L:ℝ) := by
    simp [Work.KMTAreas.A7.lmaxR, Work.Analysis.EndVar.lmax]
  have hMW : Work.KMTAreas.A7.modelWeight A ρ L L L L
      = (1 + (L:ℝ))^A * (2:ℝ)^(A * (2:ℝ)^(ρ*(L:ℝ))) := by
    rw [Work.KMTAreas.A7.modelWeight, hlmax]
  calc (2:ℝ)^(-(2:ℝ)^((L:ℝ)/C₀-2)) * Work.KMTAreas.A7.modelWeight A ρ L L L L
      = (2:ℝ)^(-(2:ℝ)^(α*(L:ℝ)-2)) * ((1 + (L:ℝ))^A * (2:ℝ)^(A*(2:ℝ)^(ρ*(L:ℝ)))) := by
        rw [hExpEq, hMW]
    _ ≤ (2:ℝ)^(-(2:ℝ)^(α*(L:ℝ)-2)) * (2:ℝ)^((2:ℝ)^(α*(L:ℝ)-2) - c*(L:ℝ)) :=
        mul_le_mul_of_nonneg_left hWle (by positivity)
    _ = (2:ℝ)^(-(c*(L:ℝ))) := by
        rw [← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
        congr 1
        ring

end

end Work.KMTPlan.A6
