import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps
import Submission.Work.KMTAreas.A7.Large.Defs

namespace Work.KMTAreas.A7

open Work.Analysis.EndVar

/-! ## Elementary arithmetic of the weight `2^{C·max(2^{ρL}, L)}`

The lemma `spike_sum_weight` absorbs the cardinalities of the two arithmetic frequency sets
`diffFreqs ρ l₁`, `diffFreqs ρ l₂`, the (bounded) prime `q` and the scale factor
`2^{Asp (k₁+k₂)}` into a single factor `2^{C · max (2^{ρL}) L}`, where
`L = lmaxR l₁ l₂ k₁ k₂ = max (max l₁ l₂) (max k₁ k₂)`.
-/

/-- `2^x * 2^y = 2^{x+y}` for real exponents. -/
lemma spike_two_rpow_mul (x y : ℝ) : (2 : ℝ) ^ x * (2 : ℝ) ^ y = (2 : ℝ) ^ (x + y) :=
  (Real.rpow_add (by norm_num) x y).symm

/-- Monotonicity of `2^(·)` on `ℝ`. -/
lemma spike_two_rpow_mono {x y : ℝ} (h : x ≤ y) : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

lemma spike_two_rpow_nonneg (x : ℝ) : (0 : ℝ) ≤ (2 : ℝ) ^ x := Real.rpow_nonneg (by norm_num) x

lemma spike_two_rpow_pos (x : ℝ) : (0 : ℝ) < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x

/-- If `logb 2 X ≤ n` then `X ≤ 2^n`. -/
lemma spike_two_rpow_le_of_logb_le {X : ℝ} (hX : 0 < X) {n : ℕ}
    (h : Real.logb 2 X ≤ (n : ℝ)) : X ≤ (2 : ℝ) ^ (n : ℝ) := by
  have h1 : (2 : ℝ) ^ (Real.logb 2 X) ≤ (2 : ℝ) ^ ((n : ℝ)) := spike_two_rpow_mono h
  rwa [Real.rpow_logb (by norm_num) (by norm_num) hX] at h1

/-! ### The four order lemmas for `lmaxR` -/

lemma spike_lmaxR_nonneg (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ lmaxR l₁ l₂ k₁ k₂ := by
  unfold lmaxR lmax
  have h1 : (0 : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) :=
    le_trans (Int.natCast_nonneg l₁) (le_trans (le_max_left _ _) (le_max_left _ _))
  exact_mod_cast h1

lemma spike_le_lmaxR_fst (l₁ l₂ k₁ k₂ : ℕ) : (l₁ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  unfold lmaxR lmax
  exact_mod_cast (le_trans (le_max_left (l₁ : ℤ) (l₂ : ℤ))
      (le_max_left (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ))) :
      (l₁ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)))

lemma spike_le_lmaxR_snd (l₁ l₂ k₁ k₂ : ℕ) : (l₂ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  unfold lmaxR lmax
  exact_mod_cast (le_trans (le_max_right (l₁ : ℤ) (l₂ : ℤ))
      (le_max_left (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ))) :
      (l₂ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)))

lemma spike_le_lmaxR_thd (l₁ l₂ k₁ k₂ : ℕ) : (k₁ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  unfold lmaxR lmax
  exact_mod_cast (le_trans (le_max_left (k₁ : ℤ) (k₂ : ℤ))
      (le_max_right (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ))) :
      (k₁ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)))

lemma spike_le_lmaxR_fth (l₁ l₂ k₁ k₂ : ℕ) : (k₂ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  unfold lmaxR lmax
  exact_mod_cast (le_trans (le_max_right (k₁ : ℤ) (k₂ : ℤ))
      (le_max_right (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ))) :
      (k₂ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)))

theorem spike_sum_weight (ρ : ℝ) (hρ : 0 < ρ) (Ccard Cper Csp Asp : ℝ)
    (hCcard : 0 < Ccard) (hCper : 0 < Cper) (hCsp : 0 < Csp) (hAsp : 0 ≤ Asp) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (l₁ l₂ k₁ k₂ N q : ℕ), 1 ≤ N → 1 ≤ q →
        ((Work.KMTAreas.A7.diffFreqs ρ l₁).card : ℝ)
            ≤ Ccard * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ))) →
        ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ)
            ≤ Ccard * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))) →
        (q : ℝ) ≤ (2 : ℝ) ^ (Cper * (2 : ℝ) ^ (ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)) →
        200 * (((Work.KMTAreas.A7.diffFreqs ρ l₁).card : ℝ) * ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ))
            * (Csp * (q : ℝ) * (2 : ℝ) ^ (Asp * ((k₁ : ℝ) + (k₂ : ℝ))) / (N : ℝ))
          ≤ (2 : ℝ) ^ (C * max ((2 : ℝ) ^ (ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂))
                (Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂))
              / (N : ℝ) := by
  -- Choose a natural `n` dominating the logarithms of the fixed constants.
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (max (Real.logb 2 200) (Real.logb 2 Ccard)) (max (Real.logb 2 Csp) 1))
  have hlog200 : Real.logb 2 200 ≤ (n : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
  have hlogCcard : Real.logb 2 Ccard ≤ (n : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
  have hlogCsp : Real.logb 2 Csp ≤ (n : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  have h200 : (200 : ℝ) ≤ (2 : ℝ) ^ (n : ℝ) :=
    spike_two_rpow_le_of_logb_le (by norm_num) hlog200
  have hCcard_le : Ccard ≤ (2 : ℝ) ^ (n : ℝ) :=
    spike_two_rpow_le_of_logb_le hCcard hlogCcard
  have hCsp_le : Csp ≤ (2 : ℝ) ^ (n : ℝ) :=
    spike_two_rpow_le_of_logb_le hCsp hlogCsp
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set C : ℝ := 4 * (n : ℝ) + 2 + Cper + 2 * Asp + 1 with hCdef
  refine ⟨C, ?_, ?_⟩
  · rw [hCdef]; positivity
  · intro l₁ l₂ k₁ k₂ N q hN hq hcard1 hcard2 hqbound
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    set L : ℝ := lmaxR l₁ l₂ k₁ k₂ with hL
    set a : ℝ := (2 : ℝ) ^ (ρ * L) with ha
    set M : ℝ := max a L with hM
    set A1 : ℝ := ((diffFreqs ρ l₁).card : ℝ) with hA1
    set A2 : ℝ := ((diffFreqs ρ l₂).card : ℝ) with hA2
    set Z : ℝ := (2 : ℝ) ^ (Asp * ((k₁ : ℝ) + (k₂ : ℝ))) with hZ
    have hA1nn : 0 ≤ A1 := by rw [hA1]; positivity
    have hA2nn : 0 ≤ A2 := by rw [hA2]; positivity
    have hZnn : 0 ≤ Z := by rw [hZ]; exact spike_two_rpow_nonneg _
    have hL0 : 0 ≤ L := by rw [hL]; exact spike_lmaxR_nonneg _ _ _ _
    have hL1 : (l₁ : ℝ) ≤ L := by rw [hL]; exact spike_le_lmaxR_fst _ _ _ _
    have hL2 : (l₂ : ℝ) ≤ L := by rw [hL]; exact spike_le_lmaxR_snd _ _ _ _
    have hk1L : (k₁ : ℝ) ≤ L := by rw [hL]; exact spike_le_lmaxR_thd _ _ _ _
    have hk2L : (k₂ : ℝ) ≤ L := by rw [hL]; exact spike_le_lmaxR_fth _ _ _ _
    have hρL : 0 ≤ ρ * L := mul_nonneg hρ.le hL0
    have ha1 : 1 ≤ a := by rw [ha]; exact Real.one_le_rpow (by norm_num) hρL
    have hM1 : 1 ≤ M := by rw [hM]; exact le_trans ha1 (le_max_left _ _)
    have haM : a ≤ M := by rw [hM]; exact le_max_left _ _
    have hLM : L ≤ M := by rw [hM]; exact le_max_right _ _
    -- bounds for the individual factors
    have hA1le : A1 ≤ (2 : ℝ) ^ ((n : ℝ) + a) := by
      have h2l : (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ))) ≤ (2 : ℝ) ^ a := by
        rw [ha]
        exact spike_two_rpow_mono (spike_two_rpow_mono (mul_le_mul_of_nonneg_left hL1 hρ.le))
      have hstep : A1 ≤ Ccard * (2 : ℝ) ^ a :=
        le_trans hcard1 (mul_le_mul_of_nonneg_left h2l hCcard.le)
      calc A1 ≤ Ccard * (2 : ℝ) ^ a := hstep
        _ ≤ (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ a :=
            mul_le_mul_of_nonneg_right hCcard_le (spike_two_rpow_nonneg a)
        _ = (2 : ℝ) ^ ((n : ℝ) + a) := spike_two_rpow_mul _ _
    have hA2le : A2 ≤ (2 : ℝ) ^ ((n : ℝ) + a) := by
      have h2l : (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))) ≤ (2 : ℝ) ^ a := by
        rw [ha]
        exact spike_two_rpow_mono (spike_two_rpow_mono (mul_le_mul_of_nonneg_left hL2 hρ.le))
      have hstep : A2 ≤ Ccard * (2 : ℝ) ^ a :=
        le_trans hcard2 (mul_le_mul_of_nonneg_left h2l hCcard.le)
      calc A2 ≤ Ccard * (2 : ℝ) ^ a := hstep
        _ ≤ (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ a :=
            mul_le_mul_of_nonneg_right hCcard_le (spike_two_rpow_nonneg a)
        _ = (2 : ℝ) ^ ((n : ℝ) + a) := spike_two_rpow_mul _ _
    have hqle : (q : ℝ) ≤ (2 : ℝ) ^ (Cper * a) := hqbound
    have hZle : Z ≤ (2 : ℝ) ^ (2 * Asp * L) := by
      rw [hZ]
      refine spike_two_rpow_mono ?_
      have hk : (k₁ : ℝ) + (k₂ : ℝ) ≤ 2 * L := by linarith only [hk1L, hk2L]
      calc Asp * ((k₁ : ℝ) + (k₂ : ℝ)) ≤ Asp * (2 * L) :=
            mul_le_mul_of_nonneg_left hk hAsp
        _ = 2 * Asp * L := by ring
    -- assemble
    have hpart1 : 200 * (A1 * A2) ≤
        (2 : ℝ) ^ (n : ℝ) * ((2 : ℝ) ^ ((n : ℝ) + a) * (2 : ℝ) ^ ((n : ℝ) + a)) := by
      have h12 : A1 * A2 ≤ (2 : ℝ) ^ ((n : ℝ) + a) * (2 : ℝ) ^ ((n : ℝ) + a) :=
        mul_le_mul hA1le hA2le hA2nn (spike_two_rpow_nonneg _)
      calc 200 * (A1 * A2) ≤ (2 : ℝ) ^ (n : ℝ) * (A1 * A2) :=
            mul_le_mul_of_nonneg_right h200 (mul_nonneg hA1nn hA2nn)
        _ ≤ (2 : ℝ) ^ (n : ℝ) * ((2 : ℝ) ^ ((n : ℝ) + a) * (2 : ℝ) ^ ((n : ℝ) + a)) :=
            mul_le_mul_of_nonneg_left h12 (spike_two_rpow_nonneg _)
    have hpart2 : Csp * (q : ℝ) * Z ≤
        (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (Cper * a) * (2 : ℝ) ^ (2 * Asp * L) := by
      have h12 : (q : ℝ) * Z ≤ (2 : ℝ) ^ (Cper * a) * (2 : ℝ) ^ (2 * Asp * L) :=
        mul_le_mul hqle hZle hZnn (spike_two_rpow_nonneg _)
      calc Csp * (q : ℝ) * Z = Csp * ((q : ℝ) * Z) := by ring
        _ ≤ Csp * ((2 : ℝ) ^ (Cper * a) * (2 : ℝ) ^ (2 * Asp * L)) :=
            mul_le_mul_of_nonneg_left h12 hCsp.le
        _ ≤ (2 : ℝ) ^ (n : ℝ) * ((2 : ℝ) ^ (Cper * a) * (2 : ℝ) ^ (2 * Asp * L)) :=
            mul_le_mul_of_nonneg_right hCsp_le (mul_nonneg (spike_two_rpow_nonneg _) (spike_two_rpow_nonneg _))
        _ = (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (Cper * a) * (2 : ℝ) ^ (2 * Asp * L) := by ring
    have key1 : 200 * (A1 * A2) * (Csp * (q : ℝ) * Z) ≤
        (2 : ℝ) ^ (n : ℝ) * ((2 : ℝ) ^ ((n : ℝ) + a) * (2 : ℝ) ^ ((n : ℝ) + a)) *
          ((2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (Cper * a) * (2 : ℝ) ^ (2 * Asp * L)) :=
      mul_le_mul hpart1 hpart2 (mul_nonneg (mul_nonneg hCsp.le (by positivity)) hZnn)
        (mul_nonneg (spike_two_rpow_nonneg _) (mul_nonneg (spike_two_rpow_nonneg _) (spike_two_rpow_nonneg _)))
    have hcomb : (2 : ℝ) ^ (n : ℝ) * ((2 : ℝ) ^ ((n : ℝ) + a) * (2 : ℝ) ^ ((n : ℝ) + a)) *
        ((2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (Cper * a) * (2 : ℝ) ^ (2 * Asp * L))
        = (2 : ℝ) ^ (4 * (n : ℝ) + 2 * a + Cper * a + 2 * Asp * L) := by
      simp only [spike_two_rpow_mul]
      congr 1
      ring
    have hexp_le : 4 * (n : ℝ) + 2 * a + Cper * a + 2 * Asp * L ≤ C * M := by
      rw [hCdef]
      have h1 : 4 * (n : ℝ) ≤ 4 * (n : ℝ) * M := by nlinarith only [hM1, hnn]
      have h2 : 2 * a ≤ 2 * M := by linarith only [haM]
      have h3 : Cper * a ≤ Cper * M := mul_le_mul_of_nonneg_left haM hCper.le
      have h4 : 2 * Asp * L ≤ 2 * Asp * M := mul_le_mul_of_nonneg_left hLM (by linarith only [hAsp])
      nlinarith only [h1, h2, h3, h4, hM1]
    have hfinal : (2 : ℝ) ^ (4 * (n : ℝ) + 2 * a + Cper * a + 2 * Asp * L)
        ≤ (2 : ℝ) ^ (C * M) := spike_two_rpow_mono hexp_le
    have key : 200 * (A1 * A2) * (Csp * (q : ℝ) * Z) ≤ (2 : ℝ) ^ (C * M) :=
      calc 200 * (A1 * A2) * (Csp * (q : ℝ) * Z)
          ≤ (2 : ℝ) ^ (n : ℝ) * ((2 : ℝ) ^ ((n : ℝ) + a) * (2 : ℝ) ^ ((n : ℝ) + a)) *
              ((2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (Cper * a) * (2 : ℝ) ^ (2 * Asp * L)) := key1
        _ = (2 : ℝ) ^ (4 * (n : ℝ) + 2 * a + Cper * a + 2 * Asp * L) := hcomb
        _ ≤ (2 : ℝ) ^ (C * M) := hfinal
    have hLHS : 200 * (A1 * A2) * (Csp * (q : ℝ) * Z / (N : ℝ))
        = (200 * (A1 * A2) * (Csp * (q : ℝ) * Z)) / (N : ℝ) := by ring
    rw [hLHS, div_le_div_iff_of_pos_right hNpos]
    exact key

end Work.KMTAreas.A7
