import Mathlib
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Work.LinnikAreas.perron_weight_near
import Submission.Work.LinnikAreas.perron_weight_far
import Submission.Work.LinnikAreas.nearSum_min_le
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

namespace Work.LinnikAreas

open scoped BigOperators

noncomputable section

/-- Values of a Dirichlet character have modulus at most one. -/
lemma norm_apply_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (a : ZMod N) :
    ‖ψ a‖ ≤ 1 := by
  by_cases h : IsUnit a
  · obtain ⟨u, rfl⟩ := h
    rw [← MulChar.coe_equivToUnitHom]
    exact le_of_eq (Complex.norm_eq_one_of_mem_rootsOfUnity
      (MulChar.apply_mem_rootsOfUnity u (χ := ψ)))
  · rw [MulChar.map_nonunit ψ h, norm_zero]
    norm_num

/-- `|Re λ(n)|` is bounded by the number of divisors of `n`. -/
lemma abs_lamR_le_card_divisors {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (n : ℕ) :
    |lamR ψ n| ≤ ((n.divisors.card : ℕ) : ℝ) := by
  have h1 : |(lam ψ n).re| ≤ ‖lam ψ n‖ := Complex.abs_re_le_norm _
  have h2 : ‖lam ψ n‖ ≤ ∑ d ∈ n.divisors, ‖ψ (d : ZMod N)‖ := by
    rw [lam]
    exact norm_sum_le _ _
  have h3 : ∑ d ∈ n.divisors, ‖ψ (d : ZMod N)‖ ≤ ∑ d ∈ n.divisors, (1 : ℝ) :=
    Finset.sum_le_sum (fun d _ => norm_apply_le_one ψ _)
  have h4 : ∑ d ∈ n.divisors, (1 : ℝ) = ((n.divisors.card : ℕ) : ℝ) := by simp
  calc |lamR ψ n| = |(lam ψ n).re| := rfl
    _ ≤ ‖lam ψ n‖ := h1
    _ ≤ ∑ d ∈ n.divisors, ‖ψ (d : ZMod N)‖ := h2
    _ ≤ ∑ d ∈ n.divisors, (1 : ℝ) := h3
    _ = ((n.divisors.card : ℕ) : ℝ) := h4

/-- The function `t ↦ t^{-3/2}` is antitone on positive reals. -/
lemma rpow_neg_three_halves_antitone {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    a ^ (-(3/2:ℝ)) ≤ b ^ (-(3/2:ℝ)) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  rw [Real.rpow_neg (le_of_lt ha) (3/2), Real.rpow_neg (le_of_lt hb) (3/2)]
  rw [inv_le_inv₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)]
  exact Real.rpow_le_rpow (le_of_lt hb) hba (by norm_num)

/-- `(x/2)^{-3/2} ≤ 4 x^{-3/2}` for `x > 0`. -/
lemma half_rpow_le_four {x : ℝ} (hx : 0 < x) :
    (x/2) ^ (-(3/2:ℝ)) ≤ 4 * x ^ (-(3/2:ℝ)) := by
  have h : (x/2) ^ (-(3/2:ℝ)) = (2:ℝ) ^ ((3:ℝ)/2) * x ^ (-(3/2:ℝ)) := by
    rw [show x/2 = (2:ℝ)⁻¹ * x by ring]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹) (le_of_lt hx)]
    rw [Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) ((3:ℝ)/2), inv_inv]
  rw [h]
  have h2 : (2:ℝ) ^ ((3:ℝ)/2) ≤ 4 := by
    have h3 : (2:ℝ) ^ ((3:ℝ)/2) ≤ (2:ℝ) ^ (2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_two] at h3
    norm_num at h3
    linarith
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hx) _)

/-- `1/x ≤ x^{-1/3}` for `x ≥ 1`. -/
lemma inv_le_rpow_neg_third {x : ℝ} (hx : 1 ≤ x) : x⁻¹ ≤ x ^ (-(1/3:ℝ)) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have h : x ^ ((1:ℝ)/3) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1:ℝ)/3 ≤ 1)
  calc x⁻¹ ≤ (x ^ ((1:ℝ)/3))⁻¹ := by
        rw [inv_le_inv₀ hx0 (Real.rpow_pos_of_pos hx0 _)]
        exact h
    _ = x ^ (-(1/3:ℝ)) := (Real.rpow_neg (le_of_lt hx0) ((1:ℝ)/3)).symm

/-- `x^{-1/2} ≤ x^{-1/3}` for `x ≥ 1`. -/
lemma rpow_neg_half_le_neg_third {x : ℝ} (hx : 1 ≤ x) :
    x ^ (-(1/2:ℝ)) ≤ x ^ (-(1/3:ℝ)) :=
  Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

theorem perron_triangle_error_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (β x T : ℝ),
      ψ ≠ 1 → 3 / 4 ≤ β → β ≤ 1 → 1 ≤ x → x ^ 2 ≤ T →
      x * (∑' n : ℕ, Work.LinnikAreas.lamR ψ n * (n : ℝ) ^ (-(1 + β)) *
              min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ≤ C * x ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨D, hDpos, hD⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1/4) (by norm_num)
  set Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3/2 : ℝ)) with hZdef
  have hZnn : 0 ≤ Z := by
    rw [hZdef]
    exact tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hsumm : Summable (fun n : ℕ => (n : ℝ) ^ (-(3/2 : ℝ))) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨D * (Z / Real.log 2 + 2 * Z + 150), ?_, ?_⟩
  · have h1 : 0 ≤ Z / Real.log 2 := div_nonneg hZnn hlog2pos.le
    nlinarith [hDpos, h1, hZnn]
  · intro N _ ψ β x T hψ hβ1 hβ2 hx hT
    have hxpos : (0:ℝ) < x := by linarith
    have hx2pos : (0:ℝ) < x ^ 2 := pow_pos hxpos 2
    have hT0 : (0:ℝ) ≤ T := le_trans hx2pos.le hT
    have hTpos : (0:ℝ) < T := by linarith
    set w : ℕ → ℝ := fun n => min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) with hwdef
    have hw0 : ∀ n, 0 ≤ w n := fun n => by
      rw [hwdef]
      exact le_min zero_le_one (one_div_nonneg.mpr (mul_nonneg hT0 (abs_nonneg _)))
    have hW : ∀ n : ℕ, w n ≤ 2 / x ^ 2 + min 1 (3 / (x * |x - (n : ℝ)|)) := by
      intro n
      rw [hwdef]
      rcases le_or_gt (2 * x) (n : ℝ) with h | h
      · refine le_trans (perron_weight_far x T n hx hT h) (le_add_of_nonneg_right ?_)
        exact le_min zero_le_one (div_nonneg (by norm_num) (mul_nonneg hxpos.le (abs_nonneg _)))
      · exact perron_weight_near x T n hx hT h.le
    set G : ℕ → ℝ := fun n => (n : ℝ) ^ (-(3/2:ℝ)) * w n with hGdef
    have hG0 : ∀ n, 0 ≤ G n := fun n => by
      rw [hGdef]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (hw0 n)
    have hGs : Summable G := by
      refine Summable.of_nonneg_of_le hG0 (fun n => ?_) hsumm
      rw [hGdef]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg n) _) (min_le_left _ _)
    set term : ℕ → ℝ :=
      fun n => lamR ψ n * (n : ℝ) ^ (-(1 + β)) * w n with htermdef
    have hpt : ∀ n : ℕ, |term n| ≤ D * G n := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · have hz : lamR ψ 0 = 0 := by simp [lamR, lam]
        have hG0' : G 0 = 0 := by
          rw [hGdef]
          simp [Real.zero_rpow (by norm_num : (-(3/2:ℝ)) ≠ 0)]
        rw [hG0', mul_zero]
        show |lamR ψ 0 * ((0:ℕ):ℝ) ^ (-(1+β)) * w 0| ≤ 0
        rw [hz]
        simp
      · have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        have h1 : |lamR ψ n| ≤ D * (n : ℝ) ^ ((1:ℝ)/4) :=
          le_trans (abs_lamR_le_card_divisors ψ n) (hD n)
        have h2 : (n : ℝ) ^ ((1:ℝ)/4) * (n : ℝ) ^ (-(1 + β)) ≤ (n : ℝ) ^ (-(3/2:ℝ)) := by
          rw [← Real.rpow_add hnpos]
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        have h3 : |term n| = |lamR ψ n| * (n : ℝ) ^ (-(1 + β)) * w n := by
          rw [htermdef, abs_mul, abs_mul,
            abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), abs_of_nonneg (hw0 n)]
        rw [h3, hGdef]
        have h4 : (0:ℝ) ≤ (n : ℝ) ^ (-(1 + β)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        have h5 : (0:ℝ) ≤ (n : ℝ) ^ (-(3/2:ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        calc |lamR ψ n| * (n : ℝ) ^ (-(1 + β)) * w n
            ≤ (D * (n : ℝ) ^ ((1:ℝ)/4)) * (n : ℝ) ^ (-(1 + β)) * w n := by
              gcongr
          _ = D * ((n : ℝ) ^ ((1:ℝ)/4) * (n : ℝ) ^ (-(1 + β))) * w n := by ring
          _ ≤ D * (n : ℝ) ^ (-(3/2:ℝ)) * w n := by
              gcongr
          _ = D * ((n : ℝ) ^ (-(3/2:ℝ)) * w n) := by ring
    have htermS : Summable term :=
      Summable.of_norm_bounded (Summable.mul_left D hGs) (fun n => hpt n)
    have hSle : (∑' n : ℕ, term n) ≤ D * (∑' n : ℕ, G n) := by
      calc (∑' n : ℕ, term n) ≤ ∑' n : ℕ, D * G n :=
            Summable.tsum_le_tsum (fun n => le_trans (le_abs_self _) (hpt n)) htermS
              (Summable.mul_left D hGs)
        _ = D * (∑' n : ℕ, G n) := tsum_mul_left
    set M : ℕ := ⌊2 * x⌋₊ with hMdef
    set M1 : ℕ := ⌊x / 2⌋₊ with hM1def
    have hMle : (M : ℝ) ≤ 2 * x := by rw [hMdef]; exact Nat.floor_le (by linarith)
    have hM1le : (M1 : ℝ) ≤ x / 2 := by rw [hM1def]; exact Nat.floor_le (by linarith)
    have hM1M : M1 ≤ M := by
      rw [hMdef, hM1def]
      exact Nat.floor_mono (by linarith)
    have htail : (∑' i : ℕ, G (i + (M + 1))) ≤ (2 / x ^ 2) * Z := by
      have hpt' : ∀ i : ℕ,
          G (i + (M + 1)) ≤ (2 / x ^ 2) * ((i + (M + 1) : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by
        intro i
        have hj : 2 * x ≤ ((i + (M + 1) : ℕ) : ℝ) := by
          have h1 : 2 * x < ((M + 1 : ℕ) : ℝ) := by
            have hlt := Nat.lt_floor_add_one (2 * x)
            rw [← hMdef] at hlt
            push_cast
            linarith
          have h2 : ((M + 1 : ℕ) : ℝ) ≤ ((i + (M + 1) : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_add_left (M + 1) i
          linarith
        have hwj : w (i + (M + 1)) ≤ 2 / x ^ 2 := perron_weight_far x T (i + (M + 1)) hx hT hj
        rw [hGdef]
        calc ((i + (M + 1) : ℕ) : ℝ) ^ (-(3/2:ℝ)) * w (i + (M + 1))
            ≤ ((i + (M + 1) : ℕ) : ℝ) ^ (-(3/2:ℝ)) * (2 / x ^ 2) :=
              mul_le_mul_of_nonneg_left hwj (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          _ = (2 / x ^ 2) * ((i + (M + 1) : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by ring
      have hg1 : Summable (fun i : ℕ => G (i + (M + 1))) :=
        (summable_nat_add_iff (M + 1) (f := G)).mpr hGs
      have hg2 : Summable (fun i : ℕ =>
          (2 / x ^ 2) * ((i + (M + 1) : ℕ) : ℝ) ^ (-(3/2:ℝ))) :=
        Summable.mul_left _ ((summable_nat_add_iff (M + 1)
          (f := fun n : ℕ => (n : ℝ) ^ (-(3/2:ℝ)))).mpr hsumm)
      have hstep := Summable.tsum_le_tsum hpt' hg1 hg2
      have hZshift : (∑' i : ℕ, ((i + 1 : ℕ) : ℝ) ^ (-(3/2:ℝ))) = Z := by
        have h := Summable.sum_add_tsum_nat_add (1) hsumm
        have h0 : ((0:ℕ):ℝ) ^ (-(3/2:ℝ)) = 0 := by
          rw [Nat.cast_zero, Real.zero_rpow (by norm_num : (-(3/2:ℝ)) ≠ 0)]
        rw [Finset.sum_range_one, h0, zero_add] at h
        rw [← hZdef] at h
        exact h
      have hshift : (∑' i : ℕ, ((i + (M + 1) : ℕ) : ℝ) ^ (-(3/2:ℝ))) ≤ Z := by
        have hle : ∀ i : ℕ,
            ((i + (M + 1) : ℕ) : ℝ) ^ (-(3/2:ℝ)) ≤ ((i + 1 : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by
          intro i
          apply rpow_neg_three_halves_antitone
          · positivity
          · push_cast
            linarith [Nat.zero_le M]
        calc (∑' i : ℕ, ((i + (M + 1) : ℕ) : ℝ) ^ (-(3/2:ℝ)))
            ≤ ∑' i : ℕ, ((i + 1 : ℕ) : ℝ) ^ (-(3/2:ℝ)) :=
              Summable.tsum_le_tsum hle
                ((summable_nat_add_iff (M+1) (f := fun n : ℕ => (n : ℝ) ^ (-(3/2:ℝ)))).mpr hsumm)
                ((summable_nat_add_iff 1 (f := fun n : ℕ => (n : ℝ) ^ (-(3/2:ℝ)))).mpr hsumm)
          _ = Z := hZshift
      rw [tsum_mul_left] at hstep
      refine le_trans hstep ?_
      exact mul_le_mul_of_nonneg_left hshift (by positivity)
    have hA : (∑ n ∈ Finset.Icc 0 M1, G n) ≤ Z / (x ^ 2 * Real.log 2) := by
      have hpt' : ∀ n ∈ Finset.Icc 0 M1,
          G n ≤ (1 / (x ^ 2 * Real.log 2)) * (n : ℝ) ^ (-(3/2:ℝ)) := by
        intro n hn
        simp only [Finset.mem_Icc] at hn
        rcases eq_or_ne n 0 with rfl | hn0
        · simp only [hGdef, Nat.cast_zero]
          rw [Real.zero_rpow (by norm_num : (-(3/2:ℝ)) ≠ 0)]
          simp
        · rw [hGdef]
          have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
          have hnle : (n : ℝ) ≤ x / 2 := by
            have h2 : (n : ℝ) ≤ ((M1 : ℕ) : ℝ) := by exact_mod_cast hn.2
            linarith
          have hxn : (2:ℝ) ≤ x / (n : ℝ) := by
            rw [le_div_iff₀ hnpos]
            linarith
          have hlog : Real.log 2 ≤ |Real.log (x / (n : ℝ))| :=
            le_trans (Real.log_le_log (by norm_num) hxn) (le_abs_self _)
          have hwle : w n ≤ 1 / (x ^ 2 * Real.log 2) := by
            rw [hwdef]
            have h1 : min 1 (1 / (T * |Real.log (x / (n:ℝ))|))
                ≤ 1 / (T * |Real.log (x / (n:ℝ))|) := min_le_right _ _
            have h2 : 1 / (T * |Real.log (x / (n:ℝ))|) ≤ 1 / (T * Real.log 2) := by
              apply one_div_le_one_div_of_le
              · exact mul_pos hTpos hlog2pos
              · exact mul_le_mul_of_nonneg_left hlog hT0
            have h3 : 1 / (T * Real.log 2) ≤ 1 / (x ^ 2 * Real.log 2) := by
              apply one_div_le_one_div_of_le
              · exact mul_pos (pow_pos hxpos 2) hlog2pos
              · exact mul_le_mul_of_nonneg_right hT hlog2pos.le
            linarith
          calc (n : ℝ) ^ (-(3/2:ℝ)) * w n
              ≤ (n : ℝ) ^ (-(3/2:ℝ)) * (1 / (x ^ 2 * Real.log 2)) :=
                mul_le_mul_of_nonneg_left hwle (Real.rpow_nonneg (Nat.cast_nonneg n) _)
            _ = (1 / (x ^ 2 * Real.log 2)) * (n : ℝ) ^ (-(3/2:ℝ)) := by ring
      calc (∑ n ∈ Finset.Icc 0 M1, G n)
          ≤ ∑ n ∈ Finset.Icc 0 M1, (1 / (x ^ 2 * Real.log 2)) * (n : ℝ) ^ (-(3/2:ℝ)) :=
            Finset.sum_le_sum hpt'
        _ = (1 / (x ^ 2 * Real.log 2)) * ∑ n ∈ Finset.Icc 0 M1, (n : ℝ) ^ (-(3/2:ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ (1 / (x ^ 2 * Real.log 2)) * Z := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Summable.sum_le_tsum (Finset.Icc 0 M1)
              (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _) hsumm
        _ = Z / (x ^ 2 * Real.log 2) := by ring
    have hB : (∑ n ∈ Finset.Icc (M1 + 1) M, G n) ≤ 150 * x ^ (-(3/2:ℝ)) := by
      have hpt' : ∀ n ∈ Finset.Icc (M1 + 1) M,
          G n ≤ 4 * x ^ (-(3/2:ℝ)) * (2 / x ^ 2 + min 1 (3 / (x * |x - (n : ℝ)|))) := by
        intro n hn
        simp only [Finset.mem_Icc] at hn
        have hn1 : x / 2 < (n : ℝ) := by
          have hfl : x / 2 < ((M1 : ℕ) : ℝ) + 1 := by
            have h := Nat.lt_floor_add_one (x / 2)
            rw [← hM1def] at h
            exact h
          have h2 : ((M1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
            have h3 : ((M1 + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
            push_cast at h3
            exact h3
          linarith
        have hn2 : (n : ℝ) ≤ 2 * x := by
          have h2 : (n : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hn.2
          linarith
        have hr : (n : ℝ) ^ (-(3/2:ℝ)) ≤ 4 * x ^ (-(3/2:ℝ)) :=
          le_trans (rpow_neg_three_halves_antitone (by linarith) hn1.le)
            (half_rpow_le_four hxpos)
        rw [hGdef]
        calc (n : ℝ) ^ (-(3/2:ℝ)) * w n
            ≤ (4 * x ^ (-(3/2:ℝ))) * (2 / x ^ 2 + min 1 (3 / (x * |x - (n : ℝ)|))) :=
              mul_le_mul hr (hW n) (hw0 n) (by positivity)
          _ = 4 * x ^ (-(3/2:ℝ)) * (2 / x ^ 2 + min 1 (3 / (x * |x - (n : ℝ)|))) := by
              ring
      have hcard : (((Finset.Icc (M1 + 1) M).card : ℕ) : ℝ) ≤ 3 * x := by
        have h1 : (Finset.Icc (M1 + 1) M).card ≤ M + 1 := by
          have hsub : Finset.Icc (M1 + 1) M ⊆ Finset.Icc 0 M := by
            intro n hn
            simp only [Finset.mem_Icc] at hn ⊢
            omega
          have := Finset.card_le_card hsub
          have h2 : (Finset.Icc (0:ℕ) M).card = M + 1 := by
            rw [Nat.card_Icc]; omega
          omega
        have h2 : ((M + 1 : ℕ) : ℝ) ≤ 3 * x := by
          push_cast
          linarith
        calc (((Finset.Icc (M1 + 1) M).card : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
              exact_mod_cast h1
          _ ≤ 3 * x := h2
      have hmin : (∑ n ∈ Finset.Icc (M1 + 1) M, min 1 (3 / (x * |x - (n : ℝ)|))) ≤ 30 := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnn) (nearSum_min_le x hx)
        · intro n hn
          simp only [Finset.mem_Icc] at hn ⊢
          obtain ⟨h1, h2⟩ := hn
          refine ⟨by omega, ?_⟩
          rw [← hMdef]
          exact h2
        · intro n _ _
          exact le_min zero_le_one (div_nonneg (by norm_num) (mul_nonneg hxpos.le (abs_nonneg _)))
      have hxhp : (0:ℝ) ≤ x ^ (-(3/2:ℝ)) := Real.rpow_nonneg hxpos.le _
      calc (∑ n ∈ Finset.Icc (M1 + 1) M, G n)
          ≤ ∑ n ∈ Finset.Icc (M1 + 1) M,
              4 * x ^ (-(3/2:ℝ)) * (2 / x ^ 2 + min 1 (3 / (x * |x - (n : ℝ)|))) :=
            Finset.sum_le_sum hpt'
        _ = 4 * x ^ (-(3/2:ℝ)) *
              (∑ n ∈ Finset.Icc (M1 + 1) M,
                (2 / x ^ 2 + min 1 (3 / (x * |x - (n : ℝ)|)))) := by
            rw [Finset.mul_sum]
        _ = 4 * x ^ (-(3/2:ℝ)) *
              ((∑ n ∈ Finset.Icc (M1 + 1) M, 2 / x ^ 2) +
               (∑ n ∈ Finset.Icc (M1 + 1) M, min 1 (3 / (x * |x - (n : ℝ)|)))) := by
            rw [Finset.sum_add_distrib]
        _ ≤ 4 * x ^ (-(3/2:ℝ)) * (3 * x * (2 / x ^ 2) + 30) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hc : (∑ n ∈ Finset.Icc (M1 + 1) M, 2 / x ^ 2)
                = ((Finset.Icc (M1 + 1) M).card : ℕ) * (2 / x ^ 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
            rw [hc]
            have hc2 : (((Finset.Icc (M1 + 1) M).card : ℕ) : ℝ) * (2 / x ^ 2) ≤ 3 * x * (2 / x ^ 2) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
            linarith [hmin]
        _ ≤ 150 * x ^ (-(3/2:ℝ)) := by
            have hb : 3 * x * (2 / x ^ 2) + 30 ≤ 36 := by
              rw [show 3 * x * (2 / x ^ 2) = 6 / x by field_simp; ring]
              have h2 : 6 / x ≤ 6 := by
                rw [div_le_iff₀ hxpos]
                linarith
              linarith
            calc 4 * x ^ (-(3/2:ℝ)) * (3 * x * (2 / x ^ 2) + 30)
                ≤ 4 * x ^ (-(3/2:ℝ)) * 36 := mul_le_mul_of_nonneg_left hb (by positivity)
              _ = 144 * x ^ (-(3/2:ℝ)) := by ring
              _ ≤ 150 * x ^ (-(3/2:ℝ)) := by
                  apply mul_le_mul_of_nonneg_right (by norm_num) hxhp
    have hGbound : (∑' n : ℕ, G n) ≤ Z / (x ^ 2 * Real.log 2) + 150 * x ^ (-(3/2:ℝ))
        + 2 * Z / x ^ 2 := by
      have hsplit := Summable.sum_add_tsum_nat_add (M + 1) hGs
      have hfin : (∑ i ∈ Finset.range (M + 1), G i) ≤ Z / (x ^ 2 * Real.log 2)
          + 150 * x ^ (-(3/2:ℝ)) := by
        have hr : Finset.range (M + 1) = Finset.Icc 0 M := by
          ext n; simp only [Finset.mem_range, Finset.mem_Icc]; omega
        rw [hr]
        have hunion : Finset.Icc 0 M = Finset.Icc 0 M1 ∪ Finset.Icc (M1 + 1) M := by
          ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hdisj : Disjoint (Finset.Icc 0 M1) (Finset.Icc (M1 + 1) M) := by
          rw [Finset.disjoint_left]; intro n h1 h2
          simp only [Finset.mem_Icc] at h1 h2; omega
        rw [hunion, Finset.sum_union hdisj]
        linarith [hA, hB]
      calc (∑' n : ℕ, G n)
          = (∑ i ∈ Finset.range (M + 1), G i) + ∑' i : ℕ, G (i + (M + 1)) := hsplit.symm
        _ ≤ (Z / (x ^ 2 * Real.log 2) + 150 * x ^ (-(3/2:ℝ))) + (2 / x ^ 2) * Z :=
            add_le_add hfin htail
        _ = Z / (x ^ 2 * Real.log 2) + 150 * x ^ (-(3/2:ℝ)) + 2 * Z / x ^ 2 := by ring
    have hfinal : x * (Z / (x ^ 2 * Real.log 2) + 150 * x ^ (-(3/2:ℝ)) + 2 * Z / x ^ 2)
        ≤ (Z / Real.log 2 + 2 * Z + 150) * x ^ (-(1/3:ℝ)) := by
      have hZlog : 0 ≤ Z / Real.log 2 := div_nonneg hZnn hlog2pos.le
      have hZnn' : 0 ≤ 2 * Z := by linarith
      have t1 : x * (Z / (x ^ 2 * Real.log 2)) ≤ (Z / Real.log 2) * x ^ (-(1/3:ℝ)) := by
        rw [show x * (Z / (x ^ 2 * Real.log 2)) = (Z / Real.log 2) * x⁻¹ by field_simp]
        exact mul_le_mul_of_nonneg_left (inv_le_rpow_neg_third hx) hZlog
      have t2 : x * (150 * x ^ (-(3/2:ℝ))) ≤ 150 * x ^ (-(1/3:ℝ)) := by
        have hxx : x * x ^ (-(3/2:ℝ)) = x ^ (-(1/2:ℝ)) := by
          nth_rewrite 1 [← Real.rpow_one x]
          rw [← Real.rpow_add hxpos]
          norm_num
        rw [show x * (150 * x ^ (-(3/2:ℝ))) = 150 * (x * x ^ (-(3/2:ℝ))) by ring, hxx]
        exact mul_le_mul_of_nonneg_left (rpow_neg_half_le_neg_third hx) (by norm_num)
      have t3 : x * (2 * Z / x ^ 2) ≤ (2 * Z) * x ^ (-(1/3:ℝ)) := by
        rw [show x * (2 * Z / x ^ 2) = (2 * Z) * x⁻¹ by field_simp]
        exact mul_le_mul_of_nonneg_left (inv_le_rpow_neg_third hx) hZnn'
      have hdist : x * (Z / (x ^ 2 * Real.log 2) + 150 * x ^ (-(3/2:ℝ)) + 2 * Z / x ^ 2)
          = x * (Z / (x ^ 2 * Real.log 2)) + x * (150 * x ^ (-(3/2:ℝ)))
            + x * (2 * Z / x ^ 2) := by ring
      rw [hdist]
      have hsum : (Z / Real.log 2 + 2 * Z + 150) * x ^ (-(1/3:ℝ))
          = (Z / Real.log 2) * x ^ (-(1/3:ℝ)) + 150 * x ^ (-(1/3:ℝ))
            + (2 * Z) * x ^ (-(1/3:ℝ)) := by ring
      rw [hsum]
      linarith [t1, t2, t3]
    calc x * (∑' n : ℕ, term n) ≤ x * (D * (∑' n : ℕ, G n)) :=
          mul_le_mul_of_nonneg_left hSle hxpos.le
      _ = D * (x * (∑' n : ℕ, G n)) := by ring
      _ ≤ D * (x * (Z / (x ^ 2 * Real.log 2) + 150 * x ^ (-(3/2:ℝ)) + 2 * Z / x ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGbound hxpos.le) hDpos.le
      _ ≤ D * ((Z / Real.log 2 + 2 * Z + 150) * x ^ (-(1/3:ℝ))) :=
          mul_le_mul_of_nonneg_left hfinal hDpos.le
      _ = (D * (Z / Real.log 2 + 2 * Z + 150)) * x ^ (-(1/3:ℝ)) := by ring

end

end Work.LinnikAreas
