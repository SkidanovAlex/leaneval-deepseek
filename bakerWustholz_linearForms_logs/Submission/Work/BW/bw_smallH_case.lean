import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.liouville_logForm
import Submission.Work.BW.fallback_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The small-`H` case of the Baker–Wüstholz bound

If the coefficient vector `b` satisfies `h'(L) = hL b d < Xbw n d` (the "small `H`" regime,
where BW's linear-forms-in-logarithms machinery is not needed), the challenge bound follows
directly from the Liouville estimate `liouville_logForm`, which gives

  `log ‖Λ‖ ≥ -∑ |bᵢ| h(αᵢ) - d log 2`,

together with the elementary arithmetic estimate `fallback_arith`, which absorbs
`n · β · dⁿ · ∏ h'(αᵢ) + d log 2` into `C(n,d) · max(log B, 1/d) · ∏ h'(αᵢ)` using
`log β ≤ Xbw n d` (i.e. `β ≤ C(n,d) / (dⁿ (n+d))`).
-/

namespace Work.BW

open Complex

/-- The modified height is always at least `1/d`. -/
private lemma one_div_finrank_le_modifiedHeight {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (β : K) :
    1 / (Module.finrank ℚ K : ℝ) ≤ BakerWustholz.modifiedHeight φ β := by
  simp only [BakerWustholz.modifiedHeight]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem bw_smallH_case {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0) (b : Fin n → ℤ) (hn : 1 ≤ n)
    (hH : hL b (Module.finrank ℚ K) < Xbw n (Module.finrank ℚ K))
    (hΛ : lam φ α b ≠ 0) {B : ℕ} (hB : 2 ≤ B) (hbB : ∀ i, (b i).natAbs ≤ B) :
    Real.log ‖lam φ α b‖ ≥
      -(BakerWustholz.C n (Module.finrank ℚ K) * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ))
          * ∏ i, BakerWustholz.modifiedHeight φ (α i)) := by
  classical
  set d : ℕ := Module.finrank ℚ K with hd
  have hd1 : 1 ≤ d := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  have hφα : ∀ i, φ (α i) ≠ 0 := fun i h => hα i (φ.injective (by rw [h, map_zero]))
  -- the maximal coefficient
  set β : ℕ := Finset.univ.sup (fun i : Fin n => (b i).natAbs) with hβ
  have hβb : ∀ i, (b i).natAbs ≤ β := fun i => by
    rw [hβ]
    exact Finset.le_sup (f := fun i : Fin n => (b i).natAbs) (Finset.mem_univ i)
  have hβB : β ≤ B := by
    rw [hβ]; exact Finset.sup_le fun i _ => hbB i
  have hlogB : Real.log 2 ≤ Real.log (B : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hB)
  have hlogβB : Real.log (β : ℝ) ≤ Real.log (B : ℝ) := by
    rcases Nat.eq_zero_or_pos β with h | h
    · rw [h]
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hB))
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hβB)
  have hlogβ : Real.log (β : ℝ) ≤ hL b d := by
    simp only [hL, hβ]
    exact le_max_left _ _
  have hβ1 : 1 ≤ β := by
    obtain ⟨i, hi⟩ : ∃ i : Fin n, b i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hΛ (by simp [lam, h])
    exact le_trans (Int.natAbs_pos.mpr hi) (hβb i)
  -- Liouville: `log ‖Λ‖ ≥ -∑ |bᵢ| h(αᵢ) - d log 2`
  have hliou := liouville_logForm φ α hα (fun i => Complex.log (φ (α i)))
    (fun i => Complex.exp_log (hφα i)) b (by simpa [lam] using hΛ)
  have hPpos : 0 < ∏ i : Fin n, BakerWustholz.modifiedHeight φ (α i) :=
    Finset.prod_pos fun i _ =>
      lt_of_lt_of_le (one_div_pos.mpr hdpos) (one_div_finrank_le_modifiedHeight φ _)
  have hPlow : (1 : ℝ) / (d : ℝ) ^ n ≤ ∏ i : Fin n, BakerWustholz.modifiedHeight φ (α i) := by
    have h1 : ∏ i : Fin n, (1 / (d : ℝ)) ≤ ∏ i : Fin n, BakerWustholz.modifiedHeight φ (α i) :=
      Finset.prod_le_prod₀ (fun i _ => le_of_lt (one_div_pos.mpr hdpos))
        (fun i _ => one_div_finrank_le_modifiedHeight φ _)
    simpa [one_div, inv_pow] using h1
  -- `∑ |bᵢ| h(αᵢ) ≤ β ∑ h(αᵢ) ≤ β d ∑ h'(αᵢ) ≤ n β dⁿ ∏ h'(αᵢ)`
  have hsum1 : (∑ i : Fin n, ((b i).natAbs : ℝ) * Height.logHeight₁ (α i))
      ≤ (β : ℝ) * ∑ i : Fin n, Height.logHeight₁ (α i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast hβb i) (Height.zero_le_logHeight₁ _)
  have hsum2 : (∑ i : Fin n, Height.logHeight₁ (α i))
      ≤ (d : ℝ) * ∑ i : Fin n, BakerWustholz.modifiedHeight φ (α i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h : Height.logHeight₁ (α i) / (d : ℝ) ≤ BakerWustholz.modifiedHeight φ (α i) :=
      le_max_left _ _
    have h2 : Height.logHeight₁ (α i) = (d : ℝ) * (Height.logHeight₁ (α i) / (d : ℝ)) := by
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left h (le_of_lt hdpos)
  have hper : ∀ i : Fin n, BakerWustholz.modifiedHeight φ (α i)
      ≤ (d : ℝ) ^ (n - 1) * ∏ j : Fin n, BakerWustholz.modifiedHeight φ (α j) := by
    intro i
    have hmul : BakerWustholz.modifiedHeight φ (α i)
        * (∏ j ∈ Finset.univ.erase i, BakerWustholz.modifiedHeight φ (α j))
        = ∏ j : Fin n, BakerWustholz.modifiedHeight φ (α j) :=
      Finset.mul_prod_erase Finset.univ (fun j => BakerWustholz.modifiedHeight φ (α j))
        (Finset.mem_univ i)
    have hle : (1 / (d : ℝ)) ^ (n - 1)
        ≤ ∏ j ∈ Finset.univ.erase i, BakerWustholz.modifiedHeight φ (α j) := by
      have h1 : ∏ j ∈ Finset.univ.erase i, (1 / (d : ℝ))
          ≤ ∏ j ∈ Finset.univ.erase i, BakerWustholz.modifiedHeight φ (α j) :=
        Finset.prod_le_prod₀ (fun j _ => le_of_lt (one_div_pos.mpr hdpos))
          (fun j _ => one_div_finrank_le_modifiedHeight φ _)
      have h2 : (Finset.univ.erase i).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      rwa [Finset.prod_const, h2] at h1
    have hpos : 0 ≤ BakerWustholz.modifiedHeight φ (α i) :=
      le_trans (le_of_lt (one_div_pos.mpr hdpos)) (one_div_finrank_le_modifiedHeight φ _)
    have h3 : BakerWustholz.modifiedHeight φ (α i) * ((1 / (d : ℝ)) ^ (n - 1))
        ≤ BakerWustholz.modifiedHeight φ (α i)
          * ∏ j ∈ Finset.univ.erase i, BakerWustholz.modifiedHeight φ (α j) :=
      mul_le_mul_of_nonneg_left hle hpos
    rw [hmul] at h3
    have h4 : BakerWustholz.modifiedHeight φ (α i)
        = (d : ℝ) ^ (n - 1)
          * (BakerWustholz.modifiedHeight φ (α i) * (1 / (d : ℝ)) ^ (n - 1)) := by
      have hpow : (d : ℝ) ^ (n - 1) * (1 / (d : ℝ)) ^ (n - 1) = 1 := by
        rw [← mul_pow, mul_one_div, div_self (ne_of_gt hdpos), one_pow]
      rw [show (d : ℝ) ^ (n - 1)
            * (BakerWustholz.modifiedHeight φ (α i) * (1 / (d : ℝ)) ^ (n - 1))
          = BakerWustholz.modifiedHeight φ (α i)
            * ((d : ℝ) ^ (n - 1) * (1 / (d : ℝ)) ^ (n - 1)) from by ring, hpow, mul_one]
    rw [h4]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hsum3 : (∑ i : Fin n, BakerWustholz.modifiedHeight φ (α i))
      ≤ (n : ℝ) * (d : ℝ) ^ (n - 1) * ∏ i : Fin n, BakerWustholz.modifiedHeight φ (α i) := by
    calc (∑ i : Fin n, BakerWustholz.modifiedHeight φ (α i))
        ≤ ∑ _i : Fin n, (d : ℝ) ^ (n - 1)
            * ∏ j : Fin n, BakerWustholz.modifiedHeight φ (α j) :=
          Finset.sum_le_sum fun i _ => hper i
      _ = (n : ℝ) * (d : ℝ) ^ (n - 1) * ∏ j : Fin n, BakerWustholz.modifiedHeight φ (α j) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsum : (∑ i : Fin n, ((b i).natAbs : ℝ) * Height.logHeight₁ (α i))
      ≤ (n : ℝ) * (β : ℝ) * (d : ℝ) ^ n * ∏ i : Fin n,
          BakerWustholz.modifiedHeight φ (α i) := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := le_of_lt hdpos
    have hβ0 : (0 : ℝ) ≤ (β : ℝ) := by positivity
    calc (∑ i : Fin n, ((b i).natAbs : ℝ) * Height.logHeight₁ (α i))
        ≤ (β : ℝ) * ∑ i : Fin n, Height.logHeight₁ (α i) := hsum1
      _ ≤ (β : ℝ) * ((d : ℝ) * ∑ i : Fin n, BakerWustholz.modifiedHeight φ (α i)) :=
          mul_le_mul_of_nonneg_left hsum2 hβ0
      _ ≤ (β : ℝ) * ((d : ℝ) * ((n : ℝ) * (d : ℝ) ^ (n - 1)
            * ∏ i : Fin n, BakerWustholz.modifiedHeight φ (α i))) := by
          refine mul_le_mul_of_nonneg_left ?_ hβ0
          exact mul_le_mul_of_nonneg_left hsum3 hd0
      _ = (n : ℝ) * (β : ℝ) * (d : ℝ) ^ n
            * ∏ i : Fin n, BakerWustholz.modifiedHeight φ (α i) := by
          have hdn : (d : ℝ) ^ (n - 1) * (d : ℝ) = (d : ℝ) ^ n := by
            rw [← pow_succ, Nat.sub_add_cancel hn]
          rw [← hdn]
          ring
  -- the arithmetic estimate
  have hβR1 : (1 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβ1
  have hβX : Real.log (β : ℝ) ≤ Xbw n d := le_of_lt (lt_of_le_of_lt hlogβ hH)
  have hM1 : Real.log (β : ℝ) ≤ max (Real.log (B : ℝ)) (1 / (d : ℝ)) :=
    le_trans hlogβB (le_max_left _ _)
  have hM2 : Real.log 2 ≤ max (Real.log (B : ℝ)) (1 / (d : ℝ)) :=
    le_trans hlogB (le_max_left _ _)
  have harith := fallback_arith hn hd1 hβR1 hβX hM1 hM2 hPpos hPlow
  have hliou' : Real.log ‖lam φ α b‖
      ≥ -(∑ i : Fin n, ((b i).natAbs : ℝ) * Height.logHeight₁ (α i))
        - (d : ℝ) * Real.log 2 := by
    simpa only [lam] using hliou
  have hgoal : Real.log ‖lam φ α b‖
      ≥ -(BakerWustholz.C n d * max (Real.log (B : ℝ)) (1 / (d : ℝ))
          * ∏ i : Fin n, BakerWustholz.modifiedHeight φ (α i)) := by
    have h2 : (∑ i : Fin n, ((b i).natAbs : ℝ) * Height.logHeight₁ (α i))
        + (d : ℝ) * Real.log 2
        ≤ BakerWustholz.C n d * max (Real.log (B : ℝ)) (1 / (d : ℝ))
          * ∏ i : Fin n, BakerWustholz.modifiedHeight φ (α i) := by
      linarith
    linarith
  exact hgoal

end Work.BW
