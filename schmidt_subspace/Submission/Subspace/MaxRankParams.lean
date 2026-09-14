import Mathlib

/-!
# The numerical parameters of the maximal-rank argument

For the maximal-rank part of the subspace theorem we need the following parameters, all
functions of `n`, `ε = -∑ γ` and `S = ∑ |γ|`:

* `Θ = ε / (100·(n+1)·S)`: the relative width of the flatness window;
* `W = Θ`: the Siegel window parameter;
* `η = Θ/8`: the Roth parameter;
* `B = ⌈100·(n+1)²·n·S/ε⌉₊ + 1`: the grid size;
* `C0 = n·B + 1`: the box constant for the grid points.

The key inequalities are `mrB_div_le` (the grid size dominates `(n+1)·n/Θ`) and `mr_hsmall`
(the `hsmall` hypothesis of the `A`-bounds).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Submission.Subspace

/-- The relative width of the flatness window. -/
noncomputable def mrTheta (n : ℕ) (ε S : ℝ) : ℝ := ε / (100 * ((n : ℝ) + 1) * S)

/-- The Roth parameter. -/
noncomputable def mrEta (n : ℕ) (ε S : ℝ) : ℝ := mrTheta n ε S / 8

/-- The grid size. -/
noncomputable def mrB (n : ℕ) (ε S : ℝ) : ℕ :=
  ⌈100 * ((n : ℝ) + 1) ^ 2 * n * S / ε⌉₊ + 1

/-- The box constant for the grid points. -/
noncomputable def mrC0 (n : ℕ) (ε S : ℝ) : ℝ := (n : ℝ) * (mrB n ε S : ℝ) + 1

lemma mrTheta_pos {n : ℕ} {ε S : ℝ} (hε : 0 < ε) (hS : 0 < S) :
    0 < mrTheta n ε S := by
  rw [mrTheta]
  exact div_pos hε (by positivity)

lemma mrTheta_le_half {n : ℕ} {ε S : ℝ} (hε : 0 < ε) (hS : 0 < S) (hεS : ε ≤ S) :
    mrTheta n ε S ≤ 1 / 2 := by
  rw [mrTheta, div_le_iff₀ (by positivity : (0:ℝ) < 100 * ((n : ℝ) + 1) * S)]
  nlinarith [hε, hS, hεS, Nat.cast_nonneg (α := ℝ) n]

lemma mrEta_pos {n : ℕ} {ε S : ℝ} (hε : 0 < ε) (hS : 0 < S) : 0 < mrEta n ε S := by
  rw [mrEta]; linarith [mrTheta_pos (n := n) hε hS]

lemma mrEta_le_half {n : ℕ} {ε S : ℝ} (hε : 0 < ε) (hS : 0 < S) (hεS : ε ≤ S) :
    mrEta n ε S ≤ 1 / 2 := by
  rw [mrEta]; linarith [mrTheta_le_half (n := n) hε hS hεS, mrTheta_pos (n := n) hε hS]

lemma mrEta_pos_lt_half {n : ℕ} {ε S : ℝ} (hε : 0 < ε) (hS : 0 < S) (hεS : ε ≤ S) :
    0 < mrEta n ε S ∧ mrEta n ε S ≤ 1 / 2 :=
  ⟨mrEta_pos hε hS, mrEta_le_half hε hS hεS⟩

lemma mrEta_lt_theta {n : ℕ} {ε S : ℝ} (hε : 0 < ε) (hS : 0 < S) :
    4 * mrEta n ε S < mrTheta n ε S := by
  rw [mrEta]; linarith [mrTheta_pos (n := n) hε hS]

lemma mrB_one_le {n : ℕ} {ε S : ℝ} : 1 ≤ mrB n ε S := by
  rw [mrB]; exact Nat.le_add_left 1 _

lemma mrB_ge {n : ℕ} {ε S : ℝ} :
    (100 * ((n : ℝ) + 1) ^ 2 * n * S / ε : ℝ) ≤ (mrB n ε S : ℝ) := by
  have h := Nat.le_ceil (100 * ((n : ℝ) + 1) ^ 2 * n * S / ε)
  rw [mrB]
  push_cast
  linarith

lemma mrB_div_le {n : ℕ} {ε S : ℝ} (hε : 0 < ε) (hS : 0 < S) :
    ((n : ℝ) + 1) * n / (mrB n ε S : ℝ) ≤ mrTheta n ε S := by
  have hpos : (0 : ℝ) < 100 * ((n : ℝ) + 1) * S := by positivity
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [mrTheta]
    simp only [Nat.cast_zero, mul_zero, zero_div]
    exact div_nonneg (le_of_lt hε) (by positivity)
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : (0 : ℝ) < 100 * ((n : ℝ) + 1) ^ 2 * n * S / ε := by positivity
    have h2 : 100 * ((n : ℝ) + 1) ^ 2 * n * S / ε ≤ (mrB n ε S : ℝ) := mrB_ge
    have h3 : ((n : ℝ) + 1) * n / (mrB n ε S : ℝ)
        ≤ ((n : ℝ) + 1) * n / (100 * ((n : ℝ) + 1) ^ 2 * n * S / ε) :=
      div_le_div_of_nonneg_left (by positivity) h1 h2
    refine le_trans h3 (le_of_eq ?_)
    rw [mrTheta]
    field_simp

lemma mrC0_one_le {n : ℕ} {ε S : ℝ} : 1 ≤ mrC0 n ε S := by
  rw [mrC0]
  have : (0 : ℝ) ≤ (n : ℝ) * (mrB n ε S : ℝ) := by positivity
  linarith

/-- The `hsmall` hypothesis of the `A`-bounds holds by construction. -/
lemma mr_hsmall {n : ℕ} {ε S : ℝ} (hε : 0 < ε) (hS : 0 < S) (hεS : ε ≤ S)
    (γ : Fin (n+1) → ℝ) (hγ : ∑ k, |γ k| ≤ S) {m : ℕ} (hm : 1 ≤ m) :
    (((m : ℝ) * mrTheta n ε S
        + ((m : ℝ) * mrTheta n ε S + (m : ℝ) * ((n : ℝ) + 1) * n / (mrB n ε S : ℝ))
        + mrTheta n ε S * (m : ℝ)) * (∑ k : Fin (n+1), |γ k|))
      < ε * (m : ℝ) / (2 * ((n : ℝ) + 1)) := by
  set Θ := mrTheta n ε S with hΘdef
  have hΘ0 : 0 < Θ := mrTheta_pos hε hS
  have hB : ((n : ℝ) + 1) * n / (mrB n ε S : ℝ) ≤ Θ := mrB_div_le hε hS
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsum0 : (0 : ℝ) ≤ (∑ k : Fin (n+1), |γ k|) := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hkey : (m : ℝ) * ((n : ℝ) + 1) * n / (mrB n ε S : ℝ)
      = (m : ℝ) * (((n : ℝ) + 1) * n / (mrB n ε S : ℝ)) := by
    field_simp
  have hbracket : (m : ℝ) * Θ + ((m : ℝ) * Θ + (m : ℝ) * ((n : ℝ) + 1) * n / (mrB n ε S : ℝ))
      + Θ * (m : ℝ) ≤ 4 * Θ * (m : ℝ) := by
    rw [hkey]
    have h1 : (m : ℝ) * (((n : ℝ) + 1) * n / (mrB n ε S : ℝ)) ≤ (m : ℝ) * Θ :=
      mul_le_mul_of_nonneg_left hB (le_of_lt hm0)
    linarith
  have hstep1 : ((m : ℝ) * Θ + ((m : ℝ) * Θ + (m : ℝ) * ((n : ℝ) + 1) * n / (mrB n ε S : ℝ))
      + Θ * (m : ℝ)) * (∑ k : Fin (n+1), |γ k|) ≤ (4 * Θ * (m : ℝ)) * S :=
    mul_le_mul hbracket hγ hsum0 (by positivity)
  have hstep2 : (4 * Θ * (m : ℝ)) * S = ε * (m : ℝ) / (25 * ((n : ℝ) + 1)) := by
    rw [hΘdef, mrTheta]
    field_simp
    ring
  have hstep3 : ε * (m : ℝ) / (25 * ((n : ℝ) + 1)) < ε * (m : ℝ) / (2 * ((n : ℝ) + 1)) := by
    have hεm : (0 : ℝ) < ε * (m : ℝ) := mul_pos hε hm0
    have hunit : 1 / (25 * ((n : ℝ) + 1)) < 1 / (2 * ((n : ℝ) + 1)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    calc ε * (m : ℝ) / (25 * ((n : ℝ) + 1))
        = ε * (m : ℝ) * (1 / (25 * ((n : ℝ) + 1))) := by ring
      _ < ε * (m : ℝ) * (1 / (2 * ((n : ℝ) + 1))) := mul_lt_mul_of_pos_left hunit hεm
      _ = ε * (m : ℝ) / (2 * ((n : ℝ) + 1)) := by ring
  calc (((m : ℝ) * mrTheta n ε S
        + ((m : ℝ) * mrTheta n ε S + (m : ℝ) * ((n : ℝ) + 1) * n / (mrB n ε S : ℝ))
        + mrTheta n ε S * (m : ℝ)) * (∑ k : Fin (n+1), |γ k|))
      = ((m : ℝ) * Θ + ((m : ℝ) * Θ + (m : ℝ) * ((n : ℝ) + 1) * n / (mrB n ε S : ℝ))
        + Θ * (m : ℝ)) * (∑ k : Fin (n+1), |γ k|) := by rw [hΘdef]
    _ ≤ (4 * Θ * (m : ℝ)) * S := hstep1
    _ = ε * (m : ℝ) / (25 * ((n : ℝ) + 1)) := hstep2
    _ < ε * (m : ℝ) / (2 * ((n : ℝ) + 1)) := hstep3

/-- The finite list of numeric lower bounds defining the threshold `mrA`. -/
noncomputable def mrAlist (n : ℕ) (ε S θ MΛ C : ℝ) (m : ℕ) : Finset ℝ :=
  {1,
   8 * (1 + mrTheta n ε S) * Real.log (C * MΛ) / (mrEta n ε S ^ (2 ^ (m - 1)) * θ),
   800 * (1 + mrTheta n ε S) * (m : ℝ) / (mrEta n ε S ^ (2 ^ (m - 1)) * θ),
   8 * (1 + mrTheta n ε S) * Real.log C / (mrEta n ε S ^ (2 ^ (m - 1)) * θ),
   (1 + mrTheta n ε S) * 512 * (n : ℝ) ^ 2 * (m : ℝ) ^ 2
     / (mrEta n ε S ^ (2 ^ (m - 1)) * θ) ^ 2,
   (1 + mrTheta n ε S) * 16 * ((n : ℝ) + 1) * Real.log C / (ε * (m : ℝ)),
   (1 + mrTheta n ε S) * 2048 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) + n) ^ 2 / ε ^ 2,
   32 * ((n : ℝ) + 1) * (1 + mrTheta n ε S) *
     (Real.log (C * MΛ) + ((n : ℝ) + 1) * Real.log 2 + Real.log (((n : ℝ) + 1) * MΛ + 1)
       + Real.log ((n : ℝ) * (mrB n ε S : ℝ) + 1)) / (ε * (m : ℝ)),
   4 * (1 + mrTheta n ε S) * ((n : ℝ) + 1)}

/-- The threshold for the size `log Q_min` of the smallest scale of the maximal-rank
configuration.  Every numeric condition of the assembled argument is implied by
`log Q_min ≥ mrA`. -/
noncomputable def mrA (n : ℕ) (ε S θ MΛ C : ℝ) (m : ℕ) : ℝ :=
  (mrAlist n ε S θ MΛ C m).max' (by simp [mrAlist])

lemma mem_mrAlist_1 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    (1 : ℝ) ∈ mrAlist n ε S θ MΛ C m := by simp [mrAlist]
lemma mem_mrAlist_2 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    8 * (1 + mrTheta n ε S) * Real.log (C * MΛ) / (mrEta n ε S ^ (2 ^ (m - 1)) * θ)
      ∈ mrAlist n ε S θ MΛ C m := by simp [mrAlist]
lemma mem_mrAlist_3 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    800 * (1 + mrTheta n ε S) * (m : ℝ) / (mrEta n ε S ^ (2 ^ (m - 1)) * θ)
      ∈ mrAlist n ε S θ MΛ C m := by simp [mrAlist]
lemma mem_mrAlist_4 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    8 * (1 + mrTheta n ε S) * Real.log C / (mrEta n ε S ^ (2 ^ (m - 1)) * θ)
      ∈ mrAlist n ε S θ MΛ C m := by simp [mrAlist]
lemma mem_mrAlist_5 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    (1 + mrTheta n ε S) * 512 * (n : ℝ) ^ 2 * (m : ℝ) ^ 2
      / (mrEta n ε S ^ (2 ^ (m - 1)) * θ) ^ 2 ∈ mrAlist n ε S θ MΛ C m := by simp [mrAlist]
lemma mem_mrAlist_6 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    (1 + mrTheta n ε S) * 16 * ((n : ℝ) + 1) * Real.log C / (ε * (m : ℝ))
      ∈ mrAlist n ε S θ MΛ C m := by simp [mrAlist]
lemma mem_mrAlist_7 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    (1 + mrTheta n ε S) * 2048 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) + n) ^ 2 / ε ^ 2
      ∈ mrAlist n ε S θ MΛ C m := by simp [mrAlist]
lemma mem_mrAlist_8 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    32 * ((n : ℝ) + 1) * (1 + mrTheta n ε S) *
      (Real.log (C * MΛ) + ((n : ℝ) + 1) * Real.log 2 + Real.log (((n : ℝ) + 1) * MΛ + 1)
        + Real.log ((n : ℝ) * (mrB n ε S : ℝ) + 1)) / (ε * (m : ℝ))
      ∈ mrAlist n ε S θ MΛ C m := by simp [mrAlist]
lemma mem_mrAlist_9 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    4 * (1 + mrTheta n ε S) * ((n : ℝ) + 1) ∈ mrAlist n ε S θ MΛ C m := by simp [mrAlist]

lemma mrA_ge_one {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} : (1 : ℝ) ≤ mrA n ε S θ MΛ C m :=
  Finset.le_max' _ _ (mem_mrAlist_1)

lemma le_mrA_2 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    8 * (1 + mrTheta n ε S) * Real.log (C * MΛ) / (mrEta n ε S ^ (2 ^ (m - 1)) * θ)
      ≤ mrA n ε S θ MΛ C m := Finset.le_max' _ _ mem_mrAlist_2

lemma le_mrA_3 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    800 * (1 + mrTheta n ε S) * (m : ℝ) / (mrEta n ε S ^ (2 ^ (m - 1)) * θ)
      ≤ mrA n ε S θ MΛ C m := Finset.le_max' _ _ mem_mrAlist_3

lemma le_mrA_4 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    8 * (1 + mrTheta n ε S) * Real.log C / (mrEta n ε S ^ (2 ^ (m - 1)) * θ)
      ≤ mrA n ε S θ MΛ C m := Finset.le_max' _ _ mem_mrAlist_4

lemma le_mrA_5 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    (1 + mrTheta n ε S) * 512 * (n : ℝ) ^ 2 * (m : ℝ) ^ 2
      / (mrEta n ε S ^ (2 ^ (m - 1)) * θ) ^ 2 ≤ mrA n ε S θ MΛ C m :=
  Finset.le_max' _ _ mem_mrAlist_5

lemma le_mrA_6 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    (1 + mrTheta n ε S) * 16 * ((n : ℝ) + 1) * Real.log C / (ε * (m : ℝ))
      ≤ mrA n ε S θ MΛ C m := Finset.le_max' _ _ mem_mrAlist_6

lemma le_mrA_7 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    (1 + mrTheta n ε S) * 2048 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) + n) ^ 2 / ε ^ 2
      ≤ mrA n ε S θ MΛ C m := Finset.le_max' _ _ mem_mrAlist_7

lemma le_mrA_8 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    32 * ((n : ℝ) + 1) * (1 + mrTheta n ε S) *
      (Real.log (C * MΛ) + ((n : ℝ) + 1) * Real.log 2 + Real.log (((n : ℝ) + 1) * MΛ + 1)
        + Real.log ((n : ℝ) * (mrB n ε S : ℝ) + 1)) / (ε * (m : ℝ))
      ≤ mrA n ε S θ MΛ C m := Finset.le_max' _ _ mem_mrAlist_8

lemma le_mrA_9 {n : ℕ} {ε S θ MΛ C : ℝ} {m : ℕ} :
    4 * (1 + mrTheta n ε S) * ((n : ℝ) + 1) ≤ mrA n ε S θ MΛ C m :=
  Finset.le_max' _ _ mem_mrAlist_9

end Submission.Subspace
