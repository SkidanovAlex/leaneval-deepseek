import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Asm.Params
import Submission.Work.Deep.GKO.OneFact.N5.Asm.arithOK_of_bounds

/-!
# The numeric threshold of the elementary one-factorization route (N5)

`ArithOK α n r ε β` collects the numerical side conditions of the N5 assembly at a fixed `n`, `r`
(see `Submission/Work/Deep/GKO/OneFact/N5/Asm/Params.lean`).  This module proves that for
`β = p - ε` they hold for *all* `r` with `α n ≤ r ≤ n`, once `n` is large enough: every condition
only involves the `o(n)` quantities `n^{2/3}` (the error of the balanced cut), the `o(n)`
parameters `mpar`, `Lpar`, `spar`, `bpar` and the linear quantities `r`, `ε n`.

The proof has three parts.

* The constant slack: with `β = p - ε`, `ε ≤ p/2`, `ε ≤ 1/2`, `ε ≤ α/16` one has
  `ηpar β ε = (βε/64)² ≤ βε/8`, `ηpar β ε ≤ α/8` and `ηpar β ε + 8√(ηpar β ε) ≤ α/4`.
* The asymptotic facts: for every `C > 0` and `a < 1` one has `C n^a ≤ n` for all large `n`
  (from `x^a ≤ x^1/C` eventually for real `x`, i.e. `x^{a-1} → 0` since `a - 1 < 0`).
* The pointwise core `arithOK_of_bounds`, which gives `ArithOK` once these bounds are available.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Deep.GKO.OneFact.N5.Asm

noncomputable section

open scoped BigOperators
open Filter

/-! ## Elementary asymptotic helpers -/

/-- For `C > 0` and exponents `a < b`, eventually `x ^ a ≤ x ^ b / C`. -/
theorem eventually_rpow_le_div (C : ℝ) (hC : 0 < C) {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in Filter.atTop, x ^ a ≤ x ^ b / C := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually (Filter.eventually_ge_atTop C)]
    with x h1 h2
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one h1
  have h0 : 0 ≤ x ^ a := Real.rpow_nonneg hx.le a
  have h2' : 1 ≤ x ^ (b - a) / C := by rw [le_div_iff₀ hC, one_mul]; exact h2
  calc x ^ a = x ^ a * 1 := (mul_one _).symm
    _ ≤ x ^ a * (x ^ (b - a) / C) := mul_le_mul_of_nonneg_left h2' h0
    _ = x ^ b / C := by rw [← mul_div_assoc, ← Real.rpow_add hx, add_sub_cancel]

/-- For `C > 0` and `a < 1`, eventually `C * n ^ a ≤ n` for natural `n`. -/
theorem eventually_const_mul_rpow_le_nat (C : ℝ) (hC : 0 < C) {a : ℝ} (ha : a < 1) :
    ∀ᶠ n : ℕ in Filter.atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) := by
  have h : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ a ≤ (n : ℝ) ^ (1 : ℝ) / C :=
    tendsto_natCast_atTop_atTop.eventually (eventually_rpow_le_div C hC ha)
  filter_upwards [h] with n hn
  rw [Real.rpow_one] at hn
  have h' : C * (n : ℝ) ^ a ≤ C * ((n : ℝ) / C) := mul_le_mul_of_nonneg_left hn (le_of_lt hC)
  have hdiv : C * ((n : ℝ) / C) = (n : ℝ) := by field_simp
  rwa [hdiv] at h'

/-- For `δ > 0`, eventually `c ≤ δ * n` for natural `n`. -/
theorem eventually_const_le_mul_nat (c δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, c ≤ δ * (n : ℝ) := by
  have h : ∀ᶠ n : ℕ in Filter.atTop, c / δ ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop (c / δ))
  filter_upwards [h] with n hn
  have h' : δ * (c / δ) ≤ δ * (n : ℝ) := mul_le_mul_of_nonneg_left hn (le_of_lt hδ)
  have hdiv : δ * (c / δ) = c := by field_simp
  rwa [hdiv] at h'

/-- For `A ≥ 0`, `δ > 0` and `a < 1`, eventually `A * n ^ a ≤ δ * n`. -/
theorem eventually_mul_rpow_le_mul (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) {a : ℝ} (ha : a < 1) :
    ∀ᶠ n : ℕ in Filter.atTop, A * (n : ℝ) ^ a ≤ δ * (n : ℝ) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · filter_upwards with n
    rw [← hA0, zero_mul]
    exact mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg n)
  · have h := eventually_const_mul_rpow_le_nat (2 * A / δ) (by positivity) ha
    filter_upwards [h] with n hn
    have h' : δ / 2 * ((2 * A / δ) * (n : ℝ) ^ a) ≤ δ / 2 * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    have hunfold : δ / 2 * ((2 * A / δ) * (n : ℝ) ^ a) = A * (n : ℝ) ^ a := by
      field_simp
    calc A * (n : ℝ) ^ a = δ / 2 * ((2 * A / δ) * (n : ℝ) ^ a) := hunfold.symm
      _ ≤ δ / 2 * (n : ℝ) := h'
      _ ≤ δ * (n : ℝ) := by
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          exact mul_le_mul_of_nonneg_right (by linarith : δ / 2 ≤ δ) hn0

/-! ## The threshold statement -/

theorem threshold_arith (α p : ℝ) (hα : 0 < α) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∀ ε β : ℝ, 0 < ε → ε ≤ 1 / 2 → ε ≤ p / 2 → ε ≤ α / 16 → β = p - ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℕ, α * (n : ℝ) ≤ (r : ℝ) → r ≤ n →
        Work.Deep.GKO.OneFact.N5.Asm.ArithOK α n r ε β := by
  intro ε β hε hε2 hεp hεα hβeq
  -- ## Basic numeric facts about `β = p - ε`
  have hβpos : 0 < β := by rw [hβeq]; linarith [hp, hεp]
  have hβle1 : β ≤ 1 := by rw [hβeq]; linarith
  have hβε : 0 < β * ε := mul_pos hβpos hε
  have hβε1 : β * ε ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hβle1 (le_of_lt hε)
    linarith [h, hε2]
  have hβεα : β * ε ≤ α / 16 := by
    have h := mul_le_mul_of_nonneg_right hβle1 (le_of_lt hε)
    linarith [h, hεα]
  have hηpos : 0 < ηpar β ε := by rw [ηpar]; exact pow_pos (by positivity) 2
  -- ## The three constant bounds on `ηpar β ε = (βε/64)²`
  have hβ8 : ηpar β ε ≤ β * ε / 8 := by
    have ht0 : 0 ≤ β * ε := le_of_lt hβε
    have h1 : (β * ε) * (β * ε) ≤ (β * ε) * (1 / 2) := mul_le_mul_of_nonneg_left hβε1 ht0
    rw [ηpar]
    nlinarith [h1]
  have hηs : ηpar β ε ≤ α / 8 := by
    have ht0 : 0 ≤ β * ε := le_of_lt hβε
    have h1 : (β * ε) * (β * ε) ≤ (β * ε) * (1 / 2) := mul_le_mul_of_nonneg_left hβε1 ht0
    rw [ηpar]
    nlinarith [h1, hβεα]
  have hηα : ηpar β ε + 8 * Real.sqrt (ηpar β ε) ≤ α / 4 := by
    have hsqrt : Real.sqrt (ηpar β ε) = β * ε / 64 := by
      rw [ηpar]; exact Real.sqrt_sq (by positivity)
    have h2 : β * ε / 8 ≤ α / 128 := by linarith [hβεα]
    rw [hsqrt]
    linarith [hηs, h2]
  -- ## The asymptotic side conditions
  have hP1ev : ∀ᶠ n : ℕ in Filter.atTop,
      5 * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ β * ε * (n : ℝ) / 8 := by
    have h := eventually_mul_rpow_le_mul 5 (β * ε / 8) (by norm_num) (by positivity)
      (show (2 : ℝ) / 3 < 1 by norm_num)
    filter_upwards [h] with n hn
    calc 5 * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ (β * ε / 8) * (n : ℝ) := hn
      _ = β * ε * (n : ℝ) / 8 := by ring
  have hP2ev : ∀ᶠ n : ℕ in Filter.atTop,
      (150 / ηpar β ε + 7) * (n : ℝ) ^ ((2 : ℝ) / 3) + 2 ≤ 21 * α / 256 * (n : ℝ) := by
    have hA : (0 : ℝ) ≤ 150 / ηpar β ε + 7 := by
      have := div_nonneg (by norm_num : (0 : ℝ) ≤ 150) (le_of_lt hηpos)
      linarith
    have h1 := eventually_mul_rpow_le_mul (150 / ηpar β ε + 7) (21 * α / 512) hA
      (by positivity) (show (2 : ℝ) / 3 < 1 by norm_num)
    have h2 := eventually_const_le_mul_nat 2 (21 * α / 512) (by positivity)
    filter_upwards [h1, h2] with n hn1 hn2
    have hsum : (21 * α / 512) * (n : ℝ) + (21 * α / 512) * (n : ℝ)
        = 21 * α / 256 * (n : ℝ) := by ring
    linarith [hn1, hn2, hsum]
  have hP3ev : ∀ᶠ n : ℕ in Filter.atTop,
      4 * (n : ℝ) ^ ((2 : ℝ) / 3) + 2 ≤ α * (n : ℝ) := by
    have h1 := eventually_mul_rpow_le_mul 4 (α / 2) (by norm_num) (by positivity)
      (show (2 : ℝ) / 3 < 1 by norm_num)
    have h2 := eventually_const_le_mul_nat 2 (α / 2) (by positivity)
    filter_upwards [h1, h2] with n hn1 hn2
    have hsum : (α / 2) * (n : ℝ) + (α / 2) * (n : ℝ) = α * (n : ℝ) := by ring
    linarith [hn1, hn2, hsum]
  have hP4ev : ∀ᶠ n : ℕ in Filter.atTop,
      8 * Real.sqrt (320 / α) * (n : ℝ) ^ ((5 : ℝ) / 6) + 7 * (n : ℝ) ^ ((2 : ℝ) / 3)
        + 25 ≤ α / 8 * (n : ℝ) := by
    have h1 := eventually_mul_rpow_le_mul (8 * Real.sqrt (320 / α)) (α / 32) (by positivity)
      (by positivity) (show (5 : ℝ) / 6 < 1 by norm_num)
    have h2 := eventually_mul_rpow_le_mul 7 (α / 32) (by norm_num) (by positivity)
      (show (2 : ℝ) / 3 < 1 by norm_num)
    have h3 := eventually_const_le_mul_nat 25 (α / 32) (by positivity)
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
    have hαn : (0 : ℝ) ≤ α * (n : ℝ) := mul_nonneg (le_of_lt hα) (Nat.cast_nonneg n)
    have hsum : (α / 32) * (n : ℝ) + (α / 32) * (n : ℝ) + (α / 32) * (n : ℝ)
        = 3 * (α * (n : ℝ)) / 32 := by ring
    nlinarith [hn1, hn2, hn3, hαn, hsum]
  have hP5ev : ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt (320 / α) * (n : ℝ) ^ ((5 : ℝ) / 6) + 3
        ≤ 31 * (β * ε) / 128 * (n : ℝ) := by
    have h1 := eventually_mul_rpow_le_mul (Real.sqrt (320 / α)) (31 * (β * ε) / 256)
      (by positivity) (by positivity) (show (5 : ℝ) / 6 < 1 by norm_num)
    have h2 := eventually_const_le_mul_nat 3 (31 * (β * ε) / 256) (by positivity)
    filter_upwards [h1, h2] with n hn1 hn2
    have hsum : (31 * (β * ε) / 256) * (n : ℝ) + (31 * (β * ε) / 256) * (n : ℝ)
        = 31 * (β * ε) / 128 * (n : ℝ) := by ring
    linarith [hn1, hn2, hsum]
  have hP6ev : ∀ᶠ n : ℕ in Filter.atTop,
      7 * (n : ℝ) ^ ((2 : ℝ) / 3) + 1 ≤ α / 16 * (n : ℝ) := by
    have h1 := eventually_mul_rpow_le_mul 7 (α / 32) (by norm_num) (by positivity)
      (show (2 : ℝ) / 3 < 1 by norm_num)
    have h2 := eventually_const_le_mul_nat 1 (α / 32) (by positivity)
    filter_upwards [h1, h2] with n hn1 hn2
    have hsum : (α / 32) * (n : ℝ) + (α / 32) * (n : ℝ) = α / 16 * (n : ℝ) := by ring
    linarith [hn1, hn2, hsum]
  have hLev : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ ηpar β ε * (n : ℝ) :=
    eventually_const_le_mul_nat 2 (ηpar β ε) hηpos
  -- ## Assembly
  have hmain : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ r : ℕ, α * (n : ℝ) ≤ (r : ℝ) → r ≤ n → ArithOK α n r ε β := by
    filter_upwards [hP1ev, hP2ev, hP3ev, hP4ev, hP5ev, hP6ev, hLev,
      Filter.eventually_ge_atTop (1 : ℕ)] with n hP1 hP2 hP3 hP4 hP5 hP6 hL2 hn1
    intro r hrα _
    have hLfloor : ηpar β ε * (n : ℝ) - 1 < ((Lpar β ε n : ℕ) : ℝ) := by
      have := Nat.sub_one_lt_floor (ηpar β ε * (n : ℝ))
      simpa [Lpar] using this
    have hLlo : ηpar β ε * (n : ℝ) / 2 ≤ ((Lpar β ε n : ℕ) : ℝ) := by linarith
    have hL1 : 1 ≤ Lpar β ε n := by
      have h : (1 : ℝ) ≤ ((Lpar β ε n : ℕ) : ℝ) := by linarith
      exact_mod_cast h
    exact arithOK_of_bounds hα hβε hβ8 hηα hηs hεα hn1 hL1 hLlo hP1 hP2 hP3 hP4 hP5 hP6 hrα
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hmain
  exact ⟨N, hN⟩

end

end Work.Deep.GKO.OneFact.N5.Asm
