/-
# Continued-fraction data for a Diophantine number: the bridge `cf_data_bridge`

For irrational `α` with `DiophBelow α b₀` and `ε > 0` we produce denominator-like numbers
`q : ℕ → ℕ` and errors `Δ : ℕ → ℝ` (`Δ m = fracDist (q m · α)`) with the full continued-fraction
package used in AJ §9:

* `0 < q m`, `q` strictly increasing;
* `1/(q (m+1) + q m) < Δ m < 1/q (m+1)`;
* (`best approximation`) `Δ m ≤ fracDist (k α)` for `q m ≤ k < q (m+1)`;
* (`linear growth of multiples`) `j Δ m ≤ fracDist (j q m · α)` for `2 j q m ≤ q (m+1)`;
* (`Diophantine saving`) `q (m+1) ≤ exp ((b₀+ε) q m)` eventually.

The construction takes `q m := Q_{m+2}` where `Q_n` are the denominators of the continued
fraction convergents of `Int.fract α ∈ (0,1)`, and `Δ m = fracDist (q m · fract α)`, so that the
classical identities (`Q_{n+1} β - P_{n+1} = (-1)^{n+1}/(Q_{n+1} x_{n+1}⁻¹ + Q_n)` and the
determinant identity `Q_n P_{n+1} - P_n Q_{n+1} = (-1)^n`) apply verbatim.
-/
import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.CFDefs
import Submission.Work.TMC16Core.CF.cf_saving

noncomputable section

namespace Work.TMC16Core.CF

open Work.TMC16Core.Basic

/-! ## 1. Elementary facts about `fracDist` and `round` -/

theorem fracDist_nonneg' (x : ℝ) : 0 ≤ fracDist x := abs_nonneg (x - round x)

theorem fracDist_le_half' (x : ℝ) : fracDist x ≤ 1 / 2 := by
  simpa only [fracDist] using abs_sub_round x

theorem round_eq_of_abs_sub_lt_half {x : ℝ} {m : ℤ} (h : |x - (m : ℝ)| < 1 / 2) :
    round x = m := by
  have h' : -(1 / 2) < x - (m : ℝ) ∧ x - (m : ℝ) < 1 / 2 := abs_lt.mp h
  rw [round_eq_iff, Set.mem_Ico]
  constructor <;> linarith [h'.1, h'.2]

theorem fracDist_eq_of_abs_sub_lt_half {x : ℝ} {m : ℤ} (h : |x - (m : ℝ)| < 1 / 2) :
    fracDist x = |x - (m : ℝ)| := by
  rw [fracDist, round_eq_of_abs_sub_lt_half h]

theorem fracDist_add_intCast (x : ℝ) (m : ℤ) : fracDist (x + (m : ℝ)) = fracDist x := by
  rw [fracDist, fracDist, round_add_intCast, Int.cast_add]
  congr 1
  ring

/-- `fracDist` only depends on `α` through its fractional part. -/
theorem fracDist_mul_natCast_fract (α : ℝ) (k : ℕ) :
    fracDist ((k : ℝ) * α) = fracDist ((k : ℝ) * Int.fract α) := by
  have hf : (⌊α⌋ : ℝ) + Int.fract α = α := Int.floor_add_fract α
  have h : (k : ℝ) * α = (k : ℝ) * Int.fract α + ((k : ℤ) * ⌊α⌋ : ℤ) := by
    calc (k : ℝ) * α = (k : ℝ) * ((⌊α⌋ : ℝ) + Int.fract α) := by rw [hf]
      _ = (k : ℝ) * Int.fract α + (k : ℝ) * (⌊α⌋ : ℝ) := by ring
      _ = (k : ℝ) * Int.fract α + ((k : ℤ) * ⌊α⌋ : ℤ) := by push_cast; ring
  rw [h, fracDist_add_intCast]

/-- If `j · |x - p| < 1/2` then `fracDist` of `j x` is exactly `j |x - p|`. -/
theorem fracDist_mul_natCast_of_abs_sub_lt_half {x : ℝ} {p : ℤ} {j : ℕ}
    (h : (j : ℝ) * |x - (p : ℝ)| < 1 / 2) :
    fracDist ((j : ℝ) * x) = (j : ℝ) * |x - (p : ℝ)| := by
  have hkey : (j : ℝ) * x - ((j * p : ℤ) : ℝ) = (j : ℝ) * (x - (p : ℝ)) := by
    push_cast; ring
  have habs : |(j : ℝ) * x - ((j * p : ℤ) : ℝ)| = (j : ℝ) * |x - (p : ℝ)| := by
    rw [hkey, abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
  rw [fracDist, round_eq_of_abs_sub_lt_half (by rw [habs]; exact h), habs]

/-! ## 2. The continued fraction of `β ∈ (0,1)` -/

variable {β : ℝ}

/-- For irrational `β ∈ (0,1)` every tail `cfX β n` lies in `(0,1)` and is irrational. -/
theorem cfX_mem (h0 : 0 < β) (h1 : β < 1) (hi : Irrational β) :
    ∀ n, 0 < cfX β n ∧ cfX β n < 1 ∧ Irrational (cfX β n) := by
  intro n
  induction n with
  | zero => exact ⟨h0, h1, hi⟩
  | succ n ih =>
    obtain ⟨hpos, hlt, hirr⟩ := ih
    have hy : Irrational ((cfX β n)⁻¹) := hirr.inv
    refine ⟨?_, ?_, ?_⟩
    · rw [cfX_succ, Int.fract_pos]
      exact hy.ne_int ⌊(cfX β n)⁻¹⌋
    · rw [cfX_succ]
      exact Int.fract_lt_one _
    · rw [cfX_succ, ← Int.self_sub_floor ((cfX β n)⁻¹)]
      exact hy.sub_intCast ⌊(cfX β n)⁻¹⌋

/-- The tail relation `1/xₙ = aₙ + xₙ₊₁`. -/
theorem cfA_spec (n : ℕ) : (cfA β n : ℝ) + cfX β (n + 1) = (cfX β n)⁻¹ := by
  rw [cfA_apply, cfX_succ]
  exact Int.floor_add_fract _

theorem cfA_pos (hx : ∀ n, 0 < cfX β n ∧ cfX β n < 1) (n : ℕ) : 1 ≤ cfA β n := by
  rw [cfA_apply]
  have hp : (0 : ℝ) < cfX β n := (hx n).1
  have hl : cfX β n < 1 := (hx n).2
  have h1' : (1 : ℝ) ≤ (cfX β n)⁻¹ := (one_le_inv₀ hp).mpr hl.le
  have h1 : ((1 : ℤ) : ℝ) ≤ (cfX β n)⁻¹ := by simpa using h1'
  exact Int.le_floor.mpr h1

theorem cfQ_pos (ha : ∀ n, 1 ≤ cfA β n) : ∀ n, 1 ≤ cfQ β n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => rw [cfQ_one]; exact ha 0
  | more n ihn ihn1 =>
    rw [cfQ_add_two]
    have h1 : 1 ≤ cfA β (n + 1) := ha _
    have h2 : 1 ≤ cfQ β (n + 1) := ihn1
    have h3 : 1 ≤ cfQ β n := ihn
    have h4 : (1 : ℤ) ≤ cfA β (n + 1) * cfQ β (n + 1) := by
      calc (1 : ℤ) = 1 * 1 := by ring
        _ ≤ cfA β (n + 1) * cfQ β (n + 1) := mul_le_mul h1 h2 (by norm_num) (by linarith)
    linarith

theorem cfQ_lt_succ (ha : ∀ n, 1 ≤ cfA β n) (hQ : ∀ n, 1 ≤ cfQ β n) :
    ∀ n, 1 ≤ n → cfQ β n < cfQ β (n + 1) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [cfQ_add_two]
  have h1 : 1 ≤ cfA β (m + 1) := ha _
  have h2 : 1 ≤ cfQ β (m + 1) := hQ _
  have h3 : 1 ≤ cfQ β m := hQ _
  have h4 : 1 * cfQ β (m + 1) ≤ cfA β (m + 1) * cfQ β (m + 1) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  linarith

/-- The determinant identity for the convergents of `β`. -/
theorem cfP_det (β : ℝ) : ∀ n, cfQ β n * cfP β (n + 1) - cfP β n * cfQ β (n + 1) = (-1 : ℤ) ^ n := by
  intro n
  induction n with
  | zero => rw [cfQ_zero, cfP_zero, cfP_one]; ring
  | succ n ih =>
    have hrec : cfQ β (n + 1) * cfP β (n + 2) - cfP β (n + 1) * cfQ β (n + 2)
        = -(cfQ β n * cfP β (n + 1) - cfP β n * cfQ β (n + 1)) := by
      rw [cfQ_add_two β n, cfP_add_two β n]
      ring
    rw [hrec, ih, pow_succ]
    ring


/-! ## 3. Continued fractions: the two structural estimates

These are proved here (rather than imported) so that the final theorem depends only on
`CFDefs` and Mathlib.
-/

/-- **Best approximation of the second kind** (fallback version). -/
theorem cf_best_approx {β : ℝ} {Q P : ℕ → ℤ} (hQpos : ∀ n, 1 ≤ Q n)
    (hdet : ∀ n, Q n * P (n + 1) - P n * Q (n + 1) = (-1) ^ n)
    {δ : ℕ → ℝ} (hδpos : ∀ n, 0 < δ n)
    (herr : ∀ n, (Q n : ℝ) * β - (P n : ℝ) = (-1) ^ n * δ n)
    (n : ℕ) {k ℓ : ℤ} (hk : 0 < k) (hkq : k < Q (n + 1)) :
    δ n ≤ |k * β - (ℓ : ℝ)| := by
  have hQn : (1 : ℤ) ≤ Q n := hQpos n
  have hQn1 : (1 : ℤ) ≤ Q (n + 1) := hQpos (n + 1)
  have hDsq : (Q n * P (n + 1) - P n * Q (n + 1)) * (Q n * P (n + 1) - P n * Q (n + 1)) = 1 := by
    rw [hdet n]
    rcases Nat.even_or_odd n with h | h
    · rw [h.neg_one_pow]; norm_num
    · rw [h.neg_one_pow]; norm_num
  obtain ⟨a, b, hak, haℓ⟩ :
      ∃ a b : ℤ, k = a * Q n + b * Q (n + 1) ∧ ℓ = a * P n + b * P (n + 1) := by
    refine ⟨(Q n * P (n + 1) - P n * Q (n + 1)) * (k * P (n + 1) - ℓ * Q (n + 1)),
      (Q n * P (n + 1) - P n * Q (n + 1)) * (ℓ * Q n - k * P n), ?_, ?_⟩
    · calc k = k * ((Q n * P (n + 1) - P n * Q (n + 1)) * (Q n * P (n + 1) - P n * Q (n + 1))) := by
            rw [hDsq]; ring
        _ = (Q n * P (n + 1) - P n * Q (n + 1)) * (k * P (n + 1) - ℓ * Q (n + 1)) * Q n
              + (Q n * P (n + 1) - P n * Q (n + 1)) * (ℓ * Q n - k * P n) * Q (n + 1) := by ring
    · calc ℓ = ℓ * ((Q n * P (n + 1) - P n * Q (n + 1)) * (Q n * P (n + 1) - P n * Q (n + 1))) := by
            rw [hDsq]; ring
        _ = (Q n * P (n + 1) - P n * Q (n + 1)) * (k * P (n + 1) - ℓ * Q (n + 1)) * P n
              + (Q n * P (n + 1) - P n * Q (n + 1)) * (ℓ * Q n - k * P n) * P (n + 1) := by ring
  have hval : (k : ℝ) * β - (ℓ : ℝ)
      = (-1 : ℝ) ^ n * ((a : ℝ) * δ n - (b : ℝ) * δ (n + 1)) := by
    have hsplit : (k : ℝ) * β - (ℓ : ℝ)
        = (a : ℝ) * ((Q n : ℝ) * β - (P n : ℝ))
          + (b : ℝ) * ((Q (n + 1) : ℝ) * β - (P (n + 1) : ℝ)) := by
      rw [hak, haℓ]; push_cast; ring
    rw [hsplit, herr n, herr (n + 1)]
    have hsign : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by rw [pow_succ]; ring
    rw [hsign]; ring
  have habs : |(k : ℝ) * β - (ℓ : ℝ)| = |(a : ℝ) * δ n - (b : ℝ) * δ (n + 1)| := by
    rw [hval, abs_mul, abs_neg_one_pow, one_mul]
  rw [habs]
  have hcase : (1 ≤ a ∧ b ≤ 0) ∨ (a ≤ -1 ∧ 1 ≤ b) := by
    by_cases ha : 1 ≤ a
    · refine Or.inl ⟨ha, ?_⟩
      by_contra hb
      have hb1 : 1 ≤ b := by omega
      have h4 : (1 : ℤ) * Q n + 1 * Q (n + 1) ≤ a * Q n + b * Q (n + 1) :=
        add_le_add (mul_le_mul_of_nonneg_right ha (by omega))
          (mul_le_mul_of_nonneg_right hb1 (by omega))
      rw [hak] at hkq
      linarith
    · have ha0 : a ≤ 0 := by omega
      have ha' : a ≤ -1 := by
        rcases lt_or_eq_of_le ha0 with h | h
        · omega
        · exfalso
          subst h
          simp only [zero_mul, zero_add] at hak
          have hb1 : 1 ≤ b := by
            by_contra hb
            have hb0 : b ≤ 0 := by omega
            have h4 : b * Q (n + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb0 (by omega)
            rw [hak] at hk
            linarith
          have h4 : (1 : ℤ) * Q (n + 1) ≤ b * Q (n + 1) :=
            mul_le_mul_of_nonneg_right hb1 (by omega)
          rw [hak] at hkq
          linarith
      refine Or.inr ⟨ha', ?_⟩
      by_contra hb
      have hb0 : b ≤ 0 := by omega
      have h4 : a * Q n + b * Q (n + 1) ≤ 0 :=
        add_nonpos (mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega))
          (mul_nonpos_of_nonpos_of_nonneg hb0 (by omega))
      rw [hak] at hk
      linarith
  rcases hcase with ⟨ha1, hb0⟩ | ⟨ha1, hb1⟩
  · have hA : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have hB : (b : ℝ) ≤ 0 := by exact_mod_cast hb0
    have hnn : 0 ≤ (a : ℝ) * δ n + (-(b : ℝ)) * δ (n + 1) :=
      add_nonneg (mul_nonneg (by linarith) (le_of_lt (hδpos n)))
        (mul_nonneg (by linarith) (le_of_lt (hδpos (n + 1))))
    have heq : (a : ℝ) * δ n - (b : ℝ) * δ (n + 1)
        = (a : ℝ) * δ n + (-(b : ℝ)) * δ (n + 1) := by ring
    rw [heq, abs_of_nonneg hnn]
    nlinarith [hδpos n, hδpos (n + 1), hA, hB]
  · have hA : (a : ℝ) ≤ -1 := by exact_mod_cast ha1
    have hB : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    have hnn : 0 ≤ (-(a : ℝ)) * δ n + (b : ℝ) * δ (n + 1) :=
      add_nonneg (mul_nonneg (by linarith) (le_of_lt (hδpos n)))
        (mul_nonneg (by linarith) (le_of_lt (hδpos (n + 1))))
    have heq : (a : ℝ) * δ n - (b : ℝ) * δ (n + 1)
        = -((-(a : ℝ)) * δ n + (b : ℝ) * δ (n + 1)) := by ring
    rw [heq, abs_neg, abs_of_nonneg hnn]
    nlinarith [hδpos n, hδpos (n + 1), hA, hB]

/-- The linear-fractional identity for the convergents of `β ∈ (0,1)` irrational,
in cleared form: `1/β = (Q_{n+1} + Q_n x_{n+1})/(P_{n+1} + P_n x_{n+1})`. -/
theorem cf_tail_lf {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β) :
    ∀ n, β⁻¹ * ((cfP β (n + 1) : ℝ) + (cfP β n : ℝ) * cfX β (n + 1))
      = (cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) * cfX β (n + 1) := by
  have hX : ∀ n, cfX β n ≠ 0 := fun n => ne_of_gt (cfX_mem hβ0 hβ1 hi n).1
  have hβ : β ≠ 0 := ne_of_gt hβ0
  intro n
  induction n with
  | zero =>
    have h0 := cfA_spec (β := β) 0
    rw [cfX_zero] at h0
    change β⁻¹ * ((cfP β 1 : ℝ) + (cfP β 0 : ℝ) * cfX β 1)
      = (cfQ β 1 : ℝ) + (cfQ β 0 : ℝ) * cfX β 1
    simp only [cfP_zero, cfP_one, cfQ_zero, cfQ_one, zero_mul, add_zero, mul_one]
    linarith [h0]
  | succ n ih =>
    have hA := cfA_spec (β := β) (n + 1)
    have hx0 : cfX β (n + 1) ≠ 0 := hX (n + 1)
    have hP : (cfP β (n + 2) : ℝ)
        = (cfA β (n + 1) : ℝ) * (cfP β (n + 1) : ℝ) + (cfP β n : ℝ) := by
      rw [cfP_add_two]; push_cast; ring
    have hQ : (cfQ β (n + 2) : ℝ)
        = (cfA β (n + 1) : ℝ) * (cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) := by
      rw [cfQ_add_two]; push_cast; ring
    have hsub : cfX β (n + 2) = (cfX β (n + 1))⁻¹ - (cfA β (n + 1) : ℝ) := by linarith [hA]
    have hG' : β⁻¹ * ((cfP β n : ℝ) + (cfP β (n + 1) : ℝ) * (cfX β (n + 1))⁻¹)
        = (cfQ β n : ℝ) + (cfQ β (n + 1) : ℝ) * (cfX β (n + 1))⁻¹ := by
      have hih := ih
      field_simp [hβ, hx0] at hih ⊢
      linarith [hih]
    have eq1 : (cfA β (n + 1) : ℝ) * (cfP β (n + 1) : ℝ) + (cfP β n : ℝ)
        + (cfP β (n + 1) : ℝ) * ((cfX β (n + 1))⁻¹ - (cfA β (n + 1) : ℝ))
        = (cfP β n : ℝ) + (cfP β (n + 1) : ℝ) * (cfX β (n + 1))⁻¹ := by ring
    have eq2 : (cfA β (n + 1) : ℝ) * (cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ)
        + (cfQ β (n + 1) : ℝ) * ((cfX β (n + 1))⁻¹ - (cfA β (n + 1) : ℝ))
        = (cfQ β n : ℝ) + (cfQ β (n + 1) : ℝ) * (cfX β (n + 1))⁻¹ := by ring
    rw [hP, hQ, hsub, eq1, eq2]
    exact hG'

/-- The error identity for the convergents of `β ∈ (0,1)` irrational. -/
theorem cf_error_identity {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β) (m : ℕ) :
    (cfQ β (m + 1) : ℝ) * β - (cfP β (m + 1) : ℝ)
      = (-1) ^ (m + 1) / ((cfQ β (m + 1) : ℝ) * (cfX β (m + 1))⁻¹ + (cfQ β m : ℝ)) := by
  have hX : ∀ n, cfX β n ≠ 0 := fun n => ne_of_gt (cfX_mem hβ0 hβ1 hi n).1
  have hβ : β ≠ 0 := ne_of_gt hβ0
  have hx0 : cfX β (m + 1) ≠ 0 := hX (m + 1)
  have hlf := cf_tail_lf hβ0 hβ1 hi m
  have hPβ : (cfP β (m + 1) : ℝ) + (cfP β m : ℝ) * cfX β (m + 1)
      = β * ((cfQ β (m + 1) : ℝ) + (cfQ β m : ℝ) * cfX β (m + 1)) := by
    have h := congrArg (fun t : ℝ => β * t) hlf
    field_simp [hβ] at h ⊢
    linarith [h]
  have hdetR : (cfQ β m : ℝ) * (cfP β (m + 1) : ℝ) - (cfP β m : ℝ) * (cfQ β (m + 1) : ℝ)
      = (-1 : ℝ) ^ m := by
    have h := cfP_det β m
    exact_mod_cast h
  have h1 : (cfQ β (m + 1) : ℝ) * (cfP β m : ℝ) - (cfP β (m + 1) : ℝ) * (cfQ β m : ℝ)
      = (-1 : ℝ) ^ (m + 1) := by
    have h := hdetR
    rw [pow_succ]
    linear_combination -h
  have hkey : ((cfQ β (m + 1) : ℝ) * β - (cfP β (m + 1) : ℝ))
      * ((cfQ β (m + 1) : ℝ) + (cfQ β m : ℝ) * cfX β (m + 1))
      = (-1 : ℝ) ^ (m + 1) * cfX β (m + 1) := by
    calc ((cfQ β (m + 1) : ℝ) * β - (cfP β (m + 1) : ℝ))
          * ((cfQ β (m + 1) : ℝ) + (cfQ β m : ℝ) * cfX β (m + 1))
        = (cfQ β (m + 1) : ℝ)
            * (β * ((cfQ β (m + 1) : ℝ) + (cfQ β m : ℝ) * cfX β (m + 1)))
          - (cfP β (m + 1) : ℝ)
            * ((cfQ β (m + 1) : ℝ) + (cfQ β m : ℝ) * cfX β (m + 1)) := by ring
      _ = (cfQ β (m + 1) : ℝ)
            * ((cfP β (m + 1) : ℝ) + (cfP β m : ℝ) * cfX β (m + 1))
          - (cfP β (m + 1) : ℝ)
            * ((cfQ β (m + 1) : ℝ) + (cfQ β m : ℝ) * cfX β (m + 1)) := by rw [hPβ]
      _ = cfX β (m + 1) * ((cfQ β (m + 1) : ℝ) * (cfP β m : ℝ)
            - (cfP β (m + 1) : ℝ) * (cfQ β m : ℝ)) := by ring
      _ = (-1 : ℝ) ^ (m + 1) * cfX β (m + 1) := by rw [h1]; ring
  have hden : ((cfQ β (m + 1) : ℝ) * (cfX β (m + 1))⁻¹ + (cfQ β m : ℝ)) ≠ 0 := by
    have h1 : (0 : ℝ) < (cfQ β (m + 1) : ℝ) := by
      have h := cfQ_pos (fun n => cfA_pos (fun k => ⟨(cfX_mem hβ0 hβ1 hi k).1, (cfX_mem hβ0 hβ1 hi k).2.1⟩) n) (m + 1)
      exact_mod_cast (lt_of_lt_of_le zero_lt_one h)
    have h2 : (0 : ℝ) < (cfX β (m + 1))⁻¹ := inv_pos.mpr (cfX_mem hβ0 hβ1 hi (m + 1)).1
    have h3 : (0 : ℝ) < (cfQ β m : ℝ) := by
      have h := cfQ_pos (fun n => cfA_pos (fun k => ⟨(cfX_mem hβ0 hβ1 hi k).1, (cfX_mem hβ0 hβ1 hi k).2.1⟩) n) m
      exact_mod_cast (lt_of_lt_of_le zero_lt_one h)
    exact ne_of_gt (add_pos (mul_pos h1 h2) h3)
  rw [eq_div_iff hden]
  have hfold : (cfQ β (m + 1) : ℝ) + (cfQ β m : ℝ) * cfX β (m + 1)
      = cfX β (m + 1) * ((cfQ β (m + 1) : ℝ) * (cfX β (m + 1))⁻¹ + (cfQ β m : ℝ)) := by
    field_simp
  have hkey2 : cfX β (m + 1)
      * (((cfQ β (m + 1) : ℝ) * β - (cfP β (m + 1) : ℝ))
        * ((cfQ β (m + 1) : ℝ) * (cfX β (m + 1))⁻¹ + (cfQ β m : ℝ)))
      = cfX β (m + 1) * (-1 : ℝ) ^ (m + 1) := by
    calc cfX β (m + 1) * (((cfQ β (m + 1) : ℝ) * β - (cfP β (m + 1) : ℝ))
          * ((cfQ β (m + 1) : ℝ) * (cfX β (m + 1))⁻¹ + (cfQ β m : ℝ)))
        = ((cfQ β (m + 1) : ℝ) * β - (cfP β (m + 1) : ℝ))
          * (cfX β (m + 1) * ((cfQ β (m + 1) : ℝ) * (cfX β (m + 1))⁻¹ + (cfQ β m : ℝ))) := by ring
      _ = ((cfQ β (m + 1) : ℝ) * β - (cfP β (m + 1) : ℝ))
          * ((cfQ β (m + 1) : ℝ) + (cfQ β m : ℝ) * cfX β (m + 1)) := by rw [← hfold]
      _ = (-1 : ℝ) ^ (m + 1) * cfX β (m + 1) := hkey
      _ = cfX β (m + 1) * (-1 : ℝ) ^ (m + 1) := by ring
  exact mul_left_cancel₀ hx0 hkey2

/-- The full error package for the convergents of `β ∈ (0,1)` irrational (fallback version). -/
theorem cf_error_package {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β)
    {δ : ℕ → ℝ}
    (hδ : ∀ n, δ n = 1 / ((cfQ β (n + 2) : ℝ) * (cfX β (n + 2))⁻¹
        + (cfQ β (n + 1) : ℝ))) :
    (∀ n, 0 < δ n) ∧
    (∀ n, (cfQ β (n + 2) : ℝ) * β - (cfP β (n + 2) : ℝ) = (-1) ^ n * δ n) ∧
    (∀ n, δ n < 1 / (cfQ β (n + 3) : ℝ)) ∧
    (∀ n, 1 / ((cfQ β (n + 3) : ℝ) + (cfQ β (n + 2) : ℝ)) < δ n) := by
  have hx := cfX_mem hβ0 hβ1 hi
  have hA : ∀ n, 1 ≤ cfA β n := fun n => cfA_pos (fun k => ⟨(hx k).1, (hx k).2.1⟩) n
  have hQ : ∀ n, 1 ≤ cfQ β n := cfQ_pos hA
  have hQr : ∀ n, (0 : ℝ) < (cfQ β n : ℝ) := by
    intro n
    have h := hQ n
    have h' : (1 : ℝ) ≤ (cfQ β n : ℝ) := by exact_mod_cast h
    linarith
  have hXr : ∀ n, (0 : ℝ) < (cfX β n)⁻¹ := fun n => inv_pos.mpr (hx n).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rw [hδ n]
    exact one_div_pos.mpr (add_pos (mul_pos (hQr (n + 2)) (hXr (n + 2))) (hQr (n + 1)))
  · intro n
    have h : (cfQ β (n + 2) : ℝ) * β - (cfP β (n + 2) : ℝ)
        = (-1 : ℝ) ^ (n + 2) / ((cfQ β (n + 2) : ℝ) * (cfX β (n + 2))⁻¹
          + (cfQ β (n + 1) : ℝ)) := by
      have h0 := cf_error_identity hβ0 hβ1 hi (n + 1)
      simpa using h0
    have hsign : (-1 : ℝ) ^ (n + 2) = (-1) ^ n := by rw [pow_add]; norm_num
    rw [hδ n, h, hsign, div_eq_mul_inv, one_div]
  · intro n
    have hA2 := cfA_spec (β := β) (n + 2)
    have hQ3 : (cfQ β (n + 3) : ℝ) = (cfA β (n + 2) : ℝ) * (cfQ β (n + 2) : ℝ)
        + (cfQ β (n + 1) : ℝ) := by
      rw [cfQ_add_two]; push_cast; ring
    have hstrict : (cfA β (n + 2) : ℝ) < (cfX β (n + 2))⁻¹ := by
      have := (hx (n + 3)).1
      linarith [hA2]
    have hW : (cfQ β (n + 3) : ℝ)
        < (cfQ β (n + 2) : ℝ) * (cfX β (n + 2))⁻¹ + (cfQ β (n + 1) : ℝ) := by
      rw [hQ3]
      have h1 : (cfQ β (n + 2) : ℝ) * (cfA β (n + 2) : ℝ)
          < (cfQ β (n + 2) : ℝ) * (cfX β (n + 2))⁻¹ :=
        mul_lt_mul_of_pos_left hstrict (hQr (n + 2))
      linarith
    rw [hδ n]
    exact one_div_lt_one_div_of_lt (hQr (n + 3)) hW
  · intro n
    have hA2 := cfA_spec (β := β) (n + 2)
    have hQ3 : (cfQ β (n + 3) : ℝ) = (cfA β (n + 2) : ℝ) * (cfQ β (n + 2) : ℝ)
        + (cfQ β (n + 1) : ℝ) := by
      rw [cfQ_add_two]; push_cast; ring
    have hlt1 : cfX β (n + 3) < 1 := (hx (n + 3)).2.1
    have hy : (cfX β (n + 2))⁻¹ < (cfA β (n + 2) : ℝ) + 1 := by linarith [hA2]
    have hWlt : (cfQ β (n + 2) : ℝ) * (cfX β (n + 2))⁻¹ + (cfQ β (n + 1) : ℝ)
        < (cfQ β (n + 3) : ℝ) + (cfQ β (n + 2) : ℝ) := by
      rw [hQ3]
      have h1 : (cfQ β (n + 2) : ℝ) * (cfX β (n + 2))⁻¹
          < (cfQ β (n + 2) : ℝ) * ((cfA β (n + 2) : ℝ) + 1) :=
        mul_lt_mul_of_pos_left hy (hQr (n + 2))
      linarith
    have hWpos : (0 : ℝ) < (cfQ β (n + 2) : ℝ) * (cfX β (n + 2))⁻¹ + (cfQ β (n + 1) : ℝ) :=
      add_pos (mul_pos (hQr (n + 2)) (hXr (n + 2))) (hQr (n + 1))
    rw [hδ n]
    exact one_div_lt_one_div_of_lt hWpos hWlt


/-! ## 4. The construction -/

/-- **Continued-fraction data for `β ∈ (0,1)` irrational.** -/
theorem cf_data_bridge_aux {β b₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβi : Irrational β)
    (hb₀ : 0 ≤ b₀) (hDioph : DiophBelow β b₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ → ℕ, ∃ Δ : ℕ → ℝ,
      (∀ m, 0 < q m) ∧ StrictMono q ∧
      (∀ m, 1 ≤ m → q (m - 1) + 1 ≤ q m) ∧
      (∀ m, 0 < Δ m) ∧
      (∀ m, Δ m = fracDist ((q m : ℝ) * β)) ∧
      (∀ m, Δ m < 1 / ((q (m + 1) : ℝ))) ∧
      (∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m) ∧
      (∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * β)) ∧
      (∀ m j : ℕ, 1 ≤ j → 2 * j * q m ≤ q (m + 1) →
        (j : ℝ) * Δ m ≤ fracDist (((j * q m : ℕ) : ℝ) * β)) ∧
      (∀ᶠ m : ℕ in Filter.atTop,
        ((q (m + 1) : ℕ) : ℝ) ≤ Real.exp ((b₀ + ε) * (q m : ℝ))) := by
  have hx := cfX_mem hβ0 hβ1 hβi
  have hA : ∀ n, 1 ≤ cfA β n := fun n => cfA_pos (fun k => ⟨(hx k).1, (hx k).2.1⟩) n
  have hQ : ∀ n, 1 ≤ cfQ β n := cfQ_pos hA
  have hQlt : ∀ n, 1 ≤ n → cfQ β n < cfQ β (n + 1) := cfQ_lt_succ hA hQ
  set q : ℕ → ℕ := fun m => (cfQ β (m + 2)).toNat with hqdef
  have hqZ : ∀ m, ((q m : ℕ) : ℤ) = cfQ β (m + 2) := by
    intro m
    rw [hqdef]
    exact Int.toNat_of_nonneg (by linarith [hQ (m + 2)])
  set δ : ℕ → ℝ :=
    fun m => 1 / ((cfQ β (m + 2) : ℝ) * (cfX β (m + 2))⁻¹ + (cfQ β (m + 1) : ℝ)) with hδdef
  have hδspec : ∀ n, δ n = 1 / ((cfQ β (n + 2) : ℝ) * (cfX β (n + 2))⁻¹
      + (cfQ β (n + 1) : ℝ)) := fun n => rfl
  obtain ⟨hδpos, hδerr, hδup, hδlo⟩ := cf_error_package hβ0 hβ1 hβi (δ := δ) hδspec
  have hqcast : ∀ m, ((q m : ℕ) : ℝ) = (cfQ β (m + 2) : ℝ) := by
    intro m
    have := hqZ m
    exact_mod_cast this
  have hqpos : ∀ m, 0 < q m := by
    intro m
    have h1 : (1 : ℤ) ≤ (q m : ℤ) := by rw [hqZ m]; exact hQ (m + 2)
    omega
  have hqmono : StrictMono q := by
    refine strictMono_nat_of_lt_succ (fun m => ?_)
    have h1 : cfQ β (m + 2) < cfQ β (m + 3) := hQlt (m + 2) (by omega)
    have h2 : ((q m : ℕ) : ℤ) = cfQ β (m + 2) := hqZ m
    have h3 : ((q (m + 1) : ℕ) : ℤ) = cfQ β (m + 3) := hqZ (m + 1)
    have h4 : (q m : ℤ) < (q (m + 1) : ℤ) := by rw [h2, h3]; exact h1
    omega
  have habs : ∀ m, |(q m : ℝ) * β - (cfP β (m + 2) : ℝ)| = δ m := by
    intro m
    rw [hqcast m, hδerr m, abs_mul, abs_of_pos (hδpos m)]
    rw [abs_neg_one_pow, one_mul]
  have hQ2 : ∀ m, (2 : ℝ) ≤ (cfQ β (m + 3) : ℝ) := by
    have hbase : (2 : ℤ) ≤ cfQ β 2 := by
      rw [cfQ_add_two β 0]
      have h1 : 1 ≤ cfA β 1 := hA 1
      have h2 : 1 ≤ cfQ β 1 := hQ 1
      have h4 : (1 : ℤ) ≤ cfA β 1 * cfQ β 1 := by
        calc (1 : ℤ) = 1 * 1 := by ring
          _ ≤ cfA β 1 * cfQ β 1 := mul_le_mul h1 h2 (by norm_num) (by linarith)
      have h0 : cfQ β 0 = 1 := cfQ_zero β
      linarith
    intro m
    have hmono : Monotone (fun n => cfQ β (n + 1)) :=
      (strictMono_nat_of_lt_succ (fun n => hQlt (n + 1) (by omega))).monotone
    have hstep := hmono (show 1 ≤ m + 2 by omega)
    have hstep' : (2 : ℤ) ≤ cfQ β (m + 3) := le_trans hbase hstep
    exact_mod_cast hstep'
  have hΔeq : ∀ m, fracDist ((q m : ℝ) * β) = δ m := by
    intro m
    have hhalf : |(q m : ℝ) * β - (cfP β (m + 2) : ℝ)| < 1 / 2 := by
      rw [habs m]
      have h1 : δ m < 1 / (cfQ β (m + 3) : ℝ) := hδup m
      have h2 : 1 / (cfQ β (m + 3) : ℝ) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (hQ2 m)
      linarith
    rw [fracDist_eq_of_abs_sub_lt_half hhalf, habs m]
  have hdet : ∀ n : ℕ, cfQ β (n + 2) * cfP β (n + 3) - cfP β (n + 2) * cfQ β (n + 3)
      = (-1 : ℤ) ^ n := by
    intro n
    have h := cfP_det β (n + 2)
    have hpar : (-1 : ℤ) ^ (n + 2) = (-1) ^ n := by rw [pow_add]; norm_num
    rwa [hpar] at h
  set Δ : ℕ → ℝ := fun m => fracDist ((q m : ℝ) * β) with hΔdef
  have hΔeq' : ∀ m, Δ m = δ m := by
    intro m
    simp only [hΔdef]
    exact hΔeq m
  refine ⟨q, Δ, hqpos, hqmono, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have : q (m - 1) < q m := hqmono (by omega)
    omega
  · intro m
    rw [hΔeq' m]
    exact hδpos m
  · intro m
    exact (hΔeq' m).trans (hΔeq m).symm
  · intro m
    rw [hΔeq' m]
    have h2 : ((q (m + 1) : ℕ) : ℝ) = (cfQ β (m + 3) : ℝ) := hqcast (m + 1)
    rw [h2]
    exact hδup m
  · intro m
    rw [hΔeq' m]
    have h2 : ((q (m + 1) : ℕ) : ℝ) = (cfQ β (m + 3) : ℝ) := hqcast (m + 1)
    have h3 : ((q m : ℕ) : ℝ) = (cfQ β (m + 2) : ℝ) := hqcast m
    rw [h2, h3]
    exact hδlo m
  · intro m k hk1 hk2
    have hk2' : (k : ℤ) < cfQ β (m + 3) := by
      have h1 : k < (cfQ β (m + 3)).toNat := hk2
      have h2 : ((k : ℤ)) < ((cfQ β (m + 3)).toNat : ℤ) := by exact_mod_cast h1
      rwa [Int.toNat_of_nonneg (by linarith [hQ (m + 3)])] at h2
    have hk1' : (0 : ℤ) < (k : ℤ) := by
      have : 0 < k := lt_of_lt_of_le (hqpos m) hk1
      exact_mod_cast this
    have hkey := cf_best_approx (β := β) (Q := fun n => cfQ β (n + 2))
      (P := fun n => cfP β (n + 2)) (δ := δ)
      (fun n => hQ (n + 2)) hdet hδpos hδerr m hk1' hk2' (ℓ := round ((k : ℝ) * β))
    calc Δ m = δ m := hΔeq' m
      _ ≤ |(k : ℝ) * β - (round ((k : ℝ) * β) : ℝ)| := hkey
      _ = fracDist ((k : ℝ) * β) := rfl
  · intro m j hj hjq
    rw [hΔeq' m]
    have hA1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hqm : (1 : ℝ) ≤ (q m : ℝ) := by
      have := hqpos m
      exact_mod_cast this
    have hQc : ((q (m + 1) : ℕ) : ℝ) = (cfQ β (m + 3) : ℝ) := hqcast (m + 1)
    have h2 : 2 * (j : ℝ) * (q m : ℝ) ≤ (cfQ β (m + 3) : ℝ) := by
      have h3 : ((2 * j * q m : ℕ) : ℝ) ≤ ((q (m + 1) : ℕ) : ℝ) := by exact_mod_cast hjq
      rw [hQc] at h3
      push_cast at h3
      linarith
    have hδm : (j : ℝ) * δ m < 1 / 2 := by
      have hQ3pos : (0 : ℝ) < (cfQ β (m + 3) : ℝ) := by
        have h := hQ (m + 3)
        have h' : (1 : ℝ) ≤ (cfQ β (m + 3) : ℝ) := by exact_mod_cast h
        linarith
      have h1 : (j : ℝ) * δ m < (j : ℝ) * (1 / (cfQ β (m + 3) : ℝ)) :=
        mul_lt_mul_of_pos_left (hδup m) (by linarith)
      have h2j : 2 * (j : ℝ) ≤ (cfQ β (m + 3) : ℝ) := by nlinarith [h2, hqm]
      have h4 : (j : ℝ) * (1 / (cfQ β (m + 3) : ℝ)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hQ3pos]
        linarith
      linarith
    have hmain := fracDist_mul_natCast_of_abs_sub_lt_half (x := (q m : ℝ) * β)
      (p := cfP β (m + 2)) (j := j) (by rw [habs m]; exact hδm)
    rw [habs m] at hmain
    have harg : ((j * q m : ℕ) : ℝ) * β = (j : ℝ) * ((q m : ℝ) * β) := by
      push_cast; ring
    rw [harg, hmain]
  · refine cf_saving hb₀ hDioph hε hqmono (fun m => ?_)
    have h2 : ((q (m + 1) : ℕ) : ℝ) = (cfQ β (m + 3) : ℝ) := hqcast (m + 1)
    rw [hΔeq m, h2]
    exact hδup m

/-! ## 5. The bridge -/

theorem cf_data_bridge {α b₀ : ℝ} (hα : Irrational α) (hb₀ : 0 ≤ b₀)
    (hDioph : Work.TMC16Core.DiophBelow α b₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ → ℕ, ∃ Δ : ℕ → ℝ,
      (∀ m, 0 < q m) ∧ StrictMono q ∧
      (∀ m, 1 ≤ m → q (m - 1) + 1 ≤ q m) ∧
      (∀ m, 0 < Δ m) ∧
      (∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α)) ∧
      (∀ m, Δ m < 1 / ((q (m + 1) : ℝ))) ∧
      (∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m) ∧
      (∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
        Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α)) ∧
      (∀ m j : ℕ, 1 ≤ j → 2 * j * q m ≤ q (m + 1) →
        (j : ℝ) * Δ m ≤ Work.TMC16Core.fracDist (((j * q m : ℕ) : ℝ) * α)) ∧
      (∀ᶠ m : ℕ in Filter.atTop,
        ((q (m + 1) : ℕ) : ℝ) ≤ Real.exp ((b₀ + ε) * (q m : ℝ))) := by
  set β : ℝ := Int.fract α with hβdef
  have hβ0 : 0 < β := by
    rw [hβdef]
    exact Int.fract_pos.mpr (hα.ne_int ⌊α⌋)
  have hβ1 : β < 1 := by
    rw [hβdef]
    exact Int.fract_lt_one α
  have hβi : Irrational β := by
    rw [hβdef]
    show Irrational (α - ((⌊α⌋ : ℤ) : ℝ))
    exact hα.sub_intCast ⌊α⌋
  have hkey : ∀ k : ℕ, fracDist ((k : ℝ) * α) = fracDist ((k : ℝ) * β) := by
    intro k
    rw [hβdef]
    exact fracDist_mul_natCast_fract α k
  have hDiophβ : Work.TMC16Core.DiophBelow β b₀ := by
    have h := hDioph
    simp only [DiophBelow] at h ⊢
    filter_upwards [h] with k hk
    rw [← hkey k]
    exact hk
  obtain ⟨q, Δ, hc⟩ := cf_data_bridge_aux hβ0 hβ1 hβi hb₀ hDiophβ hε
  exact ⟨q, Δ, by simpa only [hkey] using hc⟩

end Work.TMC16Core.CF
