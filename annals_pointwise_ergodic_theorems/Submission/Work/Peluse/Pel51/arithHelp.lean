import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Small arithmetic helpers for the transfer `lemma51P 2 → lemma51P 1`

These are kept in their own file so that the `ring`/`nlinarith` calls run in a *small* context:
the assembly (`Pel51/lemma51P_one_of_two.lean`) has O(40) hypotheses, and normalising ring
expressions there blows the heartbeat budget.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Pel51

open Work.Peluse

/-- `η ≤ 1` from `η ≤ C γ^e`, `C ≤ 1`, `0 < γ ≤ 1`. -/
theorem eta_le_one {C γ : ℝ} {e : ℕ} {η : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hC : C ≤ 1) (hηC : η ≤ C * γ ^ e) : η ≤ 1 := by
  have h1 : C * γ ^ e ≤ 1 * 1 :=
    mul_le_mul hC (pow_le_one₀ (le_of_lt hγ0) hγ1) (pow_nonneg (le_of_lt hγ0) e) (by norm_num)
  linarith [hηC, h1]

/-- `|b₀| ≤ (B+1) M₁` from `|b₀| ≤ B M₁`. -/
theorem abs_le_succ_mul {B₀ M₁ : ℕ} {b₀ : ℤ} (hb : |b₀| ≤ (B₀ : ℤ) * (M₁ : ℤ)) :
    |b₀| ≤ (((B₀ + 1 : ℕ)) : ℤ) * (M₁ : ℤ) := by
  have h1 : (B₀ : ℤ) * (M₁ : ℤ) ≤ (((B₀ + 1 : ℕ)) : ℤ) * (M₁ : ℤ) := by
    have h2 : (B₀ : ℤ) ≤ ((B₀ + 1 : ℕ) : ℤ) := by push_cast; omega
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  exact le_trans hb h1

/-- `|b₀ + 1| ≤ (B+1) M₁` from `|b₀| ≤ B M₁` and `1 ≤ M₁`. -/
theorem abs_add_one_le_succ_mul {B₀ M₁ : ℕ} {b₀ : ℤ} (hM₁ : 1 ≤ M₁)
    (hb : |b₀| ≤ (B₀ : ℤ) * (M₁ : ℤ)) :
    |b₀ + 1| ≤ (((B₀ + 1 : ℕ)) : ℤ) * (M₁ : ℤ) := by
  have hM₁1 : (1 : ℤ) ≤ (M₁ : ℤ) := by exact_mod_cast hM₁
  have h := abs_add_le b₀ (1 : ℤ)
  have h1 : |(1 : ℤ)| = 1 := by norm_num
  rw [h1] at h
  have h2 : |b₀| + 1 ≤ ((B₀ : ℤ) + 1) * (M₁ : ℤ) := by nlinarith [hb, hM₁1]
  have h3 : ((B₀ : ℤ) + 1) * (M₁ : ℤ) = (((B₀ + 1 : ℕ)) : ℤ) * (M₁ : ℤ) := by push_cast; ring
  rw [h3] at h2
  exact le_trans h h2

/-- The cast bookkeeping `((B+1)+1)N = (B+2)N` in `ℤ`. -/
theorem cast_two (B₀ N : ℕ) :
    ((((B₀ + 1) + 1 : ℕ)) : ℤ) * (N : ℤ) = (((B₀ + 2 : ℕ)) : ℤ) * (N : ℤ) := by
  have h : (B₀ + 1) + 1 = B₀ + 2 := by omega
  rw [h]

/-- **The regime-`2` exceptional-parameter bound.**  With `C ≤ C₂ c₀^{e₂}/(2(B₀+1))`, the strict
regime `1 < η M₁ (B₀+1)` and `ε ≤ C γ^{e₂}`, both `ε` and `1/M₁` are at most
`C₂ c₀^{e₂} γ^{e₂}/2`, hence `ε + 1/M₁ ≤ C₂ c₀^{e₂} γ^{e₂}`. -/
theorem eps_add_inv_le {B₀ M₁ : ℕ} {e₂ : ℕ} {C₂ c₀ C γ η ε : ℝ}
    (hM₁ : 1 ≤ M₁) (hC₂0 : 0 < C₂) (hc₀0 : 0 < c₀) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hηC : η ≤ C * γ ^ e₂) (hεC : ε ≤ C * γ ^ e₂)
    (hCC2 : C ≤ C₂ * c₀ ^ e₂ / (2 * ((B₀ : ℝ) + 1)))
    (hreg : 1 < η * (M₁ : ℝ) * ((B₀ : ℝ) + 1)) :
    ε + 1 / (M₁ : ℝ) ≤ C₂ * c₀ ^ e₂ * γ ^ e₂ := by
  have hM₁pos : (0 : ℝ) < (M₁ : ℝ) := by exact_mod_cast (by omega : 0 < M₁)
  set X : ℝ := C₂ * c₀ ^ e₂ * γ ^ e₂ with hXdef
  have hX0 : (0 : ℝ) ≤ X := by rw [hXdef]; positivity
  have hbase : (1 : ℝ) ≤ 2 * ((B₀ : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (B₀ : ℝ) := Nat.cast_nonneg B₀
    linarith
  have hb2 : (0 : ℝ) < 2 * ((B₀ : ℝ) + 1) := by positivity
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  -- the `ε` half
  have hεX : ε ≤ X / 2 := by
    have h1 : C₂ * c₀ ^ e₂ / (2 * ((B₀ : ℝ) + 1)) * γ ^ e₂ = X / (2 * ((B₀ : ℝ) + 1)) := by
      rw [hXdef, div_mul_eq_mul_div]
    have h2 : ε ≤ X / (2 * ((B₀ : ℝ) + 1)) := by
      have h := le_trans hεC (mul_le_mul_of_nonneg_right hCC2 (pow_nonneg (le_of_lt hγ0) e₂))
      rwa [h1] at h
    have h3 : X / (2 * ((B₀ : ℝ) + 1)) ≤ X / 2 := by
      rw [le_div_iff₀ h2pos]
      rw [div_mul_eq_mul_div]
      rw [div_le_iff₀ hb2]
      nlinarith [hbase, hX0]
    exact le_trans h2 h3
  -- the `1/M₁` half
  have h2X : 1 / (M₁ : ℝ) ≤ X / 2 := by
    have hCO : C * (2 * ((B₀ : ℝ) + 1)) ≤ C₂ * c₀ ^ e₂ := by
      have h := mul_le_mul_of_nonneg_right hCC2 (by positivity : (0 : ℝ) ≤ 2 * ((B₀ : ℝ) + 1))
      rwa [div_mul_cancel₀ _ (by positivity : (2 * ((B₀ : ℝ) + 1)) ≠ 0)] at h
    have hstep1 : C * γ ^ e₂ * (M₁ : ℝ) * ((B₀ : ℝ) + 1)
        = (C * (2 * ((B₀ : ℝ) + 1))) * (γ ^ e₂ * (M₁ : ℝ)) / 2 := by ring
    have hstep2 : (C * (2 * ((B₀ : ℝ) + 1))) * (γ ^ e₂ * (M₁ : ℝ)) / 2
        ≤ (C₂ * c₀ ^ e₂) * (γ ^ e₂ * (M₁ : ℝ)) / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCO (by positivity)) h2nn
    have hstep3 : (C₂ * c₀ ^ e₂) * (γ ^ e₂ * (M₁ : ℝ)) / 2 = X * (M₁ : ℝ) / 2 := by
      rw [hXdef]; ring
    have hstep : C * γ ^ e₂ * (M₁ : ℝ) * ((B₀ : ℝ) + 1) ≤ X * (M₁ : ℝ) / 2 := by
      rw [hstep1]
      rw [hstep3] at hstep2
      exact hstep2
    have hηle : η * (M₁ : ℝ) * ((B₀ : ℝ) + 1)
        ≤ C * γ ^ e₂ * (M₁ : ℝ) * ((B₀ : ℝ) + 1) := by
      have h := mul_le_mul_of_nonneg_right hηC
        (by positivity : (0 : ℝ) ≤ (M₁ : ℝ) * ((B₀ : ℝ) + 1))
      calc η * (M₁ : ℝ) * ((B₀ : ℝ) + 1) = η * ((M₁ : ℝ) * ((B₀ : ℝ) + 1)) := by ring
        _ ≤ C * γ ^ e₂ * ((M₁ : ℝ) * ((B₀ : ℝ) + 1)) := h
        _ = C * γ ^ e₂ * (M₁ : ℝ) * ((B₀ : ℝ) + 1) := by ring
    have hlt : 1 < X * (M₁ : ℝ) / 2 := lt_of_lt_of_le (lt_of_lt_of_le hreg hηle) hstep
    have hlt2 : 2 ≤ X * (M₁ : ℝ) := by
      rw [lt_div_iff₀ h2pos] at hlt
      linarith [hlt]
    rw [div_le_iff₀ hM₁pos]
    have heq : X / 2 * (M₁ : ℝ) = X * (M₁ : ℝ) / 2 := by ring
    rw [heq]
    linarith [hlt2]
  have hfin : ε + 1 / (M₁ : ℝ) ≤ X := by linarith [hεX, h2X]
  rw [hXdef] at hfin
  exact hfin

end Work.Peluse.Pel51
