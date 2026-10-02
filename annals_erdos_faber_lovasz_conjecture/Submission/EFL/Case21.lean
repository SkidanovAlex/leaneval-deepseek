import Submission.EFL.LargeEdgeCase2
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Case 2.1 of Theorem 6.1 with the instance-dependent `ζ`

The paper's Case 2.1 (`r₃ < (1−δ)√n`) uses the *instance-dependent*
parameter `ζ := 1 − r₃/√n`, which satisfies `ζ > δ`.  All the `ζ`-dependent
margins of `case2_data` (`hm : Corollary65Margins`, the two `n`-room
inequalities, the colour budget and `hmarginA`) are derived here from
`δ`-based margins that hold for all large `n`, so that the statement of the
case can be discharged by the parameter hierarchy.

The key numeric choices are

* `ζ := 1 − r₃/√n`,
* `B₀ := ⌈sizeFactor (3σ) 1 · r₃⌉₊` (so `B₀ ≤ (1+α)r₃` with
  `α = sizeFactor (3σ) 1 − 1 + 1/r₃ ≤ δ/10⁶`),
* `Δ := (1 + δ/10⁵) n`,

and the four `Corollary65Margins` fields are then arithmetic; the only
non-elementary input is `Real.exp 6 ≤ 414`, which supplies the `3%` slack
between `5/(6e⁶) = 0.002066` and `1/500 = 0.002`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The Case-2.1 slack: `Δ := (1 + case21eps δ) n`. -/
def case21eps (δ : ℝ) : ℝ := δ / 10 ^ 5

theorem case21eps_pos {δ : ℝ} (hδ0 : 0 < δ) : 0 < case21eps δ := by
  simp only [case21eps]; positivity

/-- `Real.exp 6 ≤ 414` (`e⁶ ≈ 403.4`). -/
theorem real_exp_six_le : Real.exp 6 ≤ 414 := by
  have h1 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    have h := Real.exp_nat_mul (x := (1 : ℝ)) 6
    simpa using h
  rw [h1]
  have h3 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h4 : (Real.exp 1) ^ 6 ≤ (2.7182818286 : ℝ) ^ 6 :=
    pow_le_pow_left₀ (le_of_lt h3) (le_of_lt Real.exp_one_lt_d9) 6
  have h5 : (2.7182818286 : ℝ) ^ 6 ≤ 414 := by norm_num
  linarith

/-- `1/500 + 1/10⁵ ≤ 5/(6e⁶)`: the `3%` slack between `1/500` and
`5/(6e⁶)`. -/
theorem five_sixth_exp_ge : (1 : ℝ) / 500 + 1 / 10 ^ 5 ≤ 5 / (6 * Real.exp 6) := by
  have h1 : Real.exp 6 ≤ 414 := real_exp_six_le
  have hpos : 0 < Real.exp 6 := Real.exp_pos 6
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 6 * Real.exp 6)]
  nlinarith [h1, hpos]

/-- The Case-2.1 parameter `ζ := 1 − r₃/√n` satisfies `δ < ζ ≤ 1`. -/
theorem case21_zeta {n r₃ : ℕ} {δ : ℝ} (hn : 0 < n) (hδ0 : 0 < δ)
    (hup : (r₃ : ℝ) < (1 - δ) * Real.sqrt (n : ℝ)) :
    δ < 1 - (r₃ : ℝ) / Real.sqrt (n : ℝ) ∧
      0 < 1 - (r₃ : ℝ) / Real.sqrt (n : ℝ) ∧
      1 - (r₃ : ℝ) / Real.sqrt (n : ℝ) ≤ 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos hnpos
  have hr : (0 : ℝ) ≤ (r₃ : ℝ) := Nat.cast_nonneg r₃
  have hlt : (r₃ : ℝ) / Real.sqrt (n : ℝ) < 1 - δ := by
    rw [div_lt_iff₀ hsp]; exact hup
  have hge : 0 ≤ (r₃ : ℝ) / Real.sqrt (n : ℝ) := div_nonneg hr (le_of_lt hsp)
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **`hΔge`**: `B₀(n−r₃)/(r₃−1) ≤ Δ = (1+δ/10⁵)n`, using `r₃ ≥ 10⁷/δ` and
`B₀ ≤ (1+α)r₃` with `α ≤ δ/10⁶`. -/
theorem case21_margin_Dge {n r₃ : ℕ} {δ α : ℝ} {B₀ : ℕ}
    (hn : 0 < n) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 3)
    (hr₃ : 2 ≤ r₃) (hr₃big : 10 ^ 7 / δ ≤ (r₃ : ℝ))
    (hα : α ≤ δ / 10 ^ 6) (hα0 : 0 ≤ α)
    (hB₀ : (B₀ : ℝ) ≤ (1 + α) * (r₃ : ℝ)) :
    (B₀ : ℝ) * ((n : ℝ) - (r₃ : ℝ)) / ((r₃ : ℝ) - 1) ≤ (1 + case21eps δ) * (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr3R : (2 : ℝ) ≤ (r₃ : ℝ) := by exact_mod_cast hr₃
  have hden : 0 < (r₃ : ℝ) - 1 := by linarith
  have hb : 10 ^ 6 ≤ δ * ((r₃ : ℝ) - 1) := by
    have h1 : 10 ^ 7 ≤ δ * (r₃ : ℝ) := by
      rw [div_le_iff₀ hδ0] at hr₃big; linarith [hr₃big]
    have h2 : δ ≤ 1 := by linarith only [hδ1]
    nlinarith [h1, h2, hδ0]
  have hrec : 1 / ((r₃ : ℝ) - 1) ≤ δ / 10 ^ 6 := by
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 10 ^ 6)]
    linarith [hb]
  have hA : (B₀ : ℝ) * ((n : ℝ) - (r₃ : ℝ)) / ((r₃ : ℝ) - 1) ≤
      (B₀ : ℝ) * (n : ℝ) / ((r₃ : ℝ) - 1) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hden)
    have hstep : (n : ℝ) - (r₃ : ℝ) ≤ (n : ℝ) :=
      by linarith [(Nat.cast_nonneg r₃ : (0 : ℝ) ≤ (r₃ : ℝ))]
    exact mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg B₀)
  have hB : (B₀ : ℝ) * (n : ℝ) / ((r₃ : ℝ) - 1) ≤
      (1 + α) * (r₃ : ℝ) * (n : ℝ) / ((r₃ : ℝ) - 1) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB₀ (Nat.cast_nonneg n))
      (le_of_lt hden)
  have h3 : (r₃ : ℝ) / ((r₃ : ℝ) - 1) ≤ 1 + δ / 10 ^ 6 := by
    have h4 : (r₃ : ℝ) / ((r₃ : ℝ) - 1) = 1 + 1 / ((r₃ : ℝ) - 1) := by
      rw [div_eq_iff (ne_of_gt hden), add_mul, one_mul,
        div_mul_cancel₀ (1 : ℝ) (ne_of_gt hden)]
      ring
    rw [h4]; linarith [hrec]
  have h6 : (1 + α) * (1 + δ / 10 ^ 6) ≤ 1 + case21eps δ := by
    simp only [case21eps]
    nlinarith [hα, hα0, hδ0, hδ1]
  calc (B₀ : ℝ) * ((n : ℝ) - (r₃ : ℝ)) / ((r₃ : ℝ) - 1)
      ≤ (1 + α) * (r₃ : ℝ) * (n : ℝ) / ((r₃ : ℝ) - 1) := le_trans hA hB
    _ = (1 + α) * ((r₃ : ℝ) / ((r₃ : ℝ) - 1)) * (n : ℝ) := by ring
    _ ≤ (1 + α) * (1 + δ / 10 ^ 6) * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hnpos)
        exact mul_le_mul_of_nonneg_left h3 (by linarith)
    _ ≤ (1 + case21eps δ) * (n : ℝ) := mul_le_mul_of_nonneg_right h6 (le_of_lt hnpos)

/-- **`hΔthr`**: the Molloy–Reed threshold at `5ζ/6` is below `Δ`, using the
polynomial bound `Δ₀ ζ ≤ K/ζ^m` of the deep input and `ζ ≥ δ`. -/
theorem case21_margin_Dthr {n : ℕ} {δ ζ K : ℝ} {m : ℕ}
    (hn : 0 < n) (hδ0 : 0 < δ) (hζ0 : 0 < ζ) (hζge : δ ≤ ζ)
    (hK : 0 < K) (hmain : K * (6 / (5 * δ)) ^ m ≤ (n : ℝ)) :
    K / (5 * ζ / 6) ^ m ≤ (1 + case21eps δ) * (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
  have h5δ : 0 < 5 * δ / 6 := by linarith
  have h5δζ : 5 * δ / 6 ≤ 5 * ζ / 6 := by linarith
  have hpow : (5 * δ / 6) ^ m ≤ (5 * ζ / 6) ^ m := pow_le_pow_left₀ h5δ.le h5δζ m
  have hle : K / (5 * ζ / 6) ^ m ≤ K / (5 * δ / 6) ^ m :=
    div_le_div_of_nonneg_left hK.le (pow_pos h5δ m) hpow
  have heq : K / (5 * δ / 6) ^ m = K * (6 / (5 * δ)) ^ m := by
    have h : (5 * δ / 6 : ℝ) = (6 / (5 * δ))⁻¹ := by rw [inv_div]
    rw [h, inv_pow, div_inv_eq_mul]
  rw [heq] at hle
  have hε : 0 < case21eps δ := case21eps_pos hδ0
  have hge : (n : ℝ) ≤ (1 + case21eps δ) * (n : ℝ) := by nlinarith [hn0, hε]
  linarith [hle, hmain, hge]

/-- **`hcodeg`**: `n/(r₃−1) + B₀² ≤ (1−5ζ/6)Δ`. -/
theorem case21_margin_hcodeg {n r₃ : ℕ} {δ σ ζ α : ℝ} {B₀ : ℕ}
    (hn : 0 < n) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 3) (hσ0 : 0 < σ)
    (hζdef : ζ = 1 - (r₃ : ℝ) / Real.sqrt (n : ℝ)) (hζ0 : 0 < ζ) (hζle : ζ ≤ 1)
    (hζge : δ ≤ ζ)
    (hr₃ : 2 ≤ r₃) (hr₃big : 10 ^ 7 / δ ≤ (r₃ : ℝ))
    (hα : α ≤ δ / 10 ^ 6) (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2)
    (hB₀ : (B₀ : ℝ) ≤ (1 + α) * (r₃ : ℝ)) :
    (n : ℝ) / ((r₃ : ℝ) - 1) + (B₀ : ℝ) ^ 2 ≤
      (1 - 5 * ζ / 6) * ((1 + case21eps δ) * (n : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
  have hsp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos hnpos
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hnpos)
  have hr2R : (2 : ℝ) ≤ (r₃ : ℝ) := by exact_mod_cast hr₃
  have hden : 0 < (r₃ : ℝ) - 1 := by linarith
  -- `r₃ = (1-ζ)√n`
  have hrζ : (r₃ : ℝ) = (1 - ζ) * Real.sqrt (n : ℝ) := by
    have h : (r₃ : ℝ) / Real.sqrt (n : ℝ) = 1 - ζ := by
      rw [hζdef]; ring
    rw [div_eq_iff (ne_of_gt hsp)] at h
    exact h
  -- term 1: `n/(r₃-1) ≤ (δ/10⁶)n`
  have hb : 10 ^ 6 ≤ δ * ((r₃ : ℝ) - 1) := by
    have h1 : 10 ^ 7 ≤ δ * (r₃ : ℝ) := by
      rw [div_le_iff₀ hδ0] at hr₃big; linarith [hr₃big]
    have h2 : δ ≤ 1 := by linarith only [hδ1]
    nlinarith [h1, h2, hδ0]
  have ht1 : (n : ℝ) / ((r₃ : ℝ) - 1) ≤ (δ / 10 ^ 6) * (n : ℝ) := by
    rw [div_le_iff₀ hden]
    have h2 : 1 ≤ (δ / 10 ^ 6) * ((r₃ : ℝ) - 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)]
      linarith [hb]
    calc (n : ℝ) = 1 * (n : ℝ) := by ring
      _ ≤ ((δ / 10 ^ 6) * ((r₃ : ℝ) - 1)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right h2 hn0
      _ = (δ / 10 ^ 6) * (n : ℝ) * ((r₃ : ℝ) - 1) := by ring
  -- term 2: `B₀² ≤ (1+α)²(1-ζ)²n`
  have ht2 : (B₀ : ℝ) ^ 2 ≤ (1 + α) ^ 2 * (1 - ζ) ^ 2 * (n : ℝ) := by
    have h1 : (B₀ : ℝ) ^ 2 ≤ ((1 + α) * (r₃ : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg B₀) hB₀ 2
    have h2 : ((1 + α) * (r₃ : ℝ)) ^ 2 = (1 + α) ^ 2 * (1 - ζ) ^ 2 * (n : ℝ) := by
      rw [mul_pow, hrζ, mul_pow, Real.sq_sqrt (le_of_lt hnpos)]
      ring
    rw [h2] at h1
    exact h1
  -- the arithmetic: `δ/10⁶ + (1+α)²(1-ζ)² ≤ (1-5ζ/6)(1+case21eps δ)`
  have hζslack : δ / 6 ≤ (1 - 5 * ζ / 6) - (1 - ζ) ^ 2 := by
    have hkey : (1 - 5 * ζ / 6) - (1 - ζ) ^ 2 = ζ * (7 / 6 - ζ) := by ring
    nlinarith [hkey, hζ0, hζle, hζge]
  have hAc : (1 - ζ) ^ 2 ≤ (1 - 5 * ζ / 6) - δ / 6 := by linarith [hζslack]
  have hAn : (0 : ℝ) ≤ (1 - 5 * ζ / 6) - δ / 6 := by linarith [hAc, sq_nonneg (1 - ζ)]
  have hα3 : (1 + α) ^ 2 ≤ 1 + 3 * α := by nlinarith [hα0, hα1]
  have hmain1 : (1 + α) ^ 2 * (1 - ζ) ^ 2 ≤ (1 + 3 * α) * ((1 - 5 * ζ / 6) - δ / 6) :=
    mul_le_mul hα3 hAc (sq_nonneg (1 - ζ)) (by nlinarith [hα0, hα1, hζ0, hζle, hδ0])
  have hα3δ : 1 + 3 * α ≤ 1 + 3 * (δ / 10 ^ 6) := by linarith [hα]
  have hmain2 : (1 + 3 * α) * ((1 - 5 * ζ / 6) - δ / 6) ≤
      (1 + 3 * (δ / 10 ^ 6)) * ((1 - 5 * ζ / 6) - δ / 6) :=
    mul_le_mul_of_nonneg_right hα3δ hAn
  have hmain3 : δ / 10 ^ 6 + (1 + 3 * (δ / 10 ^ 6)) * ((1 - 5 * ζ / 6) - δ / 6) ≤
      (1 - 5 * ζ / 6) * (1 + case21eps δ) := by
    simp only [case21eps]
    nlinarith [hζ0, hζle, hδ0]
  have hkey : δ / 10 ^ 6 + (1 + α) ^ 2 * (1 - ζ) ^ 2 ≤
      (1 - 5 * ζ / 6) * (1 + case21eps δ) := by linarith [hmain1, hmain2, hmain3]
  -- combine
  have hcomb : (n : ℝ) / ((r₃ : ℝ) - 1) + (B₀ : ℝ) ^ 2 ≤
      ((δ / 10 ^ 6) + (1 + α) ^ 2 * (1 - ζ) ^ 2) * (n : ℝ) := by
    nlinarith [ht1, ht2, hn0]
  have hfin : ((δ / 10 ^ 6) + (1 + α) ^ 2 * (1 - ζ) ^ 2) * (n : ℝ) ≤
      (1 - 5 * ζ / 6) * ((1 + case21eps δ) * (n : ℝ)) := by
    have h2 := mul_le_mul_of_nonneg_right hkey hn0
    have heq : (1 - 5 * ζ / 6) * (1 + case21eps δ) * (n : ℝ) =
        (1 - 5 * ζ / 6) * ((1 + case21eps δ) * (n : ℝ)) := by ring
    linarith [h2, heq.le, heq.ge]
  exact le_trans hcomb hfin

/-- **`hfinal`**: `(1 − 5ζ/(6e⁶))Δ ≤ (1 − ζ/500)n`. -/
theorem case21_margin_hfinal {n : ℕ} {δ ζ : ℝ}
    (hn : 0 < n) (hδ0 : 0 < δ) (hζ0 : 0 < ζ) (hζge : δ ≤ ζ) :
    (1 - 5 * ζ / (6 * Real.exp 6)) * ((1 + case21eps δ) * (n : ℝ)) ≤
      (1 - ζ / 500) * (n : ℝ) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hexp : (0 : ℝ) < Real.exp 6 := Real.exp_pos 6
  have hε0 : 0 ≤ case21eps δ := le_of_lt (case21eps_pos hδ0)
  have hε : case21eps δ ≤ ζ / 10 ^ 5 := by
    simp only [case21eps]; linarith [hζge]
  have h2 : 6 * Real.exp 6 * (1 / 500 + 1 / 10 ^ 5) ≤ 5 := by
    have hk := five_sixth_exp_ge
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 6 * Real.exp 6)] at hk
    linarith [hk]
  have hkey : (case21eps δ + ζ / 500) * (6 * Real.exp 6) ≤
      5 * ζ * (1 + case21eps δ) := by
    have hstep1 : (case21eps δ + ζ / 500) * (6 * Real.exp 6) ≤
        (ζ / 10 ^ 5 + ζ / 500) * (6 * Real.exp 6) :=
      mul_le_mul_of_nonneg_right (by linarith [hε])
        (by positivity : (0 : ℝ) ≤ 6 * Real.exp 6)
    have hstep2 : (ζ / 10 ^ 5 + ζ / 500) * (6 * Real.exp 6) =
        (6 * Real.exp 6 * (1 / 500 + 1 / 10 ^ 5)) * ζ := by ring
    have hstep3 : (6 * Real.exp 6 * (1 / 500 + 1 / 10 ^ 5)) * ζ ≤ 5 * ζ :=
      mul_le_mul_of_nonneg_right h2 (le_of_lt hζ0)
    have hstep4 : 5 * ζ ≤ 5 * ζ * (1 + case21eps δ) := by nlinarith [hε0, hζ0]
    linarith [hstep1, hstep2.le, hstep2.ge, hstep3, hstep4]
  have hmain : case21eps δ + ζ / 500 ≤ 5 * ζ * (1 + case21eps δ) / (6 * Real.exp 6) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 6 * Real.exp 6)).mpr hkey
  have hmain' : case21eps δ - 5 * ζ / (6 * Real.exp 6) * (1 + case21eps δ) ≤ -ζ / 500 := by
    have h5 : 5 * ζ * (1 + case21eps δ) / (6 * Real.exp 6) =
        5 * ζ / (6 * Real.exp 6) * (1 + case21eps δ) := by ring
    linarith [hmain, h5.le, h5.ge]
  calc (1 - 5 * ζ / (6 * Real.exp 6)) * ((1 + case21eps δ) * (n : ℝ))
      = (1 + case21eps δ - 5 * ζ / (6 * Real.exp 6) * (1 + case21eps δ)) * (n : ℝ) := by
        ring
    _ ≤ (1 - ζ / 500) * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hn0
        linarith [hmain']


/-- **Case 2.1 of Theorem 6.1 with the instance-dependent `ζ`.**  The
paper's Case 2.1 (`r₃ < (1−δ)√n`) with `ζ := 1 − r₃/√n`, `B₀ :=
⌈sizeFactor (3σ) 1 · r₃⌉₊` and `Δ := (1 + δ/10⁵)n`: all the `ζ`-dependent
hypotheses of `case2_nonExtremal` are produced from `δ`-based margins that
hold for all large `n`. -/
theorem case2_nonExtremal' {Δ₀ : ℝ → ℝ} {C : ℝ} {m : ℕ}
    (hC : 0 < C)
    (hΔ₀bnd : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → Δ₀ ζ' ≤ C / ζ' ^ m)
    (hMRe : ∀ (ζ' : ℝ), 0 < ζ' → ζ' ≤ 1 → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ' ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ') * Δ ^ 2 / 2) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ' / Real.exp 6) * Δ ∧ G.Colorable k)
    {n r₁ r₀ : ℕ} {β γ₂ σ δ γ₁ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅) (hlin : 𝓗.IsLinear) (hn : 0 < n) (h2n : 2 ≤ n) (hβ : 0 < β)
    (hσ0 : 0 < σ) (hγ₁σ : γ₁ ≤ σ / 2) (hσ32 : 3 * σ / 2 ≤ 1) (hr₀ : 1 ≤ r₀) (h2r₀ : 2 ≤ r₀)
    (h2r₁ : 2 ≤ r₁) (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 256) (hδV : δ ≤ volBound app3tau app3K)
    (hr₃up : (r₃ : ℝ) < (1 - δ) * Real.sqrt (n : ℝ))
    (hδbig : δ ≤ 1 / 10 ^ 3)
    (hr₃big : 10 ^ 7 / δ ≤ (r₃ : ℝ))
    (hαδ : 3 * tauQuarter (3 * σ) ≤ δ / 10 ^ 7)
    (hΔ₀δ : C * (6 / (5 * δ)) ^ m ≤ (n : ℝ))
    (hk2δ : 2 * δ ^ 2 + 2 * σ ≤ δ / 1000)
    (hbig3 : (r₃ : ℝ) ≤ β * (n : ℝ) / 4)
    (hnbig : 16 / Real.sqrt δ ≤ (n : ℝ))
    (hσsmall : (2 : ℝ) * σ + 1 / (n : ℝ) ≤ 1 / 12000)
    (hmarginAδ : ((2 : ℝ) / ((β / 5) / 2) + 1) *
      ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤ δ * (n : ℝ) / 1000)
    (h69m : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((1 / 6000 : ℝ) * (n : ℝ)) / 4)
    (h69b : (((bigFinset (β / 5) (case2H3med r₁ r₀ 𝓗 H₃)).card : ℕ) : ℝ) <
      ((1 / 6000 : ℝ) * (n : ℝ)) / 2)
    (h69mσ : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((σ / 4) * (n : ℝ)) / 4)
    (h69bσ : (((bigFinset (β / 5) (case2Right r₁ r₀ 𝓗 Good₁ Good₂)).card : ℕ) : ℝ) <
      ((σ / 4) * (n : ℝ)) / 2)
    (h2βn : (2 : ℝ) ≤ (β / 5) * (n : ℝ))
    {Cmed : Finset (Fin n)} (hCmed : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ))
    (h2σδ : 2000 * σ ≤ δ)
    (hroom1C : (Cmed.card : ℝ) + (1 / 1000) * (n : ℝ) + 1 ≤ (n : ℝ))
    (hroom2C : (Cmed.card : ℝ) + 2 ≤ 2 * σ * (n : ℝ))
    (hbudgetC : (1 - 2 * σ) * (n : ℝ) + 2 ≤ (⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ : ℝ))
    (hβc : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hσn : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hγm : (γ₂ / 3) * (n : ℝ) + 32 / β ^ 2 ≤ (1 - 2 * σ) * (n : ℝ))
    (hKroom : ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ + Cmed.card ≤ n)
    (hslack : 1 + 32 / β ^ 2 ≤ (σ / 4) * (n : ℝ))
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    {φmed : (𝓗.medEdges r₁ r₀).Coloring (Fin n)} (hφmed : φmed.UsesColourSet Cmed)
    (hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ)) :
    LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  classical
  -- the instance-dependent parameters
  have hζb := case21_zeta (n := n) (r₃ := r₃) hn hδ0 hr₃up
  set ζ : ℝ := 1 - (r₃ : ℝ) / Real.sqrt (n : ℝ) with hζdef
  have hζgt : δ < ζ := hζb.1
  have hζpos : 0 < ζ := hζb.2.1
  have hζle : ζ ≤ 1 := hζb.2.2
  have hζge : δ ≤ ζ := le_of_lt hζgt
  set α : ℝ := 3 * tauQuarter (3 * σ) + 1 / (r₃ : ℝ) with hαdef
  set B₀ : ℕ := ⌈sizeFactor (3 * σ) 1 * (r₃ : ℝ)⌉₊ with hB₀def
  set Δ : ℝ := (1 + case21eps δ) * (n : ℝ) with hΔdef
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
  have hδ1' : δ ≤ 1 := by linarith only [hδbig]
  have hr3R : (2 : ℝ) ≤ (r₃ : ℝ) := by exact_mod_cast hB.hr₃
  have hr3pos : (0 : ℝ) < (r₃ : ℝ) := by linarith
  -- `1/r₃ ≤ δ/10⁷`
  have hrecδ : 1 / (r₃ : ℝ) ≤ δ / 10 ^ 7 := by
    rw [div_le_div_iff₀ hr3pos
      (by norm_num : (0 : ℝ) < 10 ^ 7)]
    have h2 : 10 ^ 7 ≤ δ * (r₃ : ℝ) := by
      rw [div_le_iff₀ hδ0] at hr₃big; linarith [hr₃big]
    linarith [h2]
  -- `α ≤ δ/10⁶`, `α ≤ 1/2`
  have hαδ' : α ≤ δ / 10 ^ 6 := by rw [hαdef]; linarith [hαδ, hrecδ]
  have hα0 : 0 ≤ α := by
    rw [hαdef]
    have h1 : 0 ≤ tauQuarter (3 * σ) := tauQuarter_nonneg (3 * σ)
    have h2 : (0 : ℝ) < (r₃ : ℝ) := hr3pos
    positivity
  have hα1 : α ≤ 1 / 2 := by
    rw [hαdef]
    have h1 : δ / 10 ^ 7 ≤ 1 / 4 := by linarith [hδ1']
    linarith [hαδ, hrecδ, h1]
  -- `B₀` bounds
  have hsizeFactor : sizeFactor (3 * σ) 1 = 1 + 3 * tauQuarter (3 * σ) := by
    simp only [sizeFactor, Nat.cast_one, one_pow, mul_one]
  have hsfpos : (0 : ℝ) < sizeFactor (3 * σ) 1 := by
    rw [hsizeFactor]
    have h1 : 0 ≤ tauQuarter (3 * σ) := tauQuarter_nonneg (3 * σ)
    linarith
  have hB₀ : sizeFactor (3 * σ) 1 * (r₃ : ℝ) ≤ (B₀ : ℝ) := by
    rw [hB₀def]; exact Nat.le_ceil _
  have hB₀lt : (B₀ : ℝ) ≤ sizeFactor (3 * σ) 1 * (r₃ : ℝ) + 1 := by
    rw [hB₀def]
    exact le_of_lt (Nat.ceil_lt_add_one (mul_nonneg hsfpos.le hr3pos.le))
  have hB₀le : (B₀ : ℝ) ≤ (1 + α) * (r₃ : ℝ) := by
    have hr₃ne : (r₃ : ℝ) ≠ 0 := ne_of_gt hr3pos
    have h2 : sizeFactor (3 * σ) 1 * (r₃ : ℝ) + 1 = (1 + α) * (r₃ : ℝ) := by
      rw [hsizeFactor, hαdef]
      field_simp
      ring
    linarith [hB₀lt, h2.le, h2.ge]
  -- the `ζ`-instantiations of the `δ`-margins
  have hk2 : 2 * δ ^ 2 ≤ ζ / 1000 - 2 * σ := by
    have h1 : δ / 1000 ≤ ζ / 1000 := by linarith [hζge]
    linarith [hk2δ, h1]
  have hmarginA : ((2 : ℝ) / ((β / 5) / 2) + 1) *
      ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤ ζ * (n : ℝ) / 1000 := by
    have h1 : δ * (n : ℝ) / 1000 ≤ ζ * (n : ℝ) / 1000 := by
      have h2 : δ * (n : ℝ) ≤ ζ * (n : ℝ) := mul_le_mul_of_nonneg_right hζge hn0
      linarith [h2]
    linarith [hmarginAδ, h1]
  -- the two ceilings: `⌈(1-ζ/1000)n⌉₊ + ⌈(ζ/1000-2σ)n⌉₊ < (1-2σ)n + 2`
  have hζ2σ : 2 * σ ≤ ζ / 1000 := by linarith [h2σδ, hζge]
  have hceil1 : (⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ : ℝ) < (1 - ζ / 1000) * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by nlinarith [hζle, hn0])
  have hceil2 : (⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ : ℝ) < (ζ / 1000 - 2 * σ) * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by nlinarith [hζ2σ, hn0])
  have hceilsum : ((⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ : ℝ) +
      (⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ : ℝ)) < (1 - 2 * σ) * (n : ℝ) + 2 := by
    have heq : (1 - ζ / 1000) * (n : ℝ) + 1 + ((ζ / 1000 - 2 * σ) * (n : ℝ) + 1) =
        (1 - 2 * σ) * (n : ℝ) + 2 := by ring
    linarith [hceil1, hceil2, heq.le, heq.ge]
  have huniv : (Finset.univ \ Cmed).card = n - Cmed.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hc_le : Cmed.card ≤ n := by
    have h1 : (Cmed.card : ℝ) ≤ (n : ℝ) := by
      have h2 : (1 / 1000 : ℝ) * (n : ℝ) + 1 ≥ 0 := by positivity
      nlinarith [hroom1C, h2]
    exact_mod_cast h1
  have hroom1 : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ ≤ (Finset.univ \ Cmed).card := by
    rw [huniv, Nat.ceil_le, Nat.cast_sub hc_le]
    have h2 : (1 - ζ / 1000) * (n : ℝ) ≤ (n : ℝ) - (Cmed.card : ℝ) := by
      nlinarith [hroom1C, hζle, hn0]
    linarith
  have hroom2 : ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ + ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ ≤
      (Finset.univ \ Cmed).card := by
    rw [huniv]
    have h3 : ((⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ + ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ : ℕ) : ℝ) <
        ((n - Cmed.card : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hc_le]
      have h2 : (1 - 2 * σ) * (n : ℝ) + 2 ≤ (n : ℝ) - (Cmed.card : ℝ) := by
        nlinarith [hroom2C]
      have heq : (1 - ζ / 1000) * (n : ℝ) + 1 + ((ζ / 1000 - 2 * σ) * (n : ℝ) + 1) =
          (1 - 2 * σ) * (n : ℝ) + 2 := by ring
      linarith [hceil1, hceil2, h2, heq.le, heq.ge]
    have h4 : ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ + ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ <
        (n - Cmed.card) + 1 := by exact_mod_cast h3
    omega
  have hbudget0 : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ + ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ ≤
      ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ := by
    have h3 : ((⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ + ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ : ℕ) : ℝ) <
        (⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ : ℝ) + 1 := by
      rw [Nat.cast_add]
      linarith [hceilsum, hbudgetC]
    have h4 : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ + ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ <
        ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ + 1 := by exact_mod_cast h3
    omega
  -- `r₃ ≤ n`
  have hr₁n : r₁ ≤ n := by
    obtain ⟨e, heW⟩ := Set.nonempty_iff_ne_empty.mpr hW₂ne
    have he𝓗 : e ∈ 𝓗 := nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub (hB.hW₂sub heW)))
    have h1 : (r₁ : ℝ) < (edgeSize e : ℝ) := hsize ⟨e, he𝓗⟩
    have h2 : edgeSize e ≤ n := edgeSize_le e
    have h3 : (r₁ : ℝ) < (n : ℝ) := lt_of_lt_of_le h1 (by exact_mod_cast h2)
    exact_mod_cast le_of_lt h3
  have hr₃n : r₃ ≤ n := by
    rcases hB.hW₂thr with hemp | ⟨e, he, heq⟩
    · exact absurd hemp hW₂ne
    · rw [← heq]; exact edgeSize_le e
  -- `hsize₃`
  have hsize₃ : ∀ e : case2H3med r₁ r₀ 𝓗 H₃, r₃ ≤ edgeSize (e : Set (Fin n)) := by
    intro e
    have heH₃ : (e : Set (Fin n)) ∈ H₃ := e.2.1
    have he𝓗 : (e : Set (Fin n)) ∈ 𝓗 := hB.hH₃sub heH₃
    by_cases hh : β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ)
    · exact_mod_cast (le_trans hbig3 hh)
    · have hnh : (e : Set (Fin n)) ∈ nonHuge 𝓗 β := ⟨he𝓗, hh⟩
      have h1 : (e : Set (Fin n)) ∈ Good₁ ∪ Left₁ := by rw [hB.hpart₁]; exact hnh
      have hnotG₁ : (e : Set (Fin n)) ∉ Good₁ :=
        fun hc => (Set.disjoint_left.mp hB.hdisjH₃G₁) heH₃ hc
      rw [Set.mem_union] at h1
      have hL₁ : (e : Set (Fin n)) ∈ Left₁ := by
        rcases h1 with h | h
        · exact absurd h hnotG₁
        · exact h
      have h2 : (e : Set (Fin n)) ∈ Good₂ ∪ Left₂ := by rw [hB.hpart₂]; exact hL₁
      have hnotG₂ : (e : Set (Fin n)) ∉ Good₂ :=
        fun hc => (Set.disjoint_left.mp hB.hdisjH₃G₂) heH₃ hc
      rw [Set.mem_union] at h2
      have hL₂ : (e : Set (Fin n)) ∈ Left₂ := by
        rcases h2 with h | h
        · exact absurd h hnotG₂
        · exact h
      exact hB.hsize₂ ⟨(e : Set (Fin n)), hB.hL₂sub hL₂⟩ hL₂
  -- the `Corollary65Margins` bundle
  have h5ζ0 : 0 < 5 * ζ / 6 := by linarith
  have h5ζ1 : 5 * ζ / 6 ≤ 1 := by linarith
  have hm : Corollary65Margins Δ₀ ζ r₃ B₀ n Δ :=
    { hζ0 := hζpos
      hζ1 := hζle
      hr2 := hB.hr₃
      hrn := hr₃n
      hΔge := case21_margin_Dge hn hδ0 hδbig hB.hr₃ hr₃big hαδ' hα0 hB₀le
      hΔthr := le_trans (hΔ₀bnd (5 * ζ / 6) h5ζ0 h5ζ1)
        (case21_margin_Dthr hn hδ0 hζpos hζge hC hΔ₀δ)
      hcodeg := case21_margin_hcodeg hn hδ0 hδbig hσ0 hζdef hζpos hζle hζge hB.hr₃
        hr₃big hαδ' hα0 hα1 hB₀le
      hfinal := case21_margin_hfinal hn hδ0 hζpos hζge }
  exact case2_nonExtremal (Δ₀ := Δ₀) hMRe hB hW₂ne hlin hn h2n hβ hσ0 hγ₁σ hσ32 hr₀ h2r₀
    h2r₁ hR hsize hδ0 hδ1 hδV hm hB₀ hmarginA h69m h69b
    (hζdef := hζdef) (hζpos := hζpos) (hk2 := hk2) (hnbig := hnbig) (hσsmall := hσsmall)
    (hsize₃ := hsize₃) h69mσ h69bσ h2βn hCmed hroom1 hroom2 hbudget0 hβc hn1 hσn hγm hKroom
    hslack hβn hφmed hmedb

/-- **`r₃ ≥ 10⁷/δ` in Case 2.1**: since `W₂ ≠ ∅`, `r₃` is the size of an edge
of `W₂`, hence exceeds `r₁`. -/
theorem case21_hr₃big {n r₁ : ℕ} {β δ : ℝ} {𝓗 Left₁ Left₂ W₂ : Hypergraph (Fin n)} {r₃ : ℕ}
    (hL₁sub : Left₁ ⊆ nonHuge 𝓗 β) (hL₂sub : Left₂ ⊆ Left₁) (hW₂sub : W₂ ⊆ Left₂)
    (hW₂thr : W₂ = ∅ ∨ ∃ e : Set (Fin n), e ∈ W₂ ∧ edgeSize e = r₃)
    (hW₂ne : W₂ ≠ ∅) (hr₁δ : 10 ^ 7 / δ ≤ (r₁ : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ)) :
    10 ^ 7 / δ ≤ (r₃ : ℝ) := by
  rcases hW₂thr with hemp | ⟨e, heW, heq⟩
  · exact absurd hemp hW₂ne
  · have he𝓗 : e ∈ 𝓗 := nonHuge_subset 𝓗 β (hL₁sub (hL₂sub (hW₂sub heW)))
    have h1 : (r₁ : ℝ) < (edgeSize e : ℝ) := hsize ⟨e, he𝓗⟩
    rw [heq] at h1
    linarith [h1, hr₁δ]

/-- **`r₃ ≤ βn/4` in Case 2.1**: `r₃ < (1−δ)√n ≤ √n ≤ βn/4`. -/
theorem case21_hbig3 {n r₃ : ℕ} {β δ : ℝ} (hδ0 : 0 < δ)
    (hup : (r₃ : ℝ) < (1 - δ) * Real.sqrt (n : ℝ))
    (hsqrt : 4 * Real.sqrt (n : ℝ) ≤ β * (n : ℝ)) :
    (r₃ : ℝ) ≤ β * (n : ℝ) / 4 := by
  have h1 : (1 - δ) * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    nlinarith [hδ0, Real.sqrt_nonneg (n : ℝ)]
  linarith [hup, h1, hsqrt]

end

end ErdosFaberLovaszConjecture
