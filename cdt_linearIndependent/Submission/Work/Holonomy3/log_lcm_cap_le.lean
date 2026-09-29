import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.sum_bE_le
import Submission.Work.Holonomy3.lcmUpto_log_le
import Submission.Work.Holonomy3.tauFlat_le_two_sum

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-!
# The `τ♭` denominator estimate for the fine holonomy bound

`Work.Holonomy3.sum_bE_le`, `Work.Holonomy3.lcmUpto_log_le` and
`Work.Holonomy3.tauFlat_le_two_sum` are the three arithmetic inputs; here they are assembled into
the cap `log ∏ [1,…,b_{i,h}E_{i,s}+c] ≤ (m·d·D/2)·(τ♭(b) + η)` for all exponents obeying
`E_{i,s} ≤ i·D + s·mD/d + 3mεD`.
-/

/-! ## Helpers -/

/-- `(m:ℝ) * (d/m) = d` when `m ∣ d`. -/
private lemma cast_mul_div {m d : ℕ} (hmd : m ∣ d) : (m : ℝ) * ((d / m : ℕ) : ℝ) = (d : ℝ) := by
  have h : m * (d / m) = d := by rw [mul_comm]; exact Nat.div_mul_cancel hmd
  calc (m : ℝ) * ((d / m : ℕ) : ℝ) = ((m * (d / m) : ℕ) : ℝ) := by push_cast; ring
    _ = (d : ℝ) := by rw [h]

/-- Over `Fin m × Fin (d/m) × Fin r` the constant `X` sums to `(d·r)·X` when `m ∣ d`. -/
private lemma sum_const_three {m r d : ℕ} (hmd : m ∣ d) (X : ℝ) :
    (∑ _i : Fin m, ∑ _s : Fin (d / m), ∑ _h : Fin r, X) = ((d : ℝ) * r) * X := by
  have hcast := cast_mul_div (m := m) (d := d) hmd
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hcast]; ring

/-- `log` of the lcm product is the sum of the logs. -/
private lemma log_prod_lcm {m r d c : ℕ} (b : Fin m → Fin r → ℕ) (E : Fin m → Fin (d / m) → ℕ) :
    Real.log (∏ i : Fin m, ∏ s : Fin (d / m), ∏ h : Fin r,
        ((Submission.CDTPlan.lcmUpto (b i h * E i s + c) : ℕ) : ℝ))
      = ∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r,
          Real.log ((Submission.CDTPlan.lcmUpto (b i h * E i s + c) : ℕ) : ℝ) := by
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [Real.log_prod]
      intro h _
      exact_mod_cast Nat.lcmUpto_ne_zero _
    · intro s _
      exact Finset.prod_ne_zero_iff.mpr fun h _ => by exact_mod_cast Nat.lcmUpto_ne_zero _
  · intro i _
    exact Finset.prod_ne_zero_iff.mpr fun s _ =>
      Finset.prod_ne_zero_iff.mpr fun h _ => by exact_mod_cast Nat.lcmUpto_ne_zero _

/-- Splitting the constant `c` out of the lcm arguments. -/
private lemma sum_args_split {m r d c : ℕ} (hmd : m ∣ d) (b : Fin m → Fin r → ℕ)
    (E : Fin m → Fin (d / m) → ℕ) :
    (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, ((b i h * E i s + c : ℕ) : ℝ))
      = (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, ((b i h * E i s : ℕ) : ℝ))
        + (d : ℝ) * r * c := by
  have hsplit : (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, ((b i h * E i s + c : ℕ) : ℝ))
      = (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, ((b i h * E i s : ℕ) : ℝ))
        + (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, (c : ℝ)) := by
    simp only [Nat.cast_add, Finset.sum_add_distrib]
  rw [hsplit, sum_const_three hmd (c : ℝ)]

/-- Pulling a constant factor out of the threefold sum. -/
private lemma sum_mul_three {m r d : ℕ} (a : ℝ) (f : Fin m → Fin (d / m) → Fin r → ℝ) :
    (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, a * f i s h)
      = a * (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, f i s h) := by
  simp only [Finset.mul_sum]

theorem log_lcm_cap_le {m r : ℕ} (hm : 0 < m) (b : Fin m → Fin r → ℕ)
    (hb : Submission.CDTPlan.ColumnShape b) (c : ℕ) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → m ∣ d →
      ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ E : Fin m → Fin (d / m) → ℕ,
      (∀ i s, (E i s : ℝ) ≤ (i.1 : ℝ) * D + (s.1 : ℝ) * m * D / d + 3 * m * ε * D) →
      Real.log (∏ i, ∏ s : Fin (d / m), ∏ h, ((Submission.CDTPlan.lcmUpto (b i h * E i s + c) : ℕ) : ℝ))
        ≤ ((m : ℝ) * d * D / 2) * (Submission.CDTPlan.tauFlat b + η) := by
  intro η hη
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  -- the total `S` of the row sums
  set S : ℝ := ∑ i : Fin m, (Submission.CDTPlan.rowSum b i : ℝ) with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hS1 : (0 : ℝ) < S + 1 := by linarith
  -- the prime-number-theorem slack
  set δ : ℝ := min 1 (η / (16 * (S + 1))) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ0 : 0 ≤ δ := le_of_lt hδpos
  have hδle1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδ2S : δ * (2 * S) ≤ η / 4 := by
    have h1 : δ ≤ η / (16 * (S + 1)) := by rw [hδdef]; exact min_le_right _ _
    calc δ * (2 * S) ≤ (η / (16 * (S + 1))) * (2 * S) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = η * (2 * S) / (16 * (S + 1)) := by ring
      _ ≤ η / 4 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (S + 1))]
          nlinarith [hη.le, hS0]
  obtain ⟨K, hK⟩ := lcmUpto_log_le δ hδpos
  set Z : ℕ := Nat.ceil ((8 * (r : ℝ) * c + 4 * K * r) / ((m : ℝ) * η)) with hZdef
  refine ⟨min 1 (m * η / (48 * (S + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  refine ⟨max m 1, ?_⟩
  intro d hd hmd
  have hdm : m ≤ d := le_trans (le_max_left m 1) hd
  have hd1 : 1 ≤ d := le_trans (le_max_right m 1) hd
  refine ⟨max 1 Z, ?_⟩
  intro D hDle
  have hD1 : 1 ≤ D := le_trans (le_max_left 1 Z) hDle
  have hmηpos : 0 < (m : ℝ) * η := mul_pos hmR hη
  have hDth : (8 * (r : ℝ) * c + 4 * K * r) / ((m : ℝ) * η) ≤ (D : ℝ) := by
    have h1 : (Z : ℝ) ≤ (D : ℝ) := by
      have h : Z ≤ max 1 Z := le_max_right 1 Z
      exact_mod_cast le_trans h hDle
    have h2 : (8 * (r : ℝ) * c + 4 * K * r) / ((m : ℝ) * η) ≤ (Z : ℝ) := by
      rw [hZdef]; exact Nat.le_ceil _
    linarith
  have hDbig : 8 * (r : ℝ) * c + 4 * K * r ≤ (m : ℝ) * (D : ℝ) * η := by
    have h := mul_le_mul_of_nonneg_right hDth (le_of_lt hmηpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hmηpos)] at h
    nlinarith [h]
  intro ε hε hεlt E hE
  -- absorption of `ε`
  have hεS : 6 * ε * S ≤ (m : ℝ) * η / 8 := by
    have hεle : ε ≤ m * η / (48 * (S + 1)) := le_trans (le_of_lt hεlt) (min_le_right _ _)
    calc 6 * ε * S ≤ 6 * (m * η / (48 * (S + 1))) * S := by
          apply mul_le_mul_of_nonneg_right _ hS0
          linarith
      _ = (m * η) * (6 * S / (48 * (S + 1))) := by ring
      _ ≤ (m * η) * (1 / 8) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 48 * (S + 1))]
          linarith [hS0]
      _ = (m : ℝ) * η / 8 := by ring
  -- absorption of `τ♭`
  have hT2 : Submission.CDTPlan.tauFlat b ≤ 2 * S := by
    have h := tauFlat_le_two_sum hm b
    rwa [← hSdef] at h
  have hδT : δ * Submission.CDTPlan.tauFlat b ≤ η / 4 := by
    have h1 : δ * Submission.CDTPlan.tauFlat b ≤ δ * (2 * S) :=
      mul_le_mul_of_nonneg_left hT2 hδ0
    linarith [hδ2S]
  -- log of the product
  have hlog := log_prod_lcm (c := c) b E
  have hpt : ∀ (i : Fin m) (s : Fin (d / m)) (h : Fin r),
      Real.log ((Submission.CDTPlan.lcmUpto (b i h * E i s + c) : ℕ) : ℝ)
        ≤ (1 + δ) * ((b i h * E i s + c : ℕ) : ℝ) + K := fun i s h => hK _
  have hsum1 : (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r,
        Real.log ((Submission.CDTPlan.lcmUpto (b i h * E i s + c) : ℕ) : ℝ))
      ≤ (1 + δ) * ((∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, ((b i h * E i s : ℕ) : ℝ))
          + (d : ℝ) * r * c) + K * ((d : ℝ) * r) := by
    calc (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r,
          Real.log ((Submission.CDTPlan.lcmUpto (b i h * E i s + c) : ℕ) : ℝ))
        ≤ ∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r,
            ((1 + δ) * ((b i h * E i s + c : ℕ) : ℝ) + K) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro s _
          exact Finset.sum_le_sum fun h _ => hpt i s h
      _ = (1 + δ) * (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r,
              ((b i h * E i s + c : ℕ) : ℝ))
            + K * (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, (1 : ℝ)) := by
          simp only [Finset.sum_add_distrib]
          rw [sum_mul_three (1 + δ) (fun i s h => ((b i h * E i s + c : ℕ) : ℝ)),
            sum_const_three hmd K, sum_const_three hmd (1 : ℝ), mul_one]
          ring
      _ = (1 + δ) * ((∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, ((b i h * E i s : ℕ) : ℝ))
            + (d : ℝ) * r * c) + K * ((d : ℝ) * r) := by
          rw [sum_args_split hmd b E, sum_const_three hmd (1 : ℝ)]
          ring
  -- the algebraic core
  have hA : (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, ((b i h * E i s : ℕ) : ℝ))
      ≤ ((m : ℝ) * d * D / 2) * Submission.CDTPlan.tauFlat b - (D / 2) * S
        + 3 * d * D * ε * S := by
    rw [hSdef]
    exact sum_bE_le hm hmd hdm b ε E hE
  -- final arithmetic
  have hP0 : (0 : ℝ) ≤ (m : ℝ) * d * D / 2 := by positivity
  have hfin : (1 + δ) * ((∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, ((b i h * E i s : ℕ) : ℝ))
        + (d : ℝ) * r * c) + K * ((d : ℝ) * r)
      ≤ ((m : ℝ) * d * D / 2) * (Submission.CDTPlan.tauFlat b + η) := by
    have hstepA : (1 + δ) * ((∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r,
            ((b i h * E i s : ℕ) : ℝ)) + (d : ℝ) * r * c) + K * ((d : ℝ) * r)
        ≤ (1 + δ) * ((((m : ℝ) * d * D / 2) * Submission.CDTPlan.tauFlat b - (D / 2) * S
            + 3 * d * D * ε * S) + (d : ℝ) * r * c) + K * ((d : ℝ) * r) := by
      have h1 : (∑ i : Fin m, ∑ s : Fin (d / m), ∑ h : Fin r, ((b i h * E i s : ℕ) : ℝ))
            + (d : ℝ) * r * c
          ≤ (((m : ℝ) * d * D / 2) * Submission.CDTPlan.tauFlat b - (D / 2) * S
            + 3 * d * D * ε * S) + (d : ℝ) * r * c := add_le_add hA le_rfl
      exact add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + δ)) le_rfl
    refine le_trans hstepA ?_
    have hkey : (1 + δ) * ((((m : ℝ) * d * D / 2) * Submission.CDTPlan.tauFlat b - (D / 2) * S
            + 3 * d * D * ε * S) + (d : ℝ) * r * c) + K * ((d : ℝ) * r)
        = ((m : ℝ) * d * D / 2) * Submission.CDTPlan.tauFlat b
          + δ * (((m : ℝ) * d * D / 2) * Submission.CDTPlan.tauFlat b)
          - (1 + δ) * ((D / 2) * S) + (1 + δ) * (3 * d * D * ε * S)
          + (1 + δ) * ((d : ℝ) * r * c) + K * ((d : ℝ) * r) := by ring
    rw [hkey, show ((m : ℝ) * d * D / 2) * (Submission.CDTPlan.tauFlat b + η)
        = ((m : ℝ) * d * D / 2) * Submission.CDTPlan.tauFlat b + ((m : ℝ) * d * D / 2) * η
        from by ring]
    have h1 : δ * (((m : ℝ) * d * D / 2) * Submission.CDTPlan.tauFlat b)
        ≤ ((m : ℝ) * d * D / 2) * (η / 4) := by
      have h := mul_le_mul_of_nonneg_left hδT hP0
      calc δ * (((m : ℝ) * d * D / 2) * Submission.CDTPlan.tauFlat b)
          = ((m : ℝ) * d * D / 2) * (δ * Submission.CDTPlan.tauFlat b) := by ring
        _ ≤ ((m : ℝ) * d * D / 2) * (η / 4) := h
    have h2 : (1 + δ) * (3 * d * D * ε * S) ≤ ((m : ℝ) * d * D / 2) * (η / 4) := by
      calc (1 + δ) * (3 * d * D * ε * S) ≤ 2 * (3 * d * D * ε * S) :=
            mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) + δ ≤ 2) (by positivity)
        _ = 6 * ε * S * ((d : ℝ) * D) := by ring
        _ ≤ ((m : ℝ) * η / 8) * ((d : ℝ) * D) :=
            mul_le_mul_of_nonneg_right hεS (by positivity)
        _ = ((m : ℝ) * d * D / 2) * (η / 4) := by ring
    have h3 : (1 + δ) * ((d : ℝ) * r * c) + K * ((d : ℝ) * r)
        ≤ ((m : ℝ) * d * D / 2) * (η / 2) := by
      have hb : 2 * (r : ℝ) * c + K * (r : ℝ) ≤ (m : ℝ) * D * η / 4 := by linarith [hDbig]
      calc (1 + δ) * ((d : ℝ) * r * c) + K * ((d : ℝ) * r)
          ≤ 2 * ((d : ℝ) * r * c) + K * ((d : ℝ) * r) := by
            have hmul := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) + δ ≤ 2)
              (by positivity : (0 : ℝ) ≤ (d : ℝ) * r * c)
            linarith [hmul]
        _ = (d : ℝ) * (2 * (r : ℝ) * c + K * (r : ℝ)) := by ring
        _ ≤ (d : ℝ) * ((m : ℝ) * D * η / 4) := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = ((m : ℝ) * d * D / 2) * (η / 2) := by ring
    have hneg : (0 : ℝ) ≤ (1 + δ) * ((D / 2) * S) := by positivity
    nlinarith [h1, h2, h3, hneg]
  refine le_trans ?_ hfin
  rw [hlog]
  exact hsum1

end Work.Holonomy3
