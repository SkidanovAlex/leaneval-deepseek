import Mathlib
import Submission.Work.BMF.wt_lem

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary lemmas for `completion_of_sums`

Discretisation error bounds for the trapezoidal weight `Wf`, the exact `B = 1` identity,
the two weighted `L¹` bounds for the Fourier transform, and the numerical verifications
for the two cases of the completion-of-sums argument.
-/

open Polynomial Finset Real Complex MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace

namespace Work.BMF

section Cardinality

/-- Counting the integers of `[a,b]` that lie below a real threshold `X ≥ a`. -/
lemma card_filter_Icc_lt_le (a b : ℕ) (X : ℝ) (hX : (a : ℝ) ≤ X) :
    (((Finset.Icc a b).filter (fun n : ℕ => (n : ℝ) < X)).card : ℝ) ≤ X - a + 1 := by
  have hsub : (Finset.Icc a b).filter (fun n : ℕ => (n : ℝ) < X) ⊆ Finset.Icc a (a + ⌊X - a⌋₊) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    rw [Finset.mem_Icc]
    refine ⟨h1, ?_⟩
    have hcast : ((n - a : ℕ) : ℝ) ≤ X - a := by
      rw [Nat.cast_sub h1]; linarith
    have h7 : n - a ≤ ⌊X - a⌋₊ := Nat.le_floor hcast
    omega
  calc (((Finset.Icc a b).filter (fun n : ℕ => (n : ℝ) < X)).card : ℝ)
      ≤ ((Finset.Icc a (a + ⌊X - a⌋₊)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ((⌊X - a⌋₊ + 1 : ℕ) : ℝ) := by
        congr 1
        rw [Nat.card_Icc]
        omega
    _ ≤ X - a + 1 := by
        push_cast
        linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ X - a)]

/-- Counting the integers of `[a,b]` that lie above a real threshold `X ≤ b`. -/
lemma card_filter_Icc_gt_le (a b : ℕ) (X : ℝ) (hX : X ≤ (b : ℝ)) :
    (((Finset.Icc a b).filter (fun n : ℕ => X < (n : ℝ))).card : ℝ) ≤ (b : ℝ) - X + 1 := by
  have hsub : (Finset.Icc a b).filter (fun n : ℕ => X < (n : ℝ)) ⊆ Finset.Icc ⌈X⌉₊ b := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr (le_of_lt h3), h2⟩
  have hcb : ⌈X⌉₊ ≤ b := Nat.ceil_le.mpr hX
  calc (((Finset.Icc a b).filter (fun n : ℕ => X < (n : ℝ))).card : ℝ)
      ≤ ((Finset.Icc ⌈X⌉₊ b).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ((b - ⌈X⌉₊ + 1 : ℕ) : ℝ) := by
        congr 1
        rw [Nat.card_Icc]
        omega
    _ ≤ (b : ℝ) - X + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hcb, Nat.cast_one]
        linarith [Nat.le_ceil X]

end Cardinality

section ErrorBound

/-- Discrete error bound for the trapezoidal weight `Wf B A0 C0`: the total deviation of
`Wf B A0 C0` from the indicator of `[A0,C0]` on the integer points of `[A0,B0]` is `O(B)`. -/
lemma Wf_sum_error_bound (B : ℝ) (hB : 0 < B) (A0 C0 B0 : ℕ) (hA0C0 : A0 ≤ C0) (hC0B0 : C0 ≤ B0) :
    (∑ n ∈ Finset.Icc A0 C0, (1 - Wf B (A0 : ℝ) (C0 : ℝ) (n : ℝ)))
      + (∑ n ∈ Finset.Icc (C0 + 1) B0, |Wf B (A0 : ℝ) (C0 : ℝ) (n : ℝ)|)
      ≤ 3 / 2 * B + 3 := by
  have hac : (A0 : ℝ) ≤ (C0 : ℝ) := by exact_mod_cast hA0C0
  have hpt1 : ∀ n ∈ Finset.Icc A0 C0,
      (1 - Wf B (A0 : ℝ) (C0 : ℝ) (n : ℝ))
        ≤ (if (n : ℝ) < (A0 : ℝ) + B / 2 then (1 : ℝ) else 0)
          + (if (C0 : ℝ) - B / 2 < (n : ℝ) then (1 : ℝ) else 0) := by
    intro n _
    have hnonneg : 0 ≤ Wf B (A0 : ℝ) (C0 : ℝ) (n : ℝ) := Wf_nonneg B _ _ _ hB hac
    by_cases h1 : (n : ℝ) < (A0 : ℝ) + B / 2
    · rw [if_pos h1]
      have : (0 : ℝ) ≤ (if (C0 : ℝ) - B / 2 < (n : ℝ) then (1 : ℝ) else 0) := by
        split_ifs <;> norm_num
      linarith
    · rw [if_neg h1]
      by_cases h2 : (C0 : ℝ) - B / 2 < (n : ℝ)
      · rw [if_pos h2]; linarith
      · rw [if_neg h2]
        have hone : Wf B (A0 : ℝ) (C0 : ℝ) (n : ℝ) = 1 :=
          Wf_one B _ _ _ hB hac (le_of_not_gt h1) (le_of_not_gt h2)
        rw [hone]; norm_num
  have hsum1 : (∑ n ∈ Finset.Icc A0 C0, (1 - Wf B (A0 : ℝ) (C0 : ℝ) (n : ℝ))) ≤ B + 2 := by
    have hsplit : (∑ n ∈ Finset.Icc A0 C0,
          ((if (n : ℝ) < (A0 : ℝ) + B / 2 then (1 : ℝ) else 0)
            + (if (C0 : ℝ) - B / 2 < (n : ℝ) then (1 : ℝ) else 0)))
        = (∑ n ∈ Finset.Icc A0 C0, (if (n : ℝ) < (A0 : ℝ) + B / 2 then (1 : ℝ) else 0))
          + (∑ n ∈ Finset.Icc A0 C0, (if (C0 : ℝ) - B / 2 < (n : ℝ) then (1 : ℝ) else 0)) :=
      Finset.sum_add_distrib
    have hcard1 : (∑ n ∈ Finset.Icc A0 C0, (if (n : ℝ) < (A0 : ℝ) + B / 2 then (1 : ℝ) else 0))
        = (((Finset.Icc A0 C0).filter (fun n : ℕ => (n : ℝ) < (A0 : ℝ) + B / 2)).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    have hcard2 : (∑ n ∈ Finset.Icc A0 C0, (if (C0 : ℝ) - B / 2 < (n : ℝ) then (1 : ℝ) else 0))
        = (((Finset.Icc A0 C0).filter (fun n : ℕ => (C0 : ℝ) - B / 2 < (n : ℝ))).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    have hb1 : (((Finset.Icc A0 C0).filter (fun n : ℕ => (n : ℝ) < (A0 : ℝ) + B / 2)).card : ℝ)
        ≤ B / 2 + 1 := by
      have := card_filter_Icc_lt_le A0 C0 ((A0 : ℝ) + B / 2) (by linarith)
      linarith [this]
    have hb2 : (((Finset.Icc A0 C0).filter (fun n : ℕ => (C0 : ℝ) - B / 2 < (n : ℝ))).card : ℝ)
        ≤ B / 2 + 1 := by
      have := card_filter_Icc_gt_le A0 C0 ((C0 : ℝ) - B / 2) (by linarith)
      linarith [this]
    calc (∑ n ∈ Finset.Icc A0 C0, (1 - Wf B (A0 : ℝ) (C0 : ℝ) (n : ℝ)))
        ≤ ∑ n ∈ Finset.Icc A0 C0,
            ((if (n : ℝ) < (A0 : ℝ) + B / 2 then (1 : ℝ) else 0)
              + (if (C0 : ℝ) - B / 2 < (n : ℝ) then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum hpt1
      _ = _ := hsplit
      _ ≤ B / 2 + 1 + (B / 2 + 1) := by rw [hcard1, hcard2]; linarith
      _ = B + 2 := by ring
  have hpt2 : ∀ n ∈ Finset.Icc (C0 + 1) B0,
      |Wf B (A0 : ℝ) (C0 : ℝ) (n : ℝ)| ≤ (if (n : ℝ) < (C0 : ℝ) + B / 2 then (1 : ℝ) else 0) := by
    intro n _
    by_cases h1 : (n : ℝ) < (C0 : ℝ) + B / 2
    · rw [if_pos h1]; exact Wf_abs_le_one B _ _ _ hB hac
    · rw [if_neg h1, Wf_zero_right B _ _ _ hB hac (le_of_not_gt h1)]; simp
  have hsum2 : (∑ n ∈ Finset.Icc (C0 + 1) B0, |Wf B (A0 : ℝ) (C0 : ℝ) (n : ℝ)|) ≤ B / 2 + 1 := by
    have hcard3 : (∑ n ∈ Finset.Icc (C0 + 1) B0,
          (if (n : ℝ) < (C0 : ℝ) + B / 2 then (1 : ℝ) else 0))
        = (((Finset.Icc (C0 + 1) B0).filter (fun n : ℕ => (n : ℝ) < (C0 : ℝ) + B / 2)).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    have hsub2 : (Finset.Icc (C0 + 1) B0).filter (fun n : ℕ => (n : ℝ) < (C0 : ℝ) + B / 2)
        ⊆ (Finset.Icc C0 B0).filter (fun n : ℕ => (n : ℝ) < (C0 : ℝ) + B / 2) :=
      Finset.filter_subset_filter _ (Finset.Icc_subset_Icc (by omega) le_rfl)
    have hcard4 : (((Finset.Icc (C0 + 1) B0).filter (fun n : ℕ => (n : ℝ) < (C0 : ℝ) + B / 2)).card : ℝ)
        ≤ (((Finset.Icc C0 B0).filter (fun n : ℕ => (n : ℝ) < (C0 : ℝ) + B / 2)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub2
    have hb3 : (((Finset.Icc C0 B0).filter (fun n : ℕ => (n : ℝ) < (C0 : ℝ) + B / 2)).card : ℝ)
        ≤ B / 2 + 1 := by
      have := card_filter_Icc_lt_le C0 B0 ((C0 : ℝ) + B / 2) (by linarith)
      linarith [this]
    calc (∑ n ∈ Finset.Icc (C0 + 1) B0, |Wf B (A0 : ℝ) (C0 : ℝ) (n : ℝ)|)
        ≤ ∑ n ∈ Finset.Icc (C0 + 1) B0, (if (n : ℝ) < (C0 : ℝ) + B / 2 then (1 : ℝ) else 0) :=
          Finset.sum_le_sum hpt2
      _ = _ := hcard3
      _ ≤ B / 2 + 1 := le_trans hcard4 hb3
  linarith [hsum1, hsum2]

end ErrorBound

section CaseOne

/-- With `B = 1`, `a = A0 - 1/2`, `c = C0 + 1/2`, the weight is exactly the indicator of
`[A0,C0]` at every integer `n ≥ A0`. -/
lemma Wf_one_int (A0 C0 n : ℕ) (hn : A0 ≤ n) :
    Wf 1 ((A0 : ℝ) - 1/2) ((C0 : ℝ) + 1/2) (n : ℝ) = if n ≤ C0 then 1 else 0 := by
  have hn' : (A0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hWf : Wf 1 ((A0 : ℝ) - 1/2) ((C0 : ℝ) + 1/2) (n : ℝ)
      = gH 1 ((n : ℝ) - ((A0 : ℝ) - 1/2)) - gH 1 ((n : ℝ) - ((C0 : ℝ) + 1/2)) := rfl
  have h1 : gH 1 ((n : ℝ) - ((A0 : ℝ) - 1/2)) = 1/2 :=
    gH_eq_half 1 one_pos (by linarith)
  rw [hWf, h1]
  by_cases hcn : n ≤ C0
  · have h2 : gH 1 ((n : ℝ) - ((C0 : ℝ) + 1/2)) = -(1/2) :=
      gH_eq_neg_half 1 one_pos (by
        have : (n : ℝ) ≤ (C0 : ℝ) := by exact_mod_cast hcn
        linarith)
    rw [h2, if_pos hcn]; norm_num
  · have h2 : gH 1 ((n : ℝ) - ((C0 : ℝ) + 1/2)) = 1/2 :=
      gH_eq_half 1 one_pos (by
        have hle : C0 + 1 ≤ n := by omega
        have : (C0 : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hle
        linarith)
    rw [h2, if_neg hcn]; norm_num

/-- For `B = 1`, `a = A0 - 1/2`, `c = C0 + 1/2` the weighted sum over `[A0,B0]` collapses
to the sum over `[A0,C0]`. -/
lemma Wt_one_int_sum (b : ℕ → ℂ) (A0 C0 B0 : ℕ) (hA0C0 : A0 ≤ C0) (hC0B0 : C0 ≤ B0) :
    ∑ n ∈ Finset.Icc A0 B0, b n * Wt 1 ((A0 : ℝ) - 1/2) ((C0 : ℝ) + 1/2) (n : ℝ)
      = ∑ n ∈ Finset.Icc A0 C0, b n := by
  have hpt : ∀ n ∈ Finset.Icc A0 B0,
      b n * Wt 1 ((A0 : ℝ) - 1/2) ((C0 : ℝ) + 1/2) (n : ℝ) = (if n ≤ C0 then b n else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h := Wf_one_int A0 C0 n hn.1
    have hWt : Wt 1 ((A0 : ℝ) - 1/2) ((C0 : ℝ) + 1/2) (n : ℝ)
        = ((Wf 1 ((A0 : ℝ) - 1/2) ((C0 : ℝ) + 1/2) (n : ℝ)) : ℂ) := rfl
    rw [hWt, h]
    by_cases hc : n ≤ C0 <;> simp [hc]
  calc ∑ n ∈ Finset.Icc A0 B0, b n * Wt 1 ((A0 : ℝ) - 1/2) ((C0 : ℝ) + 1/2) (n : ℝ)
      = ∑ n ∈ Finset.Icc A0 B0, (if n ≤ C0 then b n else 0) := Finset.sum_congr rfl hpt
    _ = ∑ n ∈ (Finset.Icc A0 B0).filter (fun n => n ≤ C0), b n := by rw [Finset.sum_filter]
    _ = ∑ n ∈ Finset.Icc A0 C0, b n := by
        congr 1
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hC0B0⟩, h2⟩

end CaseOne


section IntegralBounds

/-- Sharp `L¹` bound for the Fourier transform of the weight on a centred interval:
`∫_{|ξ| ≤ Ξ} |Ŵ(ξ)| ≤ 4√(A·D)` with `A = ∫|W|` and `D = (2Kphi/B)/(4π²)`. -/
lemma setIntegral_FT_norm_le_sqrt (B af cf Ξ : ℝ) (hB : 0 < B) (hac : af ≤ cf) :
    ∫ ξ in Set.Icc (-Ξ) Ξ, ‖FT (Wt B af cf) ξ‖
      ≤ 4 * Real.sqrt ((∫ t, ‖Wt B af cf t‖) * ((2 * Kphi / B) / (4 * Real.pi ^ 2))) := by
  set A : ℝ := ∫ t, ‖Wt B af cf t‖ with hAdef
  set Dl : ℝ := (2 * Kphi / B) / (4 * Real.pi ^ 2) with hDdef
  have hKphi : 0 ≤ Kphi := by rw [Kphi]; exact integral_nonneg (fun x => abs_nonneg _)
  have hA : 0 ≤ A := by rw [hAdef]; exact integral_nonneg (fun t => norm_nonneg _)
  have hD : 0 ≤ Dl := by
    rw [hDdef]; exact div_nonneg (div_nonneg (by linarith) hB.le) (by positivity)
  have hpt : ∀ᵐ ξ : ℝ ∂(volume : MeasureTheory.Measure ℝ),
      ‖FT (Wt B af cf) ξ‖ ≤ min A (Dl / ξ ^ 2) := by
    filter_upwards [MeasureTheory.ae_iff.mpr
      (show volume {ξ : ℝ | ¬ (‖FT (Wt B af cf) ξ‖ ≤ min A (Dl / ξ ^ 2))} = 0 from by
        refine measure_mono_null (fun ξ hξ => ?_) (by simp : volume ({0} : Set ℝ) = 0)
        simp only [Set.mem_setOf_eq, not_le] at hξ
        by_contra hne
        have h1 : ‖FT (Wt B af cf) ξ‖ ≤ Dl / ξ ^ 2 := by
          rw [hDdef, div_div]
          exact FT_decay B af cf hB hac hne
        exact absurd (le_min (norm_FT_le _ ξ) h1) (not_le.mpr hξ))] with ξ hξ
    exact hξ
  have hInt1 : Integrable (fun ξ : ℝ =>
      (Set.Icc (-Ξ) Ξ).indicator (fun ξ => ‖FT (Wt B af cf) ξ‖) ξ) :=
    ((integrable_FT_Wt B af cf hB hac).norm).indicator measurableSet_Icc
  have hae : (fun ξ : ℝ => (Set.Icc (-Ξ) Ξ).indicator (fun ξ => ‖FT (Wt B af cf) ξ‖) ξ)
      ≤ᵐ[volume] (fun ξ : ℝ => min A (Dl / ξ ^ 2)) := by
    filter_upwards [hpt] with ξ hξ
    rw [Set.indicator_apply]
    by_cases h : ξ ∈ Set.Icc (-Ξ) Ξ
    · rw [if_pos h]; exact hξ
    · rw [if_neg h]; exact le_min hA (by positivity)
  calc ∫ ξ in Set.Icc (-Ξ) Ξ, ‖FT (Wt B af cf) ξ‖
      = ∫ ξ : ℝ, (Set.Icc (-Ξ) Ξ).indicator (fun ξ => ‖FT (Wt B af cf) ξ‖) ξ := by
        rw [← MeasureTheory.integral_indicator (μ := volume) measurableSet_Icc
          (f := fun ξ : ℝ => ‖FT (Wt B af cf) ξ‖)]
    _ ≤ ∫ ξ : ℝ, min A (Dl / ξ ^ 2) := integral_mono_ae hInt1 (integrable_min hA hD) hae
    _ ≤ 4 * Real.sqrt (A * Dl) := integral_min_le_sqrt hA hD
    _ = 4 * Real.sqrt ((∫ t, ‖Wt B af cf t‖) * ((2 * Kphi / B) / (4 * Real.pi ^ 2))) := by
        rw [hAdef, hDdef]

/-- Tail bound for the Fourier transform of the weight: `∫_{|ξ| > Ξ} |Ŵ(ξ)| ≤ 2D/Ξ`. -/
lemma setIntegral_FT_norm_tail_le (B af cf Ξ : ℝ) (hB : 0 < B) (hac : af ≤ cf) (hΞ : 0 < Ξ) :
    ∫ ξ in {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt B af cf) ξ‖
      ≤ 2 * ((2 * Kphi / B) / (4 * Real.pi ^ 2)) / Ξ := by
  set Dl : ℝ := (2 * Kphi / B) / (4 * Real.pi ^ 2) with hDdef
  have hKphi : 0 ≤ Kphi := by rw [Kphi]; exact integral_nonneg (fun x => abs_nonneg _)
  have hD : 0 ≤ Dl := by
    rw [hDdef]; exact div_nonneg (div_nonneg (by linarith) hB.le) (by positivity)
  have hpt : ∀ ξ ∈ {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt B af cf) ξ‖ ≤ Dl / ξ ^ 2 := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := by
      intro h0
      rw [h0] at hξ
      simp at hξ
      linarith
    rw [hDdef, div_div]
    exact FT_decay B af cf hB hac hξ0
  have hae : (fun ξ : ℝ => {ξ : ℝ | Ξ < |ξ|}.indicator (fun ξ => ‖FT (Wt B af cf) ξ‖) ξ)
      ≤ᵐ[volume] (fun ξ : ℝ => Dl * ((1 : ℝ) / ξ ^ 2
        * (Set.Ioi Ξ).indicator (fun _ => (1 : ℝ)) |ξ|)) := by
    filter_upwards with ξ
    simp only [Set.indicator_apply]
    by_cases h : Ξ < |ξ|
    · have h1 : ξ ∈ {ξ : ℝ | Ξ < |ξ|} := h
      have h2 : |ξ| ∈ Set.Ioi Ξ := h
      rw [if_pos h1, if_pos h2, mul_one]
      simpa only [div_eq_mul_inv, one_mul] using hpt ξ h1
    · have h1 : ξ ∉ {ξ : ℝ | Ξ < |ξ|} := h
      rw [if_neg h1]
      have h2 : 0 ≤ (if |ξ| ∈ Set.Ioi Ξ then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      exact mul_nonneg hD (mul_nonneg (by positivity) h2)
  have hmeas : MeasurableSet {ξ : ℝ | Ξ < |ξ|} := by measurability
  calc ∫ ξ in {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt B af cf) ξ‖
      = ∫ ξ : ℝ, {ξ : ℝ | Ξ < |ξ|}.indicator (fun ξ => ‖FT (Wt B af cf) ξ‖) ξ := by
        rw [← MeasureTheory.integral_indicator (μ := volume) hmeas
          (f := fun ξ : ℝ => ‖FT (Wt B af cf) ξ‖)]
    _ ≤ ∫ ξ : ℝ, Dl * ((1 : ℝ) / ξ ^ 2 * (Set.Ioi Ξ).indicator (fun _ => (1 : ℝ)) |ξ|) :=
        integral_mono_of_nonneg (Eventually.of_forall (fun ξ => by
          rw [Set.indicator_apply]; split_ifs <;> simp [norm_nonneg]))
          (integrable_tail_inv_sq Dl Ξ hD hΞ) hae
    _ = Dl * (2 / Ξ) := by
        rw [MeasureTheory.integral_const_mul, integral_tail_inv_sq Ξ hΞ]
    _ = 2 * ((2 * Kphi / B) / (4 * Real.pi ^ 2)) / Ξ := by rw [hDdef]; ring

end IntegralBounds

end Work.BMF
