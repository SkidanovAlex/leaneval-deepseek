import Mathlib

/-!
# Abel summation against a count, *below* the threshold

`Work.LinnikAreas.sum_mul_exp_neg_le_of_count` (proved in this workspace, used by the Siegel-case
zero sums) bounds `∑ i, m i * exp (-a * lam i)` by `D * lam₁ * exp c * exp ((c - a) * Λ) / (1 - exp (c-a))`
for a set all of whose elements satisfy `lam i ≥ Λ` (`Λ` a *lower* threshold); it needs the count
to grow slower than the weight decays (`c < a`).

This file provides the complementary *upper*-threshold form: for a set whose elements satisfy
`lam i ≤ lam0`, the sum is at most `C * exp B * (lam0 + 1) * exp (max 0 ((B - a) * lam0))`,
with **no** restriction on `B` relative to `a`.  This is the bound needed to use a
`λ₁`-saving count `N(t) ≤ C e^{Bt}` on the *head* `λ ≤ λ₀` of the Abel splitting (where `B` can
exceed the weight exponent `a` for tall height layers).

The proof is the standard fibre decomposition by `⌊λ⌋`: on the fibre `⌊λ⌋ = k` the weight is at
most `e^{-ak}` and the mass is at most `N(k+1) ≤ C e^{B(k+1)}`, so the fibre contributes
`≤ C e^B e^{(B-a)k} ≤ C e^B e^{max 0 ((B-a)λ₀)}`, and there are at most `λ₀+1` fibres.
-/

namespace Work.LinnikAreas

/-- **Abel summation against a count, below the threshold.**  Let `S` be a finite set with
nonnegative weights `m`, exponents `lam ∈ [0, λ₀]`, and counting function
`N(t) = ∑_{lam i ≤ t} m i ≤ C e^{Bt}` for `0 < t ≤ λ₀ + 1`.  Then
`∑_{i∈S} m i e^{-a λ_i} ≤ C e^B (λ₀+1) e^{max 0 ((B-a)λ₀)}`. -/
lemma sum_mul_exp_neg_le_of_count_head {ι : Type*} (S : Finset ι) (m lam : ι → ℝ)
    {a B C lam0 : ℝ} (ha : 0 < a) (hm : ∀ i ∈ S, 0 ≤ m i) (hlam0 : ∀ i ∈ S, 0 ≤ lam i)
    (hlamle : ∀ i ∈ S, lam i ≤ lam0) (hlam0pos : 0 ≤ lam0) (hC : 0 ≤ C)
    (hcount : ∀ t : ℝ, 0 < t → t ≤ lam0 + 1 →
      (∑ i ∈ S.filter (fun i => lam i ≤ t), m i) ≤ C * Real.exp (B * t)) :
    (∑ i ∈ S, m i * Real.exp (-a * lam i))
      ≤ C * Real.exp B * (lam0 + 1) * Real.exp (max 0 ((B - a) * lam0)) := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS]; simp only [Finset.sum_empty]
    positivity
  · have hfib : ∀ i ∈ S, Nat.floor (lam i) ∈ Finset.range (Nat.floor lam0 + 1) := by
      intro i hi
      rw [Finset.mem_range]
      have h1 : Nat.floor (lam i) ≤ Nat.floor lam0 := Nat.floor_mono (hlamle i hi)
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hfib (fun i => m i * Real.exp (-a * lam i))]
    have hperk : ∀ k ∈ Finset.range (Nat.floor lam0 + 1),
        (∑ i ∈ S.filter (fun i => Nat.floor (lam i) = k), m i * Real.exp (-a * lam i))
        ≤ C * Real.exp B * Real.exp (max 0 ((B - a) * lam0)) := by
      intro k hk
      have hkK : k ≤ Nat.floor lam0 := by
        have := Finset.mem_range.mp hk; omega
      set Sf := S.filter (fun i => Nat.floor (lam i) = k) with hSf
      have hSfS : ∀ i ∈ Sf, i ∈ S := fun i hi => (Finset.mem_filter.mp hi).1
      have hw : (∑ i ∈ Sf, m i * Real.exp (-a * lam i))
          ≤ (∑ i ∈ Sf, m i) * Real.exp (-a * (k : ℝ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hgk : Nat.floor (lam i) = k := (Finset.mem_filter.mp hi).2
        have hkl : (k : ℝ) ≤ lam i := by
          rw [← hgk]; exact Nat.floor_le (hlam0 i (hSfS i hi))
        have hexp : Real.exp (-a * lam i) ≤ Real.exp (-a * (k : ℝ)) := by
          rw [Real.exp_le_exp]; nlinarith
        exact mul_le_mul_of_nonneg_left hexp (hm i (hSfS i hi))
      have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hk1le : (k : ℝ) + 1 ≤ lam0 + 1 := by
        have h3 : ((Nat.floor lam0 : ℕ) : ℝ) ≤ lam0 := Nat.floor_le hlam0pos
        have h4 : ((k + 1 : ℕ) : ℝ) ≤ ((Nat.floor lam0 + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : k + 1 ≤ Nat.floor lam0 + 1)
        push_cast at h4
        linarith
      have hsub : Sf ⊆ S.filter (fun i => lam i ≤ (k : ℝ) + 1) := by
        intro i hi
        have hgk : Nat.floor (lam i) = k := (Finset.mem_filter.mp hi).2
        have hlt := Nat.lt_floor_add_one (lam i)
        rw [hgk] at hlt
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, by push_cast; linarith⟩
      have hcnt : (∑ i ∈ Sf, m i) ≤ C * Real.exp (B * ((k : ℝ) + 1)) := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i hiT _ => hm i (Finset.mem_filter.mp hiT).1)) ?_
        exact hcount _ hk1pos hk1le
      refine le_trans (le_trans hw (mul_le_mul_of_nonneg_right hcnt (Real.exp_nonneg _))) ?_
      have hkey : Real.exp (B * ((k : ℝ) + 1)) * Real.exp (-a * (k : ℝ))
          ≤ Real.exp B * Real.exp (max 0 ((B - a) * lam0)) := by
        have hkl : (k : ℝ) ≤ lam0 := by
          have h3 : ((Nat.floor lam0 : ℕ) : ℝ) ≤ lam0 := Nat.floor_le hlam0pos
          exact le_trans (by exact_mod_cast hkK) h3
        have hmax : (B - a) * (k : ℝ) ≤ max 0 ((B - a) * lam0) := by
          by_cases h : 0 ≤ B - a
          · rw [max_eq_right (mul_nonneg h hlam0pos)]
            exact mul_le_mul_of_nonneg_left hkl h
          · rw [max_eq_left (mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge h)) hlam0pos)]
            exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge h)) (by positivity)
        calc Real.exp (B * ((k : ℝ) + 1)) * Real.exp (-a * (k : ℝ))
            = Real.exp (B + (B - a) * (k : ℝ)) := by
              rw [← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp B * Real.exp (max 0 ((B - a) * lam0)) := by
              rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
      calc C * Real.exp (B * ((k : ℝ) + 1)) * Real.exp (-a * (k : ℝ))
          = C * (Real.exp (B * ((k : ℝ) + 1)) * Real.exp (-a * (k : ℝ))) := by ring
        _ ≤ C * (Real.exp B * Real.exp (max 0 ((B - a) * lam0))) :=
            mul_le_mul_of_nonneg_left hkey hC
        _ = C * Real.exp B * Real.exp (max 0 ((B - a) * lam0)) := by ring
    calc (∑ k ∈ Finset.range (Nat.floor lam0 + 1),
          ∑ i ∈ S.filter (fun i => Nat.floor (lam i) = k), m i * Real.exp (-a * lam i))
        ≤ ∑ k ∈ Finset.range (Nat.floor lam0 + 1),
            C * Real.exp B * Real.exp (max 0 ((B - a) * lam0)) := Finset.sum_le_sum hperk
      _ = ((Nat.floor lam0 : ℕ) + 1 : ℝ)
            * (C * Real.exp B * Real.exp (max 0 ((B - a) * lam0))) := by
          rw [Finset.sum_const, Finset.card_range]; push_cast; ring
      _ ≤ (lam0 + 1) * (C * Real.exp B * Real.exp (max 0 ((B - a) * lam0))) := by
          have h1 : ((Nat.floor lam0 : ℕ) : ℝ) ≤ lam0 := Nat.floor_le hlam0pos
          have h2 : (0 : ℝ) ≤ C * Real.exp B * Real.exp (max 0 ((B - a) * lam0)) := by positivity
          nlinarith
      _ = C * Real.exp B * (lam0 + 1) * Real.exp (max 0 ((B - a) * lam0)) := by ring

end Work.LinnikAreas
