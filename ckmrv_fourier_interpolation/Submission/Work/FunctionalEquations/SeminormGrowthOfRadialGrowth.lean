import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.SeminormLeOfRadialBounds

/-!
# Polynomial growth of the Schwartz seminorms from radial-derivative growth

This file proves `Work.FunctionalEquations.SeminormGrowthOfRadialGrowth`: the last
sentence of CKMRV Theorem 3.1, namely that polynomial growth of the *radial* seminorms
of the coefficient functions transports to polynomial growth of Mathlib's full Schwartz
seminorms.

The analytic input is `Work.FunctionalEquations.SeminormLeOfRadialBounds`, which bounds
the `(k, l)` Schwartz seminorm of a radial Schwartz function by a universal multiple of
the sum of two families of radial-derivative bounds `B j`: one weighted by `‖x‖ ^ k`
for `j ≤ l`, and one unweighted for `j ≤ 2 * l`.  The remaining content here is purely
bookkeeping: for a fixed pair `(k, l)` there are finitely many orders `j ≤ 2 * l`, the
hypothesis `h` (taken at `(k, j)`, and at `(0, j)` for the unweighted family) supplies
for each of them a polynomial bound `C j * (m + 1) ^ (N j)`, and a sum of finitely many
such polynomials is again bounded by a single constant times a single power of `m + 1`.

## Main result

* `Work.FunctionalEquations.SeminormGrowthOfRadialGrowth`
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

theorem SeminormGrowthOfRadialGrowth {n : ℕ} [NeZero n] {k₀ : ℕ}
    (basis : SampleIdx k₀ → RSch n)
    (h : ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀) (j : Fin 4) (x : E n),
      ‖x‖ ^ k * ‖radialDeriv ℓ (⇑(basis (m, j)).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀) (j : Fin 4),
      (SchwartzMap.seminorm ℂ k l) (basis (m, j)).1 ≤ C * ((m.1 : ℝ) + 1) ^ N := by
  intro k l
  obtain ⟨C0, hC00, hmain⟩ := SeminormLeOfRadialBounds (n := n) k l
  choose Cw Nw hCw using fun t : ℕ => h k t
  choose Cu Nu hCu using fun t : ℕ => h 0 t
  set N : ℕ := ∑ t ∈ Finset.range (2 * l + 1), (Nw t + Nu t) with hNdef
  refine ⟨C0 * ((∑ t ∈ Finset.range (l + 1), (Cw t + Cu t))
      + (∑ t ∈ Finset.range (2 * l + 1), (Cw t + Cu t))), N, ?_, ?_⟩
  · apply mul_nonneg hC00
    exact add_nonneg (Finset.sum_nonneg fun t _ => add_nonneg (hCw t).1 (hCu t).1)
      (Finset.sum_nonneg fun t _ => add_nonneg (hCw t).1 (hCu t).1)
  · intro m j
    set p : ℝ := (m.1 : ℝ) + 1 with hp
    have hp1 : 1 ≤ p := by
      have h0 : (0 : ℝ) ≤ (m.1 : ℝ) := Nat.cast_nonneg _
      rw [hp]; linarith
    have hp0 : (0:ℝ) ≤ p := le_trans zero_le_one hp1
    have hNle : ∀ t, t ∈ Finset.range (2*l+1) → Nw t ≤ N ∧ Nu t ≤ N := by
      intro t ht
      have hmem : Nw t + Nu t ≤ N := by
        rw [hNdef]
        exact Finset.single_le_sum (f := fun t => Nw t + Nu t) (fun i _ => Nat.zero_le _) ht
      exact ⟨le_trans (Nat.le_add_right _ _) hmem, le_trans (Nat.le_add_left _ _) hmem⟩
    have hb1 : ∀ t, t ≤ l → ∀ x, ‖x‖^k * ‖radialDeriv t (⇑(basis (m,j)).1) x‖
        ≤ Cw t * p^(Nw t) + Cu t * p^(Nu t) := by
      intro t ht x
      have h1 := (hCw t).2 m j x
      rw [← hp] at h1
      have h2 : 0 ≤ Cu t * p^(Nu t) := mul_nonneg (hCu t).1 (pow_nonneg hp0 _)
      exact le_trans h1 (le_add_of_nonneg_right h2)
    have hb2 : ∀ t, t ≤ 2*l → ∀ x, ‖radialDeriv t (⇑(basis (m,j)).1) x‖
        ≤ Cw t * p^(Nw t) + Cu t * p^(Nu t) := by
      intro t ht x
      have h2 := (hCu t).2 m j x
      rw [← hp] at h2
      have h3 : ‖radialDeriv t (⇑(basis (m,j)).1) x‖ ≤ Cu t * p^(Nu t) := by simpa using h2
      have h4 : 0 ≤ Cw t * p^(Nw t) := mul_nonneg (hCw t).1 (pow_nonneg hp0 _)
      exact le_trans h3 (le_add_of_nonneg_left h4)
    have key := hmain (basis (m,j)).1 (basis (m,j)).2
        (fun t => Cw t * p^(Nw t) + Cu t * p^(Nu t)) hb1 hb2
    have hkey2 : ∀ s : Finset ℕ, (∀ t ∈ s, t ∈ Finset.range (2*l+1)) →
        (∑ t ∈ s, (Cw t * p^(Nw t) + Cu t * p^(Nu t)))
          ≤ (∑ t ∈ s, (Cw t + Cu t)) * p^N := by
      intro s hs
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro t ht
      have hNt := hNle t (hs t ht)
      have e1 : Cw t * p^(Nw t) ≤ Cw t * p^N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 hNt.1) (hCw t).1
      have e2 : Cu t * p^(Nu t) ≤ Cu t * p^N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 hNt.2) (hCu t).1
      calc Cw t * p^(Nw t) + Cu t * p^(Nu t) ≤ Cw t * p^N + Cu t * p^N := add_le_add e1 e2
        _ = (Cw t + Cu t) * p^N := by ring
    have hl := hkey2 (Finset.range (l+1))
      (fun t ht => Finset.mem_range.mpr (by have := Finset.mem_range.mp ht; omega))
    have h2l := hkey2 (Finset.range (2*l+1)) (fun t ht => ht)
    have hsum : (∑ t ∈ Finset.range (l+1), (Cw t * p^(Nw t) + Cu t * p^(Nu t)))
        + (∑ t ∈ Finset.range (2*l+1), (Cw t * p^(Nw t) + Cu t * p^(Nu t)))
        ≤ ((∑ t ∈ Finset.range (l+1), (Cw t + Cu t))
          + (∑ t ∈ Finset.range (2*l+1), (Cw t + Cu t))) * p^N := by
      rw [add_mul]
      exact add_le_add hl h2l
    calc (SchwartzMap.seminorm ℂ k l) (basis (m,j)).1
        ≤ C0 * ((∑ t ∈ Finset.range (l+1), (Cw t * p^(Nw t) + Cu t * p^(Nu t)))
            + (∑ t ∈ Finset.range (2*l+1), (Cw t * p^(Nw t) + Cu t * p^(Nu t)))) := key
      _ ≤ C0 * (((∑ t ∈ Finset.range (l+1), (Cw t + Cu t))
            + (∑ t ∈ Finset.range (2*l+1), (Cw t + Cu t))) * p^N) :=
            mul_le_mul_of_nonneg_left hsum hC00
      _ = C0 * ((∑ t ∈ Finset.range (l+1), (Cw t + Cu t))
            + (∑ t ∈ Finset.range (2*l+1), (Cw t + Cu t))) * p^N := by ring

end Work.FunctionalEquations
