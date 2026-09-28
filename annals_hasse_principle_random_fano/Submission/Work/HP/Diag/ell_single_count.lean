import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.FM3.ell_two_count_free

/-!
# `Work.HP.Diag.ell_single_count`

The paper's Lemma `ℓ_r(X)` (Browning–Le Boudec–Sawin, §3.3) for `r = 2`, in the single-vector
form used by the diagonal estimates:

`#{x ∈ ℤ^{n+1} : x ≠ 0, ‖x‖ ≤ X, 𝔡₂(x) ≤ Δ} ≪ X² Δⁿ log(2Δ)`.

This is the same statement as `Work.HP.FM3.ell_two_count_free` (the only difference being the
description of the condition `x ≠ 0` as `0 < eNorm x`), so the proof is a one-line reference.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.Diag

theorem ell_single_count (n : ℕ) (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Δ : ℝ, 1 ≤ X → 1 ≤ Δ →
      (({x : Fin (n + 1) → ℤ | 0 < eNorm x ∧ eNorm x ≤ X ∧
          dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Δ} : Set (Fin (n + 1) → ℤ)).ncard : ℝ)
        ≤ K * X ^ 2 * Δ ^ n * Real.log (2 * Δ) := by
  obtain ⟨K, hK, h⟩ := FM3.ell_two_count_free n hn
  refine ⟨K, hK, fun X Δ hX hΔ => ?_⟩
  have hset : ({x : Fin (n + 1) → ℤ | 0 < eNorm x ∧ eNorm x ≤ X ∧
        dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Δ} : Set (Fin (n + 1) → ℤ))
      = {x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ X ∧
          dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Δ} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h2, h3⟩
      intro h0
      rw [h0] at h1
      simp [eNorm] at h1
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h2, h3⟩
      by_contra h0
      have hzero : eNorm x = 0 := le_antisymm (le_of_not_gt h0) (Real.sqrt_nonneg _)
      apply h1
      funext i
      have habs : |(x i : ℝ)| ≤ eNorm x := by
        rw [eNorm, Real.le_sqrt (abs_nonneg _) (by positivity), sq_abs]
        exact Finset.single_le_sum (fun j _ => sq_nonneg ((x j : ℝ))) (Finset.mem_univ i)
      have hle : |(x i : ℝ)| ≤ 0 := by rw [← hzero]; exact habs
      have : (x i : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
      exact_mod_cast this
  rw [hset]
  exact h X Δ hX hΔ

end Work.HP.Diag
