/-
# The bad (non-narrow) scales of the linear lacunary analysis are bounded at bounded heights

`Work.KMTAreas.A7.Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n` is the predicate "the scale `n` is *core* but not
*narrow*" (`core ∧ ¬ Farey`), i.e. one of the scales at which the Ionescu--Wainger endpoint bound for
narrow symbols cannot be invoked.  The existing bound
`Work.KMTAreas.A7.exists_Lnat_le_of_bad` shows that on the bad scales the loss scale
`Lnat l₁ l₂ k₁ k₂` is bounded, but only under the hypothesis `ρ * C₀ ≤ 1/2`, which is *essential* to
its proof (it turns `2^{ρ · heightScale C₀ N}` into `√(Log N + 2)`).

At **bounded heights** (`Lnat l₁ l₂ k₁ k₂ ≤ B₀`) no such smallness is needed: `¬ Farey` gives

  `Log N < Cρc · 2^{ρ l₁} + 1 + k₁ ≤ Cρc · 2^{ρ B₀} + 1 + B₀`,

an upper bound on `Log N` depending only on `(ρ, B₀, Cρc)`, hence an upper bound on `N` — and a
`Λ`-lacunary sequence exceeds any fixed threshold after a bounded number of indices
(`Work.KMTAreas.A7.lacunary_index_bound`).  This is exactly the form of the bad-scale step that the
*linear* lacunary variational estimates need in order to be stated for **all** `0 < ρ ≤ 1` at
bounded heights (the paper's §8 `(lin-1)`, `(lin-2)`), where the bad scales are then finitely many
single scales absorbed by the crude single-scale bounds.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpAux
import Submission.Work.KMTAreas.A7.lacunary_index_bound

set_option autoImplicit false

namespace Work.KMTPlan.A6.PieceBoundedH

open PointwiseErgodicTheorems
open Work.Analysis.EndVar

/-- `2 ≤ splitCut ρ L`: the scale split is at least `2`. -/
theorem two_le_splitCut (ρ : ℝ) (L : ℕ) : 2 ≤ Work.KMTAreas.A7.splitCut ρ L := by
  have h1 : 1 ≤ 2 ^ Work.Analysis.EndVar.scaleCount 1 ρ L :=
    Nat.one_le_two_pow
  rw [Work.KMTAreas.A7.splitCut]
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ Work.Analysis.EndVar.scaleCount 1 ρ L) :=
        Nat.pow_le_pow_right (by norm_num) h1

/-- **The bad scales are bounded at bounded heights.**  For every `0 < ρ`, `C₀ ≥ 1`, `3 ≤ Cρc`,
every `Λ > 1` and every height bound `B₀` there is `n₀ : ℕ`, depending only on
`ρ, C₀, Cρc, Λ, B₀`, such that for every `Λ`-lacunary sequence `a ≥ 1` and every quadruple with
`Lnat l₁ l₂ k₁ k₂ ≤ B₀`, no index `n ≥ n₀` is a bad scale. -/
theorem badScales_bounded_of_height (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (Cρc : ℝ)
    (hCρc : 3 ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ) (B₀ : ℕ) :
    ∃ n₀ : ℕ, ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ),
      Work.KMTAreas.A7.Lnat l₁ l₂ k₁ k₂ ≤ B₀ →
      ∀ n : ℕ, n₀ ≤ n → ¬ Work.KMTAreas.A7.Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n := by
  -- the thresholds: the `Log N` bound `T`, the scale bound `X = 2^{T+2}`, the index bound `n₀`
  set T : ℕ := Nat.ceil (Cρc * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 1 + (B₀ : ℝ)) + 1 with hT
  set X : ℝ := (2 : ℝ) ^ ((T : ℝ) + 2) with hX
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hX]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  set n₀ : ℕ := Nat.ceil (Real.log X / Real.log ((Λ : NNReal) : ℝ) + 2) with hn₀
  refine ⟨n₀, ?_⟩
  intro a ha ha1 l₁ l₂ k₁ k₂ hLnat n hn hbad
  -- the height bounds
  have hl₁ : l₁ ≤ B₀ := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hLnat
  have hk₁ : k₁ ≤ B₀ := le_trans (le_trans (le_max_left k₁ k₂) (le_max_right _ _)) hLnat
  have hl₁r : (l₁ : ℝ) ≤ (B₀ : ℝ) := by exact_mod_cast hl₁
  have hk₁r : (k₁ : ℝ) ≤ (B₀ : ℝ) := by exact_mod_cast hk₁
  -- the scale `N = ⌊a n⌋` and its logarithm `M = Log N`
  set N : ℕ := Nat.floor (a n) with hN
  have hcut : Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N := hbad.1.2.1
  have h2cut := two_le_splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
  have hN3 : 3 ≤ N := by omega
  set M : ℕ := Nat.log 2 N with hM
  have hlogN : logN N = (M : ℤ) := by
    rw [logN, hM, max_eq_left (by omega : 2 ≤ N)]
  -- `¬ Farey` gives the bound `M < Cρc · 2^{ρ l₁} + 1 + k₁`
  have hnotF : Work.KMTAreas.A7.fareyK Cρc ρ l₁ < (k₁ : ℤ) - logN N := by
    have h : ¬ ((k₁ : ℤ) - logN N ≤ Work.KMTAreas.A7.fareyK Cρc ρ l₁) := by
      simpa only [Work.KMTAreas.A7.Farey] using hbad.2
    exact not_le.mp h
  have hfloor : -(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) - 1
      < ((Work.KMTAreas.A7.fareyK Cρc ρ l₁ : ℤ) : ℝ) := by
    have h := Int.lt_floor_add_one (-(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))))
    simp only [Work.KMTAreas.A7.fareyK]
    linarith
  have hcast : ((Work.KMTAreas.A7.fareyK Cρc ρ l₁ : ℤ) : ℝ) < (k₁ : ℝ) - (M : ℝ) := by
    have h := hnotF
    rw [hlogN] at h
    exact_mod_cast h
  have hM_lt : (M : ℝ) < Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + 1 + (k₁ : ℝ) := by linarith
  -- hence `M < T`
  have hrpow : (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (B₀ : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ, hl₁r])
  have hMT : (M : ℝ) < (T : ℝ) := by
    have h1 : Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + 1 + (k₁ : ℝ)
        ≤ Cρc * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 1 + (B₀ : ℝ) := by
      have h2 := mul_le_mul_of_nonneg_left hrpow (by linarith : (0 : ℝ) ≤ Cρc)
      linarith
    have h3 : Cρc * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 1 + (B₀ : ℝ) ≤ (T : ℝ) := by
      rw [hT]
      push_cast
      have := Nat.le_ceil (Cρc * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 1 + (B₀ : ℝ))
      linarith
    linarith
  have hMlt : M < T := by exact_mod_cast hMT
  -- hence `N < 2 ^ T ≤ X`, and then `(a n : ℝ) < X`
  have hNT : N < 2 ^ T := by
    have h1 : N < 2 ^ (M + 1) := by
      rw [hM]
      exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have haX : (a n : ℝ) < X := by
    have hfloor_lt : (a n : ℝ) < ((N : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (a n)
    have hone : ((N : ℕ) : ℝ) + 1 ≤ X := by
      have hN1 : N + 1 ≤ 2 ^ T := by omega
      have h1 : ((N : ℕ) : ℝ) + 1 ≤ ((2 ^ T : ℕ) : ℝ) := by
        have hcast' : ((N + 1 : ℕ) : ℝ) ≤ ((2 ^ T : ℕ) : ℝ) := by exact_mod_cast hN1
        push_cast at hcast' ⊢
        linarith
      have h2 : ((2 ^ T : ℕ) : ℝ) ≤ X := by
        have hcastT : ((2 ^ T : ℕ) : ℝ) = (2 : ℝ) ^ ((T : ℝ)) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast]
          norm_num
        rw [hX, hcastT]
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
        push_cast
        linarith
      linarith
    linarith
  -- the `Λ`-uniform index bound
  obtain ⟨K, hK, hKspec⟩ :=
    Work.KMTAreas.A7.lacunary_index_bound Λ hΛ a ha ha1 X hX1
  have hnK : n < K := hKspec n haX
  have hKn₀ : K ≤ n₀ := by
    rw [hn₀]
    exact_mod_cast (le_trans hK (Nat.le_ceil _))
  omega

end Work.KMTPlan.A6.PieceBoundedH
