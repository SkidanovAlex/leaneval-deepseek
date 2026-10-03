/-
# The bad scales of `Work.KMTAreas.A7.lacunaryBumpVarEstimate` are bounded

`Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n` is the predicate "the scale `n` is *core* but not *narrow*"
(`core ∧ ¬ Farey`), i.e. one of the scales on which the Ionescu–Wainger endpoint bound
`varEst_of_narrow_symbols_twoEndpoints` cannot be invoked.  This module proves that for a
lacunary sequence `a ≥ 1` there are **no** bad scales once the loss scale
`Lnat l₁ l₂ k₁ k₂ = max (l₁,l₂,k₁,k₂)` exceeds a constant depending only on `ρ, C₀, Cρc` -- so
the bad scales can be discarded at the cost of a constant, which is exactly what the
Borel--Cantelli/summability step of the variational assembly needs.

The argument is a squeezing one.  If `n` is bad then, writing `N = ⌊a n⌋`,
`M = Log N = log₂ (max N 2)` and `h = heightScale C₀ N = C₀ LogLog N`,

* `¬ Farey` says `k₁ - M > fareyK Cρc ρ l₁ ≥ -(Cρc 2^{ρ l₁}) - 1`, i.e.
  `M < Cρc 2^{ρ l₁} + 1 + k₁`;
* `core` gives `l₁ ≤ h` and `k₁ ≤ h` (the index set `I^{l₁,l₂,k₁,k₂}` is `{N : l,s₁,s₂ ≤ l_{(N)}}`);
* `ρ·C₀ ≤ 1/2` (the hypothesis `hρC : ρ ≤ 1/(2C₀)`) turns this into
  `2^{ρ l₁} ≤ 2^{ρ h} ≤ √(M+2)`, and `LogLog N = Nat.log 2 (M+2) ≤ logb 2 (M+2)`.

So every bad scale satisfies

  `M < Cρc √(M+2) + C₀ log₂ (M+2) + 1`   and   `Lnat l₁ l₂ k₁ k₂ ≤ h ≤ C₀ log₂ (M+2)`.

Since `√` and `log₂` grow slower than the identity (`Work.KMTAreas.A7.exists_sqrt_logb_lt`), `M`
is bounded by a constant `M₀`, and then `Lnat ≤ C₀ log₂ (M₀ + 2)`.  The bound is uniform in the
lacunary sequence `a` (and in `Λ, l₁, l₂, k₁, k₂`), as required.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpAux
import Submission.Work.KMTAreas.A7.exists_sqrt_logb_lt
import Submission.Work.KMTAreas.A7.two_rpow_heightScale_le_sqrt

namespace Work.KMTAreas.A7

open Work.Analysis.EndVar

/-! ## `Nat.log 2` is dominated by `Real.logb 2` -/

lemma elb_natlog_cast_le_logb (t : ℕ) (ht : 1 ≤ t) :
    ((Nat.log 2 t : ℕ) : ℝ) ≤ Real.logb 2 (t : ℝ) := by
  have h2 : (2 : ℝ) ^ Nat.log 2 t ≤ (t : ℝ) := by
    have := Nat.pow_log_le_self 2 (by omega : t ≠ 0)
    exact_mod_cast this
  calc ((Nat.log 2 t : ℕ) : ℝ)
      = Real.logb 2 ((2 : ℝ) ^ Nat.log 2 t) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
    _ ≤ Real.logb 2 (t : ℝ) := Real.logb_le_logb_of_le (by norm_num) (by positivity) h2

lemma elb_natlog_add_two_le_logb (M : ℕ) :
    ((Nat.log 2 (M + 2) : ℕ) : ℝ) ≤ Real.logb 2 ((M : ℝ) + 2) := by
  have h : ((Nat.log 2 (M + 2) : ℕ) : ℝ) ≤ Real.logb 2 (((M + 2 : ℕ)) : ℝ) :=
    elb_natlog_cast_le_logb (M + 2) (by omega)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

/-! ## The bad scales are bounded -/

theorem exists_Lnat_le_of_bad (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))) (Cρc : ℝ) (hCρc : 3 ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ B : ℕ, ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ),
      (∃ n, Work.KMTAreas.A7.Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n) → Work.KMTAreas.A7.Lnat l₁ l₂ k₁ k₂ ≤ B := by
  -- the real-analytic input: `√(M+2)` and `log₂(M+2)` are dominated by `M`
  obtain ⟨M₀, hM₀⟩ := exists_sqrt_logb_lt Cρc (C₀ : ℝ)
  have hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 2 := by
    have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
    have h2 : (0 : ℝ) < 2 * (C₀ : ℝ) := by linarith
    have h := (le_div_iff₀ h2).mp hρC
    linarith
  refine ⟨Nat.ceil (C₀ * Real.logb 2 ((M₀ : ℝ) + 2)), ?_⟩
  intro a ha ha1 l₁ l₂ k₁ k₂ hbad
  obtain ⟨n, hn⟩ := hbad
  set N : ℕ := Nat.floor (a n) with hNdef
  set M : ℕ := Nat.log 2 (max N 2) with hMdef
  obtain ⟨hin, hcut, hmain⟩ := hn.1
  obtain ⟨hlmax, hk₁, hk₂⟩ := hin
  -- `core` puts every scale below the height scale
  have hLle : Lnat l₁ l₂ k₁ k₂ ≤ heightScale C₀ N := by
    have h1 : l₁ ≤ heightScale C₀ N := by exact_mod_cast (le_trans (le_max_left _ _) hlmax)
    have h2 : l₂ ≤ heightScale C₀ N := by exact_mod_cast (le_trans (le_max_right _ _) hlmax)
    have h3 : k₁ ≤ heightScale C₀ N := by exact_mod_cast hk₁
    have h4 : k₂ ≤ heightScale C₀ N := by exact_mod_cast hk₂
    exact max_le (max_le h1 h2) (max_le h3 h4)
  have hlogN : logN N = (M : ℤ) := by simp only [logN, hMdef]
  -- `¬ Farey` means the window has not yet been resolved
  have hnotF : fareyK Cρc ρ l₁ < (k₁ : ℤ) - logN N := by
    have h : ¬ ((k₁ : ℤ) - logN N ≤ fareyK Cρc ρ l₁) := by simpa only [Farey] using hn.2
    exact not_le.mp h
  have hfloor : -(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) - 1
      < ((fareyK Cρc ρ l₁ : ℤ) : ℝ) := by
    have h := Int.lt_floor_add_one (-(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))))
    simp only [fareyK]
    linarith
  have hcast : ((fareyK Cρc ρ l₁ : ℤ) : ℝ) < (k₁ : ℝ) - (M : ℝ) := by
    have h := hnotF
    rw [hlogN] at h
    exact_mod_cast h
  have hM_lt : (M : ℝ) < Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + 1 + (k₁ : ℝ) := by linarith
  have hl₁h : (l₁ : ℝ) ≤ (heightScale C₀ N : ℝ) := by
    exact_mod_cast (le_trans (le_max_left _ _) hlmax)
  have hk₁h : (k₁ : ℝ) ≤ (heightScale C₀ N : ℝ) := by exact_mod_cast hk₁
  -- `ρ C₀ ≤ 1/2` makes the height scale contribute at most `√(M+2)`
  have hrpow_mono : (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (heightScale C₀ N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ, hl₁h])
  have hrpow_h : (2 : ℝ) ^ (ρ * (heightScale C₀ N : ℝ)) ≤ Real.sqrt ((M : ℝ) + 2) := by
    have h := two_rpow_heightScale_le_sqrt hρ hρC₀ N
    rw [← hMdef] at h
    exact h
  have hsqrt : Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ Cρc * Real.sqrt ((M : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left (hrpow_mono.trans hrpow_h) (by linarith)
  have hlogLog : ((logLogN N : ℕ) : ℝ) ≤ Real.logb 2 ((M : ℝ) + 2) := by
    have h1 : logLogN N = Nat.log 2 (M + 2) := by simp only [logLogN, hMdef]
    rw [h1]
    exact elb_natlog_add_two_le_logb M
  have hk₁_le : (k₁ : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) := by
    have hh : ((heightScale C₀ N : ℕ) : ℝ) = (C₀ : ℝ) * ((logLogN N : ℕ) : ℝ) := by
      simp only [heightScale, Nat.cast_mul]
    calc (k₁ : ℝ) ≤ (heightScale C₀ N : ℝ) := hk₁h
      _ = (C₀ : ℝ) * ((logLogN N : ℕ) : ℝ) := hh
      _ ≤ (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlogLog (by positivity)
  have hMbound : (M : ℝ) < Cρc * Real.sqrt ((M : ℝ) + 2)
      + (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) + 1 := by
    linarith
  -- hence `M` is bounded
  have hMlt : M < M₀ := by
    by_contra hcon
    push_neg at hcon
    have h := hM₀ M hcon
    linarith
  -- and so is the loss scale
  have hfin : ((Lnat l₁ l₂ k₁ k₂ : ℕ) : ℝ)
      ≤ (Nat.ceil (C₀ * Real.logb 2 ((M₀ : ℝ) + 2)) : ℝ) := by
    have h1 : ((Lnat l₁ l₂ k₁ k₂ : ℕ) : ℝ) ≤ ((heightScale C₀ N : ℕ) : ℝ) := by
      exact_mod_cast hLle
    have h2 : ((heightScale C₀ N : ℕ) : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) := by
      have hh : ((heightScale C₀ N : ℕ) : ℝ) = (C₀ : ℝ) * ((logLogN N : ℕ) : ℝ) := by
        simp only [heightScale, Nat.cast_mul]
      rw [hh]
      exact mul_le_mul_of_nonneg_left hlogLog (by positivity)
    have h3 : (M : ℝ) + 2 ≤ (M₀ : ℝ) + 2 := by
      have : (M : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast (le_of_lt hMlt)
      linarith
    have h4 : Real.logb 2 ((M : ℝ) + 2) ≤ Real.logb 2 ((M₀ : ℝ) + 2) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) h3
    have h6 : (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2)
        ≤ (C₀ : ℝ) * Real.logb 2 ((M₀ : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h5 : (C₀ : ℝ) * Real.logb 2 ((M₀ : ℝ) + 2)
        ≤ (Nat.ceil (C₀ * Real.logb 2 ((M₀ : ℝ) + 2)) : ℝ) := Nat.le_ceil _
    linarith
  exact_mod_cast hfin

end Work.KMTAreas.A7
