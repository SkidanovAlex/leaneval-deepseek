import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpGlue
import Submission.Work.KMTAreas.A7Hi.varphitildeNtMultBound

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- Two-endpoint multiplier input for the `g`-side modulated bump at `k₂ ≥ 1`: the signed sums
`∑_{n∈U} ω n · varphitildeNt P d (⌊a n⌋) k₂ t` satisfy the continuous `L^q(ℝ)` multiplier bound
with the same constant `C * (1 + d * k₂)` at `q = 2` and at `q = 2 * k₀`, uniformly in the finite
`U`, the signs `ω`, the lacunary `a` and `t ∈ [1/2,1]`.  This is the `g`-side analogue of the proved
`Work.KMTAreas.A7.multBound_varphiNt_two_endpoints` and is what
`Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints` consumes.  The single-exponent version
(for every `p > 1` at once) exists as `varphitildeNt_mult_bound_k2pos_hi` in
`Submission/Work/KMTAreas/A7Hi/varphitildeNtMultBound.lean` (it builds and is axiom-clean; check the
exact name with `#check`), so this reduction is short: apply it at the exponents `2` and `2 * k₀`
and combine with `Work.KMTAreas.A7.IsLqMultiplierBound.mono` and `lt_max_of_lt_left`, exactly as
`lacunaryBumpGlue.lean` does for the `f`-side.  Do NOT import
`Submission.Work.KMTAreas.A7.lacunaryBumpG_mult_bound_k2pos` (it does not compile) nor
`A7Hi/Gblock.lean` (it does not compile either). -/
theorem LoGMultBoundTwoEndpoints (P : Polynomial ℤ) (d : ℕ) (hd : 2 ≤ d) (hdP : P.natDegree ≤ d)
    (Λ : NNReal) (hΛ : 1 < Λ) (k₀ : ℕ) (hk₀ : 2 ≤ k₀) :
    ∃ C : NNReal, 0 < C ∧ ∀ (k₂ : ℕ) (hk₂ : 1 ≤ k₂) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (U : Finset ℕ) (ω : ℕ → Bool),
      Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal (2 : ℝ))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTAreas.A7.varphitildeNt P d (Nat.floor (a n)) k₂ t ξ) (C * (1 + d * k₂)) ∧
        Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTAreas.A7.varphitildeNt P d (Nat.floor (a n)) k₂ t ξ) (C * (1 + d * k₂)) := by
  have hk₀1 : (1 : ℝ) < 2 * (k₀ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ k₀)
    linarith
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    varphitildeNt_mult_bound_k2pos_hi P d hdP 2 (by norm_num) Λ hΛ
  obtain ⟨Ce, hCepos, hCe⟩ :=
    varphitildeNt_mult_bound_k2pos_hi P d hdP (2 * (k₀ : ℝ)) hk₀1 Λ hΛ
  refine ⟨max C₂ Ce, lt_max_of_lt_left hC₂pos, ?_⟩
  intro k₂ hk₂ t ht a ha ha1 U ω
  have hε : ∀ n : ℕ, ‖(if ω n then (1 : ℂ) else -1)‖ ≤ 1 := by
    intro n
    by_cases h : ω n <;> simp [h]
  have hkn : (0 : NNReal) ≤ (1 + d * k₂) := by positivity
  refine ⟨?_, ?_⟩
  · exact IsLqMultiplierBound.mono (hC₂ k₂ hk₂ t ht a ha ha1 U _ hε)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hkn)
  · exact IsLqMultiplierBound.mono (hCe k₂ hk₂ t ht a ha ha1 U _ hε)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hkn)

end Work.KMTAreas.A7
