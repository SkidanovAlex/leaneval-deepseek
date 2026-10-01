import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.siegelZeroSimple_ldUpper
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.LinnikAreas.DhCapped.twoRealZeroRepelCore
import Submission.Work.LinnikAreas.RealZeroCount.Defs
import Submission.Work.LinnikAreas.RealZeroCount.divisorKernelFinsumBound
import Submission.Work.LinnikAreas.RealZeroCount.reductionOwn
import Submission.Work.LinnikAreas.RealZeroCount.countArith
import Submission.Work.LinnikAreas.RealZeroCount.realZeroCountFinsum_eq_zero_of_nonpos

namespace Work.LinnikAreas

/-- The counting bound with the threshold made explicit in terms of the log-derivative constant
`C`: for every `C` bounding `Re (Λ′/Λ)(σ) ≤ 1/(σ-1) + C` on `(1, 5/4]` for non-principal `χ`, and
every `q ≥ max 3 (⌈exp (C + log 2/2 + 3/2)⌉₊ + 2)`, the multiplicity-weighted count of real zeros
with `λ ≤ t` (`0 ≤ t ≤ log q / 8`) is at most `3/2 + 6t`. -/
theorem realZeroLambdaCountLinear_aux (C : ℝ)
    (hC : ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), ψ ≠ 1 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 →
        (logDeriv (DirichletCharacter.completedLFunction ψ) (σ : ℂ)).re ≤ 1 / (σ - 1) + C) :
    ∀ q : ℕ, max 3 (⌈Real.exp (C + Real.log 2 / 2 + 3 / 2)⌉₊ + 2) ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ t : ℝ, 0 ≤ t → t ≤ Real.log (q : ℝ) / 8 →
          realZeroCountFinsum q χ t ≤ 3 / 2 + 6 * t := by
  intro q hq hqne χ hχ hsq t ht0 htle
  have hq2 : 2 ≤ q := by
    have h3 : 3 ≤ q := le_trans (le_max_left _ _) hq
    omega
  have hLpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlogq_ge : C + Real.log 2 / 2 + 3 / 2 ≤ Real.log (q : ℝ) := by
    have hqge : ⌈Real.exp (C + Real.log 2 / 2 + 3 / 2)⌉₊ + 2 ≤ q :=
      le_trans (le_max_right _ _) hq
    have h1 : Real.exp (C + Real.log 2 / 2 + 3 / 2) ≤
        ((⌈Real.exp (C + Real.log 2 / 2 + 3 / 2)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp (C + Real.log 2 / 2 + 3 / 2)⌉₊ : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (by omega : ⌈Real.exp (C + Real.log 2 / 2 + 3 / 2)⌉₊ ≤ q)
    have hexp : Real.exp (C + Real.log 2 / 2 + 3 / 2) ≤ (q : ℝ) := le_trans h1 h2
    calc C + Real.log 2 / 2 + 3 / 2
        = Real.log (Real.exp (C + Real.log 2 / 2 + 3 / 2)) := (Real.log_exp _).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexp
  rcases lt_or_eq_of_le ht0 with htpos | ht0eq
  · -- main case: `0 < t`
    set δ : ℝ := t / Real.log (q : ℝ) with hδdef
    have hδpos : 0 < δ := div_pos htpos hLpos
    have hδ8 : δ ≤ 1 / 8 := by
      rw [hδdef, div_le_iff₀ hLpos]
      linarith
    have hσ1sub : 1 + 2 * δ - 1 = 2 * δ := by ring
    have hσ1 : 1 ≤ 1 + 2 * δ := by linarith
    have hσ54 : 1 + 2 * δ ≤ 5 / 4 := by linarith
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hψ : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one_of_ne_one' χ hχ
    have hB : (logDeriv (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        ((1 + 2 * δ : ℝ) : ℂ)).re ≤ 1 / ((1 + 2 * δ) - 1) + C := by
      have h := hC χ.conductor χ.primitiveCharacter hψ (1 + 2 * δ) (by linarith) hσ54
      linarith
    have hred : realZeroCountFinsum q χ t ≤
        3 * δ * divisorKernelFinsum q χ (1 + 2 * δ) := by
      rw [hδdef]
      exact ReductionOwn.realZeroCountFinsum_le' hq2 χ hχ htpos
    have hD : divisorKernelFinsum q χ (1 + 2 * δ)
        ≤ 1 / (2 * δ) + C + Real.log ((χ.conductor : ℕ) : ℝ) + Real.log 2 / 2 + 3 / 2 := by
      have h := divisorKernelFinsum_le χ hχ hσ1 hB
      rw [hσ1sub] at h
      linarith
    have hkey : realZeroCountFinsum q χ t * (1 / (3 * δ))
        ≤ 1 / (2 * δ) + C + Real.log ((χ.conductor : ℕ) : ℝ) + Real.log 2 / 2 + 3 / 2 := by
      have h3δpos : 0 < 3 * δ := by linarith
      calc realZeroCountFinsum q χ t * (1 / (3 * δ))
          = realZeroCountFinsum q χ t / (3 * δ) := by ring
        _ ≤ (3 * δ * divisorKernelFinsum q χ (1 + 2 * δ)) / (3 * δ) :=
              div_le_div_of_nonneg_right hred h3δpos.le
        _ = divisorKernelFinsum q χ (1 + 2 * δ) := by field_simp
        _ ≤ 1 / (2 * δ) + C + Real.log ((χ.conductor : ℕ) : ℝ)
              + Real.log 2 / 2 + 3 / 2 := hD
    have hδL : δ * Real.log (q : ℝ) = t := by
      rw [hδdef, div_mul_cancel₀ _ (ne_of_gt hLpos)]
    have hNle : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
      · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    exact RealZeroCount.countArith hδpos hδL hLpos hNle hlogq_ge hkey
  · -- degenerate case: `t = 0`
    rw [← ht0eq]
    have hz := RealZeroCount.realZeroCountFinsum_eq_zero_of_nonpos hq2 χ hχ (le_refl (0 : ℝ))
    rw [hz]
    norm_num

/-- The multiplicity-weighted number of **real** zeros `β` of a real non-principal character `χ`
with `λ(β) = (1-β)·log q ≤ t` grows at most linearly in `t` (`λ(β) ≤ B + 6t`), uniformly in the
modulus, as long as `t ≤ log q / 8`.

Proof route (Hadamard partial fraction at a single real point — all real zeros share the same
height, so one evaluation point suffices): let `δ := t / log q`, `σ₁ := 1 + 2δ ∈ (1, 5/4]`, and
`C` the constant of `Work.LinnikAreas.siegelZeroSimple_ldUpper` (`Re (Λ'/Λ)(σ) ≤ 1/(σ-1) + C` on
`(1,5/4]`, for every non-principal character, no reality needed).  Instantiate
`Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le ψ _ _ 0 σ₁ (1/(2δ)+C) _ 1`
for `ψ := χ.primitiveCharacter` (level `N := χ.conductor`); it bounds
`∑ᶠ u, (divisor Λ_ψ (ball 0 1) u) * (Re 1/(σ₁-u) + Re 1/(1+ū))` by `1/(2δ) + C + log N + log 2/2 + 3/2`.
Every real zero `β` with `zeroMult χ (β:ℂ) ≠ 0` and `λ(β) ≤ t` has `β ∈ (7/8,1)` (`zeroMultStripPos` /
`Commons...completedL_zero_strip`), hence lies in the ball and contributes at least
`1/(σ₁-β) ≥ 1/(3δ)` (multiplicity-weighted).  So `k ≤ 3/2 + 3δ(C + log N + log 2/2 + 3/2)`, and with
`log N ≤ log q`, `δ = t/log q` this is `≤ B + 3t` for `B := 3/2 + (3/8)(C + log 2/2 + 3/2)` once
`log q ≥ C + log 2/2 + 3/2`; `q₀` absorbs that threshold and `B := 3/2` (or any larger constant)
works.  Split off `t = 0` separately (then `δ = 0`, the sum is empty since `β < 1`).  Template for the
whole bookkeeping (finsum over real points, positivity of the divisor, kernel lower bound):
`Work.LinnikAreas.DhCapped.twoRealZeroRepelCore`.  The hypothesis `χ^2 = 1` is not needed by the
route (the same proof gives the bound for every non-principal `χ`). -/
theorem realZeroLambdaCountLinear :
    ∃ q₀ : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ t : ℝ, 0 ≤ t → t ≤ Real.log (q : ℝ) / 8 →
          (∑ᶠ β : ℝ, if Work.LinnikContract.zeroMult χ ((β : ℂ)) ≠ 0 ∧
              Work.LinnikContract.lamOf q ((β : ℂ)) ≤ t
            then (Work.LinnikContract.zeroMult χ ((β : ℂ)) : ℝ) else 0)
            ≤ B + 6 * t := by
  obtain ⟨C₀, hC₀⟩ := siegelZeroSimple_ldUpper
  set C : ℝ := max C₀ 0 with hCdef
  have hC : ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), ψ ≠ 1 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 →
        (logDeriv (DirichletCharacter.completedLFunction ψ) (σ : ℂ)).re ≤ 1 / (σ - 1) + C := by
    intro N _ ψ hψ σ h1 h2
    have h := hC₀ N ψ hψ σ h1 h2
    have hle : C₀ ≤ C := le_max_left _ _
    linarith
  refine ⟨max 3 (⌈Real.exp (C + Real.log 2 / 2 + 3 / 2)⌉₊ + 2), 3 / 2, by norm_num, ?_⟩
  intro q hq hqne χ hχ hsq t ht0 htle
  show realZeroCountFinsum q χ t ≤ 3 / 2 + 6 * t
  exact realZeroLambdaCountLinear_aux C hC q hq χ hχ hsq t ht0 htle

end Work.LinnikAreas
