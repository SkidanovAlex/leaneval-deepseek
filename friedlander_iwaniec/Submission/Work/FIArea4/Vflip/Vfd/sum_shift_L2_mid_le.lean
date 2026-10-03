import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup
import Submission.Work.FIArea4.A4varbounds

/-!
# The `L²`-energy of shifts in the middle range `R < ρ ≤ 2R`

Write `shiftCoef ρ β (r,s) = β (ρ r) s` and `p14L2 R S β = Σ_{r ≤ 2R, s ≤ 2S} |β r s|²`.

If `β` is supported on `r ≤ 2R`, then for every `ρ` in the middle range `R < ρ ≤ 2R` the
shifted first coordinate `ρ * r` exceeds `2R` as soon as `r ≥ 2`.  Hence the shifted array
`(r,s) ↦ β (ρ*r) s` is supported on `r = 1`, where it reproduces the `ρ`-th row of `β`:

  `p14L2 R S (shiftCoef ρ β) = Σ_{s ≤ 2S} |β ρ s|²`.

Summing over `ρ ∈ (R, 2R]` and using that `(R, 2R] ⊆ [1, 2R]` together with the
nonnegativity of each summand gives the requested bound

  `Σ_{R < ρ ≤ 2R} p14L2 R S (shiftCoef ρ β) ≤ p14L2 R S β`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

/-- In the middle range `R < ρ`, the shifted array `(r,s) ↦ β (ρ*r) s` of an array `β` supported
on `r ≤ 2R` is concentrated on `r = 1`, so its `L²`-energy is the `ρ`-th row energy of `β`:
`p14L2 R S (shiftCoef ρ β) = Σ_{s ≤ 2S} |β ρ s|²`. -/
lemma p14L2_shiftCoef_mid (R S ρ : ℕ) (β : ℕ → ℕ → ℂ)
    (hR : 1 ≤ R) (hβ : ∀ r s, β r s ≠ 0 → r ≤ 2*R) (hρ : R < ρ) :
    Work.FIArea4.p14L2 R S (Work.FIArea4.Vflip.Vfd.shiftCoef ρ β)
      = ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (β ρ s) := by
  simp only [Work.FIArea4.p14L2, Work.FIArea4.Vflip.Vfd.shiftCoef_apply]
  have h1mem : 1 ∈ Finset.Icc 1 (2*R) := by
    simp only [Finset.mem_Icc]; omega
  rw [Finset.sum_eq_single_of_mem
      (f := fun r => ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (β (ρ*r) s)) 1 h1mem ?_]
  · simp
  · intro b hb hbne
    apply Finset.sum_eq_zero
    intro s _
    rw [Complex.normSq_eq_zero]
    by_contra h
    have hle := hβ (ρ*b) s h
    have hb2 : 2 ≤ b := by
      have h1 := (Finset.mem_Icc.mp hb).1
      omega
    have hρ2 : R + 1 ≤ ρ := hρ
    nlinarith [hle, hb2, hρ2]

/-- **The middle-range `L²` shift bound.**  For `β` supported on `r ≤ 2R`, the sum of the
`L²`-energies of the shifted arrays `shiftCoef ρ β` over the middle range `R < ρ ≤ 2R` is at
most the `L²`-energy of `β`. -/
theorem sum_shift_L2_mid_le (R S : ℕ) (β : ℕ → ℕ → ℂ) (hR : 1 ≤ R)
    (hβ : ∀ r s, β r s ≠ 0 → r ≤ 2*R) :
    ∑ ρ ∈ Finset.Ioc R (2*R),
        Work.FIArea4.p14L2 R S (Work.FIArea4.Vflip.Vfd.shiftCoef ρ β)
      ≤ Work.FIArea4.p14L2 R S β := by
  calc ∑ ρ ∈ Finset.Ioc R (2*R),
        Work.FIArea4.p14L2 R S (Work.FIArea4.Vflip.Vfd.shiftCoef ρ β)
      = ∑ ρ ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (β ρ s) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        exact p14L2_shiftCoef_mid R S ρ β hR hβ (Finset.mem_Ioc.mp hρ).1
    _ ≤ ∑ ρ ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (β ρ s) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ρ hρ
          rw [Finset.mem_Ioc] at hρ
          rw [Finset.mem_Icc]
          exact ⟨by omega, hρ.2⟩
        · intro ρ _ _
          exact Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _)
    _ = Work.FIArea4.p14L2 R S β := by
        rw [Work.FIArea4.p14L2]

end Work.FIArea4.Vflip.Vfd
