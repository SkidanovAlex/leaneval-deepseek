/-
# The halved average of the band comparison, and the uniform crude bound

Two elementary facts about the halved average used by the `ssu` assembly
(`Work.KMTPlan.A6.ssuMainBound`): that `ssuAvg` is the paper's `Ã_N` (`AhalfR TZ N X P`), and
that the twisted multiplier `BtwistEx` with the narrow window satisfies a *uniform* crude
`ℓ² × ℓ² → ℓ¹` bound for all height pairs with `max l₁ l₂ < L₀`.  They live in their own module
because `ssuMain.lean` (which proves the assembly) imports them, while the target file
`ssuBtwistExBdd.lean` imports `ssuMain`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SsuDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7
open Submission.PointwiseErgodicTheorems

theorem ssuAvg_eq_AhalfR (P : Polynomial ℤ) (N : ℕ) (h k : ℤ → ℂ) :
    ssuAvg P N h k = AhalfR TZ (N : ℝ≥0) Polynomial.X P h k := by
  funext x
  simp only [ssuAvg, AhalfR, Ahalf, Ablock, Nat.floor_natCast]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [Polynomial.eval_X, TZ_zpow]

/-- **A uniform crude bound for the small-scale case.**  For fixed `ρ`, `P` and a cutoff `L₀`,
there is a single constant `Cm > 0` such that the twisted bilinear multiplier with the narrow
window obeys the `ℓ² × ℓ² → ℓ¹` bound with constant `Cm` for all height pairs of `max` below
`L₀`.  This is `exists_bound_BtwistEx_crude` plus the finiteness of the box `[0,L₀)²`. -/
theorem ssuCrudeUniform (ρ : ℝ) (P : Polynomial ℤ) (L₀ : ℕ) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ (l₁ l₂ u : ℕ) (h k : ℤ → ℂ), max l₁ l₂ < L₀ →
      eLpNorm (fun x : ℤ => BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) h k x)
          1 Measure.count
        ≤ ENNReal.ofReal Cm * eLpNorm h 2 Measure.count * eLpNorm k 2 Measure.count := by
  classical
  choose C hCnn hC using fun l₁ l₂ : ℕ => exists_bound_BtwistEx_crude ρ P l₁ l₂
  have hCnns : 0 ≤ ∑ a ∈ Finset.range L₀, ∑ b ∈ Finset.range L₀, C a b :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hCnn a b))
  refine ⟨1 + ∑ a ∈ Finset.range L₀, ∑ b ∈ Finset.range L₀, C a b, by linarith, ?_⟩
  intro l₁ l₂ u h k hlt
  have hmem₁ : l₁ ∈ Finset.range L₀ :=
    Finset.mem_range.mpr (lt_of_le_of_lt (le_max_left _ _) hlt)
  have hmem₂ : l₂ ∈ Finset.range L₀ :=
    Finset.mem_range.mpr (lt_of_le_of_lt (le_max_right _ _) hlt)
  have hle : C l₁ l₂ ≤ 1 + ∑ a ∈ Finset.range L₀, ∑ b ∈ Finset.range L₀, C a b := by
    have h1 : C l₁ l₂ ≤ ∑ b ∈ Finset.range L₀, C l₁ b :=
      Finset.single_le_sum (fun b _ => hCnn l₁ b) hmem₂
    have h2 : ∑ b ∈ Finset.range L₀, C l₁ b
        ≤ ∑ a ∈ Finset.range L₀, ∑ b ∈ Finset.range L₀, C a b :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hCnn a b)) hmem₁
    linarith
  calc eLpNorm (fun x : ℤ => BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) h k x)
        1 Measure.count
      ≤ ENNReal.ofReal (C l₁ l₂) * eLpNorm h 2 Measure.count
          * eLpNorm k 2 Measure.count := hC l₁ l₂ u h k
    _ ≤ ENNReal.ofReal (1 + ∑ a ∈ Finset.range L₀, ∑ b ∈ Finset.range L₀, C a b)
          * eLpNorm h 2 Measure.count * eLpNorm k 2 Measure.count := by
        gcongr

end

end Work.KMTPlan.A6
