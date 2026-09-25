import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.sigmaN_nested

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

/-- **A monotone chain of finite sets is tiled by its annuli.**  If `A 0 ⊆ A 1 ⊆ A 2 ⊆ …`, then the
annuli `A (s+1) \ A s`, `s < n`, are pairwise disjoint and their union is `A n \ A 0`; summing a
function over them is therefore the same as summing over `A n` and subtracting the sum over `A 0`.
This is the geometric content of MST's decomposition `ν_{2^n} = Σ_{0 ≤ s < n} ν_{2^n}^s`. -/
theorem sum_range_sdiff_of_mono {α : Type*} [DecidableEq α] {M : Type*} [AddCommGroup M]
    (A : ℕ → Finset α) (hmono : ∀ s, A s ⊆ A (s + 1)) (f : α → M) (n : ℕ) :
    (∑ s ∈ Finset.range n, ∑ β ∈ A (s + 1) \ A s, f β)
      = (∑ β ∈ A n, f β) - ∑ β ∈ A 0, f β := by
  have hstep : ∀ s, ∑ β ∈ A (s + 1) \ A s, f β
      = (∑ β ∈ A (s + 1), f β) - ∑ β ∈ A s, f β :=
    fun s => eq_sub_iff_add_eq.mpr (Finset.sum_sdiff (hmono s))
  rw [Finset.sum_congr rfl (fun s _ => hstep s)]
  exact Finset.sum_range_sub (fun s => ∑ β ∈ A s, f β) n

/-- The MST level sets form an increasing chain in the level index (with the `𝒰(0) := ∅`
convention of `mstLevel`): `mstLevel l 0 = ∅`, and for `s ≥ 1` the inclusion
`mstU l s ⊆ mstU l (s+1)` is the failure of nesting (Σ1) `sigmaN_nested`. -/
theorem mstLevel_mono (l : ℕ) (s : ℕ) : mstLevel l s ⊆ mstLevel l (s + 1) := by
  by_cases hs : s = 0
  · subst hs
    simp [mstLevel_zero]
  · rw [show mstLevel l s = mstU l s from by rw [mstLevel, if_neg hs], mstLevel_succ]
    rw [mstU_apply, mstU_apply]
    exact sigmaN_nested (mstRho l) (Nat.pow_le_pow_left (by omega) l)

/-- **The annuli `mstLevel l (s+1) \ mstLevel l s`, `s < n`, tile `mstU l n`.**  This is the
`Finset`-level form of MST §4.2 eq. (76): the level pieces of the major-arc model sum to the
whole model, because the level sets are nested (`sigmaN_nested`) and level `0` is the empty set. -/
theorem mstU_annulus_tiling (l : ℕ) (f : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (n : ℕ)
    (hn : 1 ≤ n) :
    (∑ β ∈ Work.BourgainPlan.Maximal.mstU l n, f β)
      = ∑ s ∈ Finset.range n, ∑ β ∈ Work.BourgainPlan.Maximal.mstLevel l (s + 1) \ Work.BourgainPlan.Maximal.mstLevel l s, f β := by
  rw [sum_range_sdiff_of_mono (mstLevel l) (mstLevel_mono l) f n]
  have hun : mstLevel l n = mstU l n := by
    rw [mstLevel, if_neg (by omega : ¬ n = 0)]
  rw [hun, mstLevel_zero, Finset.sum_empty, sub_zero]

end Work.BourgainPlan.Maximal
