import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal Pointwise
open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
/-- Membership of a translate: `a + x ∈ a +ᵥ Ω` for `x ∈ Ω`. -/
private lemma vadd_mem_vadd (a : X) {Ω : Set X} {x : X} (hx : x ∈ Ω) :
    a + x ∈ a +ᵥ Ω := by
  simp only [Set.mem_vadd_set, vadd_eq_add]
  exact ⟨x, hx, rfl⟩

/-- `iterDerivNorm` is invariant under translating the function and the domain. -/
private lemma iterDerivNorm_comp_add (a : X) (i : ℕ) (f : X → ℂ) (Ω : Set X) :
    iterDerivNorm i (fun z => f (a + z)) Ω = iterDerivNorm i f (a +ᵥ Ω) := by
  unfold iterDerivNorm
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => ?_
    rw [iteratedFDerivWithin_comp_add_left i a x]
    exact le_iSup₂_of_le (a + x) (vadd_mem_vadd a hx) le_rfl
  · refine iSup₂_le fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Set.mem_vadd_set.mp hy
    refine le_iSup₂_of_le x hx ?_
    rw [vadd_eq_add, ← iteratedFDerivWithin_comp_add_left i a x]

/-- `holderSeminorm` is invariant under translating the function and the domain. -/
private lemma holderSeminorm_comp_add (a : X) (i : ℕ) (α : ℝ) (f : X → ℂ) (Ω : Set X) :
    holderSeminorm i α (fun z => f (a + z)) Ω = holderSeminorm i α f (a +ᵥ Ω) := by
  unfold holderSeminorm
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [iteratedFDerivWithin_comp_add_left i a x, iteratedFDerivWithin_comp_add_left i a y]
    have hsub : (a + x) - (a + y) = x - y := by abel
    refine le_trans (le_of_eq ?_)
      (le_holderSeminorm i α f (a +ᵥ Ω) (vadd_mem_vadd a hx) (vadd_mem_vadd a hy)
        (fun h => hxy (add_left_cancel h)))
    rw [hsub]
  · refine iSup₂_le fun u hu => iSup₂_le fun v hv => iSup_le fun huv => ?_
    obtain ⟨x, hx, rfl⟩ := Set.mem_vadd_set.mp hu
    obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hv
    have hne : x ≠ y := fun h => huv (by rw [h])
    refine le_trans (le_of_eq ?_)
      (le_holderSeminorm i α (fun z => f (a + z)) Ω hx hy hne)
    rw [vadd_eq_add, vadd_eq_add, ← iteratedFDerivWithin_comp_add_left i a x,
      ← iteratedFDerivWithin_comp_add_left i a y]
    rw [show (a + x) - (a + y) = x - y from by abel]

/-- Translation invariance of the `C^{k,α}` norm of `Submission/Work/CR/Flat/Holder.lean`:
translating the argument translates the domain, without changing the norm.  Hence the
norm only depends on the relative configuration of `f` and `Ω`. -/
theorem holderNorm_comp_add (a : X) (k : ℕ) (α : ℝ) (f : X → ℂ) (Ω : Set X) :
    holderNorm k α (fun z => f (a + z)) Ω = holderNorm k α f ((fun z => a + z) '' Ω) := by
  unfold holderNorm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iterDerivNorm_comp_add, holderSeminorm_comp_add]
  rfl

end Work.CR.Flat.Holder
