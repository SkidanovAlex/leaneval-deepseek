import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.CompletionLocalField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero Pointwise

/-- The ring of integers of a non-archimedean local field (in the sense of
`Work.LocalFields.IsLocalField`) is complete with respect to the adic topology of its maximal
ideal.

The proof uses compactness of `𝒪[k]`: the powers of the maximal ideal are closed (the ring is
Noetherian, and an ideal of a compact Hausdorff ring is closed), so the decreasing sequence of
closed sets `f n + 𝓂^n` has nonempty intersection, and any point of that intersection is an adic
limit of `f`. -/
theorem isAdicComplete_maximalIdeal {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [Work.LocalFields.IsLocalField k] :
    IsAdicComplete (IsLocalRing.maximalIdeal (Valued.integer k)) (Valued.integer k) := by
  haveI hh : IsHausdorff (IsLocalRing.maximalIdeal (Valued.integer k)) (Valued.integer k) :=
    inferInstance
  refine { haus' := fun x hx => hh.haus' x hx, prec' := fun f hf => ?_ }
  let S n : Set 𝒪[k] := f n +ᵥ ((𝓂[k] ^ n : Ideal 𝒪[k]) : Set 𝒪[k])
  have hS n : S (n + 1) ⊆ S n := by
    apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
    simpa [S] using (hf n.le_succ).symm
  have h n : IsClosed (S n) := (IsNoetherianRing.isClosed_ideal (𝓂[k] ^ n)).vadd (f n)
  obtain ⟨L, hL⟩ := (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS
    (by simp [S]) h
  refine ⟨L, fun n ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
  simpa [S, SModEq.sub_mem] using hy

end Work.LocalFields
