import Mathlib
import Submission.Work.BW.exists_finset_card_finrank_linearIndepOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If a finite family of vectors indexed by `{j : Fin n // j ≠ k}` spans a subspace of
dimension `r - 1`, then some `r - 1` of its members are linearly independent: there is an
injective `ι : Fin (r - 1) → {j : Fin n // j ≠ k}` such that `w ∘ ι` is linearly independent. -/
theorem exists_iota_of_finrank {n r : ℕ} {k : Fin n}
    (w : {j : Fin n // j ≠ k} → (Fin r → ℚ))
    (hdim : Module.finrank ℚ (Submodule.span ℚ (Set.range w)) = r - 1) :
    ∃ ι : Fin (r - 1) → {j : Fin n // j ≠ k}, Function.Injective ι ∧ LinearIndependent ℚ (w ∘ ι) := by
  classical
  -- Extract a `Finset` of `r - 1` indices on which `w` is linearly independent.
  obtain ⟨s, hscard, hsind⟩ :=
    exists_finset_card_finrank_linearIndepOn (K := ℚ) (M := Fin r → ℚ) (v := w) (n := r - 1) hdim
  -- Enumerate that Finset by `Fin (r - 1)`.
  let E : ↥s ≃ Fin (r - 1) := Finset.equivFinOfCardEq hscard
  refine ⟨fun j => (E.symm j : {j : Fin n // j ≠ k}), ?_, ?_⟩
  · intro a b hab
    exact E.symm.injective (Subtype.ext hab)
  · have hli : LinearIndependent ℚ (fun x : ↥s => w ↑x) := hsind.linearIndependent
    have hcomp : LinearIndependent ℚ ((fun x : ↥s => w ↑x) ∘ E.symm) :=
      hli.comp E.symm E.symm.injective
    convert hcomp using 1
    ext j
    rfl

end Work.BW
