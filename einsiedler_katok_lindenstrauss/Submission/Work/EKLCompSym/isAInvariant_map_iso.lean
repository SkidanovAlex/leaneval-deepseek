import Mathlib
import Submission.Work.EKLCompSym.Basic

namespace Work.EKLCompSym

/-- `A`-invariance is transported across the `S₃`-symmetry isomorphism `iso τ` of `X₃`.

If `μ` is invariant under every diagonal flow `aDiag t`, then so is the push forward
`(iso τ)_* μ`.  The point is that `iso τ` intertwines the diagonal flows:
`iso τ (aDiag t • x) = aDiag (t ∘ τ) • iso τ x` (`iso_smul`, `conjPerm_apply_aDiag`). -/
theorem isAInvariant_map_iso {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (τ : Equiv.Perm (Fin 3)) (h : Work.EKLContract.IsAInvariant μ) :
    Work.EKLContract.IsAInvariant (MeasureTheory.Measure.map (Work.EKLCompSym.iso τ) μ) := by
  intro t
  -- `iso τ` carries the flow `aDiag t` to the flow `aDiag (t ∘ τ.symm)`.
  refine ⟨(h t).measurable, ?_⟩
  rw [MeasureTheory.Measure.map_map (h t).measurable (measurable_iso τ)]
  have heq : (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ∘ iso τ
      = iso τ ∘ (fun x : Work.EKLContract.X3 =>
          Work.EKLContract.aDiag (t ∘ ⇑τ.symm) • x) := by
    funext x
    simp only [Function.comp_apply]
    rw [iso_smul τ (Work.EKLContract.aDiag (t ∘ ⇑τ.symm)) x, conjPerm_apply_aDiag,
      show ((t ∘ ⇑(Equiv.symm τ)) ∘ ⇑τ) = t from by funext i; simp]
  rw [heq, ← MeasureTheory.Measure.map_map (measurable_iso τ) (h (t ∘ ⇑τ.symm)).measurable,
    (h (t ∘ ⇑τ.symm)).map_eq]

end Work.EKLCompSym
