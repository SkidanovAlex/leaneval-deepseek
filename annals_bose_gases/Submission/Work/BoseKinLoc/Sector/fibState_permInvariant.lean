import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Sector.actPerm_slotComb_slotPerm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Sector

/-- **The fibre state of a symmetric state is symmetric.**  If `Ψ` is invariant under all permutations of the `N` particles, then the fibre `fibState S Ψ y` (the `|S|`-particle function obtained by freezing the coordinates outside `S` at `y`) is invariant under all permutations of the `|S|` slots of `S`: the permutation of the slots of `S` induced by a permutation of `Fin |S|` along the order isomorphism `slotIso S`, extended by the identity off `S`, is a permutation of `Fin N`, and `Ψ` is invariant under it.  This is what lets the per-fibre box bound (whose trial class is the symmetric class `BoxState`) be applied to the fibres produced by the sector decomposition. -/
theorem fibState_permInvariant {N : ℕ} {S : Finset (Fin N)} {Ψ : Submission.BoseGases.X N → ℝ}
    (hsym : Submission.BoseGases.PermInvariant N Ψ) (y : Work.PerSector.SlotOut N S → ℝ³) :
    Submission.BoseGases.PermInvariant S.card (fibState S Ψ y) := by
  intro σ x
  -- Unfold the fibre: `fibState S Ψ y x = Ψ (slotComb S (x ∘ slotIso S) y)`.
  simp only [fibState, Work.PerSector.slotFibreState, Work.PerSector.slotFibre]
  -- Relabelling the slots of `S` by `σ` is the same as relabelling the particles of `S` by the
  -- slot permutation `slotPerm S σ` (the identity off `S`), which leaves `Ψ` unchanged.
  have key : Work.PerSector.slotComb S
        (fun i => Submission.BoseGases.actPerm S.card σ x (slotIso S i)) y
      = Submission.BoseGases.actPerm N (slotPerm S σ)
          (Work.PerSector.slotComb S (fun i => x (slotIso S i)) y) := by
    rw [actPerm_slotComb_slotPerm S σ (fun i => x (slotIso S i)) y]
    congr 1
    funext i
    simp [Submission.BoseGases.actPerm, slotPermIn]
  rw [key]
  exact hsym (slotPerm S σ) _

end Work.BoseKinLoc.Sector
