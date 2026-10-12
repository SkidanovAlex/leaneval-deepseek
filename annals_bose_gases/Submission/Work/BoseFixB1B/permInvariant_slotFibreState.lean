import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1B.sectorCountDefs
import Submission.Work.BoseKinLoc.Sector.fibState_permInvariant
import Submission.Work.PerSector.SlotAdditive
import Submission.Work.PerSector.aemeasurable_slotFibreMass
import Submission.Work.PerSector.sum_tBamp_normSq_slotPiece
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.permInvariant_slotFibreState` — the fibre of a symmetric state is symmetric

If `Φ` is invariant under all permutations of the `N` particles, then for every slot set
`S : Finset (Fin N)`, every bijection `e : SlotIn N S ≃ Fin S.card` of its slots and every outside
configuration `y`, the transported fibre

    `slotFibreState S e Φ y : X S.card → ℝ`,  `x ↦ Φ (slotComb S (x ∘ e) y)`

is invariant under all permutations of the `S.card` slots.

The proof reduces to the canonical (`slotIso`-indexed) case
`Work.BoseKinLoc.Sector.fibState_permInvariant`: the fibre along `e` is the fibre along
`slotIso S` precomposed with the relabelling `τ = (slotIso S).symm.trans e` of `Fin S.card`
(`slotFibreState_eq_fibState_comp`), and permutation invariance is stable under precomposition
with a relabelling (`permInvariant_comp_perm`).

* `permInvariant_comp_perm` — `F` symmetric `⟹` `x ↦ F (x ∘ τ)` symmetric;
* `slotFibreState_eq_fibState_comp` — `slotFibreState S e Φ y = fibState S Φ y ∘ (· ∘ τ)`;
* `permInvariant_slotFibreState` — the target.
-/

noncomputable section

namespace Work.BoseFixB1B

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Reparametrising the particle indices preserves permutation invariance.**  If `F : X k → ℝ`
is invariant under all permutations of the `k` particles, then so is `x ↦ F (x ∘ τ)` for every
permutation `τ` of `Fin k`: relabelling the particles and then permuting them is the same as
permuting them in the relabelled order.

The relabelled permutation of `σ` is `τ.trans (σ.trans τ.symm)`, i.e. `i ↦ τ.symm (σ (τ i))`. -/
theorem permInvariant_comp_perm {k : ℕ} {F : Submission.BoseGases.X k → ℝ}
    (hF : Submission.BoseGases.PermInvariant k F) (τ : Equiv.Perm (Fin k)) :
    Submission.BoseGases.PermInvariant k
      (fun x : Submission.BoseGases.X k => F (fun i => x (τ i))) := by
  intro σ x
  show F (fun i : Fin k => Submission.BoseGases.actPerm k σ x (τ i)) = F (fun i => x (τ i))
  have h : (fun i : Fin k => Submission.BoseGases.actPerm k σ x (τ i))
      = fun i => (fun j => x (τ j)) ((τ.trans (σ.trans τ.symm)) i) := by
    funext i
    simp only [Submission.BoseGases.actPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [h]
  exact hF (τ.trans (σ.trans τ.symm)) (fun j => x (τ j))

/-- **The fibre along an arbitrary bijection of the slots is the canonical fibre, relabelled.**
For `τ := (slotIso S).symm.trans e : Equiv.Perm (Fin S.card)` (the relabelling of `Fin S.card`
that matches the slot ordering `e` against the canonical one `slotIso S`),

    `slotFibreState S e Φ y = fun x => fibState S Φ y (fun i => x (τ i))`. -/
theorem slotFibreState_eq_fibState_comp {N : ℕ} (S : Finset (Fin N))
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card) (Φ : Submission.BoseGases.X N → ℝ)
    (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) :
    Work.PerSector.slotFibreState S e Φ y
      = fun x : Submission.BoseGases.X S.card => Work.BoseKinLoc.Sector.fibState S Φ y
          (fun i => x (e ((Work.BoseKinLoc.Sector.slotIso S).symm i))) := by
  funext x
  simp only [Work.BoseKinLoc.Sector.fibState, Work.PerSector.slotFibreState,
    Work.PerSector.slotFibre, Equiv.symm_apply_apply]

/-- **The fibre state of a symmetric state is symmetric.** -/
theorem permInvariant_slotFibreState {N : ℕ} (S : Finset (Fin N))
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : Submission.BoseGases.PermInvariant N Φ) (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.PermInvariant S.card (Work.PerSector.slotFibreState S e Φ y) := by
  rw [slotFibreState_eq_fibState_comp]
  exact permInvariant_comp_perm (Work.BoseKinLoc.Sector.fibState_permInvariant hΦ y)
    (((Work.BoseKinLoc.Sector.slotIso S).symm).trans e)

end Work.BoseFixB1B
