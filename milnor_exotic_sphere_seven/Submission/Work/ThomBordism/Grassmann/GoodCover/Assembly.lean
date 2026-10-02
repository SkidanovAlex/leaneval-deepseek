import Mathlib
import Submission.Work.ThomBordism.Grassmann.GoodCover.Defs
import Submission.Work.ThomBordism.Grassmann.finsetCoveredConnected

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Item 3: the `(k-1)`-connectivity of the Thom space, from a good cover of the Grassmannian

`thomSpaceConnected_of_pieces`: if `{U i}` is a finite open cover of `G̃r_k(ℝ^{k+m})` and every
piece `far 1 ∪ π⁻¹ (⋂ i ∈ S, U i)` is `(k-1)`-connected, then `Th γ` is `(k-1)`-connected.

The proof is the finite-cover Mayer–Vietoris theorem for homotopy groups
(`Work.ThomBordism.Grassmann.finsetCoveredConnected`, proved) applied to the open cover
`{far 1 ∪ π⁻¹ (U i)}` of `Th γ` with parameter `k+1`: the finite intersections are the pieces
`far 1 ∪ π⁻¹ (⋂ i ∈ S, U i)`, which are `(k-1)`-connected, hence `(k+1-|S|)`-connected because
`|S| ≥ 1`.

Unlike `thomSpaceConnectedAssembly` (which is tied to the chart-cell cover and whose piece
hypothesis can *fail* for the intersections of chart cells), this statement takes an arbitrary
finite cover; `GoodCover/Main.lean` instantiates it with a good cover subordinate to the chart
cells, whose finite intersections are contractible.
-/

open scoped Topology
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

/-- The homeomorphism `↥(univ : Set X) ≃ₜ X`. -/
def univHomeo (X : Type*) [TopologicalSpace X] : ↥(Set.univ : Set X) ≃ₜ X where
  toFun x := x.1
  invFun x := ⟨x, trivial⟩
  left_inv x := by ext; rfl
  right_inv x := by rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- **Item 3 from a finite cover by pieces of the Thom space.**

Let `U : Fin m' → Set (OG k m)` be a finite family of open sets covering the Grassmannian.  If for
every nonempty `S : Finset (Fin m')` the piece `far 1 ∪ π⁻¹ (⋂ i ∈ S, U i)` is `(k-1)`-connected,
then `Th γ` is `(k-1)`-connected: every `π_i(Th γ, ∞)` with `i < k` is trivial. -/
theorem thomSpaceConnected_of_pieces (k m m' : ℕ) (hm' : 1 ≤ m') (U : Fin m' → Set (OG k m))
    (hUopen : ∀ i, IsOpen (U i)) (hUcov : (⋃ i, U i) = Set.univ)
    (hpiece : ∀ S : Finset (Fin m'), S.Nonempty → ∀ j : ℕ, j < k →
      ∀ x : ↥(⋂ i ∈ S, pieceCover k m (U i)),
        Subsingleton (HomotopyGroup (Fin j) ↥(⋂ i ∈ S, pieceCover k m (U i)) x)) :
    ThomSpaceConnected k m := by
  classical
  haveI : Nonempty (Fin m') := ⟨⟨0, hm'⟩⟩
  intro i hi
  -- the Mayer–Vietoris step with parameter `k+1`
  have hne : ∀ S : Finset (Fin m'), S.Nonempty → S ⊆ Finset.univ →
      (⋂ j ∈ S, pieceCover k m (U j)).Nonempty :=
    fun S _ _ => nonempty_iInter_pieceCover k m U S
  have hcon : ∀ S : Finset (Fin m'), S.Nonempty → S ⊆ Finset.univ →
      ∀ j, j < k + 1 - S.card → ∀ x : ↥(⋂ j ∈ S, pieceCover k m (U j)),
        Subsingleton (HomotopyGroup (Fin j) ↥(⋂ j ∈ S, pieceCover k m (U j)) x) := by
    intro S hS _ j hj x
    have hc : 1 ≤ S.card := Finset.card_pos.mpr hS
    exact hpiece S hS j (by omega) x
  have hmain := finsetCoveredConnected (fun i : Fin m' => pieceCover k m (U i))
    (fun i => isOpen_pieceCover k m (hUopen i)) Finset.univ Finset.univ_nonempty (k + 1)
    (by omega) hne hcon
  have hcov := iUnion_univ_pieceCover k m m' U hUcov
  have hfin : ∀ j < k + 1 - 1, ∀ x : ↥(⋃ i ∈ (Finset.univ : Finset (Fin m')),
      pieceCover k m (U i)), Subsingleton (HomotopyGroup (Fin j) _ x) := hmain
  rw [show k + 1 - 1 = k from by omega] at hfin
  have hbase : ((univHomeo (TautologicalThomSpace k m)).symm.trans
      (Homeomorph.setCongr hcov).symm) (thomBasepoint k m)
        = (⟨thomBasepoint k m, by rw [hcov]; trivial⟩ :
            ↥(⋃ i ∈ (Finset.univ : Finset (Fin m')), pieceCover k m (U i))) :=
    Subtype.ext rfl
  exact subsingleton_homotopyGroup_of_homeomorph _ hbase i
    (hfin i hi ⟨thomBasepoint k m, by rw [hcov]; trivial⟩)

end

end Work.ThomBordism.Grassmann
