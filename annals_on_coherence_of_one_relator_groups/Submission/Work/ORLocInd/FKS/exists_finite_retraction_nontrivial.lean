import Mathlib
import Submission.Work.OROneRel.presentedGroup_iso_coprod_of_supported
import Submission.Work.OROneRel.finite_relatorLetters

namespace Work.ORLocInd.FKS

open Work.OROneRel

universe u

/-- Reduction to finitely many generators.  A nontrivial element `u` of a free group
`FreeGroup α` on an arbitrary (possibly infinite) generating type stays nontrivial after applying the
retraction onto the free group on the finite set `S` of letters occurring in `u`.

Suggested proof: let `S` be the finite set of letters occurring in the reduced word
`FreeGroup.toWord u` (so that `Work.OROneRel.SupportedOn u (S : Set α)`), and let `ρ` be
`FreeGroup.lift (fun a => if ha : a ∈ S then FreeGroup.of (the element of the subtype S given by a)
else 1)`.  Then the composite of `FreeGroup.map (Subtype.val)` with `ρ` sends `u` to `u` --- this is
the computation in `Work.OROneRel.exists_map_subtype_val_eq_of_supportedOn` --- so `ρ u ≠ 1`. -/
theorem exists_finite_retraction_nontrivial {α : Type u} {u : FreeGroup α} (hu : u ≠ 1) :
    ∃ (S : Finset α) (ρ : FreeGroup α →* FreeGroup ↥S), ρ u ≠ 1 := by
  classical
  have hfin : (relatorLetters u).Finite := finite_relatorLetters u
  let S : Finset α := hfin.toFinset
  -- every letter occurring in `u` belongs to `S`
  have hL : ∀ x ∈ FreeGroup.toWord u, x.1 ∈ S := by
    intro x hx
    exact hfin.mem_toFinset.mpr ⟨x.2, hx⟩
  -- the retraction of `F(α)` onto `F(S)` killing the unused generators
  let ρ : FreeGroup α →* FreeGroup ↥S :=
    FreeGroup.lift (fun a : α => if ha : a ∈ S then FreeGroup.of (⟨a, ha⟩ : ↥S) else 1)
  -- the same map, viewed as a map `F(α) →* F(α)`
  let g : α → FreeGroup α := fun a => if ha : a ∈ S then FreeGroup.of a else 1
  have key : FreeGroup.lift (fun a : α => FreeGroup.of a) (FreeGroup.mk (FreeGroup.toWord u)) =
      FreeGroup.lift g (FreeGroup.mk (FreeGroup.toWord u)) := by
    rw [FreeGroup.lift_mk, FreeGroup.lift_mk]
    congr 1
    apply List.map_congr_left
    intro x hx
    simp [g, hL x hx]
  -- including `F(S)` back into `F(α)` undoes `ρ` on `u`
  have hcomp : (FreeGroup.map (fun a : ↥S => (a : α))).comp ρ = FreeGroup.lift g := by
    have hρdef : ρ = FreeGroup.lift
        (fun a : α => if ha : a ∈ S then FreeGroup.of (⟨a, ha⟩ : ↥S) else 1) := rfl
    rw [hρdef]
    refine FreeGroup.ext_hom _ _ fun a => ?_
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    by_cases ha : a ∈ S
    · simp [ha, g, FreeGroup.map.of]
    · simp [ha, g]
  have hfix : FreeGroup.map (fun a : ↥S => (a : α)) (ρ u) = u := by
    rw [← MonoidHom.comp_apply, hcomp]
    have hu_mk : u = FreeGroup.mk (FreeGroup.toWord u) := FreeGroup.mk_toWord.symm
    rw [hu_mk, ← key, FreeGroup.lift_of_apply]
  refine ⟨S, ρ, ?_⟩
  intro h
  apply hu
  rw [← hfix, h, map_one]

end Work.ORLocInd.FKS
