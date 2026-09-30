import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Curve.exists_affine_principal
import Submission.Work.CurveBasics.Linear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Curve

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem exists_finite_affine_cover_with_equations {k : Type u} [Field k] {C : Curve k}
    (D : Curve.Div C) :
    ∃ (n : ℕ) (W : Fin n → C.left.Opens) (t : Fin n → C.functionField),
      (∀ i, AlgebraicGeometry.IsAffineOpen (W i)) ∧ (∀ i, Nonempty (W i)) ∧
      (∀ z : C.left, ∃ i, z ∈ W i) ∧ (∀ i, t i ≠ 0) ∧
      (∀ i, ∀ Q : Curve.Place C, Q.point ∈ W i → C.ordAt (t i) Q = -D Q) := by
  classical
  -- For every point `z` of `C`, `exists_affine_principal` produces an affine open `W z ∋ z`
  -- carrying a local equation `t z` for `-D`.
  choose W t hWaff hzW htne htord using fun z => exists_affine_principal D z
  -- These opens cover `C`; by compactness, finitely many of them already cover `C`.
  have hcover : (Set.univ : Set C.left) ⊆ ⋃ z, (W z : Set C.left) := by
    intro z _
    exact Set.mem_iUnion.mpr ⟨z, hzW z⟩
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover isCompact_univ
    (fun z => (W z : Set C.left)) (fun z => (W z).isOpen) hcover
  -- Re-index the finite subcover by `Fin s.card`.
  let e : s ≃ Fin s.card := Finset.equivFin s
  let idx : Fin s.card → C.left := fun i => (e.symm i : C.left)
  refine ⟨s.card, fun i => W (idx i), fun i => t (idx i),
    fun i => hWaff (idx i), fun i => ⟨⟨idx i, hzW (idx i)⟩⟩, ?_, fun i => htne (idx i),
    fun i Q hQ => htord (idx i) Q hQ⟩
  intro z
  obtain ⟨w, hws, hzw⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ z))
  refine ⟨e ⟨w, hws⟩, ?_⟩
  have hidx : idx (e ⟨w, hws⟩) = w := by
    simp [idx, e]
  show z ∈ W (idx (e ⟨w, hws⟩))
  rw [hidx]
  exact hzw

end Work.CurveBasics.Curve
