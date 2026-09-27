import Mathlib
import Submission.Work.Drive.omegaChainInterface
import Submission.Work.Drive.rotLens_rotCapping_isAction
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.SeamMeetDefs

/-!
# Rotation equivariance of the radial sweeps, and rotation invariance of the triple counts

The endgame of the chain route (`SWEEP_TRANSPORT_NOTES.md` §4 item 5, `OrderAlgebra.lean`) needs the
counts of the three radial sweeps to depend only on the **differences** of the rotation parameters of
the three planes: the functional identity of `OrderAlgebra.e_add_of_triple` is the statement that
`n (P_u, P_v, P_w)` is invariant under translating all three labels by the same angle, and
multiplicativity then reads `n_P = e (v-u) · e (w-u)`.

This file provides that invariance at the level of the *sweeps*:

* `Work.Drive.levelOf_rotCapping` — the rotation acts on the slice `ℝP³` only, hence preserves the
  radial coordinate (`Work.Drive.Phi_rot_equivariant`);
* `Work.Drive.rotCapping_shadow` — therefore the rotation commutes with the shadow;
* `Work.Drive.clampedSweep_rotCapping` — **the radial sweep of a rotated plane is the rotation of the
  sweep**: `clampedSweep c ψ (rotCapping v ∘ P) = rotCapping v ∘ clampedSweep c ψ P`;
* `Work.Drive.topBdryMeet_comp_injective` / `bottomBdryMeet_comp_injective` and their
  `topBdryMeet_rotCapping_clampedSweep` / `bottomBdryMeet_rotCapping_clampedSweep` corollaries — the
  boundary triple counts of three chains are unchanged by post-composing **all three** chains with one
  injective map, in particular with a common rotation.

Together these give, for three planes `P k = rotCapping (u k) ∘ P`, the translation invariance
`n (u_0, u_1, u_2) = n (0, u_1 - u_0, u_2 - u_0)` of every count of the triples: rotate everything by
`-u_0` (the counts are invariant by the last two lemmas, and the rotated sweeps are the sweeps of the
rotated planes by the third).
-/

namespace Work.Drive

open scoped Manifold ContDiff

/-- The rotation of the capping space is injective, being a group action (`rotCapping_add`,
`rotCapping_zero`). -/
theorem rotCapping_injective' (v : UnitAddCircle) : Function.Injective (rotCapping v) := by
  intro x y hxy
  have h1 : rotCapping (-v + v) x = rotCapping (-v + v) y := by
    rw [rotCapping_add, Function.comp_apply, Function.comp_apply]
    exact congrArg (rotCapping (-v)) hxy
  simpa [neg_add_cancel, rotCapping_zero] using h1

/-- **The rotation preserves the radial coordinate.**  `rotCapping v` acts on the slice coordinate of
the model `(0,∞) × ℝP³` only (`Work.Drive.Phi_rot_equivariant`). -/
theorem levelOf_rotCapping (v : UnitAddCircle) (p : CappingSpace) :
    levelOf (rotCapping v p) = levelOf p := by
  rw [levelOf, levelOf]
  have h : (cappingSpaceHomeoProj (rotCapping v p)).1 = (cappingSpaceHomeoProj p).1 := by
    show (Φ (rotCapping v p)).1 = (Φ p).1
    rw [(Phi_rot_equivariant v).1 p]
  exact congrArg (fun x : Set.Ioi (0 : ℝ) => (x : ℝ)) h

/-- **The rotation commutes with the shadow** (the shadow only rescales the radius, and the rotation
preserves it). -/
theorem rotCapping_shadow (v : UnitAddCircle) (c : ℝ) (hc : 0 < c) (p : CappingSpace) :
    rotCapping v (shadow c hc p) = shadow c hc (rotCapping v p) := by
  have h1 : shadow c hc (rotCapping v p)
      = scaleCapping (pos (c / levelOf p) (div_pos hc (levelOf_pos p))) (rotCapping v p) := by
    unfold shadow
    congr 1
    apply Subtype.ext
    simp [pos, levelOf_rotCapping]
  rw [h1]
  unfold shadow
  exact rotCapping_scaleCapping v _ p

/-- **The radial sweep of a rotated plane is the rotation of the sweep.**  The sweep rescales the
radius by a factor depending only on the radial coordinate of the plane, which the rotation preserves
(`levelOf_rotCapping`), and the rotation commutes with the radial dilation
(`rotCapping_scaleCapping`). -/
theorem clampedSweep_rotCapping (v : UnitAddCircle) (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3)) :
    clampedSweep c ψ (fun y => rotCapping v (P y)) x
      = rotCapping v (clampedSweep c ψ P x) := by
  rw [clampedSweep_apply, clampedSweep_apply]
  have hsc : clampScale c ψ (fun y => rotCapping v (P y)) x = clampScale c ψ P x := by
    simp only [clampScale, levelOf_rotCapping]
  have hpos : pos (clampScale c ψ (fun y => rotCapping v (P y)) x)
        (clampScale_pos c ψ (fun y => rotCapping v (P y)) x)
      = pos (clampScale c ψ P x) (clampScale_pos c ψ P x) :=
    Subtype.ext hsc
  rw [hpos]
  exact (rotCapping_scaleCapping v _ (P (mk2 (x 0) (x 1)))).symm

/-- **The boundary triple counts are invariant under a common injective map.**  The defining
conditions of `tripleBdryMeet` are equalities `D 0 (x 0) = D 1 (x 1) = D 2 (x 2)` together with the box
conditions; post-composing all three chains with one injective map leaves them unchanged. -/
theorem tripleBdryMeet_comp_injective (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (ρ : M → M) (hρ : Function.Injective ρ)
    (k : Fin 3) :
    tripleBdryMeet M (fun k' => ρ ∘ D k') k = tripleBdryMeet M D k := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, hρ hx.2.1, hρ hx.2.2.1, hx.2.2.2⟩
  · intro hx
    exact ⟨hx.1, congrArg ρ hx.2.1, congrArg ρ hx.2.2.1, hx.2.2.2⟩

/-- The **top** boundary triple counts are invariant under a common injective map. -/
theorem topBdryMeet_comp_injective (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (ρ : M → M) (hρ : Function.Injective ρ)
    (k : Fin 3) :
    topBdryMeet M (fun k' => ρ ∘ D k') k = topBdryMeet M D k := by
  rw [topBdryMeet, topBdryMeet, tripleBdryMeet_comp_injective M D ρ hρ k]

/-- The **bottom** boundary triple counts are invariant under a common injective map. -/
theorem bottomBdryMeet_comp_injective (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (ρ : M → M) (hρ : Function.Injective ρ)
    (k : Fin 3) :
    bottomBdryMeet M (fun k' => ρ ∘ D k') k = bottomBdryMeet M D k := by
  rw [bottomBdryMeet, bottomBdryMeet, tripleBdryMeet_comp_injective M D ρ hρ k]

/-- **The top boundary count of the sweeps is unchanged when all three planes are rotated**:
`n (rot u_0 · P_0, rot u_1 · P_1, rot u_2 · P_2) = n (P_0, P_1, P_2)` for the `n = topBdryMeet` of the
three radial sweeps.  This is the translation invariance of the counts of the chain route. -/
theorem topBdryMeet_rotCapping_clampedSweep (v : UnitAddCircle) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (k : Fin 3) :
    topBdryMeet CappingSpace
        (fun k' => clampedSweep (c k') ψ (fun y => rotCapping v (P k' y))) k
      = topBdryMeet CappingSpace
        (fun k' => clampedSweep (c k') ψ (P k')) k := by
  have h : (fun k' => clampedSweep (c k') ψ (fun y => rotCapping v (P k' y)))
      = fun k' => rotCapping v ∘ clampedSweep (c k') ψ (P k') := by
    funext k' x
    exact clampedSweep_rotCapping v (c k') ψ (P k') x
  rw [h, topBdryMeet_comp_injective CappingSpace _ (rotCapping v) (rotCapping_injective' v) k]

/-- The **bottom** boundary count of the sweeps is likewise unchanged under a common rotation. -/
theorem bottomBdryMeet_rotCapping_clampedSweep (v : UnitAddCircle) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (k : Fin 3) :
    bottomBdryMeet CappingSpace
        (fun k' => clampedSweep (c k') ψ (fun y => rotCapping v (P k' y))) k
      = bottomBdryMeet CappingSpace
        (fun k' => clampedSweep (c k') ψ (P k')) k := by
  have h : (fun k' => clampedSweep (c k') ψ (fun y => rotCapping v (P k' y)))
      = fun k' => rotCapping v ∘ clampedSweep (c k') ψ (P k') := by
    funext k' x
    exact clampedSweep_rotCapping v (c k') ψ (P k') x
  rw [h, bottomBdryMeet_comp_injective CappingSpace _ (rotCapping v) (rotCapping_injective' v) k]

end Work.Drive
