import Mathlib
import Submission.Work.Drive.omegaChainInterface

/-!
# The rotations of the slice and of the capping space form an `S¹`-action

This file proves `Work.Drive.rotLens_rotCapping_isAction`: the descended rotation maps
`Work.Drive.rotLens` (on the Heegaard slice `LensSpace`) and `Work.Drive.rotCapping` (on the
four-dimensional capping space `CappingSpace`) are continuous and satisfy the action laws
`φ (u + v) = φ u ∘ φ v`, `φ 0 = id`.

The proofs descend the corresponding statements for the concrete maps `rotLensSum` / `rotSum` on the
disjoint unions along the identification relations `lensRel` / `cappingRel`.
-/

namespace Work.Drive

noncomputable section

open scoped Topology

/-! ## Continuity of the concrete maps -/

lemma continuous_rotCapTorus (v : UnitAddCircle) : Continuous (rotCapTorus v) := by
  unfold rotCapTorus
  fun_prop

lemma continuous_rotConfTorus (v : UnitAddCircle) : Continuous (rotConfTorus v) := by
  unfold rotConfTorus
  fun_prop

lemma continuous_rotConfig (v : UnitAddCircle) : Continuous (rotConfig v) := by
  unfold rotConfig
  fun_prop

lemma continuous_rotCap (v : UnitAddCircle) : Continuous (rotCap v) := by
  unfold rotCap
  fun_prop

lemma continuous_rotLensSum (v : UnitAddCircle) : Continuous (rotLensSum v) := by
  rw [continuous_sum_dom]
  refine ⟨?_, ?_⟩
  · refine Continuous.congr (continuous_inl.comp (continuous_rotCapTorus v)) ?_
    intro p
    rfl
  · refine Continuous.congr (continuous_inr.comp (continuous_rotConfTorus v)) ?_
    intro p
    rfl

lemma continuous_rotSum (v : UnitAddCircle) : Continuous (rotSum v) := by
  rw [continuous_sum_dom]
  refine ⟨?_, ?_⟩
  · refine Continuous.congr (continuous_inl.comp (continuous_rotConfig v)) ?_
    intro p
    rfl
  · refine Continuous.congr (continuous_inr.comp (continuous_rotCap v)) ?_
    intro p
    rfl

/-! ## The action laws for the concrete maps -/

lemma rotCapTorus_add_apply (u v : UnitAddCircle) (p : CapTorus) :
    rotCapTorus (u + v) p = rotCapTorus u (rotCapTorus v p) := by
  obtain ⟨θ, z⟩ := p
  show (θ + (u + v), z) = ((θ + v) + u, z)
  rw [show θ + (u + v) = (θ + v) + u by abel]

lemma rotConfTorus_add_apply (u v : UnitAddCircle) (p : ConfTorus) :
    rotConfTorus (u + v) p = rotConfTorus u (rotConfTorus v p) := by
  obtain ⟨z, η⟩ := p
  show (z, η + (u + v)) = (z, (η + v) + u)
  rw [show η + (u + v) = (η + v) + u by abel]

lemma rotConfig_add_apply (u v : UnitAddCircle) (p : ConfigPiece) :
    rotConfig (u + v) p = rotConfig u (rotConfig v p) := by
  obtain ⟨⟨r, c, η⟩, hp⟩ := p
  refine Subtype.ext ?_
  show (r, c, η + (u + v)) = (r, c, (η + v) + u)
  rw [show η + (u + v) = (η + v) + u by abel]

lemma rotCap_add_apply (u v : UnitAddCircle) (p : CapPiece) :
    rotCap (u + v) p = rotCap u (rotCap v p) := by
  obtain ⟨⟨r, θ, z⟩, hp⟩ := p
  refine Subtype.ext ?_
  show (r, θ + (u + v), z) = (r, (θ + v) + u, z)
  rw [show θ + (u + v) = (θ + v) + u by abel]

lemma rotLensSum_add (u v : UnitAddCircle) :
    rotLensSum (u + v) = rotLensSum u ∘ rotLensSum v := by
  funext p
  rcases p with p | p
  · show rotLensSum (u + v) (Sum.inl p) = rotLensSum u (rotLensSum v (Sum.inl p))
    rw [rotLensSum_inl, rotLensSum_inl, rotLensSum_inl, rotCapTorus_add_apply]
  · show rotLensSum (u + v) (Sum.inr p) = rotLensSum u (rotLensSum v (Sum.inr p))
    rw [rotLensSum_inr, rotLensSum_inr, rotLensSum_inr, rotConfTorus_add_apply]

lemma rotSum_add (u v : UnitAddCircle) :
    rotSum (u + v) = rotSum u ∘ rotSum v := by
  funext p
  rcases p with p | p
  · show rotSum (u + v) (Sum.inl p) = rotSum u (rotSum v (Sum.inl p))
    rw [rotSum_inl, rotSum_inl, rotSum_inl, rotConfig_add_apply]
  · show rotSum (u + v) (Sum.inr p) = rotSum u (rotSum v (Sum.inr p))
    rw [rotSum_inr, rotSum_inr, rotSum_inr, rotCap_add_apply]

lemma rotLensSum_zero : rotLensSum (0 : UnitAddCircle) = id := by
  funext p
  rcases p with ⟨θ, z⟩ | ⟨z, η⟩
  · show Sum.inl (rotCapTorus 0 (θ, z)) = Sum.inl (θ, z)
    rw [show rotCapTorus 0 (θ, z) = (θ, z) by simp [rotCapTorus]]
  · show Sum.inr (rotConfTorus 0 (z, η)) = Sum.inr (z, η)
    rw [show rotConfTorus 0 (z, η) = (z, η) by simp [rotConfTorus]]

lemma rotSum_zero : rotSum (0 : UnitAddCircle) = id := by
  funext p
  rcases p with ⟨⟨r, c, η⟩, hp⟩ | ⟨⟨r, θ, z⟩, hp⟩
  · show Sum.inl (rotConfig 0 ⟨(r, c, η), hp⟩) = Sum.inl ⟨(r, c, η), hp⟩
    congr 1
    refine Subtype.ext ?_
    simp [rotConfig]
  · show Sum.inr (rotCap 0 ⟨(r, θ, z), hp⟩) = Sum.inr ⟨(r, θ, z), hp⟩
    congr 1
    refine Subtype.ext ?_
    simp [rotCap]

/-! ## Descending to the quotients -/

lemma rotLens_add (u v : UnitAddCircle) :
    rotLens (u + v) = rotLens u ∘ rotLens v := by
  funext x
  induction x using Quotient.inductionOn with
  | h p =>
    show rotLens (u + v) (Quotient.mk'' p) = rotLens u (rotLens v (Quotient.mk'' p))
    rw [rotLens_mk, rotLens_mk, rotLens_mk, rotLensSum_add, Function.comp_apply]

lemma rotCapping_add (u v : UnitAddCircle) :
    rotCapping (u + v) = rotCapping u ∘ rotCapping v := by
  funext x
  induction x using Quotient.inductionOn with
  | h p =>
    show rotCapping (u + v) (Quotient.mk'' p) = rotCapping u (rotCapping v (Quotient.mk'' p))
    rw [rotCapping_mk, rotCapping_mk, rotCapping_mk, rotSum_add, Function.comp_apply]

lemma rotLens_zero : rotLens (0 : UnitAddCircle) = id := by
  funext x
  induction x using Quotient.inductionOn with
  | h p =>
    show rotLens (0 : UnitAddCircle) (Quotient.mk'' p) = id (Quotient.mk'' p)
    rw [rotLens_mk, rotLensSum_zero]
    rfl

lemma rotCapping_zero : rotCapping (0 : UnitAddCircle) = id := by
  funext x
  induction x using Quotient.inductionOn with
  | h p =>
    show rotCapping (0 : UnitAddCircle) (Quotient.mk'' p) = id (Quotient.mk'' p)
    rw [rotCapping_mk, rotSum_zero]
    rfl

lemma continuous_rotLens (v : UnitAddCircle) : Continuous (rotLens v) := by
  refine (Topology.IsQuotientMap.continuous_iff
    (f := (Quotient.mk'' : CapTorus ⊕ ConfTorus → LensSpace))
    isQuotientMap_quotient_mk').mpr ?_
  have h : (rotLens v) ∘ (Quotient.mk'' : CapTorus ⊕ ConfTorus → LensSpace)
      = (Quotient.mk'' : CapTorus ⊕ ConfTorus → LensSpace) ∘ rotLensSum v := by
    funext p
    rfl
  rw [h]
  exact continuous_lensMk.comp (continuous_rotLensSum v)

lemma continuous_rotCapping (v : UnitAddCircle) : Continuous (rotCapping v) := by
  refine (Topology.IsQuotientMap.continuous_iff
    (f := (Quotient.mk'' : ConfigPiece ⊕ CapPiece → CappingSpace))
    isQuotientMap_quotient_mk').mpr ?_
  have h : (rotCapping v) ∘ (Quotient.mk'' : ConfigPiece ⊕ CapPiece → CappingSpace)
      = (Quotient.mk'' : ConfigPiece ⊕ CapPiece → CappingSpace) ∘ rotSum v := by
    funext p
    rfl
  rw [h]
  exact continuous_cappingMk.comp (continuous_rotSum v)

/-! ## The target -/

theorem rotLens_rotCapping_isAction :
    (∀ u v : UnitAddCircle, Work.Drive.rotLens (u + v) = Work.Drive.rotLens u ∘ Work.Drive.rotLens v) ∧
    (∀ u v : UnitAddCircle, Work.Drive.rotCapping (u + v) = Work.Drive.rotCapping u ∘ Work.Drive.rotCapping v) ∧
    Work.Drive.rotLens (0 : UnitAddCircle) = id ∧
    Work.Drive.rotCapping (0 : UnitAddCircle) = id ∧
    (∀ v : UnitAddCircle, Continuous (Work.Drive.rotLens v)) ∧
    (∀ v : UnitAddCircle, Continuous (Work.Drive.rotCapping v)) :=
  ⟨rotLens_add, rotCapping_add, rotLens_zero, rotCapping_zero, continuous_rotLens,
    continuous_rotCapping⟩

end

end Work.Drive
