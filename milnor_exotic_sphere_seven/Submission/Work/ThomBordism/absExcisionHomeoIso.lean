import Submission.Work.ThomBordism.absThomCompare

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The metric-free comparison `H^n(Z⁺) ≅ H^n(Z, Z∖0)`: openness, excision, homeomorphism

This file supplies the three geometric/homological facts about the metric-free `Work.ThomBordism`
comparison that its consumers need:

* `Work.ThomBordism.isOpen_absNZ` — `A = (Z∖0) ∪ {∞}` is open in `Z⁺`;
* `Work.ThomBordism.isIso_excChainZ` — the excision of `{∞}` is a quasi-isomorphism;
* `Work.ThomBordism.isIso_homeoChainZ` — the homeomorphism of pairs `(Z, Z∖0) ≅ ({∞}ᶜ, {∞}ᶜ ∩ A)`
  is a quasi-isomorphism.

They are the metric-free copies of `Work.Tubular.isOpen_onePointNonzero`,
`Work.Tubular.isIso_excChain` and `Work.Tubular.isIso_homeoChain`; the only geometric input is the
supplied `NormLike Z`, which makes the zero section compact.
-/

open CategoryTheory Limits
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}

/-! ## Openness of `A = (Z∖0) ∪ {∞}` -/

/-- The zero section inside `Z⁺` is closed: it is the image of a closed compact subset of `Z`. -/
theorem isClosed_onePointZeroZ {Z : RealBundle B F ι} (N : NormLike Z) :
    IsClosed (onePointZeroZ Z) :=
  OnePoint.isClosed_image_coe.mpr ⟨N.isClosed_zero, N.isCompact_zero⟩

/-- The complement of the zero section, inside `Z⁺`, is exactly `A = (Z∖0) ∪ {∞}`. -/
theorem compl_onePointZeroZ (Z : RealBundle B F ι) :
    (onePointZeroZ Z)ᶜ = absNZ Z := by
  ext p
  constructor
  · intro hp
    rw [absNZ, Set.mem_union]
    cases p with
    | infty => exact Or.inr rfl
    | coe q => exact Or.inl ⟨q, fun hq => hp ⟨q, hq, rfl⟩, rfl⟩
  · intro hp hz
    rw [absNZ, Set.mem_union] at hp
    rcases hp with ⟨q, hq, hqp⟩ | hinf
    · rw [← hqp] at hz
      obtain ⟨q', hq', heq⟩ := hz
      rw [OnePoint.coe_eq_coe] at heq
      exact hq (heq ▸ hq')
    · rw [hinf] at hz
      obtain ⟨q, _, hqp⟩ := hz
      exact OnePoint.coe_ne_infty q hqp

/-- **`A` is open in `Z⁺`**: it is the complement of the (compact, hence closed) zero section. -/
theorem isOpen_absNZ {Z : RealBundle B F ι} (N : NormLike Z) : IsOpen (absNZ Z) := by
  rw [← compl_onePointZeroZ Z]
  exact (isClosed_onePointZeroZ N).isOpen_compl

/-- The two open sets `{∞}ᶜ` and `A` cover `Z⁺`. -/
theorem infZ_union_absNZ (Z : RealBundle B F ι) : infZ Z ∪ absNZ Z = Set.univ := by
  rw [infZ, absNZ,
    Set.union_comm (OnePoint.some '' Work.Thom.zeroComplement Z) {OnePoint.infty},
    ← Set.union_assoc, Set.compl_union_self]
  exact Set.univ_union _

/-! ## The excision of `{∞}` and the homeomorphism of pairs -/

/-- **The excision of `{∞}` is a quasi-isomorphism.** -/
theorem isIso_excChainZ {Z : RealBundle B F ι} (N : NormLike Z) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (excChainZ Z) n) := by
  rw [excChainZ]
  exact Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (OnePoint Z.TotalSpace))
    (infZ Z) (absNZ Z) OnePoint.isClosed_infty.isOpen_compl (isOpen_absNZ N)
    (infZ_union_absNZ Z) n

/-- **The homeomorphism of pairs `(Z, Z∖0) ≅ ({∞}ᶜ, {∞}ᶜ ∩ A)` is a quasi-isomorphism.** -/
theorem isIso_homeoChainZ (Z : RealBundle B F ι) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (homeoChainZ Z) n) :=
  Work.Tubular.isIso_relChainsMapOf_homeoSub (X := TopCat.of Z.TotalSpace)
    (Y := TopCat.of ↥(infZ Z)) (someHomeoZ Z) (some_mem_excSubZ Z) (homeoSubMapZ_spec Z) n

theorem absExcisionHomeoIso {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (N : Work.ThomBordism.NormLike Z) (n : ℕ) :
    IsOpen (Work.ThomBordism.absNZ Z) ∧
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.ThomBordism.excChainZ Z) n) ∧
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.ThomBordism.homeoChainZ Z) n) :=
  ⟨isOpen_absNZ N, isIso_excChainZ N n, isIso_homeoChainZ Z n⟩

end

end Work.ThomBordism
