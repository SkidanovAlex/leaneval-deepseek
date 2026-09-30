import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

set_option linter.style.haveILetI false

universe u

namespace Work.Domain.Engine

namespace AffineFiberCrux

/-! ## The `S`-fibre of `Y` at `x` -/

/-- The `S`-fibre `Spec κ(x) ×_S Y` of `Y` at `x`. -/
noncomputable abbrev baseChange (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (x : X) : Scheme.{u} :=
  Limits.pullback ((X.fromSpecResidueField x) ≫ Work.Domain.overHom S X) (Work.Domain.overHom S Y)

/-- The canonical morphism `Spec κ(x) ×_S Y ⟶ X ×_S Y`. -/
noncomputable abbrev baseChangeToProd (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (x : X) : baseChange S X Y x ⟶ Work.Domain.prod S X Y :=
  pullback.lift (pullback.fst _ _ ≫ X.fromSpecResidueField x) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

/-- The structure morphism `Spec κ(x) ×_S Y ⟶ Y` is affine: it is the base change of the affine
morphism `Spec κ(x) ⟶ S`. -/
lemma isAffineHom_baseChangeπ (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S] (x : X) :
    IsAffineHom (pullback.snd ((X.fromSpecResidueField x) ≫ Work.Domain.overHom S X)
      (Work.Domain.overHom S Y)) := by
  haveI hc : IsAffineHom ((X.fromSpecResidueField x) ≫ Work.Domain.overHom S X) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun s => ?_
    obtain ⟨U, hUaff, hsU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := S) (x := s) (U := ⊤) trivial
    exact ⟨U, hsU, hUaff, IsAffineOpen.of_subsingleton fun a _ b _ => Subsingleton.elim a b⟩
  haveI : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom)
      (Work.Domain.overHom S Y) :=
    MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStableUnderBaseChange _ _
  exact MorphismProperty.pullback_snd _ _ hc

/-! ## The fibre of `pr₁` over `x` -/

/-- The fibre `Γ ×_X Spec κ(x)` of `pr₁` over `x`, in raw pullback form. -/
noncomputable abbrev fiberRaw (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] (x : X) : Scheme.{u} :=
  Limits.pullback (Work.Domain.PartialMap.pr₁ S g) (X.fromSpecResidueField x)

/-- The scheme `Spec κ(x) ×_X (X ×_S Y)`. -/
noncomputable abbrev fiberOverX (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (x : X) : Scheme.{u} :=
  Limits.pullback (pullback.fst (Work.Domain.overHom S X) (Work.Domain.overHom S Y))
    (X.fromSpecResidueField x)

/-- The projection `Spec κ(x) ×_X (X ×_S Y) ⟶ X ×_S Y`. -/
noncomputable abbrev fiberOverXToProd (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (x : X) : fiberOverX S X Y x ⟶ Work.Domain.prod S X Y :=
  pullback.fst (pullback.fst (Work.Domain.overHom S X) (Work.Domain.overHom S Y))
    (X.fromSpecResidueField x)

/-- The double pullback `Γ ×_{X ×_S Y} (Spec κ(x) ×_X (X ×_S Y))`. -/
noncomputable abbrev graphOverFiberOverX (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] (x : X) : Scheme.{u} :=
  Limits.pullback (Work.Domain.PartialMap.graphι S g) (fiberOverXToProd S X Y x)

/-- Pasting isomorphism: the double pullback computing the fibre of `pr₁` over `x`. -/
noncomputable abbrev pasteIso (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] (x : X) :
    graphOverFiberOverX S X Y g x ≅ fiberRaw S X Y g x :=
  pullbackRightPullbackFstIso (pullback.fst (Work.Domain.overHom S X) (Work.Domain.overHom S Y))
    (X.fromSpecResidueField x) (Work.Domain.PartialMap.graphι S g)

/-- Symmetry isomorphism `Spec κ(x) ×_X (X ×_S Y) ≅ (X ×_S Y) ×_X Spec κ(x)`. -/
noncomputable abbrev symmIso (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (x : X) : fiberOverX S X Y x ≅
      Limits.pullback (X.fromSpecResidueField x)
        (pullback.fst (Work.Domain.overHom S X) (Work.Domain.overHom S Y)) :=
  pullbackSymmetry (pullback.fst (Work.Domain.overHom S X) (Work.Domain.overHom S Y))
    (X.fromSpecResidueField x)

/-- Base change isomorphism `(X ×_S Y) ×_X Spec κ(x) ≅ Spec κ(x) ×_S Y`. -/
noncomputable abbrev baseChangeIso (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (x : X) : Limits.pullback (X.fromSpecResidueField x)
        (pullback.fst (Work.Domain.overHom S X) (Work.Domain.overHom S Y)) ≅ baseChange S X Y x :=
  pullbackRightPullbackFstIso (Work.Domain.overHom S X) (Work.Domain.overHom S Y)
    (X.fromSpecResidueField x)

/-- The canonical morphism from the fibre of `pr₁` over `x` to the `S`-fibre `Spec κ(x) ×_S Y`:
the projection of the double pullback onto its second factor, transported along the pasting
isomorphisms. -/
noncomputable abbrev fibreToBaseChange (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] (x : X) : fiberRaw S X Y g x ⟶ baseChange S X Y x :=
  (pasteIso S X Y g x).inv ≫
    pullback.snd (Work.Domain.PartialMap.graphι S g) (fiberOverXToProd S X Y x) ≫
    (symmIso S X Y x).hom ≫ (baseChangeIso S X Y x).hom

/-- The morphism from the fibre of `pr₁` over `x` to the `S`-fibre of `Y` at `x` is a closed
immersion: it is the base change of the closed immersion `graphι S g` along
`Spec κ(x) ×_S Y ⟶ X ×_S Y`. -/
theorem fibreToBaseChange_isClosedImmersion (S : Scheme.{u}) (X Y : Scheme.{u})
    [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S] (x : X) :
    IsClosedImmersion (fibreToBaseChange S X Y g x) :=
  inferInstance

/-- The closed immersion of the fibre of `pr₁` over `x` into the `S`-fibre of `Y` at `x` lies over
`Y` by the restriction of `pr₂`. -/
lemma fibreToBaseChange_snd (S : Scheme.{u}) (X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] (x : X) :
    fibreToBaseChange S X Y g x ≫
        pullback.snd ((X.fromSpecResidueField x) ≫ Work.Domain.overHom S X)
          (Work.Domain.overHom S Y) =
      pullback.fst (Work.Domain.PartialMap.pr₁ S g) (X.fromSpecResidueField x) ≫
        Work.Domain.PartialMap.pr₂ S g := by
  simp only [fibreToBaseChange, pasteIso, symmIso, baseChangeIso, Category.assoc]
  rw [pullbackRightPullbackFstIso_hom_snd]
  rw [pullbackSymmetry_hom_comp_snd_assoc]
  rw [← pullback.condition_assoc]
  rw [← pullbackRightPullbackFstIso_hom_fst_assoc]
  rw [Iso.inv_hom_id_assoc]

/-! ## A general lemma: an affine morphism into a point has affine source -/

/-- If `f : Z ⟶ Y` is affine and its image is contained in a single point `y`, then `Z` is
affine. -/
lemma isAffine_of_isAffineHom_range_singleton {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    [IsAffineHom f] (y : Y) (h : Set.range ⇑f ⊆ {y}) : IsAffine Z := by
  obtain ⟨U, hUaff, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  have hrange : Set.range ⇑f ⊆ Set.range ⇑(U.ι) := by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨w, rfl⟩
    have : f w = y := h ⟨w, rfl⟩
    rw [this]
    exact hyU
  let φ : Z ⟶ U.toScheme := IsOpenImmersion.lift U.ι f hrange
  have hfac : φ ≫ U.ι = f := IsOpenImmersion.lift_fac U.ι f hrange
  haveI : IsAffineHom (φ ≫ U.ι) := by rw [hfac]; infer_instance
  haveI : IsAffineHom φ := IsAffineHom.of_comp φ U.ι
  haveI : IsAffine U.toScheme := hUaff
  exact isAffine_of_isAffineHom φ

end AffineFiberCrux

theorem affine_fiber_pr1_crux {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S] [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)] (g : AlgebraicGeometry.Scheme.PartialMap X Y) [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g] {x : X} {y₀ : Y} (h : ∀ γ : Work.Domain.PartialMap.graph S g, Work.Domain.PartialMap.pr₁ S g γ = x → Work.Domain.PartialMap.pr₂ S g γ = y₀) : ∃ (B : AlgebraicGeometry.Scheme) (i : (Work.Domain.PartialMap.pr₁ S g).fiber x ⟶ B), AlgebraicGeometry.IsAffine B ∧ AlgebraicGeometry.IsClosedImmersion i := by
  haveI hcrux : IsAffineHom
      (pullback.fst (Work.Domain.PartialMap.pr₁ S g) (X.fromSpecResidueField x) ≫
        Work.Domain.PartialMap.pr₂ S g) := by
    haveI : IsAffineHom (pullback.snd ((X.fromSpecResidueField x) ≫ Work.Domain.overHom S X)
        (Work.Domain.overHom S Y)) := AffineFiberCrux.isAffineHom_baseChangeπ S X Y x
    haveI : IsClosedImmersion (AffineFiberCrux.fibreToBaseChange S X Y g x) :=
      AffineFiberCrux.fibreToBaseChange_isClosedImmersion S X Y g x
    rw [← AffineFiberCrux.fibreToBaseChange_snd S X Y g x]
    infer_instance
  have hrange : Set.range ⇑(pullback.fst (Work.Domain.PartialMap.pr₁ S g)
      (X.fromSpecResidueField x) ≫ Work.Domain.PartialMap.pr₂ S g) ⊆ {y₀} := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    refine h _ ?_
    have hfac := congrArg (fun φ => φ z)
      (pullback.condition (f := Work.Domain.PartialMap.pr₁ S g) (g := X.fromSpecResidueField x))
    simp only [Scheme.Hom.comp_apply] at hfac
    simp only [Work.Domain.PartialMap.pr₁, Scheme.Hom.comp_apply]
    rw [hfac]
    have : X.fromSpecResidueField x
        (pullback.snd (Work.Domain.PartialMap.pr₁ S g) (X.fromSpecResidueField x) z) ∈
        ({x} : Set X) := by
      rw [← Scheme.range_fromSpecResidueField x]
      exact ⟨_, rfl⟩
    simpa using this
  have hZ : IsAffine (AffineFiberCrux.fiberRaw S X Y g x) :=
    AffineFiberCrux.isAffine_of_isAffineHom_range_singleton _ y₀ hrange
  exact ⟨_, 𝟙 _, hZ, inferInstance⟩

end Work.Domain.Engine
