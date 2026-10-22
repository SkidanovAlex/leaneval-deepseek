import Mathlib
import Submission.Work.ANALYTIC.Basic

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

/-! ## Limits are stable under retracts of functors

`P` is a retract of the free light condensed abelian group `ℤ[ℕ∪{∞}]` (`LightCondensed.P_retract`),
hence `tensorLeft P` is a retract of `tensorLeft ℤ[ℕ∪{∞}]` in the functor category (apply the
functor `tensoringLeft LightCondAb` to the retract).  The first lemma below is the standard
observation that a retract of a limit-preserving functor is limit preserving: given
`i : F ⟶ G`, `r : G ⟶ F` with `i ≫ r = 𝟙 F`, and given that `G` sends a limit cone `c` to a limit
cone, a cone `s` for `F` is pushed forward along `i` to a cone for `G`, lifted along the limit
property of `G`, and retracted back along `r`; uniqueness of the lift uses `i ≫ r = 𝟙 F`. -/

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- The retract identity, objectwise: `(i ≫ r).app X = 𝟙 _` for a retract of functors. -/
theorem retract_app_eq {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (h : Retract F G) (X : C) :
    h.i.app X ≫ h.r.app X = 𝟙 (F.obj X) := by
  have h' := NatTrans.congr_app h.retract X
  simpa only [NatTrans.comp_app, NatTrans.id_app] using h'

/-- If `F` is a retract of the functor `G` and `G` sends the limit cone `c` to a limit cone, then
`F` sends `c` to a limit cone as well.  Only the retract identity `i ≫ r = 𝟙 F` is used. -/
noncomputable def isLimit_mapCone_of_retract {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {F G : C ⥤ D} (h : Retract F G) {J : Type u₃} [Category.{v₃} J]
    {K : J ⥤ C} {c : Cone K} (hg : IsLimit (G.mapCone c)) : IsLimit (F.mapCone c) := by
  refine IsLimit.ofExistsUnique fun s => ?_
  -- push the cone `s` for `F` forward along `i : F ⟶ G`
  let s' : Cone (K ⋙ G) := (Cone.postcompose (Functor.whiskerLeft K h.i)).obj s
  have hs' : ∀ j, s'.π.app j = s.π.app j ≫ h.i.app (K.obj j) := fun j => by
    simp only [s', Cone.postcompose_obj_π, NatTrans.comp_app, Functor.whiskerLeft_app]
  refine ⟨hg.lift s' ≫ h.r.app c.pt, ?_, ?_⟩
  · intro j
    have hfac := hg.fac s' j
    rw [Functor.mapCone_π_app G c j, hs' j] at hfac
    have hr : G.map (c.π.app j) ≫ h.r.app (K.obj j) = h.r.app c.pt ≫ F.map (c.π.app j) :=
      h.r.naturality (c.π.app j)
    rw [Functor.mapCone_π_app F c j, Category.assoc, ← hr, ← Category.assoc, hfac, Category.assoc,
      retract_app_eq h (K.obj j)]
    simp
  · intro m hm
    simp only [Functor.mapCone_π_app] at hm
    have hm' : m ≫ h.i.app c.pt = hg.lift s' := by
      apply hg.uniq s'
      intro j
      have hi : F.map (c.π.app j) ≫ h.i.app (K.obj j) = h.i.app c.pt ≫ G.map (c.π.app j) :=
        h.i.naturality (c.π.app j)
      rw [Functor.mapCone_π_app G c j, Category.assoc, ← hi, ← Category.assoc, hm j, ← hs' j]
    calc m = m ≫ 𝟙 (F.obj c.pt) := (Category.comp_id m).symm
      _ = m ≫ (h.i.app c.pt ≫ h.r.app c.pt) := by rw [retract_app_eq h c.pt]
      _ = (m ≫ h.i.app c.pt) ≫ h.r.app c.pt := (Category.assoc _ _ _).symm
      _ = hg.lift s' ≫ h.r.app c.pt := by rw [hm']

/-- A retract of a functor preserving limits of shape `J` also preserves limits of shape `J`. -/
theorem preservesLimitsOfShape_of_retract {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F G : C ⥤ D} (h : Retract F G) (J : Type u₃) [Category.{v₃} J]
    [PreservesLimitsOfShape J G] : PreservesLimitsOfShape J F where
  preservesLimit := fun {_K} =>
    ⟨fun {_c} hc => ⟨isLimit_mapCone_of_retract h (isLimitOfPreserves G hc)⟩⟩

/-- A retract of a functor preserving finite limits also preserves finite limits. -/
theorem preservesFiniteLimits_of_retract {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F G : C ⥤ D} (h : Retract F G) [PreservesFiniteLimits G] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_retract h J

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- `P = ℤ[ℕ∪{∞}]/ℤ[∞]` is flat, i.e. `tensorLeft P` preserves finite limits.  This is the
instance needed to build `(tensorLeft P).mapDerivedCategory` (hence `PreSolid`).  Route: by
`Submission.Blueprint.FlatProp`, `tensorLeft ℤ[ℕ∪{∞}]` preserves finite limits, and `P` is a retract
of `ℤ[ℕ∪{∞}]` (`LightCondensed.P_retract`), so `tensorLeft P` is a retract of an exact functor;
finite limits are stable under retracts (a retract of a limit cone is a limit cone, by the
retract identities).  Note `Submission.Blueprint.FlatProp` is available through
`Submission.Work.ANALYTIC.Basic`. -/
theorem flat_P (hflat : Submission.Blueprint.FlatProp) :
    PreservesFiniteLimits (tensorLeft _root_.LightCondensed.P) := by
  haveI hfree : PreservesFiniteLimits (tensorLeft ((free ℤ).obj (ℕ∪{∞}).toCondensed)) :=
    hflat ((ℕ∪{∞}).toCondensed)
  exact preservesFiniteLimits_of_retract
    (LightCondensed.P_retract.map (tensoringLeft LightCondAb))

end Work.ANALYTIC

/-- The statement of `Work.ANALYTIC.Work.ANALYTIC.flat_P` under the name
`Work.ANALYTIC.flat_P`, which is the name derived from the module path
`Submission.Work.ANALYTIC.flat_P`. -/
theorem flat_P (hflat : Submission.Blueprint.FlatProp) :
    PreservesFiniteLimits (tensorLeft _root_.LightCondensed.P) :=
  _root_.Work.ANALYTIC.Work.ANALYTIC.flat_P hflat

end

end Work.ANALYTIC
