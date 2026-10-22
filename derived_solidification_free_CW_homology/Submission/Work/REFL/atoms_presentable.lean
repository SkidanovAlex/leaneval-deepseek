import Mathlib
import Submission.Work.REFL.Basic

/-!
# AREA REFL — the free objects `ℤ[S]` are finitely presentable

This file proves `Work.REFL.atoms_presentable`: the free light condensed abelian group `ℤ[S]` on
a light profinite set `S` is `ℵ₀`-presentable (compact), i.e. `Hom(ℤ[S], -)` commutes with
filtered colimits.

The only input is `Work.REFL.SectionsFiltered`, the statement that filtered colimits of light
condensed abelian groups are computed sectionwise, i.e. that `M ↦ M(S)` preserves filtered
colimits.

The argument is the one announced in `Submission/Work/REFL/Basic.lean`:

* `Work.REFL.atomPoints` identifies `Hom(ℤ[S], M)` with the `S`-sections of `M`.  The
  free–forgetful adjunction `free ℤ ⊣ forget ℤ` (`LightCondensed.freeForgetAdjunction`)
  transports `Hom(ℤ[S], M)` to `Hom_{LightCondSet}(ℤ[S]₀, M₀)` for the underlying light
  condensed sets, and the sheaf-Yoneda lemma (`GrothendieckTopology.yonedaEquiv`) computes the
  latter as `M₀(S) = M(S)`.
* `Work.REFL.atomPoints_natural` says this identification is natural in `M`.
* Combining with `SectionsFiltered`, the functor `Hom(ℤ[S], -)` preserves filtered colimits,
  which is the elementwise formulation of `IsCardinalPresentable` provided by
  `CategoryTheory.IsCardinalPresentable.mk`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.REFL

open _root_.LightCondensed

/-- Sections at a light profinite set, followed by the underlying-set functor of `ModuleCat`,
as a functor to `Type`. -/
abbrev sectionsSet (S : LightProfinite.{0}) : LightCondAb ⥤ Type :=
  sections S ⋙ CategoryTheory.forget (ModuleCat.{0} ℤ)

/-- **The points of `ℤ[S]`.**  The bijection `Hom(ℤ[S], M) ≃ M(S)`, obtained by combining the
free–forgetful adjunction `free ℤ ⊣ forget ℤ` with the sheaf-Yoneda lemma.

The right-hand side is written using `LightCondensed.forget` rather than `sectionsSet S`, so that
the two composite equivalences are definitionally aligned. -/
noncomputable def atomPoints (S : LightProfinite.{0}) (M : LightCondAb) :
    (((LightCondensed.free ℤ).obj ((coherentTopology LightProfinite.{0}).yoneda.obj S)) ⟶ M) ≃
      (((LightCondensed.forget ℤ).obj M).obj.obj (Opposite.op S)) :=
  (((LightCondensed.freeForgetAdjunction ℤ).homEquiv
      ((coherentTopology LightProfinite.{0}).yoneda.obj S) M).trans
    ((coherentTopology LightProfinite.{0}).yonedaEquiv))

/-- **Naturality of `atomPoints`.**  Both ingredients (`Adjunction.homEquiv` in its right variable,
and `GrothendieckTopology.yonedaEquiv`) are natural. -/
theorem atomPoints_natural (S : LightProfinite.{0}) {M N : LightCondAb} (f : M ⟶ N)
    (g : ((LightCondensed.free ℤ).obj ((coherentTopology LightProfinite.{0}).yoneda.obj S)) ⟶ M) :
    atomPoints S N (g ≫ f) =
      (((LightCondensed.forget ℤ).map f).hom.app (Opposite.op S)) (atomPoints S M g) := by
  simp only [atomPoints, Equiv.trans_apply]
  rw [CategoryTheory.Adjunction.homEquiv_naturality_right]
  rw [GrothendieckTopology.yonedaEquiv_comp]

/-- **`ℤ[S]` is `ℵ₀`-presentable.**  Stated for the representable object
`(coherentTopology LightProfinite).yoneda.obj S`, which is definitionally `S.toCondensed`.

Proof.  We use the elementwise characterisation `CategoryTheory.IsCardinalPresentable.mk` of
presentability.  Let `c` be a colimit cocone in `LightCondAb` over a functor `F` indexed by an
`ℵ₀`-filtered category `J` (which is in particular filtered).  Since `sections S` preserves
`J`-colimits (`SectionsFiltered`), and the forgetful functor of `ModuleCat` does too, the functor
`sectionsSet S` preserves them, so `(sectionsSet S).mapCocone c` is a colimit cocone in `Type`,
where the elementwise description of filtered colimits of types applies
(`Types.jointly_surjective_of_isColimit`, `Types.FilteredColimit.isColimit_eq_iff'`).
Transporting along `atomPoints` (natural in the target, hence compatible with the cocone maps)
gives both required conditions. -/
theorem atoms_presentable_aux (h : Work.REFL.SectionsFiltered) (S : LightProfinite.{0}) :
    CategoryTheory.IsCardinalPresentable
      ((LightCondensed.free ℤ).obj ((coherentTopology LightProfinite.{0}).yoneda.obj S))
      (Cardinal.aleph0 : Cardinal.{0}) := by
  refine CategoryTheory.IsCardinalPresentable.mk (fun J _ _ F c hc => ?_)
  have hfil : IsFiltered J := isFiltered_of_isCardinalFiltered J (Cardinal.aleph0 : Cardinal.{0})
  have hpres : PreservesColimitsOfShape J (sectionsSet S) := by
    have := h J S
    infer_instance
  have hcΦ : IsColimit ((sectionsSet S).mapCocone c) := isColimitOfPreserves (sectionsSet S) hc
  constructor
  · -- every morphism `ℤ[S] ⟶ c.pt` factors through a single stage
    intro g
    obtain ⟨j, a, ha⟩ := Types.jointly_surjective_of_isColimit hcΦ (atomPoints S c.pt g)
    refine ⟨j, (atomPoints S (F.obj j)).symm a, ?_⟩
    apply (atomPoints S c.pt).injective
    rw [atomPoints_natural]
    rw [show atomPoints S (F.obj j) ((atomPoints S (F.obj j)).symm a) = a from
      Equiv.apply_symm_apply _ _]
    exact ha
  · -- two morphisms that agree after a stage agree after a later stage
    intro j f₁ f₂ hff
    have h2 : (sectionsSet S).map (c.ι.app j) (atomPoints S (F.obj j) f₁) =
        (sectionsSet S).map (c.ι.app j) (atomPoints S (F.obj j) f₂) := by
      change (((LightCondensed.forget ℤ).map (c.ι.app j)).hom.app (Opposite.op S))
          (atomPoints S (F.obj j) f₁) =
        (((LightCondensed.forget ℤ).map (c.ι.app j)).hom.app (Opposite.op S))
          (atomPoints S (F.obj j) f₂)
      rw [← atomPoints_natural, ← atomPoints_natural, hff]
    obtain ⟨j', a, ha⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hcΦ (atomPoints S (F.obj j) f₁)
        (atomPoints S (F.obj j) f₂)).mp h2
    refine ⟨j', a, ?_⟩
    apply (atomPoints S (F.obj j')).injective
    rw [atomPoints_natural, atomPoints_natural]
    exact ha

theorem atoms_presentable (h : Work.REFL.SectionsFiltered) : Work.REFL.AtomsPresentable := by
  intro S
  exact atoms_presentable_aux h S

end Work.REFL
