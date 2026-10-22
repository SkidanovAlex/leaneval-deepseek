import Mathlib
import Submission.Work.ATOM.Toolkit.EA
import Submission.Work.ATOM.zfreeTensorIso_natural
import Submission.Work.ATOM.Defs
import Submission.Work.ANALYTIC.whiskerRight_sub_lightCondMod

/-!
# The quotient map `ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]` is `shift`-equivariant

The epimorphism `EA S : ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]` of
`Submission/Work/ATOM/Toolkit/EA.lean` is the quotient killing the sub-object
`ℤ[{∞} × S]`.  Both sides carry a "shift" endomorphism:

* on `P ⊗ ℤ[S]` it is `oneMinusShift ▷ ℤ[S] = (1 - S) ⊗ id`, where `P = ℤ[ℕ∪{∞}]/ℤ[∞]` and
  `S` denotes the shift operator on `P` (see `ChallengeDeps`);
* on `ℤ[(ℕ∪{∞}) × S]` it is `1 - (shift × id)`.

`EA_shift` says that these two endomorphisms are intertwined by `EA S`.  This is the identity
that makes the *reduced* quotient map a map of `P`-modules, and is the input of the
`1 - S`-calculus of `REFS/03` in the case of an arbitrary light profinite `S`
(compare `Work.ATOM.homD_pre_oneMinusShift_bijective`).

The proof is elementary once the two structural facts below are available:
`zmap` is compatible with the tensorator `zfreeTensorIso` (naturality of the tensorator of the
monoidal functor `ℤ[-]`), and `oneMinusShift` is by construction the descent of
`oneMinusShift' = 1 - shift` along the cokernel projection `P_proj`.
-/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid

/-- `zmap` intertwines the tensorator `zfreeTensorIso` with the tensor product: the naturality
square of the tensorator of the monoidal functor `ℤ[-]` in its first variable.
(This is `Work.ATOM.zfreeTensorIso_natural` with the second variable set to `𝟙 Y`.) -/
theorem zmap_whiskerRight_zfreeTensorIso {X X' Y : LightProfinite.{0}} (f : X ⟶ X') :
    (Work.ATOM.zmap f ▷ Work.ATOM.zfree Y) ≫ (Work.ATOM.zfreeTensorIso X' Y).hom =
      (Work.ATOM.zfreeTensorIso X Y).hom ≫ Work.ATOM.zmap (f ▷ Y) := by
  -- `zfreeTensorIso` is the tensorator `μ` of the monoidal functor `lightProfiniteToLightCondSet ⋙
  -- free ℤ`, and `zmap` is its action on morphisms.
  have hμ : ∀ (A B : LightProfinite.{0}),
      (Work.ATOM.zfreeTensorIso A B).hom
        = Functor.LaxMonoidal.μ (lightProfiniteToLightCondSet ⋙ free ℤ) A B := fun _ _ => rfl
  rw [hμ]
  exact Functor.LaxMonoidal.μ_natural_left (F := lightProfiniteToLightCondSet ⋙ free ℤ) f Y

/-- `oneMinusShift` on `P = ℤ[ℕ∪{∞}]/ℤ[∞]` is the descent of `oneMinusShift' = 1 - shift` on
`ℤ[ℕ∪{∞}]`; unwinding the definition of a descent along a cokernel projection gives
`P_proj ≫ oneMinusShift = oneMinusShift' ≫ P_proj`. -/
theorem P_proj_oneMinusShift :
    LightCondensed.P_proj ≫ LightCondensed.oneMinusShift =
      LightCondensed.oneMinusShift' ≫ LightCondensed.P_proj :=
  cokernel.π_desc_assoc _ _ _ _

/-- **`EA` is `shift`-equivariant.**  With `EA S : ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]` the quotient
killing `ℤ[{∞} × S]`, the morphism `1 - S` on `P ⊗ ℤ[S]` corresponds to `1 - (shift × id)` on
`ℤ[(ℕ∪{∞}) × S]`. -/
theorem EA_shift (S : LightProfinite.{0}) :
    Work.ATOM.EA S ≫ (oneMinusShift ▷ Work.ATOM.zfree S) =
      (𝟙 _ - Work.ATOM.zmap (LightProfinite.shift ▷ S)) ≫ Work.ATOM.EA S := by
  have hcoh := zmap_whiskerRight_zfreeTensorIso (X := ℕ∪{∞}) (X' := ℕ∪{∞}) (Y := S)
    LightProfinite.shift
  -- Conjugate the coherence square by the isomorphism `zfreeTensorIso`: `zmap (shift ▷ S)` is the
  -- transport of `zmap shift ▷ ℤ[S]` along `e = zfreeTensorIso (ℕ∪{∞}) S`.
  have h2 : (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv ≫
        (Work.ATOM.zmap LightProfinite.shift ▷ Work.ATOM.zfree S) ≫
          (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).hom =
      Work.ATOM.zmap (LightProfinite.shift ▷ S) := by
    calc (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv ≫
          (Work.ATOM.zmap LightProfinite.shift ▷ Work.ATOM.zfree S) ≫
            (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).hom
        = (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv ≫
            ((Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).hom ≫
              Work.ATOM.zmap (LightProfinite.shift ▷ S)) := by rw [hcoh]
      _ = Work.ATOM.zmap (LightProfinite.shift ▷ S) := by
            rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hZS : Work.ATOM.zmap (LightProfinite.shift ▷ S) ≫
        (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv =
      (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv ≫
        (Work.ATOM.zmap LightProfinite.shift ▷ Work.ATOM.zfree S) := by
    calc Work.ATOM.zmap (LightProfinite.shift ▷ S) ≫ (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv
        = ((Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv ≫
            (Work.ATOM.zmap LightProfinite.shift ▷ Work.ATOM.zfree S) ≫
              (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).hom) ≫
              (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv := by rw [h2]
      _ = (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv ≫
            (Work.ATOM.zmap LightProfinite.shift ▷ Work.ATOM.zfree S) := by
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- Whiskering distributes over subtraction (this is the only place where the additivity of the
  -- monoidal structure of `LightCondAb` is used).
  have hcomp : (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv ≫
      (𝟙 ((Work.ATOM.zfree (ℕ∪{∞})) ⊗ (Work.ATOM.zfree S)) -
        (Work.ATOM.zmap LightProfinite.shift ▷ Work.ATOM.zfree S)) =
      (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv -
        (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv ≫
          (Work.ATOM.zmap LightProfinite.shift ▷ Work.ATOM.zfree S) := by
    rw [Preadditive.comp_sub, Category.comp_id]
  have hU : LightCondensed.oneMinusShift' ▷ Work.ATOM.zfree S =
      𝟙 ((Work.ATOM.zfree (ℕ∪{∞})) ⊗ (Work.ATOM.zfree S)) -
        (Work.ATOM.zmap LightProfinite.shift ▷ Work.ATOM.zfree S) := by
    rw [LightCondensed.oneMinusShift',
      whiskerRight_sub_lightCondMod ℤ (Work.ATOM.zfree S)]
    exact congrArg (fun t => t - (Work.ATOM.zmap LightProfinite.shift ▷ Work.ATOM.zfree S))
      (MonoidalCategory.id_whiskerRight (Work.ATOM.zfree (ℕ∪{∞})) (Work.ATOM.zfree S))
  -- Unfold `EA` and compute both composites down to the same normal form.
  simp only [Work.ATOM.EA]
  rw [← Category.assoc]
  rw [Preadditive.sub_comp]
  rw [Category.id_comp]
  rw [hZS]
  rw [← hcomp]
  rw [Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight]
  rw [P_proj_oneMinusShift]
  rw [MonoidalCategory.comp_whiskerRight]
  rw [hU]
  rw [Category.assoc]

end Work.ANALYTIC
