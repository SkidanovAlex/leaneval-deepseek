import Mathlib
import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

/-- **An open immersion over `Spec 𝕜` between irreducible `𝕜`-schemes induces a `𝕜`-linear
isomorphism of function fields.**

For an open immersion `j : U ⟶ Z` of irreducible schemes with `j ≫ (Z ↘ Spec 𝕜) = (U ↘ Spec 𝕜)`,
the stalk map `j.stalkMap (genericPoint U)` (transported along
`AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion` so that its source is `κ(Z)`) is an
isomorphism `κ(Z) ≃+* κ(U)`, and it intertwines the structure maps
`Work.CrauderKatz.functionFieldResMap 𝕜 Z` and `Work.CrauderKatz.functionFieldResMap 𝕜 U`.

The intertwining is proved at the level of global sections: by
`AlgebraicGeometry.Scheme.Hom.germ_stalkMap` with `U := ⊤` and
`(Z ↘ Spec 𝕜).appTop ≫ j.appTop = (U ↘ Spec 𝕜).appTop`
(`AlgebraicGeometry.Scheme.Hom.comp_appTop` and the hypothesis `hj`), the composite
`Z.germToFunctionField ⊤ ≫ F` equals `j.appTop ≫ U.germToFunctionField ⊤`; applying
`ΓSpecIso.inv ≫` on the left gives the claim. -/
theorem functionFieldEquiv_of_isOpenImmersionOver (𝕜 : Type) [Field 𝕜] {U Z : Scheme.{0}}
    [IrreducibleSpace U] [IrreducibleSpace Z]
    [U.Over (Spec (CommRingCat.of 𝕜))] [Z.Over (Spec (CommRingCat.of 𝕜))]
    (j : U ⟶ Z) [IsOpenImmersion j]
    (hj : j ≫ (Z ↘ Spec (CommRingCat.of 𝕜)) = (U ↘ Spec (CommRingCat.of 𝕜))) :
    ∃ e : (Z.functionField : Type) ≃+* (U.functionField : Type),
      e.toRingHom.comp (Work.CrauderKatz.functionFieldResMap 𝕜 Z) =
        Work.CrauderKatz.functionFieldResMap 𝕜 U := by
  let htopU : Nonempty (⊤ : U.Opens) := ⟨⟨genericPoint U, trivial⟩⟩
  let htopZ : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  -- An open immersion carries the generic point of its source to that of its target.
  have hgen : j (genericPoint U) = genericPoint Z := genericPoint_eq_of_isOpenImmersion j
  -- The induced map on stalks, with source `κ(Z) = Z.presheaf.stalk (genericPoint Z)`.
  let F : Z.functionField ⟶ U.functionField :=
    (Z.presheaf.stalkCongr (Inseparable.of_eq hgen)).inv ≫ j.stalkMap (genericPoint U)
  haveI : IsIso F := inferInstance
  refine ⟨(asIso F).commRingCatIsoToRingEquiv, ?_⟩
  change F.hom.comp (Work.CrauderKatz.functionFieldResMap 𝕜 Z) =
    Work.CrauderKatz.functionFieldResMap 𝕜 U
  -- `F` intertwines the germs at the generic points.
  have hgerm : Z.germToFunctionField ⊤ ≫ F = j.appTop ≫ U.germToFunctionField ⊤ := by
    have h1 : Z.germToFunctionField ⊤ ≫
        (Z.presheaf.stalkCongr (Inseparable.of_eq hgen)).inv =
        Z.presheaf.germ ⊤ (j (genericPoint U)) (by trivial) := by
      rw [TopCat.Presheaf.stalkCongr_inv]
      exact TopCat.Presheaf.germ_stalkSpecializes (Z.presheaf) (by trivial)
        (Inseparable.of_eq hgen).le
    have h2 : Z.presheaf.germ ⊤ (j (genericPoint U)) (by trivial) ≫
        j.stalkMap (genericPoint U) = j.appTop ≫ U.germToFunctionField ⊤ := by
      rw [Hom.germ_stalkMap j ⊤ (genericPoint U) trivial]
      simp only [Hom.preimage_top j]
    rw [show F = (Z.presheaf.stalkCongr (Inseparable.of_eq hgen)).inv ≫
        j.stalkMap (genericPoint U) from rfl, ← Category.assoc, h1, h2]
  -- Apply `ΓSpecIso.inv ≫ _` on the left and use that `j` is a morphism over `Spec 𝕜`.
  have hmain : (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
      (Z ↘ Spec (CommRingCat.of 𝕜)).appTop ≫ Z.germToFunctionField ⊤ ≫ F =
      (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
      (U ↘ Spec (CommRingCat.of 𝕜)).appTop ≫ U.germToFunctionField ⊤ := by
    calc (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
          (Z ↘ Spec (CommRingCat.of 𝕜)).appTop ≫ Z.germToFunctionField ⊤ ≫ F
        = (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
            ((Z ↘ Spec (CommRingCat.of 𝕜)).appTop ≫
              (Z.germToFunctionField ⊤ ≫ F)) := rfl
      _ = (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
            ((Z ↘ Spec (CommRingCat.of 𝕜)).appTop ≫
              (j.appTop ≫ U.germToFunctionField ⊤)) := by rw [hgerm]
      _ = (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
            (((Z ↘ Spec (CommRingCat.of 𝕜)).appTop ≫ j.appTop) ≫
              U.germToFunctionField ⊤) := by
            rw [← Category.assoc ((Z ↘ Spec (CommRingCat.of 𝕜)).appTop) j.appTop
              (U.germToFunctionField ⊤)]
      _ = (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
            ((U ↘ Spec (CommRingCat.of 𝕜)).appTop ≫ U.germToFunctionField ⊤) := by
            rw [← Hom.comp_appTop j (Z ↘ Spec (CommRingCat.of 𝕜)), hj]
  exact congrArg CommRingCat.Hom.hom hmain

/-- **A partial isomorphism over `Spec 𝕜` between integral `𝕜`-schemes induces a `𝕜`-linear isomorphism of function fields.**

`X`, `Y` are integral schemes over `Spec 𝕜`, and `i` is a partial isomorphism between them which is
a morphism over `Spec 𝕜` (`i.IsOver`).  Then the function fields `κ(X)`, `κ(Y)` are isomorphic in a
way compatible with the structure maps `Work.CrauderKatz.functionFieldResMap 𝕜 X : 𝕜 → κ(X)` and
`Work.CrauderKatz.functionFieldResMap 𝕜 Y : 𝕜 → κ(Y)`.

Suggested route.  For an open immersion `j : U ⟶ Z` between integral schemes over `Spec 𝕜` (with
`j ≫ (Z ↘ Spec 𝕜) = (U ↘ Spec 𝕜)`), the stalk map `j.stalkMap (genericPoint U)` is an isomorphism of
`κ(Z)` onto `κ(U)` (transport it along `AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion`, which
needs only irreducibility of `U` and `Z`), and it intertwines the structure maps: by
`AlgebraicGeometry.Scheme.Hom.germ_stalkMap` with `U := ⊤`,
`germ_Z ⊤ ≫ j.stalkMap η_U = j.appTop ≫ germ_U ⊤`, and `(Z ↘ Spec 𝕜).appTop ≫ j.appTop =
(U ↘ Spec 𝕜).appTop`; hence applying `ΓSpecIso.inv ≫` gives the compatibility.  Now apply this three
times: to `i.source.ι` (giving `κ(X) ≅ κ(i.source)`, with the `Over`-structure
`⟨i.source.ι ≫ (X ↘ Spec 𝕜)⟩` on `i.source.toScheme` — note `i.source` and `i.target` are nonempty
because they are dense in the irreducible `X`, `Y`), to `i.iso.hom : i.source.toScheme ≅
i.target.toScheme` over `Spec 𝕜` (which is exactly the `i.IsOver` hypothesis), and to
`i.target.ι`; compose. -/
theorem funFieldAlgEquiv_of_partialIsoOver (𝕜 : Type) [Field 𝕜] (X Y : AlgebraicGeometry.Scheme)
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [AlgebraicGeometry.Scheme.Over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [AlgebraicGeometry.Scheme.Over Y (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (h : ∃ i : AlgebraicGeometry.Scheme.PartialIso X Y,
      AlgebraicGeometry.Scheme.PartialIso.IsOver
        (CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
        (CategoryTheory.over Y (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))) i) :
    ∃ e : (X.functionField : Type) ≃+* (Y.functionField : Type),
      e.toRingHom.comp (Work.CrauderKatz.functionFieldResMap 𝕜 X) =
        Work.CrauderKatz.functionFieldResMap 𝕜 Y := by
  obtain ⟨i, hi⟩ := h
  -- The source and target of `i` are nonempty (dense in an irreducible scheme).
  haveI hneS : Nonempty (↑i.source) := by
    obtain ⟨x, hx⟩ := i.dense_source.nonempty
    exact ⟨⟨x, hx⟩⟩
  haveI hneT : Nonempty (↑i.target) := by
    obtain ⟨y, hy⟩ := i.dense_target.nonempty
    exact ⟨⟨y, hy⟩⟩
  -- The `Over (Spec 𝕜)`-structures induced on the source and target of `i`.
  letI srcOver : (i.source.toScheme).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨i.source.ι ≫ (X ↘ Spec (CommRingCat.of 𝕜))⟩
  letI tgtOver : (i.target.toScheme).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨i.target.ι ≫ (Y ↘ Spec (CommRingCat.of 𝕜))⟩
  -- (1) `κ(X) ≅ κ(i.source)` via the open immersion `i.source.ι`.
  obtain ⟨e₁, he₁⟩ := functionFieldEquiv_of_isOpenImmersionOver (𝕜 := 𝕜)
    (Z := X) (U := ↑i.source) i.source.ι rfl
  -- (2) `κ(i.target) ≅ κ(i.source)` via the isomorphism `i.iso.hom`, which is over `Spec 𝕜`
  --     exactly by the hypothesis `hi`.
  obtain ⟨e₂, he₂⟩ := functionFieldEquiv_of_isOpenImmersionOver (𝕜 := 𝕜)
    (Z := ↑i.target) (U := ↑i.source) i.iso.hom
      (show i.iso.hom ≫ (↑i.target ↘ Spec (CommRingCat.of 𝕜)) =
        (↑i.source ↘ Spec (CommRingCat.of 𝕜)) from hi)
  -- (3) `κ(Y) ≅ κ(i.target)` via the open immersion `i.target.ι`.
  obtain ⟨e₃, he₃⟩ := functionFieldEquiv_of_isOpenImmersionOver (𝕜 := 𝕜)
    (Z := Y) (U := ↑i.target) i.target.ι rfl
  refine ⟨e₁.trans (e₂.symm.trans e₃.symm), ?_⟩
  ext a
  show e₃.symm (e₂.symm (e₁ ((Work.CrauderKatz.functionFieldResMap 𝕜 X) a))) =
    (Work.CrauderKatz.functionFieldResMap 𝕜 Y) a
  rw [show e₁ ((Work.CrauderKatz.functionFieldResMap 𝕜 X) a) =
      (Work.CrauderKatz.functionFieldResMap 𝕜 (↑i.source)) a from
        RingHom.congr_fun he₁ a]
  rw [show e₂.symm ((Work.CrauderKatz.functionFieldResMap 𝕜 (↑i.source)) a) =
      (Work.CrauderKatz.functionFieldResMap 𝕜 (↑i.target)) a from by
    have hc : e₂ ((Work.CrauderKatz.functionFieldResMap 𝕜 (↑i.target)) a) =
        (Work.CrauderKatz.functionFieldResMap 𝕜 (↑i.source)) a :=
      RingHom.congr_fun he₂ a
    rw [← hc, RingEquiv.symm_apply_apply]]
  rw [show e₃.symm ((Work.CrauderKatz.functionFieldResMap 𝕜 (↑i.target)) a) =
      (Work.CrauderKatz.functionFieldResMap 𝕜 Y) a from by
    have hc : e₃ ((Work.CrauderKatz.functionFieldResMap 𝕜 Y) a) =
        (Work.CrauderKatz.functionFieldResMap 𝕜 (↑i.target)) a :=
      RingHom.congr_fun he₃ a
    rw [← hc, RingEquiv.symm_apply_apply]]

end

end Work.K3Inputs
