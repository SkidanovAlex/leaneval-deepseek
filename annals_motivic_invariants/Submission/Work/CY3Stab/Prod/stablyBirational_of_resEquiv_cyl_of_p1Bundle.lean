import Mathlib
import Submission.Work.CY3Stab.Prod.CylResEquivAux
import Submission.Work.CY3Stab.Prod.wProd_wProd_one_iso_wProd
import Submission.Work.CY3Stab.Prod.resAlgEquiv_genericPoint_wProd_one
import Submission.Work.CY3Stab.Prod.stablyBirat_of_birationalMap_wProd

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.stablyBirational_of_resEquiv_cyl_of_p1Bundle`

**The cancellation step of the stabilisation of Lin--Shinder's `thm:bir-generation` (c)** (Lin,
Shinder, *Motivic invariants of birational maps*, Annals **199** (1), 2024, proof of
`thm:bir-generation`, case (c), and the appendix `cor-CYnSB`).

If two points `p`, `p'` of an `𝕜`-scheme `P` are `ℙ¹`-bundles over the `𝕜`-varieties `Z`, `Z'`
(`Work.K3Inputs.IsP1BundleOver`: `κ(p) ≅ κ(Z)(t)`, `κ(p') ≅ κ(Z')(t)`), and the *cylinder points*
of `p`, `p'` in `𝔸ᵏ × P` have `𝕜`-isomorphic residue fields, then `Z` and `Z'` are stably
birational.

## Mathematical content

`κ(prodPt P p k) = κ(p)(t₁,…,t_k)` and `κ(p) = κ(Z)(t)`, so the hypothesis is a
`𝕜`-isomorphism `κ(Z)(t₁,…,t_{k+1}) ≅ κ(Z')(t₁,…,t_{k+1})`, i.e. an isomorphism of the function
fields of `Z × 𝔸^{k+1}` and `Z' × 𝔸^{k+1}`; the two varieties are then birational
(`Work.CY3.resEquiv_genericPoint_birationalMap`), whence stable birationality with exponents
`(k+1, k+1)`.

No *cylinder rigidity* (the paper's Lemma `lem-stbirCY`) is used: the number of transcendental
variables on the two sides is the same, so the affine exponent built into
`Work.K3.StablyBirational` absorbs it.  The transpose of this statement — the *rigidity*
`κ(p) ≅ κ(p')` from the cylinder points — is false in general and is *not* claimed here.

## Organisation of the proof

The `ResEquiv` at the cylinder points of `p`, `p'` is replaced by a chain of `ResEquiv` statements
between the *generic points* of the cylinders, through the intermediate cylinder points over the
generic points:

```
genPt (𝔸^{k+1} × Z)  ~~  prodPt Z (genPt Z) (k+1)             [prodPt_genericPoint, X = Z]
                     ~~  prodPt (𝔸¹ × Z) (genPt (𝔸¹ × Z)) k  [nesting: 𝔸ᵏ × 𝔸¹ ≅ 𝔸^{k+1}]
                     ~~  prodPt P p k                         [resEquiv_prodPt_of_resEquiv + (F1) of p]
                     ~~  prodPt P p' k                        [the hypothesis]
                     ~~  genPt (𝔸^{k+1} × Z')                 [the same chain over Z']
```

The pieces are:

* `Work.CY3Stab.Prod.prodPt_genericPoint` (`CylResEquivAux`): the cylinder point over the generic
  point is the generic point of the cylinder (a coheight computation plus
  `Work.K3.eq_genericPoint_of_coheight_eq_zero`);
* `Work.CY3Stab.Prod.wProd_wProd_one_iso_wProd`: the nesting `𝔸ᵏ × (𝔸¹ × X) ≅ 𝔸^{k+1} × X` over
  `Spec 𝕜`, and `Work.CY3Stab.Prod.resEquiv_of_iso` for the transport of `ResEquiv`;
* `Work.CY3Stab.Prod.resAlgEquiv_genericPoint_wProd_one`: the one-variable case `κ(genPt (𝔸¹×X))
  ≅ κ(X)(t)` of the (F1) clause, which together with
  `Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv` transports the `ℙ¹`-bundle structure of `p` to
  the cylinder point;
* `Work.CY3Stab.Prod.stablyBirat_of_birationalMap_wProd`: a birational map of two *equal-exponent*
  cylinders is a stable birationality of the bases (`WProd X n = X ×_𝕜 𝔸ⁿ` is `X ×_𝕜 𝔸ⁿ` with the
  factors exchanged, so the birationality transports along `pullbackSymmetry`).

## A note on the `Over`-structure of the cylinder

`𝔸ᵏ × X` carries *two* natural structure morphisms to `Spec 𝕜`, `pullback.fst ≫ (𝔸ᵏ ↘ Spec 𝕜)`
(`Work.CY3Stab.wProdOver`) and `pullback.snd ≫ (X ↘ Spec 𝕜)`; they are equal by
`pullback.condition`, but not syntactically, and instance search picks the second by default.  The
statements below are phrased with the instance-search choice (the cylinders' `Over`-structures are
never registered as `Variety`-instances here, only the integrality/noetherianity that the
generic-point arguments need), and the final step converts to `Work.CY3Stab.wProdOver` explicitly.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **One side of the cancellation**: for a point `p` which is a `ℙ¹`-bundle over the
`𝕜`-variety `Z` (`Work.K3Inputs.IsP1BundleOver 𝕜 p Z`, i.e. `κ(p) ≅ κ(Z)(t)`) and any `k`, the
generic point of the cylinder `𝔸^{k+1} × Z` has the same residue field, over `𝕜`, as the cylinder
point of `p` in `𝔸ᵏ × P`.

This is the composite

`genPt (𝔸^{k+1} × Z) ~~ prodPt Z (genPt Z) (k+1) ~~ prodPt (𝔸¹ × Z) (genPt (𝔸¹ × Z)) k ~~ prodPt P p k`

of the generic-point identification `prodPt_genericPoint`, the nesting
`wProd_wProd_one_iso_wProd` (twice, with `resEquiv_of_iso`), and the transport
`resEquiv_prodPt_of_resEquiv` applied to `IsP1BundleOver 𝕜 p Z` composed with
`resAlgEquiv_genericPoint_wProd_one`. -/
theorem resEquiv_genericPoint_cyl_of_isP1BundleOver (𝕜 : Type) [Field 𝕜] (k : ℕ)
    {P : AlgebraicGeometry.Scheme.{0}} [P.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    {Z : AlgebraicGeometry.Scheme.{0}} [MotivicInvariants.Variety 𝕜 Z] {p : P}
    (hp : Work.K3Inputs.IsP1BundleOver 𝕜 p Z)
    [IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) P p k).tensor]
    [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) Z (k + 1))] :
    ResEquiv 𝕜 (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) Z (k + 1)))
      (Work.CY3Stab.prodPt (𝕜 := 𝕜) P p k) := by
  -- the instances needed by the generic-point arguments (never registered as
  -- `Variety`-instances: the `Over`-structure of the intermediate cylinders must stay the one
  -- found by instance search, which is the one appearing in the sibling statements)
  haveI hln1 : IsLocallyNoetherian (WProd (𝕜 := 𝕜) Z 1) :=
    @Work.K3Inputs.isLocallyNoetherian_of_variety 𝕜 _ (WProd (𝕜 := 𝕜) Z 1) (varietyWProd Z 1)
  haveI hIn1 : IsIntegral (WProd (𝕜 := 𝕜) Z 1) := isIntegral_wProd (𝕜 := 𝕜) 1
  haveI hIr2 : IrreducibleSpace (WProd (𝕜 := 𝕜) (WProd (𝕜 := 𝕜) Z 1) k) := by
    haveI : IsIntegral (WProd (𝕜 := 𝕜) (WProd (𝕜 := 𝕜) Z 1) k) :=
      isIntegral_wProd (𝕜 := 𝕜) (X := WProd (𝕜 := 𝕜) Z 1) k
    exact inferInstance
  haveI hInZ : IsIntegral Z := (inferInstance : Variety 𝕜 Z).isIntegral
  haveI hLZ : IsLocallyNoetherian Z :=
    @Work.K3Inputs.isLocallyNoetherian_of_variety 𝕜 _ Z inferInstance
  haveI hTD1 : IsDomain (cylTriplet (𝕜 := 𝕜) (WProd (𝕜 := 𝕜) Z 1)
      (genericPoint (WProd (𝕜 := 𝕜) Z 1)) k).tensor :=
    isDomain_cylTriplet_tensor 𝕜 k _ _
  haveI hTD2 : IsDomain (cylTriplet (𝕜 := 𝕜) Z (genericPoint Z) (k + 1)).tensor :=
    isDomain_cylTriplet_tensor 𝕜 (k + 1) Z (genericPoint Z)
  -- the generic points of the cylinders
  have hgp1 : prodPt (𝕜 := 𝕜) (WProd (𝕜 := 𝕜) Z 1) (genericPoint (WProd (𝕜 := 𝕜) Z 1)) k =
      genericPoint (WProd (𝕜 := 𝕜) (WProd (𝕜 := 𝕜) Z 1) k) :=
    prodPt_genericPoint (𝕜 := 𝕜) (X := WProd (𝕜 := 𝕜) Z 1) k
  have hgp2 : prodPt (𝕜 := 𝕜) Z (genericPoint Z) (k + 1) =
      genericPoint (WProd (𝕜 := 𝕜) Z (k + 1)) :=
    prodPt_genericPoint (𝕜 := 𝕜) (X := Z) (k + 1)
  have hgp2r : ResEquiv 𝕜 (genericPoint (WProd (𝕜 := 𝕜) Z (k + 1)))
      (prodPt (𝕜 := 𝕜) Z (genericPoint Z) (k + 1)) := by
    rw [hgp2]
    exact Work.Motivic.ResEquiv.refl 𝕜 _
  -- the nesting `prodPt (𝔸¹ × Z) (genPt (𝔸¹ × Z)) k ~~ prodPt Z (genPt Z) (k+1)`
  have hnest : ResEquiv 𝕜 (prodPt (𝕜 := 𝕜) (WProd (𝕜 := 𝕜) Z 1)
        (genericPoint (WProd (𝕜 := 𝕜) Z 1)) k)
      (prodPt (𝕜 := 𝕜) Z (genericPoint Z) (k + 1)) := by
    rw [hgp1, hgp2]
    obtain ⟨E, hE⟩ := wProd_wProd_one_iso_wProd (𝕜 := 𝕜) Z k
    haveI hEover : E.hom.IsOver (Spec (CommRingCat.of 𝕜)) :=
      (Hom.isOver_iff (Spec (CommRingCat.of 𝕜))).mpr hE
    have hem : E.hom (genericPoint (WProd (𝕜 := 𝕜) (WProd (𝕜 := 𝕜) Z 1) k)) =
        genericPoint (WProd (𝕜 := 𝕜) Z (k + 1)) :=
      Work.CrauderKatz.genericPoint_map_of_iso E
    have h1 : ResEquiv 𝕜 (genericPoint (WProd (𝕜 := 𝕜) (WProd (𝕜 := 𝕜) Z 1) k))
        (E.hom (genericPoint (WProd (𝕜 := 𝕜) (WProd (𝕜 := 𝕜) Z 1) k))) :=
      resEquiv_of_iso E _
    rwa [hem] at h1
  -- the `ℙ¹`-bundle structure of the cylinder's generic point, and its transport
  have ha : ResEquiv 𝕜 p (genericPoint (WProd (𝕜 := 𝕜) Z 1)) :=
    resEquiv_of_resAlgEquiv hp (resAlgEquiv_genericPoint_wProd_one (𝕜 := 𝕜) Z)
  have hb : ResEquiv 𝕜 (prodPt (𝕜 := 𝕜) P p k)
      (prodPt (𝕜 := 𝕜) (WProd (𝕜 := 𝕜) Z 1) (genericPoint (WProd (𝕜 := 𝕜) Z 1)) k) :=
    resEquiv_prodPt_of_resEquiv 𝕜 k p (genericPoint (WProd (𝕜 := 𝕜) Z 1)) ha
  exact Work.Motivic.ResEquiv.trans hgp2r
    (Work.Motivic.ResEquiv.trans (Work.Motivic.ResEquiv.symm hnest)
      (Work.Motivic.ResEquiv.symm hb))

/-- **The chain through both sides**: the two one-sided statements
`resEquiv_genericPoint_cyl_of_isP1BundleOver` for `p` and `p'`, glued by the hypothesis at the
cylinder points of `P`. -/
theorem resEquiv_genericPoint_cyl_of_resEquiv (𝕜 : Type) [Field 𝕜] (k : ℕ)
    {Z Z' : AlgebraicGeometry.Scheme.{0}} [MotivicInvariants.Variety 𝕜 Z]
    [MotivicInvariants.Variety 𝕜 Z'] {P : AlgebraicGeometry.Scheme.{0}}
    [P.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] {p p' : P}
    (hp : Work.K3Inputs.IsP1BundleOver 𝕜 p Z) (hp' : Work.K3Inputs.IsP1BundleOver 𝕜 p' Z')
    [IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) P p k).tensor]
    [IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) P p' k).tensor]
    [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) Z (k + 1))]
    [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) Z' (k + 1))]
    (h : ResEquiv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) P p k)
      (Work.CY3Stab.prodPt (𝕜 := 𝕜) P p' k)) :
    ResEquiv 𝕜 (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) Z (k + 1)))
      (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) Z' (k + 1))) :=
  Work.Motivic.ResEquiv.trans
    (resEquiv_genericPoint_cyl_of_isP1BundleOver (𝕜 := 𝕜) (k := k) (P := P) (Z := Z)
      (p := p) hp)
    (Work.Motivic.ResEquiv.trans h
      (Work.Motivic.ResEquiv.symm
        (resEquiv_genericPoint_cyl_of_isP1BundleOver (𝕜 := 𝕜) (k := k) (P := P) (Z := Z')
          (p := p') hp')))

/-- **The cancellation step of the stabilisation of Lin--Shinder's `thm:bir-generation` (c)**: if
`p`, `p'` are `ℙ¹`-bundles over the `𝕜`-varieties `Z`, `Z'` and the cylinder points of `p`, `p'` in
`𝔸ᵏ × P` have `𝕜`-isomorphic residue fields, then `Z` and `Z'` are stably birational.

See the module documentation for the mathematical content and the organisation of the proof. -/
theorem stablyBirational_of_resEquiv_cyl_of_p1Bundle (𝕜 : Type) [Field 𝕜] (k : ℕ)
    {Z Z' : AlgebraicGeometry.Scheme.{0}} [MotivicInvariants.Variety 𝕜 Z]
    [MotivicInvariants.Variety 𝕜 Z'] {P : AlgebraicGeometry.Scheme.{0}}
    [P.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] {p p' : P}
    (hp : Work.K3Inputs.IsP1BundleOver 𝕜 p Z) (hp' : Work.K3Inputs.IsP1BundleOver 𝕜 p' Z')
    [IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) P p k).tensor]
    [IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) P p' k).tensor]
    (h : ResEquiv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) P p k)
      (Work.CY3Stab.prodPt (𝕜 := 𝕜) P p' k)) :
    Work.K3.StablyBirational 𝕜 Z Z' := by
  haveI hIrZ : IrreducibleSpace (WProd (𝕜 := 𝕜) Z (k + 1)) := by
    haveI : IsIntegral (WProd (𝕜 := 𝕜) Z (k + 1)) := isIntegral_wProd (𝕜 := 𝕜) (X := Z) (k + 1)
    exact inferInstance
  haveI hIrZ' : IrreducibleSpace (WProd (𝕜 := 𝕜) Z' (k + 1)) := by
    haveI : IsIntegral (WProd (𝕜 := 𝕜) Z' (k + 1)) :=
      isIntegral_wProd (𝕜 := 𝕜) (X := Z') (k + 1)
    exact inferInstance
  -- the `Over`-structure of the two cylinders as found by instance search, captured so that the
  -- `Variety`-structures below are compatible with the `ResEquiv` statements above
  letI hCZ : (WProd (𝕜 := 𝕜) Z (k + 1)).Over (Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs ((WProd (𝕜 := 𝕜) Z (k + 1)).Over (Spec (CommRingCat.of 𝕜)))
  letI hCZ' : (WProd (𝕜 := 𝕜) Z' (k + 1)).Over (Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs ((WProd (𝕜 := 𝕜) Z' (k + 1)).Over (Spec (CommRingCat.of 𝕜)))
  have hccZ : (CategoryTheory.over (WProd (𝕜 := 𝕜) Z (k + 1)) (Spec (CommRingCat.of 𝕜))) =
      (Work.CY3Stab.wProdOver (𝕜 := 𝕜) Z (k + 1)).1 := by
    show (pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) (k + 1) ↘ Spec (CommRingCat.of 𝕜))
        (Z ↘ Spec (CommRingCat.of 𝕜)) ≫ (Z ↘ Spec (CommRingCat.of 𝕜))) =
      (pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) (k + 1) ↘ Spec (CommRingCat.of 𝕜))
        (Z ↘ Spec (CommRingCat.of 𝕜)) ≫
          (Work.CY3Stab.AffineK (𝕜 := 𝕜) (k + 1) ↘ Spec (CommRingCat.of 𝕜)))
    exact pullback.condition.symm
  have hccZ' : (CategoryTheory.over (WProd (𝕜 := 𝕜) Z' (k + 1)) (Spec (CommRingCat.of 𝕜))) =
      (Work.CY3Stab.wProdOver (𝕜 := 𝕜) Z' (k + 1)).1 := by
    show (pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) (k + 1) ↘ Spec (CommRingCat.of 𝕜))
        (Z' ↘ Spec (CommRingCat.of 𝕜)) ≫ (Z' ↘ Spec (CommRingCat.of 𝕜))) =
      (pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) (k + 1) ↘ Spec (CommRingCat.of 𝕜))
        (Z' ↘ Spec (CommRingCat.of 𝕜)) ≫
          (Work.CY3Stab.AffineK (𝕜 := 𝕜) (k + 1) ↘ Spec (CommRingCat.of 𝕜)))
    exact pullback.condition.symm
  letI hVZ : Variety 𝕜 (WProd (𝕜 := 𝕜) Z (k + 1)) :=
    { «over» := hCZ
      isIntegral := (varietyWProd Z (k + 1)).isIntegral
      isSeparated := hccZ ▸ (varietyWProd Z (k + 1)).isSeparated
      locallyOfFiniteType := hccZ ▸ (varietyWProd Z (k + 1)).locallyOfFiniteType
      quasicompact := hccZ ▸ (varietyWProd Z (k + 1)).quasicompact }
  letI hVZ' : Variety 𝕜 (WProd (𝕜 := 𝕜) Z' (k + 1)) :=
    { «over» := hCZ'
      isIntegral := (varietyWProd Z' (k + 1)).isIntegral
      isSeparated := hccZ' ▸ (varietyWProd Z' (k + 1)).isSeparated
      locallyOfFiniteType := hccZ' ▸ (varietyWProd Z' (k + 1)).locallyOfFiniteType
      quasicompact := hccZ' ▸ (varietyWProd Z' (k + 1)).quasicompact }
  -- the two cylinders are birational, hence `Z` and `Z'` are stably birational
  obtain ⟨Φ⟩ := Work.CY3.resEquiv_genericPoint_birationalMap (𝕜 := 𝕜)
    (X := WProd (𝕜 := 𝕜) Z (k + 1)) (Y := WProd (𝕜 := 𝕜) Z' (k + 1))
    (resEquiv_genericPoint_cyl_of_resEquiv (𝕜 := 𝕜) (k := k) (Z := Z) (Z' := Z')
      (P := P) (p := p) (p' := p') hp hp' h)
  exact Work.K3Inputs.StablyBirat_to_stablyBirational Z Z'
    (stablyBirat_of_birationalMap_wProd (𝕜 := 𝕜) (X := Z) (Y := Z') (k + 1) ⟨Φ⟩)

end

end Work.CY3Stab.Prod
