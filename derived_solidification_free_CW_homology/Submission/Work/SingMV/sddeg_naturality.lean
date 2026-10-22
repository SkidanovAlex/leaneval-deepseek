import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# Naturality of the degreewise barycentric subdivision

`Work.SingMV.sddeg X n` is the `n`-th degree of the barycentric subdivision operator on the
singular chains of `X`: it is defined by the universal property of the coproduct
`C_n(X) = ⨁_{σ : Δⁿ ⟶ X} ℤ` (`Cofan.IsColimit.desc` applied to
`(TopCat.toSSet.obj X).isColimitChainComplexXCofan`), sending the generator of a singular
simplex `σ` to the pushforward of the subdivision `Sd n` of the fundamental simplex along `σ`.

This file proves that `sddeg` is **natural** in the space: for `f : X ⟶ Y` the square

```
C_n(X) --sddeg X n--> C_n(X)
   |                       |
 C_n(f)                  C_n(f)
   v                       v
C_n(Y) --sddeg Y n--> C_n(Y)
```

commutes. This is what makes `sddeg` a candidate for a chain map, and it is used in the
Mayer–Vietoris/barycentric-subdivision argument (`Submission.Blueprint.SingMVProp`).

## Proof outline

The singular chains are a coproduct of copies of `ℤ` indexed by the singular `n`-simplices
(`SSet.isColimitChainComplexXCofan`), so it suffices to check the identity on the summand
inclusions. For a simplex `x` of the singular simplicial set of `X`:

* `sddeg_fac` computes `genHom X n x ≫ sddeg X n`, i.e. the composite of the summand inclusion
  with the subdivision, by the defining universal property of `sddeg`;
* `genHom_comp` computes the composite of a summand inclusion with the map on chains induced
  by `f` (`SSet.ι_chainComplexMap_f`);
* `singC_map_gen` identifies the pushforward of `Sd n` along `σ` followed by `C_n(f)` with the
  pushforward along `f ∘ σ`, using `TopCat.toSSetObjEquiv`-naturality (`rfl`) and functoriality
  of the singular chain complex.

## Implementation note

The coproduct `((Submission.Blueprint.singC).obj X).X n` of singular chains is *definitionally*
the coproduct `((TopCat.toSSet.obj X).chainComplex ℤ).X n` computed by Mathlib, but this
identification needs `δ`-reduction of the reducible `def`s defining `singC` and involves a
change of universe-free notation; we therefore introduce `genHom`, whose *declared* type is
stated directly in terms of `singC`, so that the universal property can be applied without any
definitional-unfolding mismatches.
-/

open CategoryTheory Limits Convexity
open scoped BigOperators Simplicial

noncomputable section

namespace Work.SingMV

/-! ## The summand inclusions of the coproduct of singular chains -/

/-- The inclusion of the `ℤ`-summand of the singular `n`-chains of `X` corresponding to a
simplex `x` of the singular simplicial set of `X`, i.e. the coproduct leg
`R ⟶ (X.chainComplex R).X n` restricted to `R = ℤ`.

Its type is stated with `Submission.Blueprint.singC`, so that it can be composed with the
singular-chain maps of the blueprint without any definitional unfolding. -/
def genHom (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    ModuleCat.of ℤ ℤ ⟶ ((Submission.Blueprint.singC).obj X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) x

/-- **The defining property of `sddeg`**: the composite of the summand inclusion of a singular
simplex `x` with the degreewise subdivision is the map `ℤ ⟶ C_n(X)` sending `1` to the
pushforward of the subdivision `Sd n` of the fundamental simplex along the continuous map
`singEquiv X n x : Δⁿ ⟶ X`. -/
lemma sddeg_fac (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    genHom X n x ≫ sddeg X n
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
          ↥(((Submission.Blueprint.singC).obj X).X n)
          (((Submission.Blueprint.singC).map (TopCat.ofHom ((singEquiv X n) x))).f n (Sd n))) :=
  Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
        ↥(((Submission.Blueprint.singC).obj X).X n)
        (((Submission.Blueprint.singC).map (TopCat.ofHom ((singEquiv X n) σ))).f n (Sd n)))) x

/-- Two morphisms out of the singular `n`-chains of `X` which agree on every summand inclusion
are equal. This is the universal property of `C_n(X)` as a coproduct, phrased for the summand
inclusions `genHom`. -/
lemma genHom_hom_ext {X : TopCat} {n : ℕ} {T : ModuleCat ℤ}
    {φ ψ : ((Submission.Blueprint.singC).obj X).X n ⟶ T}
    (h : ∀ x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)),
        genHom X n x ≫ φ = genHom X n x ≫ ψ) : φ = ψ :=
  (TopCat.toSSet.obj X).chainComplex_hom_ext (R := ModuleCat.of ℤ ℤ) (n := n) h

/-- The map on singular `n`-chains induced by `f : X ⟶ Y` intertwines the summand inclusions
corresponding to a simplex and its image. -/
lemma genHom_comp (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    genHom X n x ≫ ((Submission.Blueprint.singC).map f).f n
      = genHom Y n ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) x) :=
  SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) (TopCat.toSSet.map f)
    (ModuleCat.of ℤ ℤ) x

/-! ## The value of `sddeg` on a pushed-forward chain -/

/-- The map `ℤ ⟶ C_n(Y)` singled out by an element `a ∈ C_n(X)` is the composite of the map
singled out by `a` with any morphism `g : C_n(X) ⟶ C_n(Y)`. -/
lemma ofHom_toSpanSingleton_comp {A B : ModuleCat ℤ} (g : A ⟶ B) (a : A) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ A a)) ≫ g
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ B (g a)) := by
  ext
  simp [LinearMap.toSpanSingleton_apply]

/-- Pushing the subdivision of the fundamental simplex forward along `σ : Δⁿ ⟶ X` and then
along `f : X ⟶ Y` is the same as pushing it forward along the composite `f ∘ σ`. -/
lemma singC_map_gen (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) (σ : singMap X n)
    (y : ((Submission.Blueprint.singC).obj (tSplx n)).X n) :
    (Submission.Blueprint.singC.map f).f n
        (((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f n y)
      = ((Submission.Blueprint.singC).map (TopCat.ofHom (f.hom.comp σ))).f n y := by
  have H1 : ((Submission.Blueprint.singC).map (TopCat.ofHom σ)) ≫ ((Submission.Blueprint.singC).map f)
      = (Submission.Blueprint.singC).map (TopCat.ofHom (f.hom.comp σ)) := by
    rw [← Functor.map_comp]
    rfl
  have H2 := congrArg (fun m => m.f n) H1
  simp only [HomologicalComplex.comp_f] at H2
  exact congrArg (fun m => m y) H2

/-! ## Naturality -/

/-- Naturality of the degreewise subdivision as an identity of morphisms of singular chains. -/
lemma sddeg_naturality_aux (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) :
    sddeg X n ≫ (Submission.Blueprint.singC.map f).f n
      = (Submission.Blueprint.singC.map f).f n ≫ sddeg Y n := by
  apply genHom_hom_ext
  intro x
  rw [← Category.assoc, ← Category.assoc]
  rw [sddeg_fac X n x, genHom_comp X Y f n x,
    sddeg_fac Y n ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) x)]
  rw [ofHom_toSpanSingleton_comp]
  rw [singC_map_gen X Y f n (singEquiv X n x) (Sd n)]
  rfl

/-- **Naturality of the degreewise barycentric subdivision** on the singular chains: for
`f : X ⟶ Y` the subdivision commutes with the map induced by `f`. -/
theorem sddeg_naturality (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (z : ((Submission.Blueprint.singC).obj X).X n) :
    ((Submission.Blueprint.singC).map f).f n (Work.SingMV.sddeg X n z) =
      Work.SingMV.sddeg Y n (((Submission.Blueprint.singC).map f).f n z) := by
  have key : (sddeg X n) ≫ ((Submission.Blueprint.singC).map f).f n
      = ((Submission.Blueprint.singC).map f).f n ≫ (sddeg Y n) := sddeg_naturality_aux X Y f n
  exact congrArg (fun m => m z) key

end Work.SingMV
