import Submission.Work.StemsB.RelCochainDualR
import Submission.Work.Serre.E3aDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality of the relative cochain/chain duality

`Submission/Work/StemsB/RelCochainDualR.lean` proves, over any coefficient ring `R`, that the
relative cochains are the `R`-duals of the relative chains,

  `relComplex R X A ≅ dualComplex R (relChainsR R X A)`,

*per pair* (`Nonempty`, via `Classical.choice`).  The chosen isomorphism is *explicit*:
`rdRIso_hom` says that its degree-`n` component is `rdRMap R X A n`, the pullback along the quotient
projection `C_n(X;R) → C_n(X,A;R)`.  This file makes it **natural in the pair**:

* `rdRProj_relChainsRMapOf` — the chain-level naturality of that projection: for a map of pairs
  `(f,g) : (X,A) → (Y,B)` compatible via `w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B`, the square
  `rdRProj R X A n ≫ (relChainsRMapOf …).f n = (chainMap R X Y f).f n ≫ rdRProj R Y B n` commutes
  (the naturality of `cokernel.π` under `cokernel.map`, which is how
  `Work.Serre.relChainsRMapOf` is defined);
* `rdRIso_natural` — the naturality of `rdRIso` itself:

  `(dualComplexMap R (relChainsR R X A) (relChainsR R Y B) (relChainsRMapOf …)).f n ≫ (rdRIso R X A n).hom
     = (rdRIso R Y B n).hom ≫ (relComplexMap R A B f hf).f n`.

This is what subproject SERRE's `Work.Serre.thetaRel_exists` (the rational relative Mayer–Vietoris
sequence) consumes; the remaining step towards their exact `DQ` form is the naturality of the
relative base change `Work.StemsB.relChainsBaseChangeRat` (a canonical
`PreservesCokernel.iso`/`cokernel.mapIso` construction, so its naturality is a diagram chase).

**Lean note.**  The value computation is delicate: `simp`/`rw` cannot match the value lemmas across
the `Subtype.ext`/`LinearMap.ext` unfolding, so each value identity is *restated locally in the shape
of the goal* (with the coercions `rdRLM R _ _` of this area's `rdRMap_apply`/`relMapLM_coe` written
explicitly) and proved by `exact <library lemma> …`; with those local lemmas the goal is closed by
four `rw`s plus the projection lemma.
-/

open CategoryTheory CategoryTheory.Limits
open Work.Cohomology

namespace Work.StemsB

noncomputable section

variable {R : Type} [CommRing R]

set_option backward.isDefEq.respectTransparency false

/-- The relative chain map induced by a map of pairs is compatible with the quotient projections. -/
theorem rdRProj_relChainsRMapOf {X Y : TopCat} (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B) (n : ℕ) :
    (rdRProj R X A n) ≫ (Work.Serre.relChainsRMapOf (R := R) X Y A B f g w).f n
      = (chainMap R X Y f).f n ≫ (rdRProj R Y B n) := by
  have hsq : relChainsRIncl R X A ≫ chainMap R X Y f
      = chainMap R (TopCat.of A) (TopCat.of B) g ≫ relChainsRIncl R Y B := by
    simp only [relChainsRIncl, chainMap]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ w
  have h := Work.Cohomology.cokernel_π_map (relChainsRIncl R X A) (relChainsRIncl R Y B)
    (chainMap R (TopCat.of A) (TopCat.of B) g) (chainMap R X Y f) hsq
  show (cokernel.π (relChainsRIncl R X A)).f n
      ≫ (cokernel.map (relChainsRIncl R X A) (relChainsRIncl R Y B)
          (chainMap R (TopCat.of A) (TopCat.of B) g) (chainMap R X Y f) hsq).f n
    = (chainMap R X Y f).f n ≫ (cokernel.π (relChainsRIncl R Y B)).f n
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, h]

/-- **Naturality of the relative cochain/chain duality** in the pair. -/
theorem rdRIso_natural {X Y : TopCat} (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B)
    (hf : ∀ x ∈ A, f x ∈ B) (n : ℕ) :
    (dualComplexMap R (relChainsR R X A) (relChainsR R Y B)
        (Work.Serre.relChainsRMapOf (R := R) X Y A B f g w)).f n ≫ (rdRIso R X A n).hom
      = (rdRIso R Y B n).hom ≫ (relComplexMap R A B f hf).f n := by
  have hproj : ∀ x : ↥((Work.Cohomology.singularChains R X).X n),
      (Work.Serre.relChainsRMapOf (R := R) X Y A B f g w).f n ((rdRProj R X A n) x)
        = (rdRProj R Y B n) ((chainMap R X Y f).f n x) := by
    intro x
    have h3 : (LinearMap.comp
          ((Work.Serre.relChainsRMapOf (R := R) X Y A B f g w).f n).hom (rdRProj R X A n).hom) x
        = (LinearMap.comp (rdRProj R Y B n).hom ((chainMap R X Y f).f n).hom) x := by
      rw [show (LinearMap.comp ((Work.Serre.relChainsRMapOf (R := R) X Y A B f g w).f n).hom
              (rdRProj R X A n).hom)
            = ModuleCat.Hom.hom ((rdRProj R X A n)
                ≫ (Work.Serre.relChainsRMapOf (R := R) X Y A B f g w).f n)
            from (ModuleCat.hom_comp _ _).symm,
          show (LinearMap.comp (rdRProj R Y B n).hom ((chainMap R X Y f).f n).hom)
            = ModuleCat.Hom.hom ((chainMap R X Y f).f n ≫ (rdRProj R Y B n))
            from (ModuleCat.hom_comp _ _).symm,
          rdRProj_relChainsRMapOf (R := R) A B f g w n]
    simpa only [LinearMap.comp_apply] using h3
  -- local value lemmas, stated with the linear-map types of the value lemmas themselves
  have vC : ∀ (φ : ↥((relChainsR R Y B).X n) →ₗ[R] R) (y : ↥((relChainsR R X A).X n)),
      ((ModuleCat.Hom.hom (dualComplexMapComp R (relChainsR R X A) (relChainsR R Y B)
        (Work.Serre.relChainsRMapOf (R := R) X Y A B f g w) n)) φ) y
      = φ ((Work.Serre.relChainsRMapOf (R := R) X Y A B f g w).f n y) :=
    fun φ y => Work.Cohomology.dualComplexMapComp_apply R _ _ _ n φ y
  have vM : ∀ (ψ : ↥(relKern R Y B n)) (y : ↥((Work.Cohomology.singularChains R X).X n)),
      rdRLM R X n (↑((relMapLM R A B f hf n) ψ)) y
        = rdRLM R X n ((ModuleCat.Hom.hom ((dualChainMap R X Y f).f n)) (↑ψ)) y :=
    fun ψ y => by rw [relMapLM_coe]
  have vD : ∀ (c : ↥((Work.Cohomology.singularCochainComplex R Y).X n))
      (z : ↥((Work.Cohomology.singularChains R X).X n)),
      rdRLM R X n ((ModuleCat.Hom.hom ((dualChainMap R X Y f).f n)) c) z
        = rdRLM R Y n c ((chainMap R X Y f).f n z) :=
    fun c z => by
      rw [dualChainMap_f_hom]
      show ((ModuleCat.Hom.hom ((chainMap R X Y f).f n)).dualMap c) z
        = (rdRLM R Y n c) ((ConcreteCategory.hom ((chainMap R X Y f).f n)) z)
      rw [LinearMap.dualMap_apply]
      rfl
  have vR : ∀ (f' : ↥((relChainsR R Y B).X n) →ₗ[R] R)
      (z : ↥((Work.Cohomology.singularChains R Y).X n)),
      rdRLM R Y n (↑((rdRMap R Y B n) f')) z = f' ((rdRProj R Y B n) z) :=
    fun f' z => rdRMap_apply R Y B n f' z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [rdRIso_hom, ModuleCat.hom_ofHom, dualComplexMap_f, relComplexMap_f]
  show rdRLM R X n (↑((rdRMap R X A n)
        ((ModuleCat.Hom.hom (dualComplexMapComp R (relChainsR R X A) (relChainsR R Y B)
          (Work.Serre.relChainsRMapOf (R := R) X Y A B f g w) n)) φ))) x
      = rdRLM R X n (↑((relMapLM R A B f hf n) ((rdRMap R Y B n) φ))) x
  rw [rdRMap_apply]
  rw [vC]
  rw [vM, vD, vR]
  rw [hproj x]

/-! ## The packaged isomorphism and its naturality -/

/-- **The relative cochain/chain duality as an explicit isomorphism of complexes**: the components
are `rdRIso R X A n` (pullback along `rdRProj`), and they commute with the differentials
(`rdRIso_comm`). -/
noncomputable def relDualIso (R : Type) [CommRing R] (X : TopCat) (A : Set X) :
    dualComplex R (relChainsR R X A) ≅ relComplex R X A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => rdRIso R X A n)
    (fun i j hij => by rw [← hij]; exact rdRIso_comm R X A i)

/-- **Naturality of the relative cochain/chain duality**, in the packaged form: the explicit
isomorphism `relDualIso` is natural in the pair.  This is the `relChainsR` form of the statement
subproject SERRE's `Work.Serre.thetaRel_exists` asserts for the `ℚ`-dual of the base change. -/
theorem relDualIso_natural {X Y : TopCat} (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B) (hf : ∀ x ∈ A, f x ∈ B) :
    dualComplexMap R (relChainsR R X A) (relChainsR R Y B)
        (Work.Serre.relChainsRMapOf (R := R) X Y A B f g w) ≫ (relDualIso R X A).hom
      = (relDualIso R Y B).hom ≫ relComplexMap R A B f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  show (dualComplexMap R (relChainsR R X A) (relChainsR R Y B)
      (Work.Serre.relChainsRMapOf (R := R) X Y A B f g w)).f n ≫ (rdRIso R X A n).hom
    = (rdRIso R Y B n).hom ≫ (relComplexMap R A B f hf).f n
  exact rdRIso_natural A B f g w hf n

end

end Work.StemsB
