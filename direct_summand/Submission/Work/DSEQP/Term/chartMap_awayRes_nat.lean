import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.chartMap_ker_transport

/-!
# `Work.DSEQP.Term.chartMap_awayRes_nat`

Naturality of the chart comparison map `Work.DSEQP.chartMap` for a morphism
`i : X ⟶ ℙᴺ_A = DSMap.PSpace A N` under the localisation maps
`Work.DSEQP.awayRes (S ⊆ T) : Away 𝒜 (x_S) →+* Away 𝒜 (x_T)` and the restriction of
sections of `𝒪_X`: the square

```
Away x_S  --awayRes-->  Away x_T
   |                      |
chartMap S             chartMap T
   v                      v
Γ(X,U_S)  --restrict-->  Γ(X,U_T)
```

commutes.  Here `U_S = i⁻¹ᵁ D₊(x_S)` and the horizontal map on the bottom is the
restriction map of the structure sheaf of `X`, viewed as a map of `A`-modules through the
presheaf `DSMap.cechPresheaf A X f`.

The proof composes two independent commutation squares:

* the *algebraic* square expressing the compatibility of Mathlib's `Proj.awayToSection`
  with `awayRes` (this is `Work.DSEQP.chartMap_awayRes_comm`, proved from
  `Proj.awayMap_awayToSection`);
* the *geometric* square expressing the naturality of `Scheme.Hom.app` with respect to
  the restriction maps of `ℙᴺ_A` and `X` (`Scheme.Hom.naturality`), together with the
  identity `i ⁻¹ᵁ D₊(·)` of `Work.DSEQP.Ucmp`/`Work.DSEQP.Dcmp`
  (`TopologicalSpace.Opens.map_homOfLE`).
-/

namespace Work.DSEQP.Term

universe a

open CategoryTheory AlgebraicGeometry

section Helpers

variable {A : Type a} [CommRing A] {N : ℕ}

/-- **Naturality of the chart isomorphism `Proj.basicOpenIsoAway`** (i.e. of
`Work.DSEQP.awayIso`) under the localisation `Work.DSEQP.awayRes`: the square

```
Away x_S  --awayRes-->  Away x_T
   |                      |
awayIso S              awayIso T
   v                      v
Γ(D₊(x_S)) --restrict--> Γ(D₊(x_T))
```

commutes at the level of elements. -/
lemma awayIso_awayRes {S T : Finset (Fin (N + 1))} (hST : S ⊆ T) (hS : S.Nonempty)
    (hT : T.Nonempty)
    (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) :
    (Work.DSEQP.awayIso (A := A) (N := N) T hT)
        (Work.DSEQP.awayRes (A := A) (N := N) hST z)
      = (((DSMap.PSpace A N).presheaf.map
          (homOfLE (Work.DSEQP.Dcmp_anti (A := A) (N := N) hST)).op).hom)
          ((Work.DSEQP.awayIso (A := A) (N := N) S hS) z) := by
  have h := Work.DSEQP.chartMap_awayRes_comm (A := A) (N := N) hST hS hT
  have h2 := DFunLike.congr_fun h z
  simp only [RingHom.comp_apply] at h2
  have h2' : (Work.DSEQP.awayIso (A := A) (N := N) T hT)
        (Work.DSEQP.awayRes (A := A) (N := N) hST z)
      = (Work.DSEQP.resST (A := A) (N := N) hST)
          ((Work.DSEQP.awayIso (A := A) (N := N) S hS) z) := h2
  rw [h2']
  rfl

variable {X : AlgebraicGeometry.Scheme.{a}}

/-- **Naturality of `Scheme.Hom.app`** for the chart inclusions `D₊(x_T) ⊆ D₊(x_S)`
(`S ⊆ T`) of `ℙᴺ_A = DSMap.PSpace A N` and their preimages `U_T ⊆ U_S` in `X`: the square

```
Γ(D₊(x_S)) --restrict--> Γ(D₊(x_T))
   |                        |
i.app D₊(x_S)           i.app D₊(x_T)
   v                        v
Γ(U_S)     --restrict-->  Γ(U_T)
```

commutes at the level of elements.  (Only the underlying ring homomorphism of `i.app` is
involved; the `A`-module structures play no role.) -/
lemma chartMap_app_nat (i : X ⟶ DSMap.PSpace A N) {S T : Finset (Fin (N + 1))} (hST : S ⊆ T)
    (w : Γ(DSMap.PSpace A N, Work.DSEQP.Dcmp (A := A) (N := N) S)) :
    (i.app (Work.DSEQP.Dcmp (A := A) (N := N) T)).hom
        (((DSMap.PSpace A N).presheaf.map
          (homOfLE (Work.DSEQP.Dcmp_anti (A := A) (N := N) hST)).op).hom w)
      = (X.presheaf.map
          (homOfLE (Work.DSEQP.Ucmp_anti (A := A) (N := N) i hST)).op).hom
          ((i.app (Work.DSEQP.Dcmp (A := A) (N := N) S)).hom w) := by
  have hm : (TopologicalSpace.Opens.map i.base).map
      (homOfLE (Work.DSEQP.Dcmp_anti (A := A) (N := N) hST))
      = homOfLE (Work.DSEQP.Ucmp_anti (A := A) (N := N) i hST) := by
    rw [TopologicalSpace.Opens.map_homOfLE]
  have h := Scheme.Hom.naturality i (homOfLE (Work.DSEQP.Dcmp_anti (A := A) (N := N) hST)).op
  have h2 := congrArg (fun φ => (CommRingCat.Hom.hom φ) w) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    Quiver.Hom.unop_op] at h2
  rw [hm] at h2
  exact h2

end Helpers

theorem chartMap_awayRes_nat {A : Type a} [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}
    {i : X ⟶ DSMap.PSpace A N} {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)}
    {S T : Finset (Fin (N + 1))} (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
    (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) :
    Work.DSEQP.chartMap i T hT (Work.DSEQP.awayRes (A := A) (N := N) hST z)
      = (DSMap.cechPresheaf A X f).map
          (CategoryTheory.homOfLE (Work.DSEQP.Ucmp_anti i hST)).op
          (Work.DSEQP.chartMap i S hS z) := by
  -- the algebraic square (`Proj.awayToSection` vs. `awayRes`)
  have hA : (Work.DSEQP.awayIso (A := A) (N := N) T hT)
      (Work.DSEQP.awayRes (A := A) (N := N) hST z)
      = (((DSMap.PSpace A N).presheaf.map
          (homOfLE (Work.DSEQP.Dcmp_anti (A := A) (N := N) hST)).op).hom)
          ((Work.DSEQP.awayIso (A := A) (N := N) S hS) z) :=
    awayIso_awayRes hST hS hT z
  -- the geometric square (`i.app` vs. restriction)
  have hB := chartMap_app_nat (A := A) (N := N) i hST
    ((Work.DSEQP.awayIso (A := A) (N := N) S hS) z)
  change (i.app (Work.DSEQP.Dcmp (A := A) (N := N) T)).hom
      ((Work.DSEQP.awayIso (A := A) (N := N) T hT)
        (Work.DSEQP.awayRes (A := A) (N := N) hST z)) = _
  rw [hA, hB]
  rfl

end Work.DSEQP.Term
