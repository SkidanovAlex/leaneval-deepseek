import Mathlib
import Submission.Work.GCBasics.Basic
import Submission.Work.GCBasics.Points

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.GroupChunk.Separated

universe u

open AlgebraicGeometry
open Work.GCBasics

/- The **valuative criterion for separatedness, converse direction**, in the "points"
formulation: if for every valuation ring `R` which is a `K`-algebra, two `R`-valued points
of `X` that agree over the fraction field of `R` are already equal, then `X.hom` satisfies
the uniqueness part of the valuative criterion.

The point of the lemma is that `ValuativeCriterion.Uniqueness` is phrased with an *arbitrary*
fraction field `K'` of the valuation ring `R` (an `IsFractionRing R K'`), whereas the
hypothesis speaks about the canonical `FractionRing R`.  The two are compared through the
`R`-algebra isomorphism `IsLocalization.algEquiv`.

Given a valuative commutative square

```
Spec K' --i₁--> X
  |             |
 Spec.map e    X.hom
  |             |
Spec R --i₂--> Spec K
```

(`e = algebraMap R K'`) we read `i₂` as an algebra structure `K →+* R`, so that a lift
`l : Spec R ⟶ X` of the square is a `K`-morphism, i.e. an `R`-point of `X`.  Two lifts
`l₁ l₂` agree after base change to `K'` (`Spec.map e ≫ l₁ = i₁ = Spec.map e ≫ l₂`); writing
`g = Spec.map (algebraMap R (FractionRing R))`, `s = Spec.map ψ` for
`ψ : FractionRing R ≃ₐ[R] K'`, one has `Spec.map e = s ≫ g`, whence
`g ≫ l₁ = Spec.map ψ.symm ≫ S.i₁ = g ≫ l₂`.  The hypothesis then gives `l₁ = l₂`. -/
open CategoryTheory in
theorem valuativeCriterion_Uniqueness_of_pts {K : Type u} [Field K] (X : Work.GCBasics.Sch K)
    (h : ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
      (p q : Work.GCBasics.RPt X R),
      Work.GCBasics.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) p
        = Work.GCBasics.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) q → p = q) :
    AlgebraicGeometry.ValuativeCriterion.Uniqueness X.hom := by
  intro S
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  -- The base change `Spec R ⟶ Spec K` of the square, read as an algebra structure `K →+* R`.
  let φ : K →+* S.R := (Spec.preimage S.i₂).hom
  letI : Algebra K S.R := φ.toAlgebra
  -- With this structure, `Spec R` over `Spec K` is the bottom-left corner of the square.
  have hspec : (specOf K S.R).hom = S.i₂ := by
    rw [specOf_hom]
    rw [show CommRingCat.ofHom (algebraMap K S.R) = Spec.preimage S.i₂ from by
      rw [RingHom.algebraMap_toAlgebra φ]
      exact CommRingCat.ofHom_hom _]
    exact Spec.map_preimage S.i₂
  -- The two lifts, as `R`-points of `X`.
  let p₁ : RPt X S.R := Over.homMk l₁ (by rw [hspec]; exact hl₁')
  let p₂ : RPt X S.R := Over.homMk l₂ (by rw [hspec]; exact hl₂')
  -- They agree after base change to the canonical fraction field of `R`.
  have key : RPt.map (IsScalarTower.toAlgHom K S.R (FractionRing S.R)) p₁
           = RPt.map (IsScalarTower.toAlgHom K S.R (FractionRing S.R)) p₂ := by
    let ψ : FractionRing S.R ≃ₐ[S.R] S.K :=
      IsLocalization.algEquiv (nonZeroDivisors S.R) (FractionRing S.R) S.K
    have hcomp : ψ.toRingHom.comp (algebraMap S.R (FractionRing S.R)) = algebraMap S.R S.K :=
      RingHom.ext fun r => ψ.commutes r
    -- `Spec.map e` factors through the canonical fraction field of `R`.
    have hsp : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S.R (FractionRing S.R))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    have hscomp : ψ.symm.toRingHom.comp ψ.toRingHom = RingHom.id (FractionRing S.R) := by
      ext x; simp
    have hs' : Spec.map (CommRingCat.ofHom ψ.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ.toRingHom)
          = 𝟙 (Spec (CommRingCat.of (FractionRing S.R))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hscomp]
      rw [show CommRingCat.ofHom (RingHom.id (FractionRing S.R))
            = 𝟙 (CommRingCat.of (FractionRing S.R)) from rfl, Spec.map_id]
    -- hence `Spec.map (algebraMap R (FractionRing R))` is also expressed through `S.i₁`.
    have hg : Spec.map (CommRingCat.ofHom (algebraMap S.R (FractionRing S.R))) =
        Spec.map (CommRingCat.ofHom ψ.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) := by
      calc Spec.map (CommRingCat.ofHom (algebraMap S.R (FractionRing S.R)))
          = 𝟙 (Spec (CommRingCat.of (FractionRing S.R))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap S.R (FractionRing S.R))) :=
            (Category.id_comp _).symm
        _ = (Spec.map (CommRingCat.ofHom ψ.symm.toRingHom) ≫
              Spec.map (CommRingCat.ofHom ψ.toRingHom)) ≫
              Spec.map (CommRingCat.ofHom (algebraMap S.R (FractionRing S.R))) := by rw [hs']
        _ = Spec.map (CommRingCat.ofHom ψ.symm.toRingHom) ≫
              (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
                Spec.map (CommRingCat.ofHom (algebraMap S.R (FractionRing S.R)))) :=
            Category.assoc _ _ _
        _ = Spec.map (CommRingCat.ofHom ψ.symm.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) := by rw [← hsp]
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (algebraMap S.R (FractionRing S.R))) ≫ l₁ =
         Spec.map (CommRingCat.ofHom (algebraMap S.R (FractionRing S.R))) ≫ l₂
    rw [hg]
    simp only [Category.assoc, hl₁, hl₂]
  -- The hypothesis applies.
  have hpq : p₁ = p₂ := h S.R p₁ p₂ key
  have hl : l₁ = l₂ := by
    have := congrArg Over.Hom.left hpq
    simpa [p₁, p₂] using this
  exact CommSq.LiftStruct.ext hl

end Work.GroupChunk.Separated
