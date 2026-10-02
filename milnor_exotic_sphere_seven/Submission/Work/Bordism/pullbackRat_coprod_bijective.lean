import Mathlib
import Submission.Work.Bordism.Middle
import Submission.Work.Bordism.chainC_coprod_iso
import Submission.Work.Bordism.cohomology_coprod_iso
import Submission.Work.Bordism.toSSet_coprod_iso
import Submission.Work.Bordism.chainC_coprod_split

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomological Künneth splitting of a disjoint union, via the pullbacks

For topological spaces `X`, `Y` and every `k`, the map

`Hᵏ(X ⊔ Y; ℚ) → Hᵏ(X; ℚ) × Hᵏ(Y; ℚ),   z ↦ (inl* z, inr* z)`

is bijective.  This is the compatibility of the cohomological Künneth splitting with the two
pullbacks, phrased at the rationalised cohomology `Work.Bordism.pullbackRat`.

The mathematical content is the chain-level splitting of `Work.Bordism.chainC_coprod_split`: there
are chain maps `p`, `q` splitting the two inclusions off the chain complex of the disjoint union
and complementary to each other.  Transposing them gives cochain maps `p*`, `q*`; the five
splitting identities dualise to `i* ∘ p* = id`, `j* ∘ q* = id`, `i* ∘ q* = 0`, `j* ∘ p* = 0` and
`p* ∘ i* + q* ∘ j* = id` on cohomology, which is exactly what is needed to exhibit
`(i*, j*)` as an isomorphism with inverse `(x, y) ↦ p* x + q* y`.  Rationalising gives the
statement.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits TensorProduct
open Work.Cohomology Work.SignatureBordism

namespace Work.Bordism

noncomputable section

/-- The dual of the zero chain map is the zero cochain map. -/
lemma dualComplexMap_zero' {R : Type} [CommRing R] (C D : ChainComplex (ModuleCat R) ℕ) :
    dualComplexMap R C D 0 = 0 :=
  (dualComplexFunctor R).map_zero (Opposite.op D) (Opposite.op C)

/-- The dual of a composite of the singular chain complexes of *spaces* (so that all the chain
complexes are displayed in the same normal form). -/
lemma dualComplexMap_compTC (X Y Z : TopCat.{0})
    (f : chainC ℤ (TopCat.toSSet.obj X) ⟶ chainC ℤ (TopCat.toSSet.obj Y))
    (g : chainC ℤ (TopCat.toSSet.obj Y) ⟶ chainC ℤ (TopCat.toSSet.obj Z)) :
    dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X)) (chainC ℤ (TopCat.toSSet.obj Z)) (f ≫ g)
      = dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj Y)) (chainC ℤ (TopCat.toSSet.obj Z)) g
        ≫ dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X)) (chainC ℤ (TopCat.toSSet.obj Y)) f :=
  dualComplexMap_comp ℤ f g

/-- The dual of the identity of the singular chain complex of a space. -/
lemma dualComplexMap_idTC (X : TopCat.{0}) :
    dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X)) (chainC ℤ (TopCat.toSSet.obj X))
      (𝟙 (chainC ℤ (TopCat.toSSet.obj X))) = 𝟙 (dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj X))) :=
  dualComplexMap_id ℤ (chainC ℤ (TopCat.toSSet.obj X))

/-- The dual of the zero chain map of singular chain complexes of spaces. -/
lemma dualComplexMap_zeroTC (X Y : TopCat.{0}) :
    dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X)) (chainC ℤ (TopCat.toSSet.obj Y)) 0 = 0 :=
  dualComplexMap_zero' _ _

/-- **The two pullbacks along the inclusions of a disjoint union present the rationalised
cohomology of the disjoint union as the product of the rationalised cohomologies of the
pieces.** -/
theorem pullbackRat_coprod_bijective (X Y : TopCat) (k : ℕ) :
    Function.Bijective (LinearMap.prod
      (Work.Bordism.pullbackRat k
        (CategoryTheory.Limits.coprod.inl : X ⟶ CategoryTheory.Limits.coprod X Y))
      (Work.Bordism.pullbackRat k
        (CategoryTheory.Limits.coprod.inr : Y ⟶ CategoryTheory.Limits.coprod X Y))) := by
  obtain ⟨p, q, h1, h2, h3, h4, h5⟩ := chainC_coprod_split X Y
  -- the dualised splitting identities
  have f1 : (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainC ℤ (TopCat.toSSet.obj X)) p)
        ≫ (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X))
            (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
            (chainMap ℤ X (X ⨿ Y) Limits.coprod.inl))
      = 𝟙 (dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj X))) := by
    have hh := dualComplexMap_compTC X (X ⨿ Y) X
      (chainMap ℤ X (X ⨿ Y) Limits.coprod.inl) p
    rw [h1, dualComplexMap_idTC] at hh
    exact hh.symm
  have f2 : (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainC ℤ (TopCat.toSSet.obj Y)) q)
        ≫ (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj Y))
            (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
            (chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr))
      = 𝟙 (dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj Y))) := by
    have hh := dualComplexMap_compTC Y (X ⨿ Y) Y
      (chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr) q
    rw [h2, dualComplexMap_idTC] at hh
    exact hh.symm
  have f3 : (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainC ℤ (TopCat.toSSet.obj Y)) q)
        ≫ (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X))
            (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
            (chainMap ℤ X (X ⨿ Y) Limits.coprod.inl))
      = 0 := by
    have hh := dualComplexMap_compTC X (X ⨿ Y) Y
      (chainMap ℤ X (X ⨿ Y) Limits.coprod.inl) q
    rw [h3, dualComplexMap_zeroTC] at hh
    exact hh.symm
  have f4 : (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainC ℤ (TopCat.toSSet.obj X)) p)
        ≫ (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj Y))
            (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
            (chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr))
      = 0 := by
    have hh := dualComplexMap_compTC Y (X ⨿ Y) X
      (chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr) p
    rw [h4, dualComplexMap_zeroTC] at hh
    exact hh.symm
  have f5 : (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X))
          (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainMap ℤ X (X ⨿ Y) Limits.coprod.inl))
        ≫ (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
            (chainC ℤ (TopCat.toSSet.obj X)) p)
      + (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj Y))
          (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr))
        ≫ (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
            (chainC ℤ (TopCat.toSSet.obj Y)) q)
      = 𝟙 (dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))) := by
    have hh := dualComplexMap_add' ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
      (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
      (p ≫ chainMap ℤ X (X ⨿ Y) Limits.coprod.inl)
      (q ≫ chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr)
    rw [h5, dualComplexMap_idTC] at hh
    rw [dualComplexMap_compTC (X ⨿ Y) X (X ⨿ Y) p
        (chainMap ℤ X (X ⨿ Y) Limits.coprod.inl),
      dualComplexMap_compTC (X ⨿ Y) Y (X ⨿ Y) q
        (chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr)] at hh
    exact hh.symm
  -- pass to homology
  have g1 : HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainC ℤ (TopCat.toSSet.obj X)) p) k
      ≫ HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X))
          (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainMap ℤ X (X ⨿ Y) Limits.coprod.inl)) k
      = 𝟙 ((dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj X))).homology k) := by
    rw [← HomologicalComplex.homologyMap_comp, f1, HomologicalComplex.homologyMap_id]
  have g2 : HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainC ℤ (TopCat.toSSet.obj Y)) q) k
      ≫ HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj Y))
          (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr)) k
      = 𝟙 ((dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj Y))).homology k) := by
    rw [← HomologicalComplex.homologyMap_comp, f2, HomologicalComplex.homologyMap_id]
  have g3 : HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainC ℤ (TopCat.toSSet.obj Y)) q) k
      ≫ HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X))
          (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainMap ℤ X (X ⨿ Y) Limits.coprod.inl)) k
      = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, f3, HomologicalComplex.homologyMap_zero]
  have g4 : HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainC ℤ (TopCat.toSSet.obj X)) p) k
      ≫ HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj Y))
          (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr)) k
      = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, f4, HomologicalComplex.homologyMap_zero]
  have g5 : HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X))
          (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainMap ℤ X (X ⨿ Y) Limits.coprod.inl)) k
      ≫ HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainC ℤ (TopCat.toSSet.obj X)) p) k
      + HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj Y))
          (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr)) k
      ≫ HomologicalComplex.homologyMap
        (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
          (chainC ℤ (TopCat.toSSet.obj Y)) q) k
      = 𝟙 ((dualComplex ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))).homology k) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_add, f5, HomologicalComplex.homologyMap_id]
  -- rationalise
  set Ah := HomologicalComplex.homologyMap
    (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj X))
      (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
      (chainMap ℤ X (X ⨿ Y) Limits.coprod.inl)) k with hAh
  set Bh := HomologicalComplex.homologyMap
    (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj Y))
      (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
      (chainMap ℤ Y (X ⨿ Y) Limits.coprod.inr)) k with hBh
  set Ph := HomologicalComplex.homologyMap
    (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
      (chainC ℤ (TopCat.toSSet.obj X)) p) k with hPh
  set Qh := HomologicalComplex.homologyMap
    (dualComplexMap ℤ (chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)))
      (chainC ℤ (TopCat.toSSet.obj Y)) q) k with hQh
  have c1 : (Ah.hom.baseChange ℚ) ∘ₗ (Ph.hom.baseChange ℚ) = LinearMap.id := by
    have hcomp : Ah.hom ∘ₗ Ph.hom = LinearMap.id := by
      have hh := congrArg ModuleCat.Hom.hom g1
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hh
      exact hh
    rw [← LinearMap.baseChange_comp Ph.hom Ah.hom, hcomp, LinearMap.baseChange_id]
  have c2 : (Bh.hom.baseChange ℚ) ∘ₗ (Qh.hom.baseChange ℚ) = LinearMap.id := by
    have hcomp : Bh.hom ∘ₗ Qh.hom = LinearMap.id := by
      have hh := congrArg ModuleCat.Hom.hom g2
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hh
      exact hh
    rw [← LinearMap.baseChange_comp Qh.hom Bh.hom, hcomp, LinearMap.baseChange_id]
  have c3 : (Ah.hom.baseChange ℚ) ∘ₗ (Qh.hom.baseChange ℚ) = 0 := by
    have hcomp : Ah.hom ∘ₗ Qh.hom = 0 := by
      have hh := congrArg ModuleCat.Hom.hom g3
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at hh
      exact hh
    rw [← LinearMap.baseChange_comp Qh.hom Ah.hom, hcomp, LinearMap.baseChange_zero]
  have c4 : (Bh.hom.baseChange ℚ) ∘ₗ (Ph.hom.baseChange ℚ) = 0 := by
    have hcomp : Bh.hom ∘ₗ Ph.hom = 0 := by
      have hh := congrArg ModuleCat.Hom.hom g4
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at hh
      exact hh
    rw [← LinearMap.baseChange_comp Ph.hom Bh.hom, hcomp, LinearMap.baseChange_zero]
  have c5 : (Ph.hom.baseChange ℚ) ∘ₗ (Ah.hom.baseChange ℚ)
        + (Qh.hom.baseChange ℚ) ∘ₗ (Bh.hom.baseChange ℚ) = LinearMap.id := by
    have hcomp : Ph.hom ∘ₗ Ah.hom + Qh.hom ∘ₗ Bh.hom = LinearMap.id := by
      have hh := congrArg ModuleCat.Hom.hom g5
      rw [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_id] at hh
      exact hh
    rw [← LinearMap.baseChange_comp Ah.hom Ph.hom,
      ← LinearMap.baseChange_comp Bh.hom Qh.hom, ← LinearMap.baseChange_add,
      hcomp, LinearMap.baseChange_id]
  -- We now package the four maps with their `ratCohomology` types, so that the element-level
  -- computation below never has to unfold any of the identification of the complexes.
  let A : ratCohomology k (TopCat.toSSet.obj (X ⨿ Y)) →ₗ[ℚ] ratCohomology k (TopCat.toSSet.obj X) :=
    pullbackRat k (Limits.coprod.inl : X ⟶ X ⨿ Y)
  let B : ratCohomology k (TopCat.toSSet.obj (X ⨿ Y)) →ₗ[ℚ] ratCohomology k (TopCat.toSSet.obj Y) :=
    pullbackRat k (Limits.coprod.inr : Y ⟶ X ⨿ Y)
  let P : ratCohomology k (TopCat.toSSet.obj X) →ₗ[ℚ] ratCohomology k (TopCat.toSSet.obj (X ⨿ Y)) :=
    Ph.hom.baseChange ℚ
  let Q : ratCohomology k (TopCat.toSSet.obj Y) →ₗ[ℚ] ratCohomology k (TopCat.toSSet.obj (X ⨿ Y)) :=
    Qh.hom.baseChange ℚ
  have hc1 : A.comp P = LinearMap.id := c1
  have hc2 : B.comp Q = LinearMap.id := c2
  have hc3 : A.comp Q = 0 := c3
  have hc4 : B.comp P = 0 := c4
  have hc5 : P.comp A + Q.comp B = LinearMap.id := c5
  have i1 : ∀ x : ratCohomology k (TopCat.toSSet.obj X), A (P x) = x := by
    intro x
    have h := LinearMap.congr_fun hc1 x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  have i2 : ∀ y : ratCohomology k (TopCat.toSSet.obj Y), B (Q y) = y := by
    intro y
    have h := LinearMap.congr_fun hc2 y
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  have i3 : ∀ y : ratCohomology k (TopCat.toSSet.obj Y), A (Q y) = 0 := by
    intro y
    have h := LinearMap.congr_fun hc3 y
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have i4 : ∀ x : ratCohomology k (TopCat.toSSet.obj X), B (P x) = 0 := by
    intro x
    have h := LinearMap.congr_fun hc4 x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have i5 : ∀ z : ratCohomology k (TopCat.toSSet.obj (X ⨿ Y)), P (A z) + Q (B z) = z := by
    intro z
    have h := LinearMap.congr_fun hc5 z
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] using h
  change Function.Bijective (LinearMap.prod A B)
  refine ⟨?_, ?_⟩
  · intro z w hzw
    have hz : A z = A w := by
      have h := congrArg Prod.fst hzw
      simpa only [LinearMap.prod_apply, Function.prod] using h
    have hw : B z = B w := by
      have h := congrArg Prod.snd hzw
      simpa only [LinearMap.prod_apply, Function.prod] using h
    calc z = P (A z) + Q (B z) := (i5 z).symm
      _ = P (A w) + Q (B w) := by rw [hz, hw]
      _ = w := i5 w
  · intro w
    refine ⟨P w.1 + Q w.2, ?_⟩
    apply Prod.ext
    · show A (P w.1 + Q w.2) = w.1
      rw [map_add, i1 w.1, i3 w.2, add_zero]
    · show B (P w.1 + Q w.2) = w.2
      rw [map_add, i4 w.1, i2 w.2, zero_add]

end

end Work.Bordism
