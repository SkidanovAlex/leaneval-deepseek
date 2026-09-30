/-
# Elementary manipulations of `specOfMap`, points and divisors
-/
import Mathlib
import Submission.Work.SpecLin.Setup.Ext

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin

variable {K : Type u} [Field K]

/-! ### `specOfMapHom` and its composition -/

/-- Two ring maps inducing the same morphism of relative spectra. -/
theorem specOfMapHom_congr {R R' : Type u} [CommRing R] [CommRing R'] [Algebra K R]
    [Algebra K R'] {f g : R →+* R'}
    (hf : ∀ k : K, f (algebraMap K R k) = algebraMap K R' k)
    (hg : ∀ k : K, g (algebraMap K R k) = algebraMap K R' k) (h : f = g) :
    specOfMapHom (K := K) f hf = specOfMapHom (K := K) g hg := by
  subst h
  rfl

/-- Composition of the morphisms induced by ring maps compatible with the structure maps to
`Spec K`. -/
theorem specOfMapHom_comp {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    [Algebra K R] [Algebra K R'] [Algebra K R''] (f : R →+* R')
    (hf : ∀ k : K, f (algebraMap K R k) = algebraMap K R' k)
    (g : R' →+* R'') (hg : ∀ k : K, g (algebraMap K R' k) = algebraMap K R'' k) :
    specOfMapHom (K := K) g hg ≫ specOfMapHom (K := K) f hf =
      specOfMapHom (K := K) (g.comp f) (fun k => by rw [RingHom.comp_apply, hf k, hg k]) := by
  apply Over.OverMorphism.ext
  simp only [specOfMapHom, Over.homMk_left, Over.comp_left, Spec.map_comp,
    CommRingCat.ofHom_comp]

/-- The ring hom underlying `IsScalarTower.toAlgHom` is the algebra map. -/
theorem toAlgHom_toRingHom (R S A : Type u) [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] :
    (IsScalarTower.toAlgHom R S A).toRingHom = algebraMap S A :=
  RingHom.ext (fun x => IsScalarTower.toAlgHom_apply R S A x)

/-- `genPt` is induced by the structure map `R → Frac R`. -/
theorem genPt_eq_specOfMap (R : Type u) [CommRing R] [IsDomain R] [Algebra K R] :
    genPt (K := K) R =
      specOfMap (K := K) (IsScalarTower.toAlgHom K R (FractionRing R)) := rfl

/-- `closedPt` is induced by the residue map `R → κ`. -/
theorem closedPt_eq_specOfMap (R : Type u) [CommRing R] [IsLocalRing R] [Algebra K R] :
    closedPt (K := K) R =
      specOfMap (K := K) (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) := by
  rw [closedPt, specOfMap]
  exact specOfMapHom_congr _ _
    (RingHom.ext (fun x => (IsScalarTower.toAlgHom_apply K R (IsLocalRing.ResidueField R) x).symm))

/-- **Naturality of `closedPt`.**  A local `K`-algebra map `R → R'` intertwines the closed points
of `Spec R` and `Spec R'` via the induced map of residue fields. -/
theorem specOfMap_residue_eq {R R' : Type u} [CommRing R] [CommRing R'] [IsLocalRing R]
    [IsLocalRing R'] [Algebra K R] [Algebra K R'] (e : R →ₐ[K] R') [IsLocalHom e] :
    specOfMap (K := K) (IsLocalRing.ResidueField.mapAlgHom e) ≫ closedPt (K := K) R =
      closedPt (K := K) R' ≫ specOfMap (K := K) e := by
  have key : (IsLocalRing.ResidueField.mapAlgHom e).toRingHom.comp
        (algebraMap R (IsLocalRing.ResidueField R)) =
      (algebraMap R' (IsLocalRing.ResidueField R')).comp e.toRingHom := by
    ext x
    change IsLocalRing.ResidueField.mapAlgHom e
        (algebraMap R (IsLocalRing.ResidueField R) x)
      = algebraMap R' (IsLocalRing.ResidueField R') (e x)
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ResidueField.mapAlgHom_residue,
      IsLocalRing.ResidueField.algebraMap_eq]
  calc specOfMap (K := K) (IsLocalRing.ResidueField.mapAlgHom e) ≫ closedPt (K := K) R
      = specOfMapHom (K := K) (IsLocalRing.ResidueField.mapAlgHom e).toRingHom _
          ≫ specOfMapHom (K := K) (algebraMap R (IsLocalRing.ResidueField R)) _ := rfl
    _ = specOfMapHom (K := K)
          ((IsLocalRing.ResidueField.mapAlgHom e).toRingHom.comp
            (algebraMap R (IsLocalRing.ResidueField R))) _ :=
        specOfMapHom_comp _ _ _ _
    _ = specOfMapHom (K := K)
          ((algebraMap R' (IsLocalRing.ResidueField R')).comp e.toRingHom) _ :=
        specOfMapHom_congr _ _ key
    _ = specOfMapHom (K := K) (algebraMap R' (IsLocalRing.ResidueField R')) _
          ≫ specOfMapHom (K := K) e.toRingHom _ :=
        (specOfMapHom_comp _ _ _ _).symm
    _ = closedPt (K := K) R' ≫ specOfMap (K := K) e := rfl

/-! ### Points and separatedness -/

/-- **Separatedness/valuative uniqueness.**  Let `X` be a separated `K`-scheme, `R` a valuation
ring which is a `K`-algebra and `F` a fraction field of `R` (with compatible `K`-algebra
structures).  Two `R`-points of `X` with the same generic fibre over `F` are equal. -/
theorem RPt.eq_of_generic_eq {X : Sch K} (hX : IsSeparated X.hom)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (F : Type u) [Field F] [Algebra K F] [Algebra R F] [IsFractionRing R F]
    [IsScalarTower K R F] {a b : RPt X R}
    (h : RPt.map (IsScalarTower.toAlgHom K R F) a = RPt.map (IsScalarTower.toAlgHom K R F) b) :
    a = b := by
  haveI : IsSeparated X.hom := hX
  have hsq : CommSq (RPt.map (IsScalarTower.toAlgHom K R F) a).left
      (Spec.map (CommRingCat.ofHom (algebraMap R F))) X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K R))) := by
    refine ⟨?_⟩
    rw [show (RPt.map (IsScalarTower.toAlgHom K R F) a).left ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K F)) from Over.w _]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K R F]
  let S : ValuativeCommSq X.hom :=
    { R := R, K := F, i₁ := (RPt.map (IsScalarTower.toAlgHom K R F) a).left,
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap K R)), commSq := hsq }
  have huniq : Subsingleton S.commSq.LiftStruct :=
    IsSeparated.valuativeCriterion X.hom S
  have hla : (RPt.map (IsScalarTower.toAlgHom K R F) a).left
      = Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ a.left := by
    rw [show (RPt.map (IsScalarTower.toAlgHom K R F) a).left
        = Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom K R F).toRingHom) ≫ a.left
      from rfl, ← toAlgHom_toRingHom K R F]
  have hlb : (RPt.map (IsScalarTower.toAlgHom K R F) b).left
      = Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ b.left := by
    rw [show (RPt.map (IsScalarTower.toAlgHom K R F) b).left
        = Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom K R F).toRingHom) ≫ b.left
      from rfl, ← toAlgHom_toRingHom K R F]
  let e1 : S.commSq.LiftStruct :=
    ⟨a.left, hla.symm, by
      show a.left ≫ X.hom = S.i₂
      rw [Over.w a]
      rfl⟩
  let e2 : S.commSq.LiftStruct :=
    ⟨b.left, by
      show Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ b.left
        = (RPt.map (IsScalarTower.toAlgHom K R F) a).left
      rw [h, hlb], by
      show b.left ≫ X.hom = S.i₂
      rw [Over.w b]
      rfl⟩
  have h12 : e1 = e2 := Subsingleton.elim e1 e2
  have hL : a.left = b.left := by
    change e1.l = e2.l
    exact congrArg CommSq.LiftStruct.l h12
  exact Over.OverMorphism.ext hL

/-- **Existence part of the valuative criterion for a curve.** -/
theorem exists_CurvePt_of_FPt {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (F : Type u) [Field F] [Algebra K F] [Algebra R F] [IsFractionRing R F]
    [IsScalarTower K R F] (x : CurveFPt C F) :
    ∃ s : CurvePt C R, RPt.map (IsScalarTower.toAlgHom K R F) s = x := by
  have hvc : ValuativeCriterion C.toOver.hom := by
    have h := C.proper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : CommSq x.left (Spec.map (CommRingCat.ofHom (algebraMap R F))) C.toOver.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K R))) := by
    refine ⟨?_⟩
    rw [show x.left ≫ C.toOver.hom = Spec.map (CommRingCat.ofHom (algebraMap K F))
      from Over.w x]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K R F]
  let S : ValuativeCommSq C.toOver.hom :=
    { R := R, K := F, i₁ := x.left,
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap K R)), commSq := hsq }
  obtain ⟨l, hl1, hl2⟩ := (ValuativeCriterion.existence hvc S).exists_lift
  refine ⟨Over.homMk l hl2, ?_⟩
  apply Over.OverMorphism.ext
  simp only [RPt.map, specOfMap, specOfMapHom, Over.homMk_left, Over.comp_left]
  exact hl1

/-! ### Divisibility and points -/

/-- **Additivity of the base change of divisors over finite sums.** -/
theorem bc_sum {C : Work.CurveBasics.Curve K} [DivBase C] {n : ℕ} {F F' : Type u} [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F') (D : Fin n → Dv C F) :
    DivBase.bc e (∑ i, D i) = ∑ i, DivBase.bc e (D i) := by
  let f : Dv C F →+ Dv C F' :=
    { toFun := DivBase.bc e, map_zero' := DivBase.bc_zero e
      map_add' := fun A B => DivBase.bc_add e A B }
  exact map_sum f D Finset.univ

/-- The divisor of `powMap s` restricted along `g : Spec F ⟶ Spec R'` is the sum of the point
divisors of the points `g ≫ s m`. -/
theorem divOf_comp_powMap {C : Work.CurveBasics.Curve K} [DivBase C] {n : ℕ}
    (G : SymGeom C n) {R' : Type u} [CommRing R'] [Algebra K R']
    {F : Type u} [Field F] [Algebra K F] (g : specOf (K := K) F ⟶ specOf (K := K) R')
    (s : Fin n → CurvePt C R') :
    G.divOf (g ≫ G.powMap s) = ∑ m, ptDiv (g ≫ s m) := by
  rw [← G.powMap_comp g s, G.divOf_powMap]

/-! ### The canonical map `FractionRing R' → F` of an `Ext` -/

/-- The composite `Spec F ⟶ Spec (Frac R') ⟶ Spec R'` is the structure map of `R'`. -/
theorem specOfMap_psi_comp_genPt {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (E : Ext K R) :
    specOfMap (K := K) E.psi ≫ genPt (K := K) E.R' =
      specOfMap (K := K) (IsScalarTower.toAlgHom K E.R' E.F) := by
  have h : E.psi.comp (IsScalarTower.toAlgHom K E.R' (FractionRing E.R')) =
      IsScalarTower.toAlgHom K E.R' E.F := by
    ext x
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, Ext.psi_algebraMap,
      IsScalarTower.toAlgHom_apply]
  rw [genPt_eq_specOfMap, ← specOfMap_comp, h]

/-- Applying `psi` to the generic fibre of an `R'`-point is the same as extending scalars along
the structure map `R' → F`. -/
theorem RPt_map_psi_comp_genPt {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (E : Ext K R) {X : Sch K} (p : RPt X E.R') :
    RPt.map E.psi (genPt (K := K) E.R' ≫ p) = RPt.map (IsScalarTower.toAlgHom K E.R' E.F) p := by
  show specOfMap E.psi ≫ (genPt (K := K) E.R' ≫ p)
      = RPt.map (IsScalarTower.toAlgHom K E.R' E.F) p
  rw [← Category.assoc, specOfMap_psi_comp_genPt E]
  rfl

/-- The point obtained from an `R`-point by extending scalars along `R → FractionRing R → F` is
the base change of its generic fibre. -/
theorem RPt_map_comp_genPt {R : Type u} [CommRing R] [IsDomain R] [Algebra K R] {F : Type u}
    [Field F] [Algebra K F] [Algebra (FractionRing R) F] [IsScalarTower K (FractionRing R) F]
    {X : Sch K} (a : RPt X R) :
    RPt.map ((IsScalarTower.toAlgHom K (FractionRing R) F).comp
        (IsScalarTower.toAlgHom K R (FractionRing R))) a
      = RPt.map (IsScalarTower.toAlgHom K (FractionRing R) F) (genPt (K := K) R ≫ a) := by
  rw [RPt.map_comp, genPt_eq_specOfMap]
  rfl

end Work.SpecLin
