import Mathlib
import Submission.Work.Domain.Resid.valueOf_api
import Submission.Work.Domain.Resid.canonPt_generic
import Submission.Work.Domain.Resid.exists_algHom_fractionRing
import Submission.Work.Domain.Resid.canonPt_closed
import Submission.Work.Domain.Resid.canonPt_closed_pt
import Submission.Work.Domain.Resid.fromSpecStalk_algebraMap

set_option autoImplicit false
set_option maxHeartbeats 4000000
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.Domain.Resid

open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} [SpecLin.DivBase C]

/-- **The generic fibre of a lift through an open subscheme.**  If `ψ` is an `A`-point of an
open subscheme `U ⊆ X` whose base change to `K(X)` is the generic point of `X`, then it is the
canonical map `Spec K(X) ⟶ U` of the stalk at the generic point: use the uniqueness of the lift
of `X.fromSpecStalk (genericPoint X)` along the open immersion `U.ι`. -/
theorem lift_left_eq_fromSpecStalkOfMem {X : Sch K} [IsIntegral X.left]
    {U : X.left.Opens} (hU : genericPoint X.left ∈ U)
    {A : Type u} [CommRing A] [Algebra K A] [Algebra A X.left.functionField]
    [IsScalarTower K A X.left.functionField]
    (ψ : RPt (Opens.toOver U) A)
    (h : RPt.map (IsScalarTower.toAlgHom K A X.left.functionField) ψ
        ≫ Opens.ιOver U = genericFPt X) :
    (RPt.map (IsScalarTower.toAlgHom K A X.left.functionField) ψ).left =
      U.fromSpecStalkOfMem (genericPoint X.left) hU := by
  have hle : Set.range ⇑(X.left.fromSpecStalk (genericPoint X.left)) ⊆ Set.range ⇑(U.ι) := by
    rw [Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
    rintro y hy
    exact hy.mem_open U.2 hU
  have h' : (RPt.map (IsScalarTower.toAlgHom K A X.left.functionField) ψ).left
      ≫ U.ι = X.left.fromSpecStalk (genericPoint X.left) := by
    have := congrArg Over.Hom.left h
    simpa [Opens.ιOver_left, genericFPt] using this
  rw [IsOpenImmersion.lift_uniq U.ι (X.left.fromSpecStalk (genericPoint X.left)) hle _ h',
    IsOpenImmersion.lift_uniq U.ι (X.left.fromSpecStalk (genericPoint X.left)) hle _
      (Scheme.Opens.fromSpecStalkOfMem_ι U (genericPoint X.left) hU)]

/-- Base change of a field point does not change which open subschemes it lands in. -/
theorem rPt_map_landsIn_iff {X : Sch K} {F F' : Type u} [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F') (p : RPt X F)
    (U : X.left.Opens) :
    RPt.LandsIn (RPt.map e p) U ↔ RPt.LandsIn p U := by
  rw [RPt.landsIn_iff, RPt.landsIn_iff]
  have h : (RPt.map e p).left (IsLocalRing.closedPoint F') =
      p.left (IsLocalRing.closedPoint F) := by
    rw [RPt.map, Over.comp_left, specOfMap_left]
    erw [Scheme.Hom.comp_apply, AlgebraicGeometry.Spec_closedPoint (f := CommRingCat.ofHom e.toRingHom)]
  rw [h]

/-- `RPt.map` is natural with respect to composition of the point with a morphism. -/
theorem rPt_map_comp {X Y : Sch K} {F F' : Type u} [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F →ₐ[K] F') (p : RPt X F) (u : X ⟶ Y) :
    RPt.map e p ≫ u = RPt.map e (p ≫ u) := by
  simp only [RPt.map, Category.assoc]

set_option maxHeartbeats 4000000 in
/-- **VALUE of the residue map at a residue point.**  For `x` in the domain of the residue map
`σ = D.residMap a b hm : X ⤏ Sym^m C`, the value of `σ` at the canonical `κ(x)`-point of `X`
represents the class of `divOf (b x) - divOf (a x)`.

This is the residue-point (`κ(x)`-level) case of RESID's VALUE property, and the crux of
`Submission/Work/Domain/Resid/residMap_value.lean`, which reduces an arbitrary field point `p`
to this case by writing `p = RPt.map e (resPt X x)` (`Work.GroupChunk.exists_factor_resPt`) and
base-changing along `e : κ(x) →ₐ[K] F`.

The proof follows the blueprint in `Submission/Work/Domain/Resid/NOTES.md` ("$VALUE"): choose a
valuation subring `A ⊆ K(X)` dominating `O_{X,x}`, lift the canonical `A`-point `φ` of `X`
through the open `σ.domain` to an `A`-point `ψ`, and apply `ResidData.specLin` to
`addMor (φ ≫ a) (ψ ≫ σ)` and `φ ≫ b`.  All three closed fibres are base changes of divisors
over `κ(x)` (`canonPt_closed_pt`), so the relation descends to `κ(x)`. -/
theorem rel_resPt {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] {symGeom : ∀ n, Work.SpecLin.SymGeom C n} {g : ℕ}
    (D : Work.Domain.Resid.ResidData (K := K) symGeom g) {X : Work.GCBasics.Sch K}
    [AlgebraicGeometry.IsIntegral X.left]
    {r m : ℕ} (hred : AlgebraicGeometry.IsReduced X.left)
    (hsep : AlgebraicGeometry.IsSeparated ((symGeom m).S).hom)
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S) (hm : g ≤ m)
    (x : X.left) (hx : x ∈ (D.residMap a b hm).domain) :
    Work.Domain.Resid.Rel symGeom a b (Work.GCBasics.resPt X x)
      (Work.Domain.Resid.valueOf hred hsep (D.residMap a b hm)
        (D.residMap_isOver a b hm) (Work.GCBasics.resPt X x)
        ((Work.GCBasics.resPt_landsIn_iff X x (D.residMap a b hm).domain).mpr hx)) := by
  haveI : IsReduced X.left := hred
  haveI : IsSeparated ((symGeom m).S).hom := hsep
  haveI hσover : (D.residMap a b hm).IsOver (Spec (CommRingCat.of K)) :=
    D.residMap_isOver a b hm
  haveI hσpover : (D.residMap a b hm).toPartialMap.IsOver (Spec (CommRingCat.of K)) :=
    inferInstance
  -- a valuation subring `A ⊆ K(X)` dominating `O_{X,x}`
  obtain ⟨A, hAdom⟩ := Work.GCBasics.exists_valuationSubring_dominating (X := X.left) x
  obtain ⟨hA, hloc⟩ := hAdom
  let ρ : X.left.presheaf.stalk x →+* A :=
    (algebraMap (X.left.presheaf.stalk x) X.left.functionField).codRestrict A.toSubring hA
  haveI : IsLocalHom ρ := hloc
  letI : Algebra K A := canonAlgebra (K := K) x ρ
  have hKA : (specOf K A).hom =
      Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x ≫ X.hom :=
    canonAlgebra_spec (K := K) x ρ
  have hρ : (algebraMap A X.left.functionField).comp ρ =
      algebraMap (X.left.presheaf.stalk x) X.left.functionField := by ext s; rfl
  have hρcat : CommRingCat.ofHom ρ ≫ CommRingCat.ofHom A.subtype =
      CommRingCat.ofHom (algebraMap (X.left.presheaf.stalk x) X.left.functionField) := by
    rw [← CommRingCat.ofHom_comp]; exact congrArg CommRingCat.ofHom hρ
  have hkey : Spec.map (CommRingCat.ofHom (algebraMap K X.left.functionField)) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap A X.left.functionField).comp (algebraMap K A))) := by
    rw [show (algebraMap A X.left.functionField) = A.subtype from rfl]
    rw [CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp]
    rw [← Work.GCBasics.specOf_hom K X.left.functionField,
      Work.GCBasics.specOf_functionField_hom]
    rw [← Work.GCBasics.specOf_hom K A, hKA]
    conv_rhs => rw [← Category.assoc]
    rw [← AlgebraicGeometry.Spec.map_comp (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom A.subtype), hρcat]
    conv_rhs => rw [← Category.assoc]
    rw [fromSpecStalk_algebraMap x]
  haveI htower : IsScalarTower K A X.left.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have hcat := Spec.map_inj.mp hkey
    have hhom := CommRingCat.hom_ext_iff.mp hcat
    rw [CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at hhom
    exact hhom
  let φ : RPt X A := canonPt x ρ hKA
  -- `φ` lands in the domain of `σ` (its closed point is `x`)
  have hφlands : RPt.LandsIn φ (D.residMap a b hm).domain := by
    rw [RPt.landsIn_iff]
    show φ.left (IsLocalRing.closedPoint A) ∈ _
    have h1 : φ.left (IsLocalRing.closedPoint A) = x := by
      show (Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x)
        (IsLocalRing.closedPoint A) = x
      erw [Scheme.Hom.comp_apply, AlgebraicGeometry.Spec_closedPoint (f := CommRingCat.ofHom ρ),
        Scheme.fromSpecStalk_closedPoint]
    rw [h1]; exact hx
  -- lift `φ` through the open subscheme `σ.domain`
  obtain ⟨ψ, hψ, hψuniq⟩ := RPt.factor_of_closed_landsIn (K := K)
    (D.residMap a b hm).domain φ hφlands
  -- `σ` as a morphism of `K`-schemes on its domain
  let σOver : Opens.toOver (D.residMap a b hm).domain ⟶ (symGeom m).S :=
    Over.homMk (D.residMap a b hm).toPartialMap.hom (by
      have h := hσpover.1
      show (D.residMap a b hm).toPartialMap.hom ≫ (symGeom m).S.hom =
        (Opens.toOver (D.residMap a b hm).domain).hom
      rw [show (Opens.toOver (D.residMap a b hm).domain).hom =
        (D.residMap a b hm).toPartialMap.domain.ι ≫ X.hom from rfl]
      exact h)
  let σA : RPt (symGeom m).S A := ψ ≫ σOver
  let aA : RPt (symGeom r).S A := φ ≫ a
  let bA : RPt (symGeom (r + m)).S A := φ ≫ b
  let WA : RPt (symGeom (r + m)).S A := addMor symGeom D.addMap aA σA
  -- the generic fibre of `ψ`
  have hg : Function.Injective ⇑(IsScalarTower.toAlgHom K A X.left.functionField) := by
    intro aa bb h; exact Subtype.val_injective h
  let pK : FPt (specOf K A) X.left.functionField :=
    specOfMap (K := K) (IsScalarTower.toAlgHom K A X.left.functionField)
  have hφgen : pK ≫ φ = genericFPt X := canonPt_generic x ρ hKA hρ
  have hψgen : RPt.map (IsScalarTower.toAlgHom K A X.left.functionField) ψ
      ≫ Opens.ιOver (D.residMap a b hm).domain = genericFPt X := by
    show pK ≫ (ψ ≫ Opens.ιOver (D.residMap a b hm).domain) = genericFPt X
    rw [hψ]; exact hφgen
  have hdom_gp : genericPoint X.left ∈ (D.residMap a b hm).domain :=
    (genericPoint_specializes _).mem_open (D.residMap a b hm).domain.2
      (D.residMap a b hm).toPartialMap.dense_domain.nonempty.choose_spec
  have hψleft : (pK ≫ ψ).left =
      (D.residMap a b hm).domain.fromSpecStalkOfMem (genericPoint X.left) hdom_gp :=
    lift_left_eq_fromSpecStalkOfMem hdom_gp ψ hψgen
  -- the generic fibre of `σA` is the generic value of the residue map
  have hσAgen : pK ≫ σA = genValue a b D.rr7 hm := by
    apply Over.OverMorphism.ext
    show (pK ≫ σA).left = (genValue a b D.rr7 hm).left
    have h1 : (pK ≫ σA).left = (pK ≫ ψ).left ≫ σOver.left := by
      dsimp only [σA]
      simp only [Over.comp_left, Category.assoc]
    rw [h1, hψleft]
    show (D.residMap a b hm).domain.fromSpecStalkOfMem (genericPoint X.left) hdom_gp ≫
        (D.residMap a b hm).toPartialMap.hom = (genValue a b D.rr7 hm).left
    rw [show (D.residMap a b hm).domain.fromSpecStalkOfMem (genericPoint X.left) hdom_gp ≫
        (D.residMap a b hm).toPartialMap.hom =
        (D.residMap a b hm).toPartialMap.fromFunctionField from rfl,
      ← Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.toRationalMap_toPartialMap]
    exact D.residMap_fromFunctionField a b hm
  -- the generic fibres of `WA` and `bA` are linearly equivalent
  let ι : FractionRing A →ₐ[K] X.left.functionField :=
    IsFractionRing.liftAlgHom (R := K) (A := A) (K := FractionRing A)
      (L := X.left.functionField) (g := IsScalarTower.toAlgHom K A X.left.functionField) hg
  have hι : ι.comp (IsScalarTower.toAlgHom K A (FractionRing A)) =
      IsScalarTower.toAlgHom K A X.left.functionField := by
    ext aa
    rw [AlgHom.comp_apply]
    show ι ((IsScalarTower.toAlgHom K A (FractionRing A)) aa) =
        (IsScalarTower.toAlgHom K A X.left.functionField) aa
    rw [show ι = IsFractionRing.liftAlgHom (R := K) (A := A) (K := FractionRing A)
      (L := X.left.functionField) (g := IsScalarTower.toAlgHom K A X.left.functionField) hg
      from rfl]
    rw [IsScalarTower.toAlgHom_apply K A (FractionRing A) aa,
      IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    exact IsScalarTower.toAlgHom_apply K A X.left.functionField aa
  have hgenLin : Work.GCBasics.LinEquiv C ((symGeom (r + m)).divOf (genPt A ≫ WA))
      ((symGeom (r + m)).divOf (genPt A ≫ bA)) := by
    refine (SpecLin.DivBase.linEquiv_bc_iff (C := C) ι _ _).mp ?_
    rw [← SpecLin.SymGeom.divOf_map ι (genPt A ≫ WA),
        ← SpecLin.SymGeom.divOf_map ι (genPt A ≫ bA)]
    change Work.GCBasics.LinEquiv C
      (SpecLin.SymGeom.divOf (Work.GCBasics.RPt.map ι (genPt A ≫ WA)))
      (SpecLin.SymGeom.divOf (Work.GCBasics.RPt.map ι (genPt A ≫ bA)))
    have hmapW : RPt.map ι (genPt A ≫ WA) = pK ≫ WA := by
      dsimp only [RPt.map, genPt]
      rw [← Category.assoc, ← specOfMap_comp, hι]
    have hmapV : RPt.map ι (genPt A ≫ bA) = pK ≫ bA := by
      dsimp only [RPt.map, genPt]
      rw [← Category.assoc, ← specOfMap_comp, hι]
    rw [hmapW, hmapV]
    have hpu : pK ≫ aA = genericFPt X ≫ a := by
      show pK ≫ (φ ≫ a) = _; rw [← Category.assoc, hφgen]
    have hpv : pK ≫ bA = genericFPt X ≫ b := by
      show pK ≫ (φ ≫ b) = _; rw [← Category.assoc, hφgen]
    have hdivW : (symGeom (r + m)).divOf (pK ≫ WA)
        = (symGeom r).divOf (pK ≫ aA) + (symGeom m).divOf (pK ≫ σA) :=
      addMor_divOf D.addMap_divOf aA σA pK
    rw [hdivW, hpv, hpu, hσAgen, add_comm]
    exact genValue_spec a b D.rr7 hm
  -- specialisation: the relation over `κ(A)`
  have hclosed : Work.GCBasics.LinEquiv C
      ((symGeom (r + m)).divOf (closedPt (K := K) A ≫ WA))
      ((symGeom (r + m)).divOf (closedPt (K := K) A ≫ bA)) :=
    D.specLin (symGeom (r + m)) A WA bA hgenLin
  -- descent to `κ(x)`
  obtain ⟨e, hpt⟩ := canonPt_closed_pt (K := K) x ρ hKA
  haveI : IsLocalHom e.toRingHom := inferInstance
  have hpx : RPt.LandsIn (resPt X x) (D.residMap a b hm).domain :=
    (resPt_landsIn_iff X x _).mpr hx
  obtain ⟨q₀, hq₀, -⟩ := RPt.factor_of_closed_landsIn (K := K)
    (D.residMap a b hm).domain (resPt X x) hpx
  -- the closed fibre of `ψ` is the base change of `q₀`
  have hclose : closedPt (K := K) A ≫ ψ = RPt.map e q₀ := by
    have hq : RPt.LandsIn (closedPt (K := K) A ≫ φ) (D.residMap a b hm).domain := by
      rw [hpt, rPt_map_landsIn_iff]
      exact hpx
    obtain ⟨qA, hqA, hqAuniq⟩ := RPt.factor_of_closed_landsIn (K := K)
      (D.residMap a b hm).domain (closedPt (K := K) A ≫ φ) hq
    have h1 : closedPt (K := K) A ≫ ψ = qA :=
      hqAuniq _ (show (closedPt (K := K) A ≫ ψ)
          ≫ Opens.ιOver (D.residMap a b hm).domain = closedPt (K := K) A ≫ φ from by
        rw [Category.assoc, hψ])
    have h2 : RPt.map e q₀ = qA :=
      hqAuniq _ (show (RPt.map e q₀)
          ≫ Opens.ιOver (D.residMap a b hm).domain = closedPt (K := K) A ≫ φ from by
        rw [rPt_map_comp, hq₀, ← hpt])
    rw [h1, h2]
  have hdivU : (symGeom r).divOf (closedPt (K := K) A ≫ aA)
      = SpecLin.DivBase.bc e ((symGeom r).divOf (resPt X x ≫ a)) := by
    rw [show closedPt (K := K) A ≫ aA = RPt.map e (resPt X x ≫ a) from by
      show closedPt (K := K) A ≫ (φ ≫ a) = _
      rw [← Category.assoc, hpt]; rfl]
    exact SpecLin.SymGeom.divOf_map e (resPt X x ≫ a)
  have hdivV : (symGeom (r + m)).divOf (closedPt (K := K) A ≫ bA)
      = SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b)) := by
    rw [show closedPt (K := K) A ≫ bA = RPt.map e (resPt X x ≫ b) from by
      show closedPt (K := K) A ≫ (φ ≫ b) = _
      rw [← Category.assoc, hpt]; rfl]
    exact SpecLin.SymGeom.divOf_map e (resPt X x ≫ b)
  have hdivσ : (symGeom m).divOf (closedPt (K := K) A ≫ σA)
      = SpecLin.DivBase.bc e ((symGeom m).divOf (q₀ ≫ σOver)) := by
    rw [show closedPt (K := K) A ≫ σA = RPt.map e (q₀ ≫ σOver) from by
      show closedPt (K := K) A ≫ (ψ ≫ σOver) = _
      rw [← Category.assoc, hclose, rPt_map_comp]]
    exact SpecLin.SymGeom.divOf_map e (q₀ ≫ σOver)
  have hdivWc : (symGeom (r + m)).divOf (closedPt (K := K) A ≫ WA)
      = (symGeom r).divOf (closedPt (K := K) A ≫ aA)
        + (symGeom m).divOf (closedPt (K := K) A ≫ σA) :=
    addMor_divOf D.addMap_divOf aA σA (closedPt (K := K) A)
  have hrelA : Work.GCBasics.LinEquiv C
      (SpecLin.DivBase.bc e ((symGeom r).divOf (resPt X x ≫ a)
        + (symGeom m).divOf (q₀ ≫ σOver)))
      (SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b))) := by
    rw [SpecLin.DivBase.bc_add, ← hdivU, ← hdivσ, ← hdivWc, ← hdivV]
    exact hclosed
  have hrelx : Work.GCBasics.LinEquiv C
      ((symGeom r).divOf (resPt X x ≫ a) + (symGeom m).divOf (q₀ ≫ σOver))
      ((symGeom (r + m)).divOf (resPt X x ≫ b)) :=
    (SpecLin.DivBase.linEquiv_bc_iff e _ _).mp hrelA
  -- identify the value of `σ` at `resPt X x` with `q₀ ≫ σOver`
  have hval : (symGeom m).divOf (valueOf hred hsep (D.residMap a b hm)
        (D.residMap_isOver a b hm) (resPt X x)
        ((resPt_landsIn_iff X x (D.residMap a b hm).domain).mpr hx))
      = (symGeom m).divOf (q₀ ≫ σOver) := by
    congr 1
    apply Over.OverMorphism.ext
    rw [valueOf_left_eq hred hsep (D.residMap a b hm) (D.residMap_isOver a b hm)
      (resPt X x) _ q₀ hq₀]
    rfl
  rw [Rel, hval,
    show (symGeom m).divOf (q₀ ≫ σOver) + (symGeom r).divOf (resPt X x ≫ a)
      = (symGeom r).divOf (resPt X x ≫ a) + (symGeom m).divOf (q₀ ≫ σOver)
      from add_comm _ _]
  exact hrelx

end

end Work.Domain.Resid
