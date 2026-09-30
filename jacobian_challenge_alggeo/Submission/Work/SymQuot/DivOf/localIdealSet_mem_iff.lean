import Mathlib
import Submission.Work.SymQuot.DivOf.ChartPt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

/-! ### The evaluation of invariant functions at a lift of a point -/

theorem topIso_inv_appTop_eq_appLE {X Y : Scheme} (U : X.Opens) (f : Y ⟶ X)
    (g : Y ⟶ U.toScheme) (hg : g ≫ U.ι = f) (h : ⊤ ≤ f ⁻¹ᵁ U) :
    U.topIso.inv ≫ g.appTop = f.appLE U ⊤ h := by
  subst hg
  have htop : U.topIso.inv = U.ι.app U ≫ (U.toScheme).presheaf.map
      (homOfLE U.ι_preimage_self.ge).op := by
    rw [show U.topIso.inv = U.ι.appLE U ⊤ U.ι_preimage_self.ge from by
      simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
      congr 1]
    rfl
  have happ : g.appTop = g.appLE ⊤ ⊤ (by rw [Scheme.Hom.preimage_top]) :=
    (Scheme.Hom.appLE_eq_app (f := g) (U := ⊤)).symm
  rw [htop, happ, Scheme.Hom.comp_appLE, Category.assoc]
  rw [Scheme.Hom.map_appLE (f := g) (e := by rw [Scheme.Hom.preimage_top])
      (i := (homOfLE U.ι_preimage_self.ge).op)]

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ} [NeZero n]
  [Work.SymQuot.CurveAffineCover C]
  {F : Type u} [Field F] [Algebra K F]
  {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : Work.SymQuot.DivOf.ChartPt C n p)

/-- **The value of an invariant function on the chart at a point equals its value at any lift**:
if `x` is a lift of `p` to an `F'`-point of `Vⁿ`, then the value `φ a` of an invariant function
`a` at `p`, pushed to `F'`, is the evaluation of `a` at `x`. -/
theorem chartPt_evalMap_eq {F' : Type u} [Field F'] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F']
    (x : Fin n → Work.SpecLin.CurveFPt C F')
    (hx : Work.SymQuot.Sym.powMap C n x = Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p)
    (h : (⊤ : (Spec (CommRingCat.of F')).Opens) ≤
      (TopologicalSpace.Opens.map ((CategoryTheory.Limits.Pi.lift x :
        Work.SpecLin.specOf (K := K) F' ⟶ Work.SymQuot.prod C.toOver n)).left.base).obj d.openOf)
    (a : ↥d.chartRingOf) :
    algebraMap F F' (d.φ a) = d.evalMap x h ↑a := by
  have hf : (Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F' ⟶ Work.SymQuot.prod C.toOver n).left ≫
      (Work.SymQuot.symData C n).quotientMap
      = Spec.map (CommRingCat.ofHom (algebraMap F F')) ≫ p.left := by
    have hh := congrArg Over.Hom.left hx
    have h1 : (IsScalarTower.toAlgHom K F F').toRingHom = algebraMap F F' := rfl
    simp only [Work.SymQuot.Sym.powMap, Work.SpecLin.RPt.map,
      Work.SpecLin.specOfMap, Work.SpecLin.specOfMapHom, Over.homMk_left, Over.comp_left] at hh
    rw [h1] at hh
    exact hh
  let f := (Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F' ⟶ Work.SymQuot.prod C.toOver n).left
  have hH' : Set.range ⇑f ⊆ Set.range ⇑d.openOf.ι := by
    rintro _ ⟨y, rfl⟩
    have h1 : y ∈ (TopologicalSpace.Opens.map f.base).obj d.openOf := h trivial
    rw [Scheme.Opens.range_ι]
    simpa using h1
  let g := IsOpenImmersion.lift d.openOf.ι f hH'
  have hg : g ≫ d.openOf.ι = f := IsOpenImmersion.lift_fac d.openOf.ι f hH'
  have hUF : p.left = d.q ≫ (Work.SymQuot.symData C n).chartι
      ⟨d.openOf, Work.SymQuot.Prod.isAffineOpen_piOpen C.toOver n d.V d.isAffineOpen_V,
        Work.SymQuot.DivOf.symPiOpen_invariant C n d.V⟩ := d.fac.symm
  have hq : d.openOf.ι ≫ (Work.SymQuot.symData C n).quotientMap
      = (Work.SymQuot.symAction C n).chartMap d.openOf
        (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V) ≫
        (Work.SymQuot.symData C n).chartι
          ⟨d.openOf, Work.SymQuot.Prod.isAffineOpen_piOpen C.toOver n d.V d.isAffineOpen_V,
            Work.SymQuot.DivOf.symPiOpen_invariant C n d.V⟩ :=
    Work.SymQuot.QuotientData.quotientMap_chartι (Work.SymQuot.symData C n)
      ⟨d.openOf, Work.SymQuot.Prod.isAffineOpen_piOpen C.toOver n d.V d.isAffineOpen_V,
        Work.SymQuot.DivOf.symPiOpen_invariant C n d.V⟩
  have hchart : g ≫ (Work.SymQuot.symAction C n).chartMap d.openOf
        (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V)
      = Spec.map (CommRingCat.ofHom (algebraMap F F')) ≫ d.q := by
    apply (cancel_mono ((Work.SymQuot.symData C n).chartι
      ⟨d.openOf, Work.SymQuot.Prod.isAffineOpen_piOpen C.toOver n d.V d.isAffineOpen_V,
        Work.SymQuot.DivOf.symPiOpen_invariant C n d.V⟩)).mp
    rw [Category.assoc, ← hq, ← Category.assoc, hg, hf, Category.assoc, hUF]
  let Aring : CommRingCat.{u} := Work.SymQuot.GAction.chartRing (Work.SymQuot.symAction C n)
    d.openOf (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V)
  have hA : CommRingCat.ofHom (algebraMap F F')
      = ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap F F'))).appTop) ≫
        (Scheme.ΓSpecIso (CommRingCat.of F')).hom := by
    rw [← Scheme.ΓSpecIso_inv_naturality (f := CommRingCat.ofHom (algebraMap F F'))]
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hHF : (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom (algebraMap F F')
      = (Spec.map (CommRingCat.ofHom (algebraMap F F'))).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of F')).hom := by
    conv_lhs => rw [hA]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  let sub2 : Aring ⟶ Γ((Work.SymQuot.prod C.toOver n).left, d.openOf) :=
    CommRingCat.ofHom (Subring.subtype d.chartRingOf)
  have hD : (Scheme.ΓSpecIso Aring).inv ≫ ((Work.SymQuot.symAction C n).chartMap d.openOf
        (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V)).appTop
      = sub2 ≫ d.openOf.topIso.inv := by
    rw [show (Work.SymQuot.symAction C n).chartMap d.openOf
        (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V)
        = d.openOf.toSpecΓ ≫ Spec.map sub2 from rfl]
    rw [Scheme.Hom.comp_appTop]
    slice_lhs 0 2 => rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality (R := Aring)
      (f := sub2)]
    rw [Scheme.Opens.toSpecΓ_appTop]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
  have hE : d.openOf.topIso.inv ≫ g.appTop = f.appLE d.openOf ⊤ h :=
    topIso_inv_appTop_eq_appLE d.openOf f g hg h
  have hcat : (Scheme.ΓSpecIso Aring).inv ≫ d.q.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom (algebraMap F F')
      = sub2 ≫ f.appLE d.openOf ⊤ h ≫
        (Scheme.ΓSpecIso (CommRingCat.of F')).hom := by
    slice_lhs 2 4 => rw [hHF]
    rw [show (Scheme.ΓSpecIso Aring).inv ≫ d.q.appTop ≫
          (Spec.map (CommRingCat.ofHom (algebraMap F F'))).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of F')).hom
        = (Scheme.ΓSpecIso Aring).inv ≫ ((d.q.appTop ≫
            (Spec.map (CommRingCat.ofHom (algebraMap F F'))).appTop) ≫
            (Scheme.ΓSpecIso (CommRingCat.of F')).hom) from by simp only [Category.assoc]]
    rw [← Scheme.Hom.comp_appTop]
    try simp only [Category.assoc]
    slice_lhs 1 2 => rw [← hchart]
    slice_lhs 1 2 => rw [Scheme.Hom.comp_appTop]
    slice_lhs 0 2 => rw [← Category.assoc, hD]
    try simp only [Category.assoc]
    rw [show sub2 ≫ d.openOf.topIso.inv ≫
          Scheme.Hom.appTop g ≫ (Scheme.ΓSpecIso (CommRingCat.of F')).hom
        = sub2 ≫ ((d.openOf.topIso.inv ≫
            Scheme.Hom.appTop g) ≫ (Scheme.ΓSpecIso (CommRingCat.of F')).hom)
        from by simp only [Category.assoc]]
    rw [hE]
    try simp only [Category.assoc]
  exact congrArg (fun (φ : Aring ⟶ CommRingCat.of F') => φ.hom a) hcat

/-! ### Polynomial lemmas -/

/-- **For a polynomial of degree `≤ n`, mapping it along a ring hom is the sum of its values on
the coefficients.** -/
theorem localIdealAux_map_eq_sum_range_C_mul_X_pow {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (q : Polynomial R) (n : ℕ) (h : q.natDegree ≤ n) :
    q.map f = ∑ i ∈ Finset.range (n + 1), Polynomial.C (f (q.coeff i)) * Polynomial.X ^ i := by
  have h1 : q = ∑ i ∈ Finset.range (n + 1),
      Polynomial.C (q.coeff i) * Polynomial.X ^ i := by
    conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq q]
    rw [Polynomial.sum_def]
    refine Finset.sum_subset
      (f := fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ i) ?_ ?_
    · intro i hi
      rw [Polynomial.mem_support_iff] at hi
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (le_trans (Polynomial.le_natDegree_of_ne_zero hi) h))
    · intro i _ hi
      rw [Polynomial.mem_support_iff, not_not] at hi
      rw [hi, Polynomial.C_0, zero_mul]
  conv_lhs => rw [h1]
  rw [Polynomial.map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]

/-- **A product of `n` linear factors is `X^n` iff all the roots vanish.** -/
theorem localIdealAux_prod_X_sub_C_eq_X_pow_iff {F : Type u} [Field F] {n : ℕ} [NeZero n] (lam : Fin n → F) :
    (∏ m : Fin n, (Polynomial.X - Polynomial.C (lam m)) = Polynomial.X ^ n) ↔
      ∀ m, lam m = 0 := by
  constructor
  · intro hb m
    by_contra hm
    have hev := congrArg (Polynomial.eval (lam m)) hb
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_pow] at hev
    rw [Finset.prod_eq_zero (Finset.mem_univ m) (sub_self (lam m))] at hev
    exact absurd hev.symm (pow_ne_zero n hm)
  · intro hb
    rw [Finset.prod_congr rfl (fun m _ => by rw [hb m, Polynomial.C_0, sub_zero]),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The local ideal of a point of `Symⁿ C`

The local ideal of the point `p` is the set of `b` whose characteristic polynomial is `Tⁿ`; we
show that it is also the set of `b` vanishing at every coordinate of any lift `x` of `p`. -/

theorem localIdealSet_mem_iff {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {n : ℕ} [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : Work.SymQuot.DivOf.ChartPt C n p)
    {F' : Type u} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    (x : Fin n → Work.SpecLin.CurveFPt C F')
    (hx : Work.SymQuot.Sym.powMap C n x = Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p)
    (h : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of F')).Opens) ≤
      (TopologicalSpace.Opens.map ((CategoryTheory.Limits.Pi.lift x :
        Work.SpecLin.specOf (K := K) F' ⟶ Work.SymQuot.prod C.toOver n)).left.base).obj d.openOf)
    (b : C.left.presheaf.obj (Opposite.op d.V)) :
    b ∈ d.localIdealSet ↔
      ∀ m, d.evalMap x h (Work.SymQuot.DivOf.coordPullbackAt C n d.V m b) = 0 := by
  have hdeg : (Work.SymQuot.DivOf.charpoly C n d.V b).natDegree ≤ n := by
    rw [Work.SymQuot.DivOf.charpoly]
    refine le_trans (Polynomial.natDegree_prod_le Finset.univ
      (fun m : Fin n => Polynomial.X - Polynomial.C
        (Work.SymQuot.DivOf.coordPullbackAt C n d.V m b))) ?_
    refine le_trans (Finset.sum_le_sum (f := fun i : Fin n =>
        (Polynomial.X - Polynomial.C
          (Work.SymQuot.DivOf.coordPullbackAt C n d.V i b)).natDegree)
      (g := fun _ : Fin n => (1 : ℕ)) fun i _ => Polynomial.natDegree_X_sub_C_le _) ?_
    simp
  have h1 : Polynomial.map (algebraMap F F') (d.charpolyValue b)
      = ∑ i ∈ Finset.range (n + 1),
          Polynomial.C (d.evalMap x h ((Work.SymQuot.DivOf.charpoly C n d.V b).coeff i)) *
            Polynomial.X ^ i := by
    rw [Work.SymQuot.DivOf.ChartPt.charpolyValue_def, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      chartPt_evalMap_eq d x hx h]
  have h2 : Polynomial.map (d.evalMap x h) (Work.SymQuot.DivOf.charpoly C n d.V b)
      = ∑ i ∈ Finset.range (n + 1),
          Polynomial.C (d.evalMap x h ((Work.SymQuot.DivOf.charpoly C n d.V b).coeff i)) *
            Polynomial.X ^ i :=
    localIdealAux_map_eq_sum_range_C_mul_X_pow (d.evalMap x h) (Work.SymQuot.DivOf.charpoly C n d.V b) n hdeg
  have h3 : Polynomial.map (d.evalMap x h) (Work.SymQuot.DivOf.charpoly C n d.V b)
      = ∏ m : Fin n, (Polynomial.X - Polynomial.C
          (d.evalMap x h (Work.SymQuot.DivOf.coordPullbackAt C n d.V m b))) := by
    rw [Work.SymQuot.DivOf.charpoly, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hmap : Polynomial.map (algebraMap F F') (d.charpolyValue b)
      = ∏ m : Fin n, (Polynomial.X - Polynomial.C
          (d.evalMap x h (Work.SymQuot.DivOf.coordPullbackAt C n d.V m b))) :=
    h1.trans (h2.symm.trans h3)
  have key1 : d.charpolyValue b = Polynomial.X ^ n ↔
      Polynomial.map (algebraMap F F') (d.charpolyValue b) = Polynomial.X ^ n := by
    constructor
    · intro hh
      rw [hh, Polynomial.map_pow, Polynomial.map_X]
    · intro hh
      refine Polynomial.map_injective (algebraMap F F') (algebraMap F F').injective ?_
      rw [hh, Polynomial.map_pow, Polynomial.map_X]
  rw [Work.SymQuot.DivOf.ChartPt.mem_localIdealSet, key1, hmap]
  exact (localIdealAux_prod_X_sub_C_eq_X_pow_iff (F := F') (n := n)
    (fun m => d.evalMap x h (Work.SymQuot.DivOf.coordPullbackAt C n d.V m b)))

end Work.SymQuot.DivOf
