import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.SymQuot.DivOf.bcSec_secAlpha
import Submission.Work.SymQuot.DivOf.bcSec_secConst
import Submission.Work.SymQuot.DivOf.lift_mem_V

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open Work.CurveBasics

/-! ## Auxiliary lemmas for `genGenerator_map_eq` -/

/-- **Compatibility of `Polynomial.eval` with a ring homomorphism**: applying `Φ` to the value of a
polynomial `Q` at `A` is evaluating the image polynomial at `Φ A`. -/
lemma map_eval_eq_eval_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (Φ : R →+* S) (A : R) (Q : Polynomial R) :
    Φ (Polynomial.eval A Q) = Polynomial.eval (Φ A) (Polynomial.map Φ Q) :=
  (Polynomial.eval₂_hom (p := Q) Φ A).symm.trans
    (Polynomial.eval_map (p := Q) Φ (Φ A)).symm

/-- **`MvPolynomial.map` of a composition of ring homs** (the two-variable version, with the index
type made explicit so that it can be used as a rewrite rule). -/
lemma mvPolynomial_map_comp {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    {σ : Type*} (f : R →+* S) (g : S →+* T) :
    (MvPolynomial.map (σ := σ) g).comp (MvPolynomial.map (σ := σ) f)
      = MvPolynomial.map (σ := σ) (g.comp f) :=
  RingHom.ext fun q => MvPolynomial.map_map f g q

/-- `MvPolynomial.map` written as a sum over the support. -/
lemma mvPolynomial_map_eq_sum_support {R S : Type*} [CommSemiring R] [CommSemiring S]
    {σ : Type*} (f : R →+* S) (q : MvPolynomial σ R) :
    MvPolynomial.map f q = ∑ α ∈ q.support, MvPolynomial.monomial α (f (q.coeff α)) := by
  conv_lhs => rw [MvPolynomial.as_sum (p := q)]
  rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [MvPolynomial.map_monomial]

/-- **The coefficients of the generic characteristic polynomial evaluated at a lift.**

Applying the base change `F → F''` to `d.genCharpolyValue b` is the same as evaluating the generic
characteristic polynomial `genCharpoly C n d.V b` coefficientwise by the evaluation map
`d.evalMap x _` of the lift `x`.  (Each coefficient of `genCharpoly` is `S_n`-invariant, so its
value at the chart point `φ` and its evaluation at the lift agree by `chartPt_evalMap_eq`.) -/
lemma map_algebraMap_genCharpolyValue_eq {K : Type u} [Field K] {C : Curve K} {n : ℕ} [NeZero n]
    [Work.SymQuot.CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F] {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) {F'' : Type u} [Field F''] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F'') p)
    {r : ℕ} (b : Fin r → C.left.presheaf.obj (Opposite.op d.V)) :
    Polynomial.map (MvPolynomial.map (algebraMap F F'')) (d.genCharpolyValue b) =
      Polynomial.map (MvPolynomial.map (d.evalMap x (lift_mem_V d x hx)))
        (genCharpoly C n d.V b) := by
  set h := lift_mem_V d x hx with hh
  have hdegG : (genCharpoly C n d.V b).natDegree ≤ n := by
    rw [genCharpoly]
    refine le_trans (Polynomial.natDegree_prod_le Finset.univ
      (fun m : Fin n => Polynomial.X - Polynomial.C (∑ i : Fin r,
        MvPolynomial.C (coordPullbackAt C n d.V m (b i)) * MvPolynomial.X i))) ?_
    refine le_trans (Finset.sum_le_sum (f := fun m : Fin n => (Polynomial.X - Polynomial.C
        (∑ i : Fin r, MvPolynomial.C (coordPullbackAt C n d.V m (b i)) *
          MvPolynomial.X i)).natDegree) (g := fun _ : Fin n => (1:ℕ)) fun m _ =>
        Polynomial.natDegree_X_sub_C_le _) ?_
    simp
  have hmapG : Polynomial.map (MvPolynomial.map (d.evalMap x h)) (genCharpoly C n d.V b)
      = ∑ k ∈ Finset.range (n+1), Polynomial.C (MvPolynomial.map (d.evalMap x h)
          ((genCharpoly C n d.V b).coeff k)) * Polynomial.X^k :=
    localIdealAux_map_eq_sum_range_C_mul_X_pow _ _ n hdegG
  have hterm : ∀ k, MvPolynomial.map (algebraMap F F'')
        (∑ α ∈ ((genCharpoly C n d.V b).coeff k).support, MvPolynomial.monomial α
          (d.φ ⟨((genCharpoly C n d.V b).coeff k).coeff α,
            genCharpoly_coeff_coeff_mem d.V b k α⟩))
      = MvPolynomial.map (d.evalMap x h) ((genCharpoly C n d.V b).coeff k) := by
    intro k
    conv_rhs => rw [mvPolynomial_map_eq_sum_support]
    conv_lhs => rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.map_monomial]
    congr 1
    exact chartPt_evalMap_eq d x hx h ⟨_, genCharpoly_coeff_coeff_mem d.V b k α⟩
  rw [hmapG]
  rw [ChartPt.genCharpolyValue, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hterm k]

/-- **The generic characteristic polynomial evaluated at a lift** is the product of the linear
factors `T - b_i(x_m)`, in the multi-variable polynomial ring over `F''`. -/
lemma map_evalMap_genCharpoly_eq {K : Type u} [Field K] {C : Curve K} {n : ℕ} [NeZero n]
    [Work.SymQuot.CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F] {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) {F'' : Type u} [Field F''] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F'') p)
    {r : ℕ} (b : Fin r → C.left.presheaf.obj (Opposite.op d.V)) :
    Polynomial.map (MvPolynomial.map (d.evalMap x (lift_mem_V d x hx))) (genCharpoly C n d.V b)
    = ∏ m : Fin n, (Polynomial.X - Polynomial.C (∑ i : Fin r,
        MvPolynomial.C (valAtLift d x (lift_mem_V d x hx) m (b i)) * MvPolynomial.X i)) := by
  rw [genCharpoly, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 1
  simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, valAtLift_apply,
    coordPullbackAt_apply]

theorem genGenerator_map_eq {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) {F'' : Type u} [Field F''] [Algebra K F'']
    [Algebra F F''] [IsScalarTower K F F''] (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F'') p)
    {r : ℕ} (b : Fin r → C.left.presheaf.obj (Opposite.op d.V)) :
    MvPolynomial.map (bcSec (C := C) F F'' d.V) (d.genGenerator b) =
      ∏ m : Fin n, ∑ i : Fin r,
        MvPolynomial.C (secAlpha C F'' d.V (b i) - secConst C F'' d.V
          (valAtLift d x (lift_mem_V d x hx) m (b i))) * MvPolynomial.X i := by
  have key_cw := map_algebraMap_genCharpolyValue_eq d x hx b
  have hG := map_evalMap_genCharpoly_eq d x hx b
  have hbsf : (bcSec (C := C) F F'' d.V).comp (secConst C F d.V) =
      (secConst C F'' d.V).comp (algebraMap F F'') :=
    RingHom.ext fun c => bcSec_secConst (C := C) F F'' d.V c
  have hA : MvPolynomial.map (bcSec (C := C) F F'' d.V)
      (∑ i : Fin r, MvPolynomial.C (secAlpha C F d.V (b i)) * MvPolynomial.X i)
      = ∑ i : Fin r, MvPolynomial.C (secAlpha C F'' d.V (b i)) * MvPolynomial.X i := by
    simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, bcSec_secAlpha]
  have hGG : Polynomial.map (MvPolynomial.map (secConst C F'' d.V))
        (∏ m : Fin n, (Polynomial.X - Polynomial.C (∑ i : Fin r,
          MvPolynomial.C (valAtLift d x (lift_mem_V d x hx) m (b i)) * MvPolynomial.X i)))
      = ∏ m : Fin n, (Polynomial.X - Polynomial.C (∑ i : Fin r,
          MvPolynomial.C (secConst C F'' d.V
            (valAtLift d x (lift_mem_V d x hx) m (b i))) * MvPolynomial.X i)) := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 1
    simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [ChartPt.genGenerator, Polynomial.eval₂_eq_eval_map, map_eval_eq_eval_map, Polynomial.map_map]
  rw [mvPolynomial_map_comp (secConst C F d.V) (bcSec (C := C) F F'' d.V)]
  rw [hbsf]
  rw [← mvPolynomial_map_comp (algebraMap F F'') (secConst C F'' d.V)]
  rw [← Polynomial.map_map, key_cw, hG, hGG, hA, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_mul, ← MvPolynomial.C_sub]

end Work.SymQuot.DivOf
