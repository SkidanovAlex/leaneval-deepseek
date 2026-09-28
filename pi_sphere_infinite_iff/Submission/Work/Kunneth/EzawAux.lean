import Mathlib
import Submission.Work.Kunneth.EZAWHomotopy
import Submission.Work.Kunneth.ezaw_ind_nat
import Submission.Work.Kunneth.EZHom

/-!
# Toolkit for the second Eilenberg–Zilber homotopy

This file collects the elementary manipulations needed to run the acyclic-models recursion for
`ezMap ≫ awMap ≃ 𝟙` on `tChain X Y`:

* components of finite sums of chain maps (`Hom_finset_sum_f`), and the resulting element-level
  expansions of the alternating coface sums `phiSum`/`psiSum` (`phiSum_f_apply`, `psiSum_f_apply`)
  together with their square-zero and mixed commutation laws on elements;
* the degree-transport toolkit `dcast` (`dcast_sub`, `dcast_neg`, `dcast_trans`,
  `chainMap_dcast`: every chain map commutes with `dcast`);
* the universal element `Ugen p q N h` of the model `tMod p q` in an arbitrary degree `N` with
  `p + q = N`, and the level defect `EmS p q N h`; their comparison with `U`/`Em`
  (`Ugen_self`, `EmS_self`) and their compatibility with `dcast` (`Ugen_dcast`, `EmS_dcast`);
* the alternating-coface form of the reciprocity data: `phiTsum`, `psiTsum` and the defect
  `dfc2` in which the alternating sums of `phiT`/`psiT` are replaced by a single application of
  `phiSum`/`psiSum`, together with the identification `dfc_eq_dfc2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## 1. Components of sums of chain maps -/

/-- The `n`-th component of a chain map, as an additive homomorphism. -/
def compHom (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (C ⟶ D) →+ ((C.X n) ⟶ (D.X n)) where
  toFun f := f.f n
  map_zero' := HomologicalComplex.zero_f C D n
  map_add' f g := rfl

/-- Evaluation of a `ℤ`-linear map at a point, as an additive homomorphism. -/
def evalHom (M N : ModuleCat ℤ) (x : ↥M) : (M ⟶ N) →+ ↥N where
  toFun f := f.hom x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `n`-th component of a finite sum of chain maps is the sum of the components. -/
lemma Hom_finset_sum_f {ι : Type*} (s : Finset ι)
    (C D : ChainComplex (ModuleCat ℤ) ℕ) (F : ι → (C ⟶ D)) (n : ℕ) :
    (∑ i ∈ s, F i).f n = ∑ i ∈ s, (F i).f n :=
  map_sum (compHom C D n) F s

/-! ## 2. The degree-transport toolkit -/

lemma dcast_sub (p q : ℕ) {n m : ℕ} (h : n = m) (x y : ↥((tMod p q).X n)) :
    dcast p q h (x - y) = dcast p q h x - dcast p q h y := by
  subst h; rfl

lemma dcast_neg (p q : ℕ) {n m : ℕ} (h : n = m) (x : ↥((tMod p q).X n)) :
    dcast p q h (-x) = -dcast p q h x := by
  subst h; rfl

lemma dcast_trans (p q : ℕ) {a b c : ℕ} (h1 : b = c) (h2 : a = b) (x : ↥((tMod p q).X a)) :
    dcast p q h1 (dcast p q h2 x) = dcast p q (h2.trans h1) x := by
  subst h1; subst h2; rfl

/-- The degree transport is determined by the degrees: transporting `x` along one proof and
transporting an already transported element along another give the same result. -/
lemma dcast_congr2 (p q : ℕ) {a b c : ℕ} (hab : a = b) (hac : a = c) (hbc : b = c)
    (x : ↥((tMod p q).X a)) :
    dcast p q hac x = dcast p q hbc (dcast p q hab x) := by
  subst hab
  rw [dcast_congr p q (h := hac) (h' := hbc)]
  rfl

/-- A chain map commutes with the degree transport. -/
lemma chainMap_dcast {C C' : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ C') {n m : ℕ} (h : n = m)
    (x : ↥(C.X n)) :
    (f.f m).hom (cast (congrArg (fun k => ↥(C.X k)) h) x)
      = cast (congrArg (fun k => ↥(C'.X k)) h) ((f.f n).hom x) := by
  subst h; rfl

/-- A chain map between models commutes with the degree transport. -/
lemma dcast_chainMap (p q p' q' : ℕ) (f : tMod p q ⟶ tMod p' q') {n m : ℕ} (h : n = m)
    (x : ↥((tMod p q).X n)) :
    (f.f m).hom (dcast p q h x) = dcast p' q' h ((f.f n).hom x) :=
  chainMap_dcast f h x

/-- `tpLof` does not depend on the proof of the bidegree identity. -/
lemma tpLof_irrel (C D : ChainComplex (ModuleCat ℤ) ℕ) (n p q : ℕ) (h h' : p + q = n)
    (z : tpSummand C D p q) :
    tpLof C D n ⟨(p, q), h⟩ z = tpLof C D n ⟨(p, q), h'⟩ z := by
  rw [Subsingleton.elim h h']

/-! ## 3. The alternating coface sums on elements -/

/-- The value of `phiSum` on an element is the alternating sum of the cofaces. -/
lemma phiSum_f_apply (p q n : ℕ) (x : ↥((tMod p q).X n)) :
    (phiSum p q).f n x = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ((phiMod p q i).f n) x := by
  have h1 : (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • phiMod p q i).f n
      = (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ) • phiMod p q i).f n :
          (tMod p q).X n ⟶ (tMod (p + 1) q).X n) :=
    Hom_finset_sum_f Finset.univ (tMod p q) (tMod (p + 1) q)
      (fun i : Fin (p + 2) => (-1 : ℤ) ^ (i : ℕ) • phiMod p q i) n
  have h2 : (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ) • phiMod p q i).f n :
        (tMod p q).X n ⟶ (tMod (p + 1) q).X n).hom x
      = ∑ i : Fin (p + 2), (((-1 : ℤ) ^ (i : ℕ) • phiMod p q i).f n).hom x :=
    map_sum (evalHom ((tMod p q).X n) ((tMod (p + 1) q).X n) x)
      (fun i : Fin (p + 2) => ((-1 : ℤ) ^ (i : ℕ) • phiMod p q i).f n) Finset.univ
  rw [phiSum_eq, h1, h2]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show ((-1 : ℤ) ^ (i : ℕ) • phiMod p q i).f n
      = (-1 : ℤ) ^ (i : ℕ) • (phiMod p q i).f n from rfl]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]

/-- The value of `psiSum` on an element is the alternating sum of the cofaces. -/
lemma psiSum_f_apply (p q n : ℕ) (x : ↥((tMod p q).X n)) :
    (psiSum p q).f n x = ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • ((psiMod p q j).f n) x := by
  have h1 : (∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • psiMod p q j).f n
      = (∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ) • psiMod p q j).f n :
          (tMod p q).X n ⟶ (tMod p (q + 1)).X n) :=
    Hom_finset_sum_f Finset.univ (tMod p q) (tMod p (q + 1))
      (fun j : Fin (q + 2) => (-1 : ℤ) ^ (j : ℕ) • psiMod p q j) n
  have h2 : (∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ) • psiMod p q j).f n :
        (tMod p q).X n ⟶ (tMod p (q + 1)).X n).hom x
      = ∑ j : Fin (q + 2), (((-1 : ℤ) ^ (j : ℕ) • psiMod p q j).f n).hom x :=
    map_sum (evalHom ((tMod p q).X n) ((tMod p (q + 1)).X n) x)
      (fun j : Fin (q + 2) => ((-1 : ℤ) ^ (j : ℕ) • psiMod p q j).f n) Finset.univ
  rw [psiSum_eq, h1, h2]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show ((-1 : ℤ) ^ (j : ℕ) • psiMod p q j).f n
      = (-1 : ℤ) ^ (j : ℕ) • (psiMod p q j).f n from rfl]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]

/-- The square of the alternating coface sum vanishes, on elements. -/
lemma phiSum_comp_apply (p q n : ℕ) (x : ↥((tMod p q).X n)) :
    (phiSum (p + 1) q).f n ((phiSum p q).f n x) = 0 := by
  have h := congrArg (fun (φ : tMod p q ⟶ tMod ((p + 1) + 1) q) => (φ.f n).hom x)
    (phiSum_comp p q)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply] using h

/-- The square of the alternating coface sum vanishes, on elements. -/
lemma psiSum_comp_apply (p q n : ℕ) (x : ↥((tMod p q).X n)) :
    (psiSum p (q + 1)).f n ((psiSum p q).f n x) = 0 := by
  have h := congrArg (fun (φ : tMod p q ⟶ tMod p ((q + 1) + 1)) => (φ.f n).hom x)
    (psiSum_comp p q)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply] using h

/-- The two alternating coface sums commute, on elements. -/
lemma psiSum_phiSum_apply (p q n : ℕ) (x : ↥((tMod p q).X n)) :
    (phiSum p (q + 1)).f n ((psiSum p q).f n x)
      = (psiSum (p + 1) q).f n ((phiSum p q).f n x) := by
  have h := congrArg (fun (φ : tMod p q ⟶ tMod (p + 1) (q + 1)) => (φ.f n).hom x)
    (psiSum_phiSum p q)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-! ## 4. Naturality of `Ezaw` in both variables, on elements -/

lemma ezaw_ind_nat_apply {X X' Y Y' : SSet} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (x : ↥((tChain X Y).X n)) :
    ((Ezaw X' Y').f n).hom (((ind f g).f n).hom x)
      = ((ind f g).f n).hom (((Ezaw X Y).f n).hom x) := by
  have h := congrArg (fun (φ : tChain X Y ⟶ tChain X' Y') => (φ.f n).hom x) (ezaw_ind_nat f g)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-! ## 5. The universal element and the defect in an arbitrary degree -/

/-- The universal element `σ_p ⊗ τ_q` of the model `tMod p q`, placed in the degree `N`
(`p + q = N`). -/
noncomputable def Ugen (p q N : ℕ) (h : p + q = N) : ↥((tMod p q).X N) :=
  tpLof (sMod p) (sMod q) N ⟨(p, q), h⟩
    (genCh (SdS p) (univS p) ⊗ₜ[ℤ] genCh (SdS q) (univS q))

/-- **The defect in an arbitrary degree**: `(Ezaw - 1)` applied to the universal element placed in
degree `N`. -/
noncomputable def EmS (p q N : ℕ) (h : p + q = N) : ↥((tMod p q).X N) :=
  ((Ezaw (SdS p) (SdS q)).f N).hom (Ugen p q N h) - Ugen p q N h

lemma Ugen_self (p q : ℕ) : Ugen p q (p + q) rfl = U p q := rfl

lemma EmS_self (p q : ℕ) : EmS p q (p + q) rfl = Em p q := rfl

lemma Ugen_congr (p q N : ℕ) (h h' : p + q = N) : Ugen p q N h = Ugen p q N h' := by
  rw [Subsingleton.elim h h']

lemma EmS_congr (p q N : ℕ) (h h' : p + q = N) : EmS p q N h = EmS p q N h' := by
  rw [Subsingleton.elim h h']

/-- The universal element of an arbitrary degree is the transport of `U`. -/
lemma Ugen_dcast (p q N : ℕ) (e : p + q = N) (h : p + q = N) :
    dcast p q e (U p q) = Ugen p q N h := by
  subst e
  rw [dcast_rfl, ← Ugen_self p q]

/-- The defect of an arbitrary degree is the transport of `Em`. -/
lemma EmS_dcast (p q N : ℕ) (e : p + q = N) (h : p + q = N) :
    dcast p q e (Em p q) = EmS p q N h := by
  have h1 : dcast p q e (((Ezaw (SdS p) (SdS q)).f (p + q)).hom (U p q))
      = ((Ezaw (SdS p) (SdS q)).f N).hom (dcast p q e (U p q)) :=
    (chainMap_dcast (Ezaw (SdS p) (SdS q)) e (U p q)).symm
  have h2 : Em p q = ((Ezaw (SdS p) (SdS q)).f (p + q)).hom (U p q) - U p q := rfl
  rw [h2, dcast_sub, h1, Ugen_dcast p q N e h]
  rfl

/-! ## 5. Faces of the universal simplex -/

/-- The `i`-th face of the universal `(p+1)`-simplex is the image of the universal `p`-simplex
under the `i`-th coface. -/
lemma univS_delta (p : ℕ) (i : Fin (p + 2)) :
    (SSet.stdSimplex.obj ⦋p + 1⦌).map (SimplexCategory.δ i).op (univS (p + 1))
      = (SSet.stdSimplex.map (SimplexCategory.δ i)).app (Opposite.op ⦋p⦌) (univS p) := by
  have h1 : (SSet.stdSimplex.obj ⦋p + 1⦌).map (SimplexCategory.δ i).op (univS (p + 1))
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) :=
    EZHom.delta_U_fst' p i
  have h2 : (SSet.stdSimplex.map (SimplexCategory.δ i)).app (Opposite.op ⦋p⦌) (univS p)
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) :=
    EZHom.delta_U_fst p i
  rw [h1, h2]

/-- The `i`-th face of the universal `(p+1)`-simplex is the image of the universal `p`-simplex
under the `i`-th coface, on chains. -/
lemma genCh_delta_univS (p : ℕ) (i : Fin (p + 2)) :
    genCh (SdS (p + 1)) ((SdS (p + 1)).map (SimplexCategory.δ i).op (univS (p + 1)))
      = ((SSet.chainComplexMap (SSet.stdSimplex.map (SimplexCategory.δ i)) zz).f p).hom
          (genCh (SdS p) (univS p)) := by
  rw [univS_delta p i]
  exact (EZHom.genCh_chainComplexMap (SSet.stdSimplex.map (SimplexCategory.δ i)) (univS p)).symm

/-- The action of the first coface on the universal element. -/
lemma phiMod_Ugen (p q N : ℕ) (h : p + q = N) (i : Fin (p + 2)) :
    ((phiMod p q i).f N).hom (Ugen p q N h)
      = tpLof (sMod (p + 1)) (sMod q) N ⟨(p, q), h⟩
          (genCh (SdS (p + 1)) ((SdS (p + 1)).map (SimplexCategory.δ i).op (univS (p + 1)))
            ⊗ₜ[ℤ] genCh (SdS q) (univS q)) := by
  have h1 : Ugen p q N h = tpLof (sMod p) (sMod q) N ⟨(p, q), h⟩
      (genCh (SdS p) (univS p) ⊗ₜ[ℤ] genCh (SdS q) (univS q)) := rfl
  rw [h1, phiMod, ind, tpMap_tpLof, TensorProduct.map_tmul,
    ← genCh_delta_univS p i, chainComplexMap_id, HomologicalComplex.id_f]
  rfl

/-- The action of the second coface on the universal element. -/
lemma psiMod_Ugen (p q N : ℕ) (h : p + q = N) (j : Fin (q + 2)) :
    ((psiMod p q j).f N).hom (Ugen p q N h)
      = tpLof (sMod p) (sMod (q + 1)) N ⟨(p, q), h⟩
          (genCh (SdS p) (univS p)
            ⊗ₜ[ℤ] genCh (SdS (q + 1))
              ((SdS (q + 1)).map (SimplexCategory.δ j).op (univS (q + 1)))) := by
  have h1 : Ugen p q N h = tpLof (sMod p) (sMod q) N ⟨(p, q), h⟩
      (genCh (SdS p) (univS p) ⊗ₜ[ℤ] genCh (SdS q) (univS q)) := rfl
  rw [h1, psiMod, ind, tpMap_tpLof, TensorProduct.map_tmul,
    ← genCh_delta_univS q j, chainComplexMap_id, HomologicalComplex.id_f]
  rfl

/-- The differential of the universal element of an arbitrary degree is the Koszul
differential. -/
lemma d_Ugen (p q N : ℕ) (h : p + q = N + 1) :
    (tMod p q).d (N + 1) N (Ugen p q (N + 1) h)
      = tpD (sMod p) (sMod q) N (Ugen p q (N + 1) h) := by
  rw [tpC_d]
  rfl

end

end Work.Kunneth
