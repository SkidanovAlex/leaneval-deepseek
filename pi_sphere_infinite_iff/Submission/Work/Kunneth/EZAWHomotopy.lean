import Mathlib
import Submission.Work.Kunneth.EZAWTensor
import Submission.Work.Kunneth.EZAWDefs

/-!
# The Eilenberg–Zilber homotopy `ezMap ≫ awMap ≃ 𝟙` (the tensor direction)

This file carries out the acyclic-models construction of a chain homotopy between the composite
`ezMap ≫ awMap` on `C_*(X) ⊗_ℤ C_*(Y)` and the identity.  The models are the pairs
`(Δ[p], Δ[q])`, with `tMod p q = C_*(Δ[p]) ⊗_ℤ C_*(Δ[q])` and universal element `U p q`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## 1. Singular chains of simplicial maps -/

lemma chainComplexMap_id (X : SSet) : SSet.chainComplexMap (𝟙 X) zz = 𝟙 (sChain X) :=
  CategoryTheory.Functor.map_id ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj zz) X

lemma chainComplexMap_comp {A B D : SSet} (φ : A ⟶ B) (ψ : B ⟶ D) :
    SSet.chainComplexMap (φ ≫ ψ) zz
      = SSet.chainComplexMap φ zz ≫ SSet.chainComplexMap ψ zz :=
  CategoryTheory.Functor.map_comp ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj zz) φ ψ

/-! ## 2. The two cosimplicial directions of the models -/

/-- The functor `X ↦ C_*(X) ⊗_ℤ C_*(Δ[q])`. -/
def Gfun (q : ℕ) : SSet ⥤ ChainComplex (ModuleCat ℤ) ℕ where
  obj X := tpC (sChain X) (sMod q)
  map := fun {_ _} f => tpMap (sChain _) (sChain _) (sMod q) (sMod q)
    (SSet.chainComplexMap f zz) (𝟙 (sMod q))
  map_id := fun X => by
    rw [chainComplexMap_id]
    exact tpMap_id (sChain X) (sMod q)
  map_comp := fun {_ _ _} f g => by
    rw [chainComplexMap_comp]
    exact (tpMap_comp (sChain _) (sChain _) (sChain _) (sMod q) (sMod q) (sMod q)
      (SSet.chainComplexMap f zz) (𝟙 (sMod q)) (SSet.chainComplexMap g zz) (𝟙 (sMod q))).symm

/-- The functor `Y ↦ C_*(Δ[p]) ⊗_ℤ C_*(Y)`. -/
def Hfun (p : ℕ) : SSet ⥤ ChainComplex (ModuleCat ℤ) ℕ where
  obj Y := tpC (sMod p) (sChain Y)
  map := fun {_ _} g => tpMap (sMod p) (sMod p) (sChain _) (sChain _)
    (𝟙 (sMod p)) (SSet.chainComplexMap g zz)
  map_id := fun Y => by
    rw [chainComplexMap_id]
    exact tpMap_id (sMod p) (sChain Y)
  map_comp := fun {_ _ _} f g => by
    rw [chainComplexMap_comp]
    exact (tpMap_comp (sMod p) (sMod p) (sMod p) (sChain _) (sChain _) (sChain _)
      (𝟙 (sMod p)) (SSet.chainComplexMap f zz) (𝟙 (sMod p)) (SSet.chainComplexMap g zz)).symm

/-- The cosimplicial object `p ↦ tMod p q` in the first variable. -/
def phiCos (q : ℕ) : CosimplicialObject (ChainComplex (ModuleCat ℤ) ℕ) :=
  SSet.stdSimplex ⋙ Gfun q

/-- The cosimplicial object `q ↦ tMod p q` in the second variable. -/
def psiCos (p : ℕ) : CosimplicialObject (ChainComplex (ModuleCat ℤ) ℕ) :=
  SSet.stdSimplex ⋙ Hfun p

/-- The cofaces of `phiCos` are the model cofaces `phiMod`. -/
lemma phiCos_delta (p q : ℕ) (i : Fin (p + 2)) :
    (phiCos q).δ i = phiMod p q i := by
  rw [phiMod, ind]
  simp only [phiCos, Gfun, CategoryTheory.Functor.comp_map, CosimplicialObject.δ]
  rw [chainComplexMap_id]

/-- The cofaces of `psiCos` are the model cofaces `psiMod`. -/
lemma psiCos_delta (p q : ℕ) (j : Fin (q + 2)) :
    (psiCos p).δ j = psiMod p q j := by
  rw [psiMod, ind]
  simp only [psiCos, Hfun, CategoryTheory.Functor.comp_map, CosimplicialObject.δ]
  rw [chainComplexMap_id]

/-- The alternating sum of the cofaces of `tMod - q` in the first variable:
`tMod p q ⟶ tMod (p+1) q`. -/
noncomputable def phiSum (p q : ℕ) : tMod p q ⟶ tMod (p + 1) q :=
  AlternatingCofaceMapComplex.objD (phiCos q) p

/-- The alternating sum of the cofaces of `tMod p -` in the second variable:
`tMod p q ⟶ tMod p (q+1)`. -/
noncomputable def psiSum (p q : ℕ) : tMod p q ⟶ tMod p (q + 1) :=
  AlternatingCofaceMapComplex.objD (psiCos p) q

/-- `phiSum` is the alternating sum of the cofaces `phiMod`. -/
lemma phiSum_eq (p q : ℕ) :
    phiSum p q = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • phiMod p q i := by
  rw [phiSum, AlternatingCofaceMapComplex.objD]
  exact Finset.sum_congr rfl (fun i _ => by rw [phiCos_delta])

/-- `psiSum` is the alternating sum of the cofaces `psiMod`. -/
lemma psiSum_eq (p q : ℕ) :
    psiSum p q = ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • psiMod p q j := by
  rw [psiSum, AlternatingCofaceMapComplex.objD]
  exact Finset.sum_congr rfl (fun j _ => by rw [psiCos_delta])

/-- The square of the alternating coface sum in the first variable vanishes. -/
theorem phiSum_comp (p q : ℕ) : phiSum p q ≫ phiSum (p + 1) q = 0 :=
  AlternatingCofaceMapComplex.d_squared (phiCos q) p

/-- The square of the alternating coface sum in the second variable vanishes. -/
theorem psiSum_comp (p q : ℕ) : psiSum p q ≫ psiSum p (q + 1) = 0 :=
  AlternatingCofaceMapComplex.d_squared (psiCos p) q

/-- The two coface sums commute. -/
lemma psiMod_phiMod (p q : ℕ) (i : Fin (p + 2)) (j : Fin (q + 2)) :
    psiMod p q j ≫ phiMod p (q + 1) i = phiMod p q i ≫ psiMod (p + 1) q j := by
  rw [psiMod, phiMod, phiMod, psiMod, ind, ind, ind, ind]
  rw [tpMap_comp, tpMap_comp]
  simp only [chainComplexMap_id, Category.id_comp, Category.comp_id]

/-- The two coface sums commute. -/
lemma psiSum_phiSum (p q : ℕ) :
    psiSum p q ≫ phiSum p (q + 1) = phiSum p q ≫ psiSum (p + 1) q := by
  rw [psiSum_eq, phiSum_eq, phiSum_eq, psiSum_eq]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [psiMod_phiMod p q j i, mul_comm]

/-! ## 3. The degree transports and the recursion data -/

/-- Transport of elements of a model along an equality of degrees. -/
def dcast (p q : ℕ) {n m : ℕ} (h : n = m) : ↥((tMod p q).X n) → ↥((tMod p q).X m) :=
  fun x => cast (congrArg (fun k => ↥((tMod p q).X k)) h) x

lemma dcast_rfl (p q n : ℕ) (x : ↥((tMod p q).X n)) : dcast p q rfl x = x := rfl

lemma dcast_add (p q : ℕ) {n m : ℕ} (h : n = m) (x y : ↥((tMod p q).X n)) :
    dcast p q h (x + y) = dcast p q h x + dcast p q h y := by
  subst h; rfl

lemma dcast_smul (p q : ℕ) {n m : ℕ} (h : n = m) (c : ℤ) (x : ↥((tMod p q).X n)) :
    dcast p q h (c • x) = c • dcast p q h x := by
  subst h; rfl

lemma dcast_zero (p q : ℕ) {n m : ℕ} (h : n = m) :
    dcast p q h (0 : ↥((tMod p q).X n)) = 0 := by
  subst h; rfl

lemma dcast_sum (p q : ℕ) {n m : ℕ} (h : n = m) {ι : Type*} (s : Finset ι)
    (f : ι → ↥((tMod p q).X n)) :
    dcast p q h (∑ i ∈ s, f i) = ∑ i ∈ s, dcast p q h (f i) := by
  subst h; rfl

/-- The degree transport does not depend on the proof of the degree equality. -/
lemma dcast_congr (p q : ℕ) {n m : ℕ} {h h' : n = m} (x : ↥((tMod p q).X n)) :
    dcast p q h x = dcast p q h' x := by
  rw [Subsingleton.elim h h']

/-- The differential commutes with the degree transport. -/
lemma d_dcast (p q : ℕ) {n m : ℕ} (h : n = m) (x : ↥((tMod p q).X n)) :
    (tMod p q).d m (m - 1) (dcast p q h x)
      = dcast p q (congrArg (fun k => k - 1) h) ((tMod p q).d n (n - 1) x) := by
  subst h; rfl

/-- A chain map commutes with the degree transport. -/
lemma phiMod_dcast (p q : ℕ) (i : Fin (p + 2)) {n m : ℕ} (h : n = m)
    (x : ↥((tMod p q).X n)) :
    ((phiMod p q i).f m).hom (dcast p q h x)
      = dcast (p + 1) q h (((phiMod p q i).f n).hom x) := by
  subst h; rfl

/-- A chain map commutes with the degree transport. -/
lemma psiMod_dcast (p q : ℕ) (j : Fin (q + 2)) {n m : ℕ} (h : n = m)
    (x : ↥((tMod p q).X n)) :
    ((psiMod p q j).f m).hom (dcast p q h x)
      = dcast p (q + 1) h (((psiMod p q j).f n).hom x) := by
  subst h; rfl

/-- The `i`-th φ-term of the recursion: the image of `W p q` under the `i`-th coface in the first
variable, placed in degree `(p+1)+q` of the model `(p+1,q)`. -/
noncomputable def phiT (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (i : Fin (p + 2)) : ↥((tMod (p + 1) q).X ((p + 1) + q)) :=
  dcast (p + 1) q (Nat.add_right_comm p 1 q).symm
    (((phiMod p q i).f (p + q + 1)).hom (W p q))

/-- The `j`-th ψ-term of the recursion: the image of `W p q` under the `j`-th coface in the second
variable, placed in degree `p+(q+1)` of the model `(p,q+1)`. -/
noncomputable def psiT (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (j : Fin (q + 2)) : ↥((tMod p (q + 1)).X (p + (q + 1))) :=
  ((psiMod p q j).f (p + q + 1)).hom (W p q)

/-- **The defect of the recursion**: the element that the acyclic-models chain `W p q` must fill,
expressed in terms of the values of `W` on the models of total degree `p+q-1`. -/
noncomputable def dfc (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    ↥((tMod p q).X (p + q)) :=
  match p, q with
  | 0, 0 => Em 0 0
  | 0, q + 1 => Em 0 (q + 1) - ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • psiT W 0 q j
  | p + 1, 0 => Em (p + 1) 0 - ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • phiT W p 0 i
  | p + 1, q + 1 =>
      Em (p + 1) (q + 1) - ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • phiT W p (q + 1) i
        - (-1 : ℤ) ^ (p + 1) • ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • psiT W (p + 1) q j

end

end Work.Kunneth
