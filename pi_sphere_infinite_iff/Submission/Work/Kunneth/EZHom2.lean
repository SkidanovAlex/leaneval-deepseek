import Mathlib
import Submission.Work.Kunneth.EZHom

/-!
# Eilenberg–Zilber: `awMap ≫ ezMap` is chain homotopic to the identity

Second half of the argument in `Submission/Work/Kunneth/EZHom.lean`: the naturality of
`ezaw = awHom ≫ ezHom` on generators, the classification of simplices of `X ⊗ Y` by maps
`Δ[n] ⊗ Δ[n] ⟶ X ⊗ Y`, and the acyclic-models construction of the chain homotopy.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open scoped MonoidalCategory Simplicial TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

namespace EZHom

/-! ## 1. Naturality of `ezaw` on generators -/

/-- The first projection of the value of a product of simplicial maps. -/
lemma tensorHom_fst {X Y X' Y' : SSet} (f : X ⟶ X') (g : Y ⟶ Y') {n : ℕ}
    (z : (sProd X Y) _⦋n⦌) :
    (((MonoidalCategoryStruct.tensorHom f g).app (Opposite.op ⦋n⦌)) z).1
      = (f.app (Opposite.op ⦋n⦌)) z.1 :=
  congrArg Prod.fst (SSet.tensorHom_app_apply f g z)

/-- The second projection of the value of a product of simplicial maps. -/
lemma tensorHom_snd {X Y X' Y' : SSet} (f : X ⟶ X') (g : Y ⟶ Y') {n : ℕ}
    (z : (sProd X Y) _⦋n⦌) :
    (((MonoidalCategoryStruct.tensorHom f g).app (Opposite.op ⦋n⦌)) z).2
      = (g.app (Opposite.op ⦋n⦌)) z.2 :=
  congrArg Prod.snd (SSet.tensorHom_app_apply f g z)

/-- The product of two `ψ`-pullbacks is taken to the two pullbacks of the images. -/
lemma tensorHom_map_op {X Y X' Y' : SSet} (f : X ⟶ X') (g : Y ⟶ Y') {p q : ℕ}
    (ψ : ⦋p+q⦌ ⟶ ⦋p⦌) (χ : ⦋p+q⦌ ⟶ ⦋q⦌) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    ((MonoidalCategoryStruct.tensorHom f g).app (Opposite.op ⦋p+q⦌))
        (show (sProd X Y) _⦋p+q⦌ from (X.map ψ.op σ, Y.map χ.op τ))
      = (show (sProd X' Y') _⦋p+q⦌ from
          (X'.map ψ.op (f.app (Opposite.op ⦋p⦌) σ),
           Y'.map χ.op (g.app (Opposite.op ⦋q⦌) τ))) := by
  refine Prod.ext ?_ ?_
  · show (((MonoidalCategoryStruct.tensorHom f g).app (Opposite.op ⦋p+q⦌))
        (show (sProd X Y) _⦋p+q⦌ from (X.map ψ.op σ, Y.map χ.op τ))).1 = _
    rw [tensorHom_fst f g (show (sProd X Y) _⦋p+q⦌ from (X.map ψ.op σ, Y.map χ.op τ))]
    rw [← ConcreteCategory.comp_apply, f.naturality ψ.op, ConcreteCategory.comp_apply]
  · show (((MonoidalCategoryStruct.tensorHom f g).app (Opposite.op ⦋p+q⦌))
        (show (sProd X Y) _⦋p+q⦌ from (X.map ψ.op σ, Y.map χ.op τ))).2 = _
    rw [tensorHom_snd f g (show (sProd X Y) _⦋p+q⦌ from (X.map ψ.op σ, Y.map χ.op τ))]
    rw [← ConcreteCategory.comp_apply, g.naturality χ.op, ConcreteCategory.comp_apply]

/-- Naturality of `ezaw = awHom ≫ ezHom` on generators. -/
theorem ezaw_nat_gen (X Y X' Y' : SSet) (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (z : (sProd X Y) _⦋n⦌) :
    (SSet.chainComplexMap (MonoidalCategoryStruct.tensorHom f g) zz).f n
        (ezaw X Y n (genCh (sProd X Y) z))
      = ezaw X' Y' n (genCh (sProd X' Y')
          ((MonoidalCategoryStruct.tensorHom f g).app (Opposite.op (SimplexCategory.mk n)) z)) := by
  rw [ezaw_gen X Y n z, ezaw_gen X' Y' n
    ((MonoidalCategoryStruct.tensorHom f g).app (Opposite.op (SimplexCategory.mk n)) z)]
  refine ((map_sum ((SSet.chainComplexMap (MonoidalCategoryStruct.tensorHom f g) zz).f n).hom
    _ Finset.univ)).trans ?_
  refine Finset.sum_congr rfl (fun p _ => ?_)
  refine ((map_sum ((SSet.chainComplexMap (MonoidalCategoryStruct.tensorHom f g) zz).f n).hom
    _ Finset.univ)).trans ?_
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [map_zsmul]
  congr 1
  rw [genCh_chainComplexMap]
  congr 1
  rw [tensorHom_cast]
  congr 1
  rw [tensorHom_map_op f g (Work.Cohomology.Crux33.aHom S.1 S.2)
    (Work.Cohomology.Crux33.bHom S.1 S.2) (Work.Cohomology.frontFace X p.val n (by omega) z.1)
    (backFaceLE Y (n - p.val) n (by omega) z.2)]
  congr 1
  · refine Prod.ext ?_ ?_
    · rw [tensorHom_fst f g z]
      rw [(frontFace_nat f (show p.val ≤ n by omega) z.1).symm]
    · rw [tensorHom_snd f g z]
      rw [(backFaceLE_nat g (show n - p.val ≤ n by omega) z.2).symm]
  · exact (by omega : ↑p + (n - ↑p) = n)

/-! ## 2. Classifying the simplices of `X ⊗ Y` -/

/-- The coface of `Zc` is the tensor product of the cofaces of the standard simplex. -/
lemma Zc_delta (n : ℕ) (i : Fin (n+2)) :
    CosimplicialObject.δ Zc i
      = MonoidalCategoryStruct.tensorHom (SSet.stdSimplex.map (SimplexCategory.δ i))
          (SSet.stdSimplex.map (SimplexCategory.δ i)) := rfl

/-- The value of `yonedaEquiv.symm` at the universal simplex. -/
lemma yonedaEquiv_symm_app_univ {X : SSet} (n : ℕ) (x : X _⦋n⦌) :
    (SSet.yonedaEquiv.symm x).app (Opposite.op ⦋n⦌)
        (show (SSet.stdSimplex.obj ⦋n⦌) _⦋n⦌ from SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) = x := by
  simpa using SSet.yonedaEquiv_symm_app_objEquiv_symm (X := X) (n := ⦋n⦌) x (𝟙 ⦋n⦌)

/-- A simplex of `X ⊗ Y` determines a map `Δ[n] ⊗ Δ[n] ⟶ X ⊗ Y`. -/
noncomputable def classify (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n⦌) : Zm n ⟶ sProd X Y :=
  MonoidalCategoryStruct.tensorHom
    ((SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).symm z.1)
    ((SSet.yonedaEquiv (X := Y) (n := ⦋n⦌)).symm z.2)

/-- `classify` recovers the simplex it was built from. -/
lemma classify_U (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n⦌) :
    (classify X Y n z).app (Opposite.op ⦋n⦌) (U n) = z := by
  refine (SSet.tensorHom_app_apply
    ((SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).symm z.1)
    ((SSet.yonedaEquiv (X := Y) (n := ⦋n⦌)).symm z.2) (U n)).trans ?_
  refine Prod.ext ?_ ?_
  · exact yonedaEquiv_symm_app_univ n z.1
  · exact yonedaEquiv_symm_app_univ n z.2

/-- The first component of the coface of the universal simplex. -/
lemma delta_U_fst (j : ℕ) (i : Fin (j+2)) :
    (SSet.stdSimplex.map (SimplexCategory.δ i)).app (Opposite.op ⦋j⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋j⦌))
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) := by
  simpa using (SSet.stdSimplex.objEquiv_symm_comp (n := ⦋j⦌) (n' := ⦋j+1⦌)
    (m := Opposite.op ⦋j⦌) (f := 𝟙 ⦋j⦌) (g := SimplexCategory.δ i)).symm

/-- The `i`-th face of the universal `(j+1)`-simplex. -/
lemma delta_U_fst' (j : ℕ) (i : Fin (j+2)) :
    (SSet.stdSimplex.obj ⦋j+1⦌).map (SimplexCategory.δ i).op
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋j+1⦌))
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) := by
  simpa [Category.comp_id] using
    (SSet.stdSimplex.map_objEquiv_symm (n := ⦋j+1⦌) (m := Opposite.op ⦋j+1⦌)
      (m' := Opposite.op ⦋j⦌) (f := 𝟙 ⦋j+1⦌) (g := (SimplexCategory.δ i).op))

/-- The faces of the universal simplex agree with the cofaces of `Zc`. -/
lemma delta_U (j : ℕ) (i : Fin (j+2)) :
    (Zc.δ i).app (Opposite.op ⦋j⦌) (U j)
      = (Zm (j+1)).δ i (U (j+1)) := by
  have hL : (MonoidalCategoryStruct.tensorHom (SSet.stdSimplex.map (SimplexCategory.δ i))
        (SSet.stdSimplex.map (SimplexCategory.δ i))).app
        (Opposite.op ⦋j⦌) (U j)
      = (show (SSet.stdSimplex.obj ⦋j+1⦌) _⦋j⦌ from
            SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i),
         show (SSet.stdSimplex.obj ⦋j+1⦌) _⦋j⦌ from
            SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := by
    rw [show (MonoidalCategoryStruct.tensorHom (SSet.stdSimplex.map (SimplexCategory.δ i))
          (SSet.stdSimplex.map (SimplexCategory.δ i))).app
          (Opposite.op ⦋j⦌) (U j)
        = ((SSet.stdSimplex.map (SimplexCategory.δ i)).app (Opposite.op ⦋j⦌) (U j).1,
           (SSet.stdSimplex.map (SimplexCategory.δ i)).app (Opposite.op ⦋j⦌) (U j).2) from
        SSet.tensorHom_app_apply _ _ (U j)]
    have h1 : (SSet.stdSimplex.map (SimplexCategory.δ i)).app (Opposite.op ⦋j⦌) (U j).1
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) := by
      rw [show (U j).1 = (show (SSet.stdSimplex.obj ⦋j⦌) _⦋j⦌ from
          SSet.stdSimplex.objEquiv.symm (𝟙 ⦋j⦌)) from rfl]
      exact delta_U_fst j i
    have h2 : (SSet.stdSimplex.map (SimplexCategory.δ i)).app (Opposite.op ⦋j⦌) (U j).2
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) := by
      rw [show (U j).2 = (show (SSet.stdSimplex.obj ⦋j⦌) _⦋j⦌ from
          SSet.stdSimplex.objEquiv.symm (𝟙 ⦋j⦌)) from rfl]
      exact delta_U_fst j i
    rw [h1, h2]
  have hR : (Zm (j+1)).δ i (U (j+1))
      = (show (SSet.stdSimplex.obj ⦋j+1⦌) _⦋j⦌ from
            SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i),
         show (SSet.stdSimplex.obj ⦋j+1⦌) _⦋j⦌ from
            SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := by
    rw [show (Zm (j+1)).δ i (U (j+1))
        = ((SSet.stdSimplex.obj ⦋j+1⦌).map (SimplexCategory.δ i).op (U (j+1)).1,
           (SSet.stdSimplex.obj ⦋j+1⦌).map (SimplexCategory.δ i).op (U (j+1)).2) from
        Work.Kunneth.prod_delta (SSet.stdSimplex.obj ⦋j+1⦌) (SSet.stdSimplex.obj ⦋j+1⦌)
          j i (U (j+1))]
    have h1 : (SSet.stdSimplex.obj ⦋j+1⦌).map (SimplexCategory.δ i).op (U (j+1)).1
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) := by
      rw [show (U (j+1)).1 = (show (SSet.stdSimplex.obj ⦋j+1⦌) _⦋j+1⦌ from
          SSet.stdSimplex.objEquiv.symm (𝟙 ⦋j+1⦌)) from rfl]
      exact delta_U_fst' j i
    have h2 : (SSet.stdSimplex.obj ⦋j+1⦌).map (SimplexCategory.δ i).op (U (j+1)).2
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) := by
      rw [show (U (j+1)).2 = (show (SSet.stdSimplex.obj ⦋j+1⦌) _⦋j+1⦌ from
          SSet.stdSimplex.objEquiv.symm (𝟙 ⦋j+1⦌)) from rfl]
      exact delta_U_fst' j i
    rw [h1, h2]
  rw [Zc_delta]
  exact hL.trans hR.symm

/-- `classify` is compatible with faces. -/
lemma classify_delta (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n+1⦌) (i : Fin (n+2)) :
    classify X Y n ((sProd X Y).δ i z) = Zc.δ i ≫ classify X Y (n+1) z := by
  rw [classify, classify, Zc_delta, MonoidalCategory.tensorHom_comp_tensorHom]
  rw [Work.Kunneth.prod_delta X Y n i z]
  congr 1
  · exact (SSet.yonedaEquiv_symm_naturality_left (X := X) (f := SimplexCategory.δ i)
      (g := z.1)).symm
  · exact (SSet.yonedaEquiv_symm_naturality_left (X := Y) (f := SimplexCategory.δ i)
      (g := z.2)).symm

/-! ## 3. The acyclic-models data -/

/-- The standard `n`-simplex. -/
abbrev Sd (n : ℕ) : SSet := SSet.stdSimplex.obj ⦋n⦌

/-- The composite `awMap ≫ ezMap` on the `n`-th model. -/
noncomputable def Fmap (n : ℕ) : sChain (Zm n) ⟶ sChain (Zm n) :=
  awMap (Sd n) (Sd n) ≫ ezMap (Sd n) (Sd n)

/-- The degreewise value of `Fmap`. -/
lemma Fmap_f_hom (n k : ℕ) : ((Fmap n).f k).hom = ezaw (Sd n) (Sd n) k := by
  rw [Fmap, HomologicalComplex.comp_f, awMap_f, ezMap_f]
  rfl

/-- The universal chain of the `n`-th model. -/
noncomputable def bigU (n : ℕ) : ↥((sChain (Zm n)).X n) :=
  genCh (sProd (Sd n) (Sd n)) (U n)

/-- The deviation of `awMap ≫ ezMap` from the identity on the universal chain. -/
noncomputable def E (n : ℕ) : ↥((sChain (Zm n)).X n) :=
  ((Fmap n).f n).hom (bigU n) - bigU n

/-- In degree zero the deviation vanishes. -/
lemma E_zero : E 0 = 0 := by
  have h : ((Fmap 0).f 0).hom (bigU 0) = bigU 0 := by
    rw [Fmap_f_hom]
    exact ezaw_gen_zero (Sd 0) (Sd 0) (U 0)
  rw [E, h, sub_self]

lemma E_def (n : ℕ) : E n = ((Fmap n).f n).hom (bigU n) - bigU n := rfl

/-- The alternating sum of the coface maps `Zc.δ i`, on chains of degree `r`. -/
noncomputable def fsum (m r : ℕ) :
    ((sChain (Zm m)).X r) ⟶ ((sChain (Zm (m+1))).X r) :=
  ∑ i : Fin (m+2), ((-1 : ℤ) ^ (i : ℕ)) • (SSet.chainComplexMap (Zc.δ i) zz).f r

/-- The coface of `Zc` on chain complexes. -/
lemma ZcR_delta (r m : ℕ) (i : Fin (m+2)) :
    CosimplicialObject.δ (ZcR r) i = (SSet.chainComplexMap (Zc.δ i) zz).f r := rfl

/-- `fsum` is the alternating coface map of `D`. -/
lemma fsum_eq_D (m r : ℕ) : fsum m r = D m r := by
  simp only [fsum, D, AlternatingCofaceMapComplex.objD]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ZcR_delta]

/-- The alternating coface sums compose to zero. -/
lemma fsum_comp (m r : ℕ) : fsum m r ≫ fsum (m+1) r = 0 := by
  rw [fsum_eq_D m r, fsum_eq_D (m+1) r]
  exact D_D m r

/-- Evaluation of `fsum` on an element. -/
lemma fsum_apply (m r : ℕ) (x : ↥((sChain (Zm m)).X r)) :
    (fsum m r) x
      = ∑ i : Fin (m+2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((SSet.chainComplexMap (Zc.δ i) zz).f r) x := by
  rw [fsum]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_smul, LinearMap.smul_apply]

/-! ## 4. Differential of the universal chains -/

/-- The `i`-th term of the boundary of the universal chain. -/
lemma d_bigU (n : ℕ) :
    ((sChain (Zm (n+1))).d (n+1) n) (bigU (n+1)) = fsum n n (bigU n) := by
  have h1 := d_genCh (Zm (n+1)) n (U (n+1))
  have h2 : ∀ i : Fin (n+2),
      genCh (Zm (n+1)) ((Zm (n+1)).δ i (U (n+1)))
        = ((SSet.chainComplexMap (Zc.δ i) zz).f n).hom (genCh (Zm n) (U n)) := by
    intro i
    rw [← delta_U n i]
    exact (genCh_chainComplexMap (Zc.δ i) (U n)).symm
  calc ((sChain (Zm (n+1))).d (n+1) n) (bigU (n+1))
      = ((sChain (Zm (n+1))).d (n+1) n).hom (genCh (Zm (n+1)) (U (n+1))) := rfl
    _ = ∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) •
          genCh (Zm (n+1)) ((Zm (n+1)).δ i (U (n+1))) := h1
    _ = ∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) •
          ((SSet.chainComplexMap (Zc.δ i) zz).f n).hom (genCh (Zm n) (U n)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [h2 i]
    _ = ∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) •
          ((SSet.chainComplexMap (Zc.δ i) zz).f n) (bigU n) := rfl
    _ = fsum n n (bigU n) := (fsum_apply n n (bigU n)).symm

/-- The coface acts on the universal chain. -/
lemma chainComplexMap_bigU (n : ℕ) (i : Fin (n+2)) :
    ((SSet.chainComplexMap (Zc.δ i) zz).f n) (bigU n)
      = genCh (sProd (Sd (n+1)) (Sd (n+1)))
          (((MonoidalCategoryStruct.tensorHom (SSet.stdSimplex.map (SimplexCategory.δ i))
              (SSet.stdSimplex.map (SimplexCategory.δ i))).app (Opposite.op ⦋n⦌)) (U n)) := by
  rw [show ((SSet.chainComplexMap (Zc.δ i) zz).f n) (bigU n)
      = ((SSet.chainComplexMap (Zc.δ i) zz).f n).hom (genCh (Zm n) (U n)) from rfl]
  rw [genCh_chainComplexMap]
  rfl

/-- Naturality of `ezaw` under the coface `Zc.δ i`. -/
lemma ezaw_nat_delta (n : ℕ) (i : Fin (n+2)) :
    ((SSet.chainComplexMap (Zc.δ i) zz).f n) (ezaw (Sd n) (Sd n) n (bigU n))
      = ezaw (Sd (n+1)) (Sd (n+1)) n
          (((SSet.chainComplexMap (Zc.δ i) zz).f n) (bigU n)) := by
  rw [chainComplexMap_bigU n i]
  exact ezaw_nat_gen (Sd n) (Sd n) (Sd (n+1)) (Sd (n+1))
    (SSet.stdSimplex.map (SimplexCategory.δ i)) (SSet.stdSimplex.map (SimplexCategory.δ i)) n (U n)

/-- `Fmap` is a chain map on the universal chain. -/
lemma Fmap_chain (n : ℕ) :
    ((Fmap (n+1)).f n).hom (((sChain (Zm (n+1))).d (n+1) n) (bigU (n+1)))
      = ((sChain (Zm (n+1))).d (n+1) n) (((Fmap (n+1)).f (n+1)).hom (bigU (n+1))) := by
  have h := HomologicalComplex.Hom.comm (Fmap (n+1)) (n+1) n
  have h2 := congrArg (fun (φ : (sChain (Zm (n+1))).X (n+1) ⟶ (sChain (Zm (n+1))).X n) =>
    φ.hom (bigU (n+1))) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2.symm

/-- Naturality of `ezaw` under the coface `Zc.δ i`, in `Fmap` form. -/
lemma Fmap_nat_delta (n : ℕ) (i : Fin (n+2)) :
    ((Fmap (n+1)).f n).hom (((SSet.chainComplexMap (Zc.δ i) zz).f n) (bigU n))
      = ((SSet.chainComplexMap (Zc.δ i) zz).f n) (((Fmap n).f n).hom (bigU n)) := by
  rw [Fmap_f_hom (n+1) n, Fmap_f_hom n n]
  exact (ezaw_nat_delta n i).symm

/-- The differential of `E`. -/
lemma dE (n : ℕ) :
    ((sChain (Zm (n+1))).d (n+1) n) (E (n+1)) = fsum n n (E n) := by
  have hF : ((sChain (Zm (n+1))).d (n+1) n) (((Fmap (n+1)).f (n+1)).hom (bigU (n+1)))
      = ((Fmap (n+1)).f n).hom (((sChain (Zm (n+1))).d (n+1) n) (bigU (n+1))) :=
    (Fmap_chain n).symm
  have h1 : ((sChain (Zm (n+1))).d (n+1) n) (E (n+1))
      = ((Fmap (n+1)).f n).hom (fsum n n (bigU n)) - fsum n n (bigU n) := by
    rw [E_def, map_sub, hF, d_bigU]
  rw [h1]
  have key : ((Fmap (n+1)).f n).hom (fsum n n (bigU n))
      = ∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) • ((SSet.chainComplexMap (Zc.δ i) zz).f n)
          (((Fmap n).f n).hom (bigU n)) := by
    rw [fsum_apply n n (bigU n)]
    refine (map_sum ((Fmap (n+1)).f n).hom _ Finset.univ).trans ?_
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul]
    congr 1
    exact Fmap_nat_delta n i
  have key2 : fsum n n (bigU n)
      = ∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) • ((SSet.chainComplexMap (Zc.δ i) zz).f n)
          (bigU n) := fsum_apply n n (bigU n)
  have key3 : fsum n n (E n)
      = ∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) • ((SSet.chainComplexMap (Zc.δ i) zz).f n)
          (((Fmap n).f n).hom (bigU n) - bigU n) := by
    rw [fsum_apply n n (E n)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rfl
  rw [key, key2, key3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sub, zsmul_sub]

/-- Splitting the alternating coface sum along the differential. -/
lemma fsum_natural (m r : ℕ) :
    fsum m (r+1) ≫ ((sChain (Zm (m+1))).d (r+1) r)
      = ((sChain (Zm m)).d (r+1) r) ≫ fsum m r := by
  have h1 : fsum m (r+1) ≫ ((sChain (Zm (m+1))).d (r+1) r)
      = ∑ i : Fin (m+2), ((-1:ℤ)^(i:ℕ)) •
          ((SSet.chainComplexMap (Zc.δ i) zz).f (r+1) ≫ ((sChain (Zm (m+1))).d (r+1) r)) := by
    simp only [fsum, Preadditive.sum_comp, Preadditive.zsmul_comp]
  have h3 : ((sChain (Zm m)).d (r+1) r) ≫ fsum m r
      = ∑ i : Fin (m+2), ((-1:ℤ)^(i:ℕ)) •
          (((sChain (Zm m)).d (r+1) r) ≫ (SSet.chainComplexMap (Zc.δ i) zz).f r) := by
    rw [fsum, Preadditive.comp_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Preadditive.comp_zsmul]
  rw [h1, h3]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [HomologicalComplex.Hom.comm (SSet.chainComplexMap (Zc.δ i) zz) (r+1) r]

/-! ## 5. The acyclic-models recursion -/

/-- The defect of the `n`-th model, as a cycle to be filled. -/
noncomputable def B (n : ℕ) (v : ↥((sChain (Zm n)).X (n+1))) :
    ↥((sChain (Zm (n+1))).X (n+1)) :=
  E (n+1) - (fsum n (n+1)) v

lemma B_def (n : ℕ) (v : ↥((sChain (Zm n)).X (n+1))) :
    B n v = E (n+1) - (fsum n (n+1)) v := rfl

/-- The defect is a cycle in degree `0`. -/
lemma B_cycle_zero (v : ↥((sChain (Zm 0)).X 1))
    (h : ((sChain (Zm 0)).d 1 0) v = 0) :
    ((sChain (Zm 1)).d 1 0) (B 0 v) = 0 := by
  have h1 : ((sChain (Zm 1)).d 1 0) (B 0 v)
      = ((sChain (Zm 1)).d 1 0) (E 1)
        - ((sChain (Zm 1)).d 1 0) ((fsum 0 1) v) := by
    rw [B_def, map_sub]
  rw [h1, dE 0]
  have h2 : ((sChain (Zm 1)).d 1 0) ((fsum 0 1) v)
      = (fsum 0 0) (((sChain (Zm 0)).d 1 0) v) := by
    rw [← ConcreteCategory.comp_apply, fsum_natural 0 0, ConcreteCategory.comp_apply]
  rw [h2, h, map_zero, E_zero, map_zero, sub_zero]

/-- The defect is a cycle, assuming the recursion equation in the previous degree. -/
lemma B_cycle (n : ℕ) (p : ↥((sChain (Zm n)).X (n+1)))
    (v : ↥((sChain (Zm (n+1))).X (n+2)))
    (h : ((sChain (Zm (n+1))).d (n+2) (n+1)) v = E (n+1) - fsum n (n+1) p) :
    ((sChain (Zm (n+2))).d (n+2) (n+1)) (B (n+1) v) = 0 := by
  have h1 : ((sChain (Zm (n+2))).d (n+2) (n+1)) (B (n+1) v)
      = ((sChain (Zm (n+2))).d (n+2) (n+1)) (E (n+2))
        - ((sChain (Zm (n+2))).d (n+2) (n+1)) ((fsum (n+1) (n+2)) v) := by
    rw [B_def, map_sub]
  rw [h1, dE (n+1)]
  have h2 : ((sChain (Zm (n+2))).d (n+2) (n+1)) ((fsum (n+1) (n+2)) v)
      = (fsum (n+1) (n+1)) (((sChain (Zm (n+1))).d (n+2) (n+1)) v) := by
    rw [← ConcreteCategory.comp_apply, fsum_natural (n+1) (n+1), ConcreteCategory.comp_apply]
  rw [h2, h, map_sub]
  rw [show (fsum (n+1) (n+1)) (E (n+1))
      - ((fsum (n+1) (n+1)) (E (n+1))
          - (fsum (n+1) (n+1)) ((fsum n (n+1)) p))
      = (fsum (n+1) (n+1)) ((fsum n (n+1)) p) by abel]
  rw [← ConcreteCategory.comp_apply, fsum_comp n (n+1)]
  simp

/-- The recursion: the pair `(w n, w (n+1))` together with the equation defining `w (n+1)`. -/
noncomputable def wst : (n : ℕ) →
    Σ' (p : ↥((sChain (Zm n)).X (n+1))) (v : ↥((sChain (Zm (n+1))).X (n+2))),
      ((sChain (Zm (n+1))).d (n+2) (n+1)) v = E (n+1) - fsum n (n+1) p :=
  Nat.rec
    ⟨0, (exists_boundary 1 (by omega) (B 0 0)
        (B_cycle_zero (0 : ↥((sChain (Zm 0)).X 1)) (by simp))).choose,
      (exists_boundary 1 (by omega) (B 0 0)
        (B_cycle_zero (0 : ↥((sChain (Zm 0)).X 1)) (by simp))).choose_spec⟩
    (fun n s => ⟨s.2.1,
      (exists_boundary (n+2) (by omega) (B (n+1) s.2.1)
        (B_cycle n s.1 s.2.1 s.2.2)).choose,
      (exists_boundary (n+2) (by omega) (B (n+1) s.2.1)
        (B_cycle n s.1 s.2.1 s.2.2)).choose_spec⟩)

/-- The `n`-th acyclicity chain of the model `Δ[n] ⊗ Δ[n]`. -/
noncomputable def w (n : ℕ) : ↥((sChain (Zm n)).X (n+1)) := (wst n).1

lemma w_zero : w 0 = 0 := rfl

lemma w_spec (n : ℕ) :
    ((sChain (Zm (n+1))).d (n+2) (n+1)) (w (n+1)) = E (n+1) - fsum n (n+1) (w n) :=
  (wst n).2.2

/-! ## 6. The chain homotopy -/

/-- The `n`-th acyclicity chain, as a morphism out of `ℤ`. -/
noncomputable def wm (n : ℕ) : zz ⟶ ((sChain (Zm n)).X (n+1)) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥((sChain (Zm n)).X (n+1)) (w n))

lemma wm_spec (n : ℕ) : (wm n).hom 1 = w n := by
  rw [wm, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]

/-- The `n`-th component of the chain homotopy `awMap ≫ ezMap ~ 𝟙`. -/
noncomputable def H (X Y : SSet) (n : ℕ) :
    ((sChain (sProd X Y)).X n) ⟶ ((sChain (sProd X Y)).X (n+1)) :=
  Cofan.IsColimit.desc ((sProd X Y).isColimitChainComplexXCofan zz n)
    (fun z : (sProd X Y) _⦋n⦌ =>
      wm n ≫ (SSet.chainComplexMap (classify X Y n z) zz).f (n+1))

lemma H_fac (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n⦌) :
    (sProd X Y).ιChainComplex z ≫ H X Y n
      = wm n ≫ (SSet.chainComplexMap (classify X Y n z) zz).f (n+1) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of the chain map of `classify` on the universal chain. -/
lemma chainComplexMap_classify_U (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n⦌) :
    ((SSet.chainComplexMap (classify X Y n z) zz).f n) (bigU n) = genCh (sProd X Y) z := by
  rw [show ((SSet.chainComplexMap (classify X Y n z) zz).f n) (bigU n)
      = ((SSet.chainComplexMap (classify X Y n z) zz).f n).hom (genCh (Zm n) (U n)) from rfl]
  rw [genCh_chainComplexMap, classify_U]

/-- Naturality of `ezaw` under `classify`. -/
lemma ezaw_nat_class (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n⦌) :
    ((SSet.chainComplexMap (classify X Y n z) zz).f n) (E n)
      = ezaw X Y n (genCh (sProd X Y) z) - genCh (sProd X Y) z := by
  have hnac : ((SSet.chainComplexMap (classify X Y n z) zz).f n)
        (ezaw (Sd n) (Sd n) n (bigU n))
      = ezaw X Y n (genCh (sProd X Y)
          ((classify X Y n z).app (Opposite.op ⦋n⦌) (U n))) :=
    ezaw_nat_gen (Sd n) (Sd n) X Y
      ((SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).symm z.1)
      ((SSet.yonedaEquiv (X := Y) (n := ⦋n⦌)).symm z.2) n (U n)
  rw [show ((SSet.chainComplexMap (classify X Y n z) zz).f n) (E n)
      = ((SSet.chainComplexMap (classify X Y n z) zz).f n) (((Fmap n).f n).hom (bigU n))
        - ((SSet.chainComplexMap (classify X Y n z) zz).f n) (bigU n) from by
    rw [E_def, map_sub]]
  rw [chainComplexMap_classify_U, Fmap_f_hom n n]
  congr 1
  exact hnac.trans
    (congrArg (fun w => ezaw X Y n (genCh (sProd X Y) w)) (classify_U X Y n z))

/-- The chain map of a composite of simplicial maps. -/
lemma chainComplexMap_comp {A B D : SSet} (φ : A ⟶ B) (ψ : B ⟶ D) (k : ℕ) :
    (SSet.chainComplexMap (φ ≫ ψ) zz).f k
      = (SSet.chainComplexMap φ zz).f k ≫ (SSet.chainComplexMap ψ zz).f k := by
  rw [show SSet.chainComplexMap (φ ≫ ψ) zz
      = SSet.chainComplexMap φ zz ≫ SSet.chainComplexMap ψ zz from
    Functor.map_comp ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj zz) φ ψ]
  rfl

/-- `classify` is natural for the coface. -/
lemma chainComplexMap_classify_delta (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n+1⦌)
    (i : Fin (n+2)) (x : ↥((sChain (Zm n)).X (n+1))) :
    ((SSet.chainComplexMap (classify X Y (n+1) z) zz).f (n+1))
        (((SSet.chainComplexMap (Zc.δ i) zz).f (n+1)) x)
      = ((SSet.chainComplexMap (classify X Y n ((sProd X Y).δ i z)) zz).f (n+1)) x := by
  rw [← ConcreteCategory.comp_apply,
    ← chainComplexMap_comp (Zc.δ i) (classify X Y (n+1) z) (n+1),
    ← classify_delta X Y n z i]

/-- The alternating coface sum, conjugated by `classify`. -/
lemma fsum_classify (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n+1⦌) :
    ((SSet.chainComplexMap (classify X Y (n+1) z) zz).f (n+1)) (fsum n (n+1) (w n))
      = ∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) •
          (((SSet.chainComplexMap (classify X Y n ((sProd X Y).δ i z)) zz).f (n+1))
            (w n)) := by
  rw [fsum_apply n (n+1) (w n)]
  refine (map_sum ((SSet.chainComplexMap (classify X Y (n+1) z) zz).f (n+1)).hom
    _ Finset.univ).trans ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul]
  congr 1
  exact chainComplexMap_classify_delta X Y n z i (w n)

/-- The differential of the value of `H` on a generator. -/
lemma d_H_val (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n+1⦌) :
    ((sChain (sProd X Y)).d (n+2) (n+1))
        (((SSet.chainComplexMap (classify X Y (n+1) z) zz).f (n+2)) (w (n+1)))
      = ezaw X Y (n+1) (genCh (sProd X Y) z) - genCh (sProd X Y) z
        - ∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) •
            (((SSet.chainComplexMap (classify X Y n ((sProd X Y).δ i z)) zz).f (n+1))
              (w n)) := by
  have h1 : ((sChain (sProd X Y)).d (n+2) (n+1))
        (((SSet.chainComplexMap (classify X Y (n+1) z) zz).f (n+2)) (w (n+1)))
      = ((SSet.chainComplexMap (classify X Y (n+1) z) zz).f (n+1))
          (((sChain (Zm (n+1))).d (n+2) (n+1)) (w (n+1))) := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm
      (SSet.chainComplexMap (classify X Y (n+1) z) zz) (n+2) (n+1),
      ConcreteCategory.comp_apply]
  rw [h1, w_spec n, map_sub, ezaw_nat_class X Y (n+1) z, fsum_classify X Y n z]

/-! ## 7. Assembly of the homotopy -/

lemma ModuleCat_zz_ext {N : ModuleCat ℤ} {f g : zz ⟶ N} (h : f.hom 1 = g.hom 1) : f = g := by
  refine ModuleCat.hom_ext (LinearMap.ext fun k => ?_)
  have hk : k = k • (1 : ℤ) := by rw [smul_eq_mul, mul_one]
  rw [hk, LinearMap.map_smul, LinearMap.map_smul, h]

/-- The value of a morphism out of `ℤ` on a generator. -/
lemma genCh_hom_apply {X : SSet} {N : ModuleCat ℤ} (k : ℕ) (σ : X _⦋k⦌)
    (φ : (sChain X).X k ⟶ N) :
    φ.hom (genCh X σ) = (X.ιChainComplex σ ≫ φ).hom 1 := by
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]

lemma genCh_ezaw (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n⦌) :
    ((sProd X Y).ιChainComplex z ≫ (awHom X Y n ≫ ezHom X Y n)).hom 1
      = ezaw X Y n (genCh (sProd X Y) z) := by
  have h1 : ezaw X Y n (genCh (sProd X Y) z) = (ezHom X Y n).hom ((awGen X Y n z).hom 1) := by
    simp only [ezaw, ModuleCat.hom_comp, LinearMap.comp_apply]
    congr 1
    have h := congrArg (fun (g : zz ⟶ (tChain X Y).X n) => g.hom 1) (awHom_gen X Y n z)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, genCh] using h
  rw [h1, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  have h := congrArg (fun (g : zz ⟶ (tChain X Y).X n) => g.hom 1) (awHom_gen X Y n z)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, genCh] using h

lemma genCh_H (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n⦌) :
    ((sProd X Y).ιChainComplex z ≫ H X Y n).hom 1
      = ((SSet.chainComplexMap (classify X Y n z) zz).f (n+1)) (w n) := by
  rw [H_fac, ModuleCat.hom_comp, LinearMap.comp_apply, wm_spec]

lemma genCh_d_H (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n+1⦌) :
    ((sProd X Y).ιChainComplex z
        ≫ (((sChain (sProd X Y)).d (n+1) n) ≫ H X Y n)).hom 1
      = ∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) •
          (((SSet.chainComplexMap (classify X Y n ((sProd X Y).δ i z)) zz).f (n+1)) (w n)) := by
  rw [← Category.assoc, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hd : ((sProd X Y).ιChainComplex z ≫ ((sChain (sProd X Y)).d (n+1) n)).hom 1
      = ∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) • genCh (sProd X Y) ((sProd X Y).δ i z) := by
    have h := congrArg (fun (g : zz ⟶ ((sChain (sProd X Y)).X n)) => g.hom 1)
      (SSet.ιChainComplex_d (X := sProd X Y) (R := zz) z)
    simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_smul, LinearMap.smul_apply,
      genCh] using h
  rw [hd]
  refine (map_sum (H X Y n).hom _ Finset.univ).trans ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul]
  congr 1
  rw [genCh_hom_apply]
  exact genCh_H X Y n ((sProd X Y).δ i z)

lemma genCh_H_d (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n⦌) :
    ((sProd X Y).ιChainComplex z
        ≫ (H X Y n ≫ ((sChain (sProd X Y)).d (n+1) n))).hom 1
      = ((sChain (sProd X Y)).d (n+1) n)
          (((SSet.chainComplexMap (classify X Y n z) zz).f (n+1)) (w n)) := by
  rw [← Category.assoc, ModuleCat.hom_comp, LinearMap.comp_apply, genCh_H]

/-- The `(i,j)`-component of the homotopy. -/
noncomputable def homMap (X Y : SSet) (i j : ℕ) :
    ((sChain (sProd X Y)).X i) ⟶ ((sChain (sProd X Y)).X j) :=
  if h : i + 1 = j then
    H X Y i ≫ eqToHom (congrArg (fun k => ((sChain (sProd X Y)).X k)) h)
  else 0

lemma homMap_succ (X Y : SSet) (i : ℕ) : homMap X Y i (i+1) = H X Y i := by
  rw [homMap, dif_pos rfl]
  exact Category.comp_id _

lemma homMap_neg (X Y : SSet) {i j : ℕ} (h : ¬ i + 1 = j) : homMap X Y i j = 0 := by
  rw [homMap, dif_neg h]

theorem H_comm_gen (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n+1⦌) :
    ezaw X Y (n+1) (genCh (sProd X Y) z)
      = (∑ i : Fin (n+2), ((-1:ℤ)^(i:ℕ)) •
            (((SSet.chainComplexMap (classify X Y n ((sProd X Y).δ i z)) zz).f (n+1)) (w n)))
        + ((sChain (sProd X Y)).d (n+2) (n+1))
            (((SSet.chainComplexMap (classify X Y (n+1) z) zz).f (n+2)) (w (n+1)))
        + genCh (sProd X Y) z := by
  rw [d_H_val X Y n z]
  abel

theorem H_comm_zero_gen (X Y : SSet) (z : (sProd X Y) _⦋0⦌) :
    ezaw X Y 0 (genCh (sProd X Y) z)
      = ((sChain (sProd X Y)).d 1 0)
          (((SSet.chainComplexMap (classify X Y 0 z) zz).f 1) (w 0))
        + genCh (sProd X Y) z := by
  rw [ezaw_gen_zero, w_zero]
  simp

theorem aw_ez_homotopy_aux (X Y : SSet) :
    Nonempty (Homotopy (awMap X Y ≫ ezMap X Y) (𝟙 (sChain (sProd X Y)))) := by
  refine ⟨{ hom := homMap X Y
            zero := fun i j h => homMap_neg X Y h
            comm := fun i => ?_ }⟩
  cases i with
  | zero =>
    rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, homMap_succ, zero_add,
      HomologicalComplex.comp_f, awMap_f, ezMap_f]
    refine SSet.chainComplex_hom_ext (fun z => ?_)
    refine ModuleCat_zz_ext ?_
    rw [Preadditive.comp_add, ModuleCat.hom_add, LinearMap.add_apply, HomologicalComplex.id_f,
      Category.comp_id]
    rw [genCh_ezaw, genCh_H_d]
    exact H_comm_zero_gen X Y z
  | succ n =>
    rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, homMap_succ, homMap_succ,
      HomologicalComplex.comp_f, awMap_f, ezMap_f]
    refine SSet.chainComplex_hom_ext (fun z => ?_)
    refine ModuleCat_zz_ext ?_
    rw [Preadditive.comp_add, Preadditive.comp_add, ModuleCat.hom_add, ModuleCat.hom_add,
      LinearMap.add_apply, LinearMap.add_apply, HomologicalComplex.id_f, Category.comp_id]
    rw [genCh_ezaw, genCh_d_H, genCh_H_d]
    exact H_comm_gen X Y n z

end EZHom

end

end Work.Kunneth
