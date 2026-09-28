import Mathlib
import Submission.Work.Kunneth.AW
import Submission.Work.Kunneth.EZMap
import Submission.Work.Kunneth.AWAux

/-!
# The chain homotopy `awMap ≫ ezMap ~ 1` (Eilenberg–Zilber theorem, one direction)

Acyclic-models proof that `awMap : C_*(X ⊗ Y) ⟶ C_*(X) ⊗ C_*(Y)` followed by
`ezMap : C_*(X) ⊗ C_*(Y) ⟶ C_*(X ⊗ Y)` is chain homotopic to the identity.
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

/-! ## 0. The cosimplicial model `m ↦ Δ[m] ⊗ Δ[m]` -/

/-- The endofunctor `X ↦ X ⊗ X` of simplicial sets. -/
noncomputable def sqSSet : SSet ⥤ SSet where
  obj X := X ⊗ X
  map f := MonoidalCategoryStruct.tensorHom f f
  map_id X := MonoidalCategory.id_tensorHom_id X X
  map_comp f g := (MonoidalCategory.tensorHom_comp_tensorHom f f g g).symm

/-- The cosimplicial object `m ↦ Δ[m] ⊗ Δ[m]` of simplicial sets. -/
noncomputable def Zc : CosimplicialObject SSet := SSet.stdSimplex ⋙ sqSSet

/-- The `m`-th model, `Δ[m] ⊗ Δ[m]`. -/
abbrev Zm (m : ℕ) : SSet := Zc.obj ⦋m⦌

/-- The universal `m`-simplex `(id_m, id_m)` of `Δ[m] ⊗ Δ[m]`. -/
noncomputable def U (m : ℕ) : (Zm m) _⦋m⦌ :=
  (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋m⦌), SSet.stdSimplex.objEquiv.symm (𝟙 ⦋m⦌))

/-- `u m` is the chain generator attached to the universal simplex. -/
noncomputable def u (m : ℕ) : zz ⟶ (sChain (Zm m)).X m :=
  (Zm m).ιChainComplex (U m)

/-- The cosimplicial object `m ↦ C_r(Δ[m] ⊗ Δ[m])` of `ℤ`-modules. -/
noncomputable def ZcR (r : ℕ) : CosimplicialObject (ModuleCat ℤ) :=
  Zc ⋙ (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj zz) ⋙
    HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) r)

/-- The alternating sum of the coface maps, transported to the chain complexes. -/
noncomputable def D (m r : ℕ) :
    (((Zm m).chainComplex zz).X r) ⟶ (((Zm (m + 1)).chainComplex zz).X r) :=
  AlternatingCofaceMapComplex.objD (ZcR r) m

/-- `D` composed with itself (in the `m`-variable) is zero. -/
theorem D_D (m r : ℕ) : D m r ≫ D (m + 1) r = 0 :=
  AlternatingCofaceMapComplex.d_squared (ZcR r) m

/-! ## 1. The augmented product and the homotopy equivalence with `single₀` -/

/-- The endofunctor `X ↦ X × X` of types. -/
noncomputable def sqF : Type ⥤ Type where
  obj A := A × A
  map f := MonoidalCategoryStruct.tensorHom f f
  map_id A := rfl
  map_comp f g := rfl

/-- The augmented simplicial object `Δ[m] ⊗ Δ[m] → Δ[0]` (over an arbitrary point). -/
noncomputable abbrev augProd (m : ℕ) : SimplicialObject.Augmented Type :=
  ((CategoryTheory.SimplicialObject.Augmented.whiskering Type Type).obj sqF).obj
    (SSet.Augmented.stdSimplex.obj ⦋m⦌)

/-- The extra degeneracy of the augmented product, inherited from the standard simplex. -/
noncomputable def edProd (m : ℕ) : SimplicialObject.Augmented.ExtraDegeneracy (augProd m) :=
  (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋m⦌).map sqF

/-- The extra degeneracy transported to `ℤ`-modules. -/
noncomputable def edMod (m : ℕ) :=
  (edProd m).map (Limits.sigmaConst.obj zz)

/-- The resulting homotopy equivalence `C_*(Δ[m] ⊗ Δ[m]) ≃ ℤ[0]`. -/
noncomputable def he (m : ℕ) := (edMod m).homotopyEquiv

/-- The target object of the augmentation of `augProd m`. -/
noncomputable def Pt (m : ℕ) : ModuleCat ℤ :=
  SimplicialObject.Augmented.point.obj
    (((SimplicialObject.Augmented.whiskering Type (ModuleCat ℤ)).obj
      (Limits.sigmaConst.obj zz)).obj (augProd m))

/-- The resulting homotopy equivalence `C_*(Δ[m] ⊗ Δ[m]) ≃ ℤ[0]`. -/
noncomputable def HE (m : ℕ) : HomotopyEquiv ((Zm m).chainComplex zz)
    ((ChainComplex.single₀ (ModuleCat ℤ)).obj (Pt m)) :=
  (edMod m).homotopyEquiv

/-- Cycles in positive degree of `C_*(Δ[m] ⊗ Δ[m])` are boundaries. -/
theorem exists_boundary (m : ℕ) (hm : 1 ≤ m)
    (B : ((Zm m).chainComplex zz).X m)
    (hB : ((Zm m).chainComplex zz).d m (m - 1) B = 0) :
    ∃ w : ((Zm m).chainComplex zz).X (m + 1),
      ((Zm m).chainComplex zz).d (m + 1) m w = B := by
  haveI hz : IsZero (((ChainComplex.single₀ (ModuleCat ℤ)).obj (Pt m)).X m) :=
    isZero_single_obj_X (ComplexShape.down ℕ) 0 (Pt m) m (by omega)
  have hzero : (HE m).hom.f m = 0 := hz.eq_of_tgt _ _
  have hcomm : dNext m (HE m).homotopyHomInvId.hom + prevD m (HE m).homotopyHomInvId.hom
      = -(𝟙 ((Zm m).chainComplex zz).X m) := by
    have h1 := (HE m).homotopyHomInvId.comm m
    rw [HomologicalComplex.comp_f, hzero, zero_comp, HomologicalComplex.id_f] at h1
    exact eq_neg_iff_add_eq_zero.mpr h1.symm
  set w : ((Zm m).chainComplex zz).X (m + 1) :=
    ((HE m).homotopyHomInvId.hom m (m + 1)) B with hw
  refine ⟨-w, ?_⟩
  have hkey : ((Zm m).chainComplex zz).d (m + 1) m w = -B := by
    have h : (dNext m (HE m).homotopyHomInvId.hom) B
        + (prevD m (HE m).homotopyHomInvId.hom) B = -B := by
      have h' := congrArg (fun (φ : ((Zm m).chainComplex zz).X m
          ⟶ ((Zm m).chainComplex zz).X m) => φ B) hcomm
      simpa using h'
    rw [dNext_nat, prevD_eq (HE m).homotopyHomInvId.hom
      (show (ComplexShape.down ℕ).Rel (m+1) m from rfl)] at h
    simp only [ConcreteCategory.comp_apply, hB, map_zero, zero_add] at h
    exact h
  have hneg : ((Zm m).chainComplex zz).d (m + 1) m (-w)
      = -(((Zm m).chainComplex zz).d (m + 1) m w) := by simp
  rw [hneg, hkey, neg_neg]

/-! ## 2. The composite `awMap ≫ ezMap` on generators -/

/-- The `ℤ`-linear map underlying the composite `awMap ≫ ezMap` in degree `n`. -/
noncomputable def ezaw (X Y : SSet) (n : ℕ) :
    ↥((sChain (sProd X Y)).X n) →ₗ[ℤ] ↥((sChain (sProd X Y)).X n) :=
  (awHom X Y n ≫ ezHom X Y n).hom

/-- The `eqToHom` transport of a generator across a degree change. -/
lemma eqToHom_genCh {Z : SSet} {a b : ℕ} (h : a = b) (χ : Z _⦋a⦌) :
    (eqToHom (congrArg (fun k => (sChain Z).X k) h)).hom (genCh Z χ)
      = genCh Z (cast (congrArg (fun k => Z _⦋k⦌) h) χ) := by
  subst h
  rfl

/-- The `(p,q)`-shuffle chain of two generators, transported to total degree `n`. -/
noncomputable def ezGenN (X Y : SSet) (p q n : ℕ) (h : p + q = n)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) : ↥((sChain (sProd X Y)).X n) :=
  (eqToHom (congrArg (fun k => (sChain (sProd X Y)).X k) h)).hom
    (Work.Cohomology.Crux33.ezGen p q X Y σ τ)

/-- The value of `ezHom` on a shuffle generator of a bidegree summand. -/
theorem ezHom_tpLof_gen (X Y : SSet) (p q n : ℕ) (h : p + q = n)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    (ezHom X Y n).hom (tpLof (sChain X) (sChain Y) n ⟨(p, q), h⟩
        (genCh X σ ⊗ₜ[ℤ] genCh Y τ))
      = ezGenN X Y p q n h σ τ := by
  rw [ezHom_apply_tpLof, ezSummandLin_tmul_chain, Work.KunnethEZ.ezChain_gen]
  rfl

/-- `ezGenN` expanded as a sum over shuffles. -/
theorem ezGenN_eq (X Y : SSet) (p q n : ℕ) (h : p + q = n)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    ezGenN X Y p q n h σ τ
      = ∑ S : Work.Cohomology.Crux33.PShuffle p q,
          (Work.Cohomology.Crux33.shufSign S.1) •
            genCh (sProd X Y)
              (cast (congrArg (fun k => (sProd X Y) _⦋k⦌) h)
                (X.map (Work.Cohomology.Crux33.aHom S.1 S.2).op σ,
                 Y.map (Work.Cohomology.Crux33.bHom S.1 S.2).op τ)) := by
  show (eqToHom (congrArg (fun k => (sChain (sProd X Y)).X k) h)).hom
      (Work.Cohomology.Crux33.ezGen p q X Y σ τ) = _
  rw [Work.Cohomology.Crux33.ezGen]
  refine (map_sum (eqToHom (congrArg (fun k => (sChain (sProd X Y)).X k) h)).hom
    (fun S : Work.Cohomology.Crux33.PShuffle p q =>
      (Work.Cohomology.Crux33.shufSign S.1) •
        genCh (sProd X Y)
          (X.map (Work.Cohomology.Crux33.aHom S.1 S.2).op σ,
           Y.map (Work.Cohomology.Crux33.bHom S.1 S.2).op τ)) Finset.univ).trans ?_
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [map_zsmul]
  congr 1
  exact eqToHom_genCh h _

/-- The composite `awMap ≫ ezMap` on a generator, expanded as a sum over shuffles. -/
theorem ezaw_gen (X Y : SSet) (n : ℕ) (z : (sProd X Y) _⦋n⦌) :
    ezaw X Y n (genCh (sProd X Y) z)
      = ∑ p : Fin (n+1), ∑ S : Work.Cohomology.Crux33.PShuffle p.val (n - p.val),
          (Work.Cohomology.Crux33.shufSign S.1) •
            genCh (sProd X Y)
              (cast (congrArg (fun k => (sProd X Y) _⦋k⦌) (by omega : p.val + (n - p.val) = n))
                ((X.map (Work.Cohomology.Crux33.aHom S.1 S.2).op
                    (Work.Cohomology.frontFace X p.val n (by omega) z.1),
                  Y.map (Work.Cohomology.Crux33.bHom S.1 S.2).op
                    (Work.Kunneth.backFaceLE Y (n - p.val) n (by omega) z.2)))) := by
  have h1 : ezaw X Y n (genCh (sProd X Y) z) = (ezHom X Y n).hom ((awGen X Y n z).hom 1) := by
    simp only [ezaw, ModuleCat.hom_comp, LinearMap.comp_apply]
    congr 1
    have h := congrArg (fun (g : zz ⟶ (tChain X Y).X n) => g.hom 1) (awHom_gen X Y n z)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, genCh] using h
  rw [h1, awGen_hom_one]
  refine (map_sum (ModuleCat.Hom.hom (ezHom X Y n))
    (fun p : Fin (n+1) => (tpLof (sChain X) (sChain Y) n ⟨(p.val, n - p.val), by omega⟩)
        (genCh X (Work.Cohomology.frontFace X p.val n (by omega) z.1) ⊗ₜ[ℤ]
          genCh Y (Work.Kunneth.backFaceLE Y (n - p.val) n (by omega) z.2))) Finset.univ).trans ?_
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact (ezHom_tpLof_gen X Y p.val (n - p.val) n (by omega)
      (Work.Cohomology.frontFace X p.val n (by omega) z.1)
      (Work.Kunneth.backFaceLE Y (n - p.val) n (by omega) z.2)).trans
    (ezGenN_eq X Y p.val (n - p.val) n (by omega) _ _)


/-! ## 3. The degree-zero identity -/

/-- A `cast` along a reflexive equality is the identity. -/
lemma cast_self {α : ℕ → Type*} {a : ℕ} (h : a = a) (x : α a) :
    cast (congrArg α h) x = x := by
  cases h
  rfl

/-- The front `m`-face of an `m`-simplex is the simplex itself. -/
lemma frontFace_self {X : SSet} (m : ℕ) (h : m ≤ m) (z : X _⦋m⦌) :
    Work.Cohomology.frontFace X m m h z = z := by
  have h' : Work.Cohomology.frontIncl m m h = 𝟙 ⦋m⦌ := by
    ext j
    rfl
  rw [Work.Cohomology.frontFace, h']
  simp

/-- The back inclusion `⦋m⦌ ⟶ ⦋m⦌` is the identity. -/
lemma backInclLE_self (m : ℕ) (h : m ≤ m) : backInclLE m m h = 𝟙 ⦋m⦌ := by
  ext j
  simp [backInclLE]

/-- The back `m`-face of an `m`-simplex is the simplex itself. -/
lemma backFaceLE_self {X : SSet} (m : ℕ) (h : m ≤ m) (z : X _⦋m⦌) :
    backFaceLE X m m h z = z := by
  rw [backFaceLE, backInclLE_self]
  simp

/-- In bidegree `(0,0)` the shuffle coordinates are the identity. -/
lemma aHom_zero (S : Work.Cohomology.Crux33.PShuffle 0 0) :
    Work.Cohomology.Crux33.aHom S.1 S.2 = 𝟙 ⦋0⦌ :=
  Subsingleton.elim _ _

/-- In bidegree `(0,0)` the shuffle coordinates are the identity. -/
lemma bHom_zero (S : Work.Cohomology.Crux33.PShuffle 0 0) :
    Work.Cohomology.Crux33.bHom S.1 S.2 = 𝟙 ⦋0⦌ :=
  Subsingleton.elim _ _

/-- The Eilenberg–Zilber sign of the empty shuffle is `1`. -/
lemma shufSign_empty (S : Work.Cohomology.Crux33.PShuffle 0 0) :
    Work.Cohomology.Crux33.shufSign S.1 = 1 := by
  simp [Work.Cohomology.Crux33.shufSign, Work.Cohomology.Crux33.invCount]

/-- An element of `PShuffle 0 0` is the empty shuffle. -/
lemma PShuffle_zero_eq (S : Work.Cohomology.Crux33.PShuffle 0 0) :
    S = ⟨∅, by simp⟩ := by
  refine Subtype.ext ?_
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro _
  have := x.isLt
  omega

/-- The type of `(0,0)`-shuffles is a singleton. -/
lemma univ_PShuffle_zero :
    (Finset.univ : Finset (Work.Cohomology.Crux33.PShuffle 0 0)) = {⟨∅, by simp⟩} := by
  ext b
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  exact PShuffle_zero_eq b

/-- The degree-zero summand of `ezaw_gen` is the generator itself. -/
lemma ezaw_gen_zero_aux (X Y : SSet) (S : Work.Cohomology.Crux33.PShuffle 0 0)
    (z : (sProd X Y) _⦋0⦌) :
    (Work.Cohomology.Crux33.shufSign S.1) •
      genCh (sProd X Y)
        (cast (congrArg (fun k => (sProd X Y) _⦋k⦌) (show (0:ℕ) + (0 - 0) = 0 from rfl))
          ((X.map (Work.Cohomology.Crux33.aHom S.1 S.2).op
              (Work.Cohomology.frontFace X 0 0 le_rfl z.1),
            Y.map (Work.Cohomology.Crux33.bHom S.1 S.2).op
              (backFaceLE Y 0 0 le_rfl z.2)))) = genCh (sProd X Y) z := by
  rw [shufSign_empty, one_smul]
  congr 1
  change ((ConcreteCategory.hom (X.map (Work.Cohomology.Crux33.aHom S.1 S.2).op))
        (Work.Cohomology.frontFace X 0 0 le_rfl z.1),
      (ConcreteCategory.hom (Y.map (Work.Cohomology.Crux33.bHom S.1 S.2).op))
        (backFaceLE Y 0 0 le_rfl z.2)) = z
  congr 1
  · rw [aHom_zero S, frontFace_self]
    simp
  · rw [bHom_zero S, backFaceLE_self]
    simp

/-- In degree `0` the composite `awMap ≫ ezMap` is the identity on generators. -/
theorem ezaw_gen_zero (X Y : SSet) (z : (sProd X Y) _⦋0⦌) :
    ezaw X Y 0 (genCh (sProd X Y) z) = genCh (sProd X Y) z := by
  refine (ezaw_gen X Y 0 z).trans ?_
  rw [Fin.sum_univ_one]
  trans ∑ _S : Work.Cohomology.Crux33.PShuffle 0 0, genCh (sProd X Y) z
  · refine Finset.sum_congr rfl (fun S _ => ?_)
    exact ezaw_gen_zero_aux X Y S z
  · rw [Finset.sum_const]
    rw [show (Finset.univ : Finset (Work.Cohomology.Crux33.PShuffle 0 0)).card = 1 from by
      rw [Finset.card_eq_one.mpr ⟨_, univ_PShuffle_zero⟩]]
    simp


/-! ## 4. Naturality of `ezaw` -/

/-- Naturality of the front face under a simplicial map. -/
lemma frontFace_nat {X X' : SSet} (f : X ⟶ X') {p n : ℕ} (h : p ≤ n) (u : X _⦋n⦌) :
    Work.Cohomology.frontFace X' p n h (f.app (Opposite.op (SimplexCategory.mk n)) u)
      = f.app (Opposite.op (SimplexCategory.mk p)) (Work.Cohomology.frontFace X p n h u) := by
  show X'.map (Work.Cohomology.frontIncl p n h).op (f.app _ u)
      = f.app _ (X.map (Work.Cohomology.frontIncl p n h).op u)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, f.naturality]

/-- Naturality of the back face under a simplicial map. -/
lemma backFaceLE_nat {X X' : SSet} (f : X ⟶ X') {q n : ℕ} (h : q ≤ n) (u : X _⦋n⦌) :
    backFaceLE X' q n h (f.app (Opposite.op (SimplexCategory.mk n)) u)
      = f.app (Opposite.op (SimplexCategory.mk q)) (backFaceLE X q n h u) := by
  show X'.map (backInclLE q n h).op (f.app _ u) = f.app _ (X.map (backInclLE q n h).op u)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, f.naturality]

/-- Naturality of the pullback `X.map ψ.op` under a simplicial map. -/
lemma map_op_nat {X X' : SSet} (f : X ⟶ X') {p n : ℕ} (ψ : ⦋n⦌ ⟶ ⦋p⦌) (u : X _⦋p⦌) :
    f.app (Opposite.op (SimplexCategory.mk n)) (X.map ψ.op u)
      = X'.map ψ.op (f.app (Opposite.op (SimplexCategory.mk p)) u) := by
  rw [← ConcreteCategory.comp_apply, f.naturality, ConcreteCategory.comp_apply]

/-- The chain map induced by a simplicial map, on generators. -/
lemma genCh_chainComplexMap {X Y : SSet} (φ : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    ((SSet.chainComplexMap φ zz).f n).hom (genCh X x)
      = genCh Y (φ.app (Opposite.op (SimplexCategory.mk n)) x) := by
  have h := SSet.ι_chainComplexMap_f X Y φ zz x
  have h2 := congrArg (fun (g : zz ⟶ (sChain Y).X n) => g.hom (1 : ℤ)) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, genCh] using h2

/-- Two `cast`s along equalities of the same type agree. -/
lemma cast_proof_irrel {Z : SSet} {a b : ℕ} {h h' : a = b} (χ : Z _⦋a⦌) :
    cast (congrArg (fun k => Z _⦋k⦌) h) χ = cast (congrArg (fun k => Z _⦋k⦌) h') χ := by
  rw [Subsingleton.elim h h']

/-- The cast of a product simplex commutes with a product of simplicial maps. -/
lemma tensorHom_cast (X Y X' Y' : SSet) (f : X ⟶ X') (g : Y ⟶ Y') {a b : ℕ} (h : a = b)
    (χ : (sProd X Y) _⦋a⦌) :
    (MonoidalCategoryStruct.tensorHom f g).app (Opposite.op (SimplexCategory.mk b))
        (cast (congrArg (fun k => (sProd X Y) _⦋k⦌) h) χ)
      = cast (congrArg (fun k => (sProd X' Y') _⦋k⦌) h)
          ((MonoidalCategoryStruct.tensorHom f g).app (Opposite.op (SimplexCategory.mk a)) χ) := by
  subst h
  rfl

end EZHom

end

end Work.Kunneth
