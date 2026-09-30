import Mathlib
import Submission.Work.Homology.Basic
import Submission.Work.Homology.HomologyBiprod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Singular homology of a clopen decomposition

For `A : Set X` clopen in a topological space `X`, every singular simplex
`Δⁿ → X` lands entirely in `A` or entirely in `Aᶜ` (the standard simplex is
connected and `A` is clopen).  Hence the singular chain complex splits as a
direct sum of the chain complexes of the two pieces
(`Work.Homology.SingChainClopenIso`), and, homology being additive, so does
singular homology in every degree — which is
`Work.Homology.SingHomologyClopen`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Homology

noncomputable section

/-! ## The simplicial-set presentation of the singular chain complex

`singChain R X` is definitionally `SSet.chainComplex R (TopCat.toSSet X)`, but in
this presentation the coproduct structure of each degree is not immediately
visible to `rw`.  The abbreviations below give the same object in the
manifestly pointwise presentation, so that the coproduct universal property can
be used directly. -/

/-- `C_*(X; R)` in the simplicial-set presentation. -/
abbrev sChain (R : ModuleCat ℤ) (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  SSet.chainComplex (TopCat.toSSet.obj X) R

/-- The map of singular chain complexes induced by a continuous map, in the
simplicial-set presentation. -/
abbrev sChainMap (R : ModuleCat ℤ) {X Y : TopCat} (f : X ⟶ Y) : sChain R X ⟶ sChain R Y :=
  SSet.chainComplexMap (TopCat.toSSet.map f) R

theorem inclChain_eq_sChainMap (R : ModuleCat ℤ) (X : TopCat) (A : Set X) :
    inclChain R X A = sChainMap R (incl A) := rfl

/-! ## The dichotomy for clopen subsets -/

/-- A continuous map from a preconnected space into `X` either has image
contained in a clopen set `A` or in its complement. -/
theorem clopen_forall_or {X : TopCat} {A : Set X} (hA : IsClopen A) {Z : Type*}
    [TopologicalSpace Z] [PreconnectedSpace Z] (f : C(Z, X)) :
    (∀ z, f z ∈ A) ∨ (∀ z, f z ∈ Aᶜ) := by
  have h : IsClopen (f ⁻¹' A) := hA.preimage f.continuous
  rcases (isClopen_iff.mp h) with h' | h'
  · right
    intro z
    have : z ∉ f ⁻¹' A := by rw [h']; exact Set.notMem_empty z
    simpa using this
  · left
    intro z
    have : z ∈ f ⁻¹' A := by rw [h']; exact Set.mem_univ z
    exact this

/-- The complement half of the dichotomy: if the image of `f` is not contained
in `A`, then it is contained in `Aᶜ`. -/
theorem forall_mem_compl_of_not_forall_mem {X : TopCat} {A : Set X} (hA : IsClopen A)
    {Z : Type*} [TopologicalSpace Z] [PreconnectedSpace Z] (f : C(Z, X))
    (h : ¬ ∀ z, f z ∈ A) : ∀ z, f z ∈ Aᶜ :=
  (clopen_forall_or hA.compl f).resolve_right fun h2 =>
    h fun z => Classical.byContradiction fun hz => h2 z hz

/-! ## Lifting simplices landing in `A` -/

/-- A singular `n`-simplex of `X` whose image lies in `A`, regarded as a
singular `n`-simplex of the subspace `A`. -/
def liftSimplex {X : TopCat} {A : Set X} {n : ℕ}
    (t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z ∈ A) :
    (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)) :=
  (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op (SimplexCategory.mk n))).symm
    ⟨fun z => ⟨TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z, h z⟩,
      Continuous.subtype_mk (TopCat.toSSetObjEquiv X _ t).continuous h⟩

theorem toSSetObjEquiv_liftSimplex {X : TopCat} {A : Set X} {n : ℕ}
    (t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z ∈ A) :
    TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op (SimplexCategory.mk n)) (liftSimplex t h)
      = ⟨fun z => ⟨TopCat.toSSetObjEquiv X _ t z, h z⟩,
          Continuous.subtype_mk (TopCat.toSSetObjEquiv X _ t).continuous h⟩ :=
  Equiv.apply_symm_apply _ _

/-- The simplex of `X` obtained from a lifted simplex is the original one. -/
theorem toSSet_map_incl_liftSimplex {X : TopCat} {A : Set X} {n : ℕ}
    (t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z ∈ A) :
    (TopCat.toSSet.map (incl A)).app (Opposite.op (SimplexCategory.mk n)) (liftSimplex t h) = t := by
  apply (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).injective
  rw [show TopCat.toSSetObjEquiv X _ ((TopCat.toSSet.map (incl A)).app _ (liftSimplex t h))
      = (incl A).hom.comp (TopCat.toSSetObjEquiv (TopCat.of A) _ (liftSimplex t h)) from rfl]
  rw [toSSetObjEquiv_liftSimplex]
  rfl

/-- Lifting a simplex of `A` along the inclusion and then forgetting the lift
gives back the original simplex. -/
theorem liftSimplex_apply_incl {X : TopCat} {A : Set X} {n : ℕ}
    (t : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ∀ z, (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))
        ((TopCat.toSSet.map (incl A)).app (Opposite.op (SimplexCategory.mk n)) t)) z ∈ A) :
    liftSimplex ((TopCat.toSSet.map (incl A)).app (Opposite.op (SimplexCategory.mk n)) t) h = t := by
  apply (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op (SimplexCategory.mk n))).injective
  rw [toSSetObjEquiv_liftSimplex]
  apply ContinuousMap.ext
  intro z
  exact Subtype.ext rfl

/-! ## The degreewise splitting of the chain complex -/

/-- On a generator of the `n`-chains of `X`, `betaFun` selects the side of `X`
in which the simplex lands. -/
def betaFun (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (hA : IsClopen A) (n : ℕ)
    (t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    R ⟶ (sChain R (TopCat.of A)).X n ⊞ (sChain R (TopCat.of (Aᶜ : Set X))).X n := by
  classical
  exact
    if h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z ∈ A then
      Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)) => R)
        (liftSimplex (A := A) t h) ≫ biprod.inl
    else
      Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of (Aᶜ : Set X))).obj
          (Opposite.op (SimplexCategory.mk n)) => R)
        (liftSimplex (A := (Aᶜ : Set X)) t
          (forall_mem_compl_of_not_forall_mem hA _ h)) ≫ biprod.inr

/-- The degreewise splitting `C_n(X;R) → C_n(A;R) ⊕ C_n(Aᶜ;R)`. -/
def beta (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (hA : IsClopen A) (n : ℕ) :
    (sChain R X).X n ⟶ (sChain R (TopCat.of A)).X n ⊞
      (sChain R (TopCat.of (Aᶜ : Set X))).X n :=
  Sigma.desc (betaFun R X A hA n)

/-- The inclusion of the chains of `A` into the chains of `X`, on generators. -/
theorem sChainMap_incl_ι (R : ModuleCat ℤ) (X : TopCat) (A : Set X) {n : ℕ}
    (t : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n))) :
    Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)) => R) t
        ≫ (sChainMap R (incl A)).f n
      = Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) => R)
          ((TopCat.toSSet.map (incl A)).app (Opposite.op (SimplexCategory.mk n)) t) :=
  SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of A)) (TopCat.toSSet.obj X)
    (TopCat.toSSet.map (incl A)) R t

/-- The `A`-component of the splitting `beta` is the inclusion of `A` into `X`. -/
theorem sChainMap_incl_f_comp_beta (R : ModuleCat ℤ) (X : TopCat) (A : Set X)
    (hA : IsClopen A) (n : ℕ) :
    (sChainMap R (incl A)).f n ≫ beta R X A hA n = biprod.inl := by
  apply Sigma.hom_ext
  intro t
  rw [← Category.assoc, sChainMap_incl_ι (R := R) (X := X) (A := A) t]
  dsimp only [beta]
  rw [Sigma.ι_comp_desc]
  have h : ∀ z, (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))
      ((TopCat.toSSet.map (incl A)).app (Opposite.op (SimplexCategory.mk n)) t)) z ∈ A :=
    fun z => (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op (SimplexCategory.mk n)) t z).2
  rw [show betaFun R X A hA n
        ((TopCat.toSSet.map (incl A)).app (Opposite.op (SimplexCategory.mk n)) t)
      = Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of A)).obj
            (Opposite.op (SimplexCategory.mk n)) => R)
          (liftSimplex (A := A)
            ((TopCat.toSSet.map (incl A)).app (Opposite.op (SimplexCategory.mk n)) t) h)
        ≫ biprod.inl by
        simp only [betaFun]; rw [dite_eq_left h]]
  rw [liftSimplex_apply_incl t h]
  rfl

/-- The `Aᶜ`-component of the splitting `beta` is the inclusion of `Aᶜ` into `X`. -/
theorem sChainMap_incl_compl_f_comp_beta (R : ModuleCat ℤ) (X : TopCat) (A : Set X)
    (hA : IsClopen A) (n : ℕ) :
    (sChainMap R (incl (Aᶜ : Set X))).f n ≫ beta R X A hA n = biprod.inr := by
  apply Sigma.hom_ext
  intro t
  rw [← Category.assoc, sChainMap_incl_ι (R := R) (X := X) (A := (Aᶜ : Set X)) t]
  dsimp only [beta]
  rw [Sigma.ι_comp_desc]
  have h : ∀ z, (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))
      ((TopCat.toSSet.map (incl (Aᶜ : Set X))).app (Opposite.op (SimplexCategory.mk n)) t)) z
        ∈ (Aᶜ : Set X) :=
    fun z => (TopCat.toSSetObjEquiv (TopCat.of (Aᶜ : Set X)) (Opposite.op
      (SimplexCategory.mk n)) t z).2
  have hnot : ¬ ∀ z, (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))
      ((TopCat.toSSet.map (incl (Aᶜ : Set X))).app (Opposite.op (SimplexCategory.mk n)) t)) z ∈ A :=
    fun hc => h default (hc default)
  rw [show betaFun R X A hA n
        ((TopCat.toSSet.map (incl (Aᶜ : Set X))).app (Opposite.op (SimplexCategory.mk n)) t)
      = Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of (Aᶜ : Set X))).obj
            (Opposite.op (SimplexCategory.mk n)) => R)
          (liftSimplex (A := (Aᶜ : Set X))
            ((TopCat.toSSet.map (incl (Aᶜ : Set X))).app (Opposite.op (SimplexCategory.mk n)) t) h)
        ≫ biprod.inr by
        simp only [betaFun]; rw [dite_eq_right hnot]]
  rw [liftSimplex_apply_incl t h]
  rfl

/-- `beta` is a left inverse of the degreewise sum of the two inclusions. -/
theorem beta_comp_desc (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (hA : IsClopen A) (n : ℕ) :
    beta R X A hA n ≫ biprod.desc ((sChainMap R (incl A)).f n)
        ((sChainMap R (incl (Aᶜ : Set X))).f n) = 𝟙 ((sChain R X).X n) := by
  apply Sigma.hom_ext
  intro t
  rw [← Category.assoc]
  dsimp only [beta]
  rw [Sigma.ι_comp_desc]
  by_cases h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z ∈ A
  · rw [show betaFun R X A hA n t
        = Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of A)).obj
              (Opposite.op (SimplexCategory.mk n)) => R) (liftSimplex (A := A) t h) ≫ biprod.inl by
        simp only [betaFun]; rw [dite_eq_left h]]
    rw [Category.assoc, biprod.inl_desc]
    rw [sChainMap_incl_ι (R := R) (X := X) (A := A) (liftSimplex (A := A) t h)]
    rw [toSSet_map_incl_liftSimplex t h]
    change Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) => R) t
      = Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) => R) t
        ≫ 𝟙 (∐ fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) => R)
    rw [Category.comp_id]
  · rw [show betaFun R X A hA n t
        = Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of (Aᶜ : Set X))).obj
              (Opposite.op (SimplexCategory.mk n)) => R)
            (liftSimplex (A := (Aᶜ : Set X)) t
              (forall_mem_compl_of_not_forall_mem hA _ h)) ≫ biprod.inr by
        simp only [betaFun]; rw [dite_eq_right h]]
    rw [Category.assoc, biprod.inr_desc]
    rw [sChainMap_incl_ι (R := R) (X := X) (A := (Aᶜ : Set X))
      (liftSimplex (A := (Aᶜ : Set X)) t (forall_mem_compl_of_not_forall_mem hA _ h))]
    rw [toSSet_map_incl_liftSimplex t (forall_mem_compl_of_not_forall_mem hA _ h)]
    change Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) => R) t
      = Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) => R) t
        ≫ 𝟙 (∐ fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) => R)
    rw [Category.comp_id]

/-- `beta` is a right inverse of the degreewise sum of the two inclusions. -/
theorem desc_comp_beta (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (hA : IsClopen A) (n : ℕ) :
    biprod.desc ((sChainMap R (incl A)).f n) ((sChainMap R (incl (Aᶜ : Set X))).f n)
        ≫ beta R X A hA n = 𝟙 _ := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, biprod.inl_desc, sChainMap_incl_f_comp_beta]
    simp
  · rw [← Category.assoc, biprod.inr_desc, sChainMap_incl_compl_f_comp_beta]
    simp

/-- **The chain level decomposition.** The singular chain complex of `X` with
coefficients in `R` is the direct sum of the chain complexes of the clopen
pieces `A` and `Aᶜ`. -/
theorem SingChainClopenIso (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (hA : IsClopen A) :
    Nonempty (singChain R X ≅
      (singChain R (TopCat.of A) ⊞ singChain R (TopCat.of (Aᶜ : Set X)))) := by
  have hcomp : ∀ n, IsIso ((biprod.desc (sChainMap R (incl A))
      (sChainMap R (incl (Aᶜ : Set X)))).f n) := by
    intro n
    have hδ : (HomologicalComplex.biprodXIso (sChain R (TopCat.of A))
          (sChain R (TopCat.of (Aᶜ : Set X))) n).inv
        ≫ (biprod.desc (sChainMap R (incl A)) (sChainMap R (incl (Aᶜ : Set X)))).f n
        = biprod.desc ((sChainMap R (incl A)).f n) ((sChainMap R (incl (Aᶜ : Set X))).f n) := by
      apply biprod.hom_ext'
      · rw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv,
          HomologicalComplex.biprod_inl_desc_f, biprod.inl_desc]
      · rw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv,
          HomologicalComplex.biprod_inr_desc_f, biprod.inr_desc]
    have hIsIso : IsIso (biprod.desc ((sChainMap R (incl A)).f n)
        ((sChainMap R (incl (Aᶜ : Set X))).f n)) :=
      IsIso.mk ⟨beta R X A hA n, desc_comp_beta R X A hA n, beta_comp_desc R X A hA n⟩
    exact IsIso.of_isIso_fac_left hδ
  have hIsIso : IsIso (biprod.desc (sChainMap R (incl A)) (sChainMap R (incl (Aᶜ : Set X)))) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact ⟨(asIso (biprod.desc (sChainMap R (incl A))
    (sChainMap R (incl (Aᶜ : Set X))))).symm⟩

/-- **Singular homology of a clopen decomposition.** For a clopen subset `A` of
a topological space `X`, the singular homology of `X` with coefficients in a
`ℤ`-module `R` splits, in every degree, as the direct sum of the singular
homologies of `A` and of its complement. -/
theorem SingHomologyClopen (R : ModuleCat ℤ) (k : ℕ) (X : TopCat) (A : Set X)
    (hA : IsClopen A) :
    Nonempty (singHomology R k X ≅
      (singHomology R k (TopCat.of A) ⊞ singHomology R k (TopCat.of (Aᶜ : Set X)))) := by
  obtain ⟨e⟩ := SingChainClopenIso R X A hA
  obtain ⟨hb⟩ := HomologyBiprod (singChain R (TopCat.of A))
    (singChain R (TopCat.of (Aᶜ : Set X))) k
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso e ≪≫ hb⟩

end

end Work.Homology
