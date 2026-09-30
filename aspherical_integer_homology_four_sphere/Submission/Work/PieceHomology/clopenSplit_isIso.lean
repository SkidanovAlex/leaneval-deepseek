/-
# Splitting singular homology along a clopen subset

For a clopen subset `A` of a topological space `X`, the map

`H_k(A) ⊞ H_k(Aᶜ) ⟶ H_k(X)`

induced by the two inclusions is an isomorphism.  This is the "homology of a
disjoint union" statement in the binary case, in the direction in which it is
used to *combine* the pieces.

The mathematics: since the standard simplex is connected and `A` is clopen,
every singular simplex of `X` lands entirely in `A` or entirely in `Aᶜ`, so the
singular chain complex splits, degreewise and compatibly with the differentials,
as `C_*(A) ⊞ C_*(Aᶜ)`; the splitting map is `Work.Homology.beta`.  Hence the
chain map `C_*(A) ⊞ C_*(Aᶜ) ⟶ C_*(X)` given by the two inclusions is an
isomorphism (`isIso_clopenChainDesc`).  Applying homology — an additive functor,
so that it turns this biproduct into the biproduct of the homologies — gives the
stated isomorphism `H_k(A) ⊞ H_k(Aᶜ) ≅ H_k(X)`.

The algebraic input needed to pass from the chain level to homology is isolated
in `homologyBiprodIso` and `desc_homologyMap` below: the canonical comparison
`H_k(A) ⊞ H_k(B) ⟶ H_k(A ⊞ B)` is an isomorphism, and it turns the homology of
a `biprod.desc` into the `biprod.desc` of the homologies.
-/
import Mathlib
import Submission.Work.Homology.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PieceHomology

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

/-! ## Homology of a binary biproduct of chain complexes -/

/-- The canonical map `H_k(A) ⊞ H_k(B) ⟶ H_k(A ⊞ B)`, induced by the maps
that the two summands of a biproduct of chain complexes induce in homology.
It is the inverse of the isomorphism "homology commutes with biproducts" of
`Work.Homology.HomologyBiprod`. -/
def homologyBiprodIso (A B : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    A.homology k ⊞ B.homology k ≅ (A ⊞ B).homology k where
  hom := biprod.desc (homologyMap (biprod.inl : A ⟶ A ⊞ B) k)
    (homologyMap (biprod.inr : B ⟶ A ⊞ B) k)
  inv := biprod.lift (homologyMap (biprod.fst : A ⊞ B ⟶ A) k)
    (homologyMap (biprod.snd : A ⊞ B ⟶ B) k)
  hom_inv_id := by
    apply Work.Homology.biprod_desc_lift
    · simp only [← homologyMap_comp, biprod.inl_fst, homologyMap_id]
    · simp only [← homologyMap_comp, biprod.inr_fst, homologyMap_zero]
    · simp only [← homologyMap_comp, biprod.inl_snd, homologyMap_zero]
    · simp only [← homologyMap_comp, biprod.inr_snd, homologyMap_id]
  inv_hom_id := by
    rw [biprod.lift_desc]
    simp only [← homologyMap_comp, ← homologyMap_add, biprod.total, homologyMap_id]

/-- The homology of `biprod.desc f g` is, under the canonical identification of
`H_k(A ⊞ B)` with `H_k(A) ⊞ H_k(B)`, the map `biprod.desc (H_k f) (H_k g)`. -/
theorem desc_homologyMap (A B C : ChainComplex (ModuleCat ℤ) ℕ) (f : A ⟶ C) (g : B ⟶ C)
    (k : ℕ) :
    biprod.desc (homologyMap f k) (homologyMap g k) =
      (homologyBiprodIso A B k).hom ≫ homologyMap (biprod.desc f g) k := by
  apply biprod.hom_ext'
  · simp only [homologyBiprodIso, biprod.inl_desc_assoc]
    rw [biprod.inl_desc, ← homologyMap_comp, biprod.inl_desc]
  · simp only [homologyBiprodIso, biprod.inr_desc_assoc]
    rw [biprod.inr_desc, ← homologyMap_comp, biprod.inr_desc]

/-- If `biprod.desc f g` is an isomorphism of chain complexes, then so is the map
`biprod.desc (H_k f) (H_k g)` that it induces in homology (under the canonical
identification `H_k(A ⊞ B) ≅ H_k(A) ⊞ H_k(B)` of `homologyBiprodIso`). -/
theorem isIso_desc_homologyMap {A B C : ChainComplex (ModuleCat ℤ) ℕ} {f : A ⟶ C} {g : B ⟶ C}
    (k : ℕ) [h : IsIso (biprod.desc f g)] :
    IsIso (biprod.desc (homologyMap f k) (homologyMap g k)) := by
  rw [desc_homologyMap]
  exact IsIso.comp_isIso' (Iso.isIso_hom (homologyBiprodIso A B k)) inferInstance

/-! ## The chain level splitting -/

/-- **The chain level decomposition.**  For a clopen `A`, the chain map
`C_*(A) ⊞ C_*(Aᶜ) ⟶ C_*(X)` induced by the two inclusions is an isomorphism
(with inverse `Work.Homology.beta`).

This is the isomorphism of `Work.Homology.SingChainClopenIso` in the form of an
`IsIso` instance, obtained from the degreewise splitting `Work.Homology.beta`
along with `Work.Homology.beta_comp_desc` and `Work.Homology.desc_comp_beta`. -/
theorem isIso_clopenChainDesc {X : TopCat} {A : Set ↑X} (hA : IsClopen A) :
    IsIso (biprod.desc (Work.Homology.singChainMap Work.Homology.ZMod (Work.Homology.incl A))
      (Work.Homology.singChainMap Work.Homology.ZMod
        (Work.Homology.incl (Aᶜ : Set ↑X)))) := by
  have hφs : IsIso (biprod.desc
      (Work.Homology.sChainMap Work.Homology.ZMod (Work.Homology.incl A))
      (Work.Homology.sChainMap Work.Homology.ZMod
        (Work.Homology.incl (Aᶜ : Set ↑X)))) := by
    have hcomp : ∀ n, IsIso ((biprod.desc
        (Work.Homology.sChainMap Work.Homology.ZMod (Work.Homology.incl A))
        (Work.Homology.sChainMap Work.Homology.ZMod
          (Work.Homology.incl (Aᶜ : Set ↑X)))).f n) := by
      intro n
      have hδ : (HomologicalComplex.biprodXIso (Work.Homology.sChain Work.Homology.ZMod (TopCat.of A))
            (Work.Homology.sChain Work.Homology.ZMod (TopCat.of (Aᶜ : Set ↑X))) n).inv
          ≫ (biprod.desc (Work.Homology.sChainMap Work.Homology.ZMod (Work.Homology.incl A))
              (Work.Homology.sChainMap Work.Homology.ZMod
                (Work.Homology.incl (Aᶜ : Set ↑X)))).f n
          = biprod.desc ((Work.Homology.sChainMap Work.Homology.ZMod
                (Work.Homology.incl A)).f n)
              ((Work.Homology.sChainMap Work.Homology.ZMod
                (Work.Homology.incl (Aᶜ : Set ↑X))).f n) := by
        apply biprod.hom_ext'
        · rw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv,
            HomologicalComplex.biprod_inl_desc_f, biprod.inl_desc]
        · rw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv,
            HomologicalComplex.biprod_inr_desc_f, biprod.inr_desc]
      have hIsIso : IsIso (biprod.desc ((Work.Homology.sChainMap Work.Homology.ZMod
            (Work.Homology.incl A)).f n)
          ((Work.Homology.sChainMap Work.Homology.ZMod
            (Work.Homology.incl (Aᶜ : Set ↑X))).f n)) :=
        IsIso.mk ⟨Work.Homology.beta Work.Homology.ZMod X A hA n,
          Work.Homology.desc_comp_beta Work.Homology.ZMod X A hA n,
          Work.Homology.beta_comp_desc Work.Homology.ZMod X A hA n⟩
      exact IsIso.of_isIso_fac_left hδ
    exact HomologicalComplex.Hom.isIso_of_components _
  exact hφs

/-! ## The main theorem -/

/-- **The split of singular homology along a clopen subset.**  For a clopen
`A ⊆ X` and any `k`, the map `H_k(A) ⊞ H_k(Aᶜ) ⟶ H_k(X)` induced by the two
inclusions is an isomorphism — the "homology of a disjoint union" isomorphism in
the direction that assembles the two pieces. -/
theorem clopenSplit_isIso {X : TopCat} {A : Set ↑X} (hA : IsClopen A) (k : ℕ) :
    CategoryTheory.IsIso (CategoryTheory.Limits.biprod.desc
      (Work.Homology.singHomologyMap Work.Homology.ZMod k (Work.Homology.incl A))
      (Work.Homology.singHomologyMap Work.Homology.ZMod k
        (Work.Homology.incl (Aᶜ : Set ↑X)))) := by
  have hφs : IsIso (biprod.desc
      (Work.Homology.sChainMap Work.Homology.ZMod (Work.Homology.incl A))
      (Work.Homology.sChainMap Work.Homology.ZMod
        (Work.Homology.incl (Aᶜ : Set ↑X)))) := isIso_clopenChainDesc hA
  exact isIso_desc_homologyMap (f := Work.Homology.sChainMap Work.Homology.ZMod
      (Work.Homology.incl A))
    (g := Work.Homology.sChainMap Work.Homology.ZMod (Work.Homology.incl (Aᶜ : Set ↑X)))
    k (h := hφs)

end

end Work.PieceHomology
