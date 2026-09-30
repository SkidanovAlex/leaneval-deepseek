import Submission.Work.Homology.Bridge
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.smallChains_homology_iso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Mayer–Vietoris, re-exported in the `Work.Homology` vocabulary

For `U, V ⊆ X` with `U ∪ V = X` open, the small-chains theorem gives the short exact sequence of
chain complexes `0 ⟶ C_*(U ∩ V) ⟶ C_*(U) ⊞ C_*(V) ⟶ C^{U,V}_*(X) ⟶ 0` and hence the
Mayer–Vietoris long exact sequence

`⋯ ⟶ H_k(U ∩ V) ⟶ H_k(U) ⊞ H_k(V) ⟶ H_k(X) ⟶ H_{k-1}(U ∩ V) ⟶ ⋯`

(`mv_exact_HX`, `mv_exact_Hrel`, `mv_exact_Hinter`); the first map is
`mvLeft = (incl_*, incl_*) : C_*(U ∩ V) → C_*(U) ⊞ C_*(V)`, the second is
`mvRightX = mvRight ≫ smallIso.hom` with `mvRight = (a, b) ↦ a - b`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Homology

noncomputable section

variable {X : TopCat}

/-- The small-chains quasi-isomorphism for an open cover. -/
theorem smallChains_homology_iso (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.smallToSing U V) n) :=
  Work.Cohomology.smallChains_homology_iso U V hU hV hcov n

/-- The Mayer–Vietoris short complex of the cover `{U, V}` is short exact. -/
theorem mvShort_shortExact (U V : Set X) :
    (Work.Cohomology.mvShort U V).ShortExact :=
  Work.Cohomology.mvShort_shortExact U V

/-- The Mayer–Vietoris complex with `H_n(X)` as its third term. -/
abbrev mvShortX (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (HomologicalComplex.homologyMap (Work.Cohomology.mvLeft U V) n)
    (Work.Cohomology.mvRightX U V hU hV hcov n) (by
      rw [Work.Cohomology.mvRightX, ← Category.assoc, ← HomologicalComplex.homologyMap_comp,
        Work.Cohomology.mvComp, HomologicalComplex.homologyMap_zero, zero_comp])

/-- The first two terms of the Mayer–Vietoris complex with the small chains as its third term. -/
abbrev mvShortSmall (U V : Set X) (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (HomologicalComplex.homologyMap (Work.Cohomology.mvLeft U V) n)
    (HomologicalComplex.homologyMap (Work.Cohomology.mvRight U V) n) (by
      rw [← HomologicalComplex.homologyMap_comp, Work.Cohomology.mvComp,
        HomologicalComplex.homologyMap_zero])

/-- **Mayer–Vietoris, exactness at `H_n(U) ⊞ H_n(V)`** for an open cover `U ∪ V = X`. -/
theorem mv_exact_HX (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (n : ℕ) : (mvShortX U V hU hV hcov n).Exact := by
  have e : mvShortSmall U V n ≅ mvShortX U V hU hV hcov n :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (Work.Cohomology.smallIso U V hU hV hcov n) (by simp [mvShortSmall, mvShortX])
      (by simp [mvShortSmall, mvShortX, Work.Cohomology.mvRightX])
  exact ShortComplex.exact_of_iso e (Work.Cohomology.mv_H_exact₂ U V n)

/-- The Mayer–Vietoris complex with `H_k(X)` as its second term (`k ≥ 1` indexing). -/
abbrev mvShortXRel (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (k : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (Work.Cohomology.mvRightX U V hU hV hcov (k + 1))
    (Work.Cohomology.mvδX U V hU hV hcov k) (by
      simp [Work.Cohomology.mvδX, Work.Cohomology.mvRightX, Category.assoc,
        Work.Cohomology.mv_comp_δ])

/-- The same complex with the small chains as its second term. -/
abbrev mvShortRel (U V : Set X) (k : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (HomologicalComplex.homologyMap (Work.Cohomology.mvRight U V) (k + 1))
    (Work.Cohomology.mvδ U V k) (Work.Cohomology.mv_comp_δ U V k)

/-- **Mayer–Vietoris, exactness at `H_k(X)`**: `H_k(U) ⊞ H_k(V) → H_k(X) → H_{k-1}(U ∩ V)`. -/
theorem mv_exact_Hrel (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (k : ℕ) : (mvShortXRel U V hU hV hcov k).Exact := by
  have e : mvShortRel U V k ≅ mvShortXRel U V hU hV hcov k :=
    ShortComplex.isoMk (Iso.refl (Work.Cohomology.HBiprod U V (k + 1)))
      (Work.Cohomology.smallIso U V hU hV hcov (k + 1))
      (Iso.refl (Work.Cohomology.HInter U V k))
      (by simp [mvShortRel, mvShortXRel, Work.Cohomology.mvRightX])
      (by simp [mvShortRel, mvShortXRel, Work.Cohomology.mvδX, Category.assoc])
  exact ShortComplex.exact_of_iso e (Work.Cohomology.mv_H_exact₃ U V k)


/-- The Mayer–Vietoris complex with `H_n(X)` as its first term (exactness at `H_n(U ∩ V)`). -/
abbrev mvShortXInter (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (Work.Cohomology.mvδX U V hU hV hcov n)
    (HomologicalComplex.homologyMap (Work.Cohomology.mvLeft U V) n) (by
      simp [Work.Cohomology.mvδX, Category.assoc, Work.Cohomology.mvδ_comp])

/-- The same complex with the small chains as its first term. -/
abbrev mvShortInter (U V : Set X) (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (Work.Cohomology.mvδ U V n)
    (HomologicalComplex.homologyMap (Work.Cohomology.mvLeft U V) n) (Work.Cohomology.mvδ_comp U V n)

/-- **Mayer–Vietoris, exactness at `H_{n+1}(X)`**: `H_{n+1}(X) → H_n(U ∩ V) → H_n(U) ⊞ H_n(V)`. -/
theorem mv_exact_Hinter (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (n : ℕ) : (mvShortXInter U V hU hV hcov n).Exact := by
  have e : mvShortInter U V n ≅ mvShortXInter U V hU hV hcov n :=
    ShortComplex.isoMk (Work.Cohomology.smallIso U V hU hV hcov (n + 1)) (Iso.refl _)
      (Iso.refl _) (by simp [mvShortInter, mvShortXInter, Work.Cohomology.mvδX, Category.assoc])
      (by simp [mvShortInter, mvShortXInter])
  exact ShortComplex.exact_of_iso e (Work.Cohomology.mv_H_exact₁ U V n)

end

end Work.Homology
