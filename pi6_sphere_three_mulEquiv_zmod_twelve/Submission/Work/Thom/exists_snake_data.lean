import Mathlib
import Submission.Work.Cohomology.relCohMV_honest_les

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The snake-lemma data of the relative Mayer–Vietoris sequence

Given a short exact sequence of cochain complexes

`0 ⟶ A --f--> B --g--> C ⟶ 0`

and a cocycle `z` in degree `k` of `C`, the snake construction produces a lift `zt ∈ B^k` of `z`
and a cocycle `w ∈ A^{k+1}` whose `f`-image is the differential of `zt`.

Here this is applied to the honest relative Mayer–Vietoris sequence
`0 → C^*(C^{U,V}(X,A)) → C^*(U,U∩A) ⊞ C^*(V,V∩A) → C^*(U∩V,U∩V∩A) → 0`
of `Work.Cohomology.hmv_shortExact`, giving `Work.Thom.exists_snake_data`.

The abstract statement `exists_lift_snake_data` is proved by reducing to the degreewise short
exactness of a short exact sequence of complexes
(`HomologicalComplex.shortExact_iff_degreewise_shortExact`).
-/

open CategoryTheory

namespace Work.Thom

/-- **The snake-lemma data for a short exact sequence of cochain complexes.** Every cocycle in the
third term lifts to a cochain of the middle term whose differential is the `f`-image of a cocycle of
the first term. -/
lemma exists_lift_snake_data {A B C : CochainComplex (ModuleCat ℤ) ℕ} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact)
    (k : ℕ) (z : C.X k) (hz : C.d k (k + 1) z = 0) :
    ∃ (zt : B.X k) (w : A.X (k + 1)),
      g.f k zt = z ∧ f.f (k + 1) w = B.d k (k + 1) zt ∧ A.d (k + 1) (k + 2) w = 0 := by
  -- degreewise short exactness of the sequence of complexes
  have hSd : ∀ i : ℕ, ((ShortComplex.mk f g hfg).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) i)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hS
  -- a lift of `z` along the surjective `g`
  have hEpik : Epi (g.f k) := (hSd k).epi_g
  obtain ⟨zt, hzt⟩ := (ModuleCat.epi_iff_surjective (g.f k)).1 hEpik z
  -- its differential is killed by `g`
  have key : ModuleCat.Hom.hom (g.f (k + 1)) (ModuleCat.Hom.hom (B.d k (k + 1)) zt) = 0 := by
    have hcomm := congrArg (fun (φ : B.X k ⟶ C.X (k + 1)) => ModuleCat.Hom.hom φ zt)
      (HomologicalComplex.Hom.comm g k (k + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
    rw [hzt, hz] at hcomm
    exact hcomm.symm
  -- exactness at the middle term produces the preimage `w`
  have hex := (ShortComplex.moduleCat_exact_iff ((ShortComplex.mk f g hfg).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) (k + 1)))).1
      (hSd (k + 1)).exact
  obtain ⟨w, hw⟩ : ∃ w : A.X (k + 1),
      ModuleCat.Hom.hom (f.f (k + 1)) w = ModuleCat.Hom.hom (B.d k (k + 1)) zt :=
    hex (ModuleCat.Hom.hom (B.d k (k + 1)) zt) key
  refine ⟨zt, w, hzt, hw, ?_⟩
  -- `w` is a cocycle, by injectivity of `f` in degree `k + 2`
  have hinj : Function.Injective (ModuleCat.Hom.hom (f.f (k + 2))) :=
    (ModuleCat.mono_iff_injective (f.f (k + 2))).1 (hSd (k + 2)).mono_f
  apply hinj
  rw [map_zero]
  have hcomm := congrArg (fun (φ : A.X (k + 1) ⟶ B.X (k + 2)) => ModuleCat.Hom.hom φ w)
    (HomologicalComplex.Hom.comm f (k + 1) (k + 2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [hw] at hcomm
  have hdd := congrArg (fun (φ : B.X k ⟶ B.X (k + 2)) => ModuleCat.Hom.hom φ zt)
    (HomologicalComplex.d_comp_d B k (k + 1) (k + 2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hdd
  rw [hdd] at hcomm
  exact hcomm.symm

/-- **The snake data of the relative Mayer–Vietoris sequence.** A cocycle of
`C^*(U ∩ V, U ∩ V ∩ A)` (the last term of the honest relative Mayer–Vietoris sequence) lifts to a
cochain of `C^*(U,U∩A) ⊞ C^*(V,V∩A)` whose differential is the image under `hmvF` of a cocycle of
`C^*(C^{U,V}(X,A))`. -/
theorem exists_snake_data (X : TopCat) (A U V : Set X) (k : ℕ)
    (z : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X A U V)).X k)
    (hz : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X A U V)).d k (k + 1) z = 0) :
    ∃ (zt : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V) ⊞
        Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V)).X k)
      (w : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)).X (k + 1)),
      (Work.Cohomology.hmvG X A U V).f k zt = z ∧
      (Work.Cohomology.hmvF X A U V).f (k + 1) w
        = (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V) ⊞
            Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V)).d k (k + 1) zt ∧
      ModuleCat.Hom.hom ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)).d (k + 1) (k + 2)) w = 0 := by
  exact exists_lift_snake_data (Work.Cohomology.hmvF X A U V) (Work.Cohomology.hmvG X A U V)
    (Work.Cohomology.hmv_comp X A U V) (Work.Cohomology.hmv_shortExact X A U V) k z hz

end Work.Thom
