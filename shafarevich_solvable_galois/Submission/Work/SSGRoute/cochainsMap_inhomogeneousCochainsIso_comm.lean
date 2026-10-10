import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.Work.SSGRoute.E0bBarChange
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the inhomogeneous cochains isomorphism under a group change

For a group homomorphism `f : H →* G`, a representation morphism `φ : Res(f)(A) ⟶ B`
(`A : Rep k G`, `B : Rep k H`), the cochain map `cochainsMap f φ` on inhomogeneous cochains is
compatible with the isomorphisms `inhomogeneousCochainsIso` identifying the inhomogeneous cochain
complex with `Hom(barComplex, -)`, in the sense that the square

```
inhomogeneousCochains A --cochainsMap f φ--> inhomogeneousCochains B
        |                                              |
        |  inhomogeneousCochainsIso A                  |  inhomogeneousCochainsIso B
        v                                              v
Hom(barComplex k G, A) --Ψ------------------> Hom(barComplex k H, B)
```

commutes, where `Ψ` is the `Hom(barComplex, -)`-level map determined by its values on the standard
generators by `barChange`.
-/

namespace Work.SSGRoute

open CategoryTheory Limits

section

variable {k : Type} [CommRing k]

/-- The `n`-th component of `groupCohomology.inhomogeneousCochainsIso` is `Rep.freeLift`: it sends
an inhomogeneous cochain `z : (Fin n → G) → A` to the representation morphism
`(Fin n → G) →₀ k[G] ⟶ A` determined by it. -/
lemma inhomogeneousCochainsIso_hom_f_apply (G : Type) [Group G] (A : Rep k G) (n : ℕ)
    (z : (Fin n → G) → A.V) :
    (ModuleCat.Hom.hom ((groupCohomology.inhomogeneousCochainsIso A).hom.f n)) z =
      Rep.freeLift k G A z := rfl

/-- The `n`-th component of `groupCohomology.cochainsMap f φ` is
`z ↦ fun y => φ (z (f ∘ y))`. -/
lemma cochainsMap_f_hom_apply (G H : Type) [Group G] [Group H] (f : H →* G)
    (A : Rep k G) (B : Rep k H) (φ : Rep.res f A ⟶ B) (n : ℕ)
    (z : (Fin n → G) → A.V) :
    (ModuleCat.Hom.hom ((groupCohomology.cochainsMap f φ).f n)) z =
      (fun y : Fin n → H => φ (z (f ∘ y))) := rfl

end

open CategoryTheory Limits in
theorem cochainsMap_inhomogeneousCochainsIso_comm (k : Type) [CommRing k] (G H : Type)
    [Group G] [Group H] (f : H →* G) (A : Rep k G) (B : Rep k H) (φ : Rep.res f A ⟶ B)
    (Ψ : (Rep.barComplex k G).linearYonedaObj k A ⟶ (Rep.barComplex k H).linearYonedaObj k B)
    (hΨ : ∀ n (g : (Rep.barComplex k G).X n ⟶ A),
        (Ψ.f n) g = SSGRoute.PTExt.barChange k G H f n ≫ (Rep.resFunctor f).map g ≫ φ) :
    groupCohomology.cochainsMap f φ ≫ (groupCohomology.inhomogeneousCochainsIso B).hom
      = (groupCohomology.inhomogeneousCochainsIso A).hom ≫ Ψ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [cochainsMap_f_hom_apply (k := k) G H f A B φ n z]
  rw [inhomogeneousCochainsIso_hom_f_apply (k := k) G A n z]
  rw [inhomogeneousCochainsIso_hom_f_apply (k := k) H B n (fun y : Fin n → H => φ (z (f ∘ y)))]
  rw [hΨ n (Rep.freeLift k G A z)]
  apply Rep.free_ext
  intro y
  rw [Rep.hom_comp, Rep.hom_comp]
  simp only [Representation.IntertwiningMap.comp_apply]
  rw [SSGRoute.PTExt.barChange_apply, map_one, Rep.resMap_hom_apply]
  simp only [Rep.freeLift, Rep.hom_ofHom, Representation.freeLift_single_single]
  rw [show (fun i : Fin n => f (y i)) = (f ∘ y) from rfl]
  simp

end Work.SSGRoute
