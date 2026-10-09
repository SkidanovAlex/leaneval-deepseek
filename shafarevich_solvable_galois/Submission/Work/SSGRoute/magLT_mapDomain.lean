import Mathlib
import Submission.Work.SSGRoute.prop5.magnus_leadingTerm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000

namespace Work.SSGRoute

open Work.SSGRoute.prop5

/-!
# Naturality of the Magnus leading term under a re-labelling of the generators

Let `FreeAssoc X = ℤ[FreeMonoid X]` be the free associative algebra on `X` and let
`fil X N` be the ideal spanned by the words of length `≥ N`.  A bijection `σ : X ≃ X`
induces a ring endomorphism `φ = MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map σ)`
of `FreeAssoc X`, which preserves word lengths and hence maps `fil X N` into itself.
It therefore descends to an endomorphism `qmap σ N` of the truncated algebra
`FreeAssoc X ⧸ fil X N`.

The two ingredients proved here are

* `fil_map_le` : `φ (fil X N) ⊆ fil X N` (lengths are preserved);
* `magnus_mapDomain` : the Magnus map is natural, i.e. the square
  `FreeGroup X --magnus--> (FreeAssoc X ⧸ fil X N)ˣ`
  commutes with `freeGroupCongr σ` on the left and `Units.map (qmap σ N)` on the right.

From these we deduce `magLT_mapDomain`: the leading term `magLT X j z` is natural in the
generators, so any representative `a` of it modulo `fil X (j+1)` maps to a representative
of `magLT X j (freeGroupCongr σ z)`.
-/

/-- The word-length filtration is preserved by the ring endomorphism of `FreeAssoc X`
induced by a map of the generators: `FreeMonoid.map` preserves word length. -/
lemma fil_map_le {X : Type*} (σ : X ≃ X) (N : ℕ) :
    (Work.SSGRoute.prop5.fil X N).map
        (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X))) ≤
      Work.SSGRoute.prop5.fil X N := by
  rw [Work.SSGRoute.prop5.fil, Ideal.map_span]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨x, ⟨w, hw, rfl⟩, rfl⟩
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  refine Ideal.subset_span ⟨FreeMonoid.map σ w, ?_, rfl⟩
  simp only [FreeMonoid.length, FreeMonoid.toList_map, List.length_map]
  exact hw

/-- The endomorphism of the truncated free associative algebra `FreeAssoc X ⧸ fil X N`
induced by a bijection `σ` of the generators. -/
noncomputable def qmap {X : Type*} (σ : X ≃ X) (N : ℕ) :
    (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N) →+*
      (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N) :=
  Ideal.Quotient.lift (Work.SSGRoute.prop5.fil X N)
    ((Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X N)).comp
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X))))
    (fun a ha => by
      rw [RingHom.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (fil_map_le σ N (Ideal.mem_map_of_mem
          (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X))) ha)))

/-- `qmap` computes on representatives. -/
lemma qmap_mk {X : Type*} (σ : X ≃ X) (N : ℕ) (y : Work.SSGRoute.prop5.FreeAssoc X) :
    qmap σ N (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X N) y)
      = Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X N)
          (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) y) := by
  rw [qmap, Ideal.Quotient.lift_mk, RingHom.comp_apply]

/-- `qmap` sends the Magnus image of a generator `of x` to the Magnus image of `of (σ x)`. -/
lemma qmap_magnus_of {X : Type*} (σ : X ≃ X) (N : ℕ) (x : X) :
    qmap σ N
        ((magnus X N (FreeGroup.of x) :
            (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)
      = ((magnus X N (FreeGroup.of (σ x)) :
            (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N) := by
  rw [magnus_of X N x, magnus_of X N (σ x), map_add, map_one, qmap_mk,
      MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, FreeMonoid.map_of]

/-- Naturality of the Magnus map: re-labelling the generators commutes with the Magnus
embedding (modulo the length filtration). -/
lemma magnus_mapDomain {X : Type*} (σ : X ≃ X) (N : ℕ) (z : FreeGroup X) :
    Units.map (qmap σ N) (magnus X N z) = magnus X N (FreeGroup.freeGroupCongr σ z) := by
  have hhom : (Units.map (qmap σ N)).comp (magnus X N)
      = (magnus X N).comp (FreeGroup.freeGroupCongr σ).toMonoidHom := by
    apply (FreeGroup.lift).symm.injective
    ext x
    simp only [FreeGroup.lift_symm_apply, MonoidHom.comp_apply, Function.comp_apply]
    rw [show (FreeGroup.freeGroupCongr σ).toMonoidHom (FreeGroup.of x)
          = FreeGroup.freeGroupCongr σ (FreeGroup.of x) from rfl]
    rw [FreeGroup.freeGroupCongr_apply, FreeGroup.map.of, Units.coe_map]
    change qmap σ N ((magnus X N (FreeGroup.of x) :
        (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)
      = ((magnus X N (FreeGroup.of (σ x)) :
          (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)
    exact qmap_magnus_of σ N x
  exact DFunLike.congr_fun hhom z

theorem magLT_mapDomain {X : Type*} (σ : X ≃ X) (j : ℕ) (hj : 1 ≤ j) (z : FreeGroup X)
    (a : Work.SSGRoute.prop5.FreeAssoc X)
    (ha : Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1)) a = Work.SSGRoute.prop5.magLT X j z) :
    Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1))
        (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) a)
      = Work.SSGRoute.prop5.magLT X j (FreeGroup.freeGroupCongr σ z) := by
  have hmk : qmap σ (j + 1) (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1)) a)
      = Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1))
          (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) a) :=
    qmap_mk σ (j + 1) a
  rw [← hmk, ha]
  have key := magnus_mapDomain σ (j + 1) z
  have hcoe : qmap σ (j + 1)
        ((magnus X (j + 1) z :
            (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))
      = ((Units.map (qmap σ (j + 1)) (magnus X (j + 1) z) :
            (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1)) := by
    rw [Units.coe_map]
    rfl
  rw [Work.SSGRoute.prop5.magLT, Work.SSGRoute.prop5.magLT, map_sub, map_one, hcoe, key]

end Work.SSGRoute
