import Submission.Work.Tubular.TubeClass.Core
import Submission.Work.Orient.Closed
import Submission.Work.Orient.Bridge
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `H_8` of the complement of a point in a connected `8`-manifold

For a connected `Man8` `V` (a closed `8`-manifold with a locally generating fundamental class
`Man8.c`, `Submission/Work/ThomBordism/Interface.lean`) and a point `v₀ : V.pt`,

  `H_8(V.pt ∖ {v₀}; ℤ) = 0`.

This is the `n = 8` case of "the top homology of a connected non-compact `n`-manifold vanishes";
here it is a consequence of the *given* fundamental class, exactly as
`Submission/Work/ThomBordism/Interface.lean` announces:

> `Man8.c_fund` is what makes ... the map `H₈(M;ℤ) → H₈(M, M∖{x};ℤ)` an isomorphism for connected
> closed ...

The proof: the long exact sequence of the pair `(V.pt, V.pt∖{v₀})` identifies `H_8(V.pt∖{v₀})`
with the kernel of the localisation `e : H_8(V.pt) → H_8(V.pt, V.pt∖{v₀})`; a class of
`H_8(V.pt ∖ {v₀})` has vanishing local class at `v₀` (the composite `H_8(V∖{v₀}) → H_8(V) →
H_8(V,V∖{v₀})` is zero), and on a *connected* compact manifold the local class determines the class
(`Work.Orient.eq_zero_of_locClass_eq_zero_at`), so the class is `0`.

The `H_9(V.pt, V.pt∖{v₀}) = 0` used below is the general vanishing of the local homology above the
dimension (`Work.Cohomology.localHomology_charted`).
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular.TubeClass

noncomputable section

open Work.Cohomology

/-- **The complement of a point in a connected `Man8` has vanishing `H_8`.** -/
theorem isZero_homology_compl_point_man8 (V : Work.ThomBordism.Man8) [ConnectedSpace V.pt]
    (v₀ : V.pt) :
    IsZero ((singularChains ℤ (TopCat.of {y : V.pt | y ≠ v₀})).homology 8) := by
  set X : TopCat := TopCat.of V.pt with hX
  set A : Set X := {y | y ≠ v₀} with hA
  have h9 : IsZero ((relChains X A).homology 9) :=
    (localHomology_charted 8 (by norm_num) V.pt v₀ 9).2 (by norm_num)
  have hf : hPairδ X A 8 = 0 := IsZero.eq_zero_of_src h9 _
  have hrange : (ModuleCat.Hom.hom (hPairδ X A 8)).range = ⊥ := by
    rw [hf]; exact LinearMap.range_zero
  have hinj : Function.Injective
      ⇑(ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) 8)) := by
    have hker : (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (inclChains X A) 8)).ker = ⊥ := by
      rw [← (hPair_exact₁ X A 8).moduleCat_range_eq_ker, hrange]
    exact LinearMap.ker_eq_bot.mp hker
  have hzero : ∀ y, (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (cokernel.π (inclChains X A)) 8))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) 8)) y) = 0 := by
    intro y
    have h1 := (hPair_exact₂ X A 8).moduleCat_range_eq_ker
    have h2 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) 8)) y ∈
        LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) 8)) :=
      ⟨y, rfl⟩
    rw [h1] at h2
    exact (LinearMap.mem_ker).mp h2
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun y₁ y₂ => ?_⟩
  have key : ∀ y : (singularChains ℤ (TopCat.of A)).homology 8,
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) 8)) y = 0 := by
    intro y
    apply Work.Orient.eq_zero_of_locClass_eq_zero_at 8 (by norm_num) X _ v₀
    show Work.Orient.locClass X 8
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) 8)) y) v₀ = 0
    rw [Work.Orient.locClass_eq_relClass]
    exact hzero y
  have hz : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) 8)) (y₁ - y₂)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) 8)) 0 := by
    rw [map_sub, key y₁, key y₂, map_zero, sub_zero]
  exact sub_eq_zero.mp (hinj hz)

/-! ## The `0`-codimensional case: `ν ≅ V` -/

/-- The zero vector is normal, in the `8`-dimensional ambient form.  (The `k`-indexed
`Work.Tubular.zero_mem_normalSpace` does not unify with `EmbeddingData V 8` without an explicit `k`,
so this is recorded separately; note that `normalSpace E x = ⊥` for `E : EmbeddingData V 8`, by
`Work.Tubular.finrank_normalSpace`.) -/
theorem zero_mem_normalSpace_eight {V : Work.ThomBordism.Man8}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V 8)
    (x : V.pt) : (0 : Work.Tubular.Euc 8) ∈ Work.Tubular.normalSpace E x := by
  rw [Work.Tubular.mem_normalSpace_iff]
  intro u _
  simp

/-- **For a `0`-codimensional normal bundle every normal vector is zero**, so the normal total space
is the base. -/
theorem vec_eq_zero_of_embeddingData_eight {V : Work.ThomBordism.Man8}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V 8)
    (p : Work.Tubular.NormalTotal E) : p.1.2 = 0 := by
  have hbot : Work.Tubular.normalSpace E p.1.1 = ⊥ := by
    have hfr := Work.Tubular.finrank_normalSpace E p.1.1
    rw [show (8 : ℕ) - 8 = 0 from by norm_num] at hfr
    exact Submodule.finrank_eq_zero.mp hfr
  have hmem := p.2
  rw [hbot] at hmem
  simpa using hmem

/-- **The normal total space of a `0`-codimensional normal bundle is the base**, via `proj`. -/
noncomputable def normalTotalHomeoOfEight {V : Work.ThomBordism.Man8}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V 8) :
    Work.Tubular.NormalTotal E ≃ₜ V.pt :=
  { toFun := fun p => p.1.1
    invFun := fun x => ⟨(x, 0), zero_mem_normalSpace_eight E x⟩
    left_inv := fun p => by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact (vec_eq_zero_of_embeddingData_eight E p).symm
    right_inv := fun _ => rfl
    continuous_toFun := continuous_subtype_val.fst
    continuous_invFun := Continuous.subtype_mk
      (f := fun x : V.pt => ((x, 0) : V.pt × Work.Tubular.Euc 8))
      (continuous_id.prodMk continuous_const) (fun x => zero_mem_normalSpace_eight E x) }

end

end Work.Tubular.TubeClass
