import Mathlib
import Submission.Work.Whitney.Signed.ModelSide

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-!
# Bookkeeping for the model side

Small, isolated identities used by the model-side evaluation
(`Submission/Work/Whitney/Signed/ModelSide.lean`), stated separately so that each is elaborated in
its own (small) context:

* `pushChain_id`, `pushChain` of an identity map;
* `capFull_pushChain_eq`, the boundary of the cap: pushing a chain along `capFull` is the same as
  pushing it along `capMapPairSph` and then along `sphFlat` (and including the sphere bundle);
* `sphUnflat_pushChain_sphFlat`, the round trip `sphUnflat ∘ sphFlat`;
* `sphPushCochain_pushChain`, the evaluation of the pushed cochain on a pushed chain;
* `isSmallChain_sphUnflat`, the band carries the band.
-/

namespace Work.Whitney

open Work.Thom Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

/-- The band, seen inside the sphere bundle `↥(Sph Y (k+1))`. -/
def BandInA (Y : Type) [TopologicalSpace Y] (k : ℕ) : Set ↥(Sph Y (k + 1)) :=
  {x | sphUnflat Y k x ∈ SphB Y k}

/-- Push-forwards along the identity are the identity. -/
theorem pushChain_id (X : TopCat) (n : ℕ) (c : (singularChains ℤ X).X n) :
    pushChain X X (𝟙 X) n c = c := by
  have hgen : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌,
      pushChain X X (𝟙 X) n (gen X n σ) = gen X n σ := by
    intro σ
    rw [pushChain_gen]
    rfl
  let Q : Submodule ℤ ((singularChains ℤ X).X n) :=
    LinearMap.ker ((pushChain X X (𝟙 X) n) - LinearMap.id)
  have hQ : Q = ⊤ := by
    refine mem_of_genSSet (TopCat.toSSet.obj X) n Q ?_
    intro σ
    show (pushChain X X (𝟙 X) n) (genSSet (TopCat.toSSet.obj X) n σ) - id _ = 0
    rw [sub_eq_zero]
    exact hgen σ
  have hmem : c ∈ Q := by rw [hQ]; exact Submodule.mem_top
  exact sub_eq_zero.mp hmem

/-- **The cap boundary identity**: pushing a chain along the cap `capFull` agrees with pushing along
`capMapPairSph`, then `sphFlat`, then including the sphere bundle in the total space. -/
theorem capFull_pushChain_eq (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (B : (singularChains ℤ (TopCat.of (Y × MBall k))).X k) :
    pushChain (TopCat.of (Y × MBall k))
        (TopCat.of (Y × EuclideanSpace ℝ (Fin (k + 1))))
        (TopCat.ofHom (capFull Y k)) k B
      = pushChain (TopCat.of ↥(Sph Y (k + 1)))
          (TopCat.of (Y × EuclideanSpace ℝ (Fin (k + 1))))
          (subtypeIncl (TopCat.of (Y × EuclideanSpace ℝ (Fin (k + 1)))) (Sph Y (k + 1))) k
          (pushChain (TopCat.of (Y × MBall k)) (TopCat.of ↥(Sph Y (k + 1)))
            (TopCat.ofHom ((sphFlat Y k).comp (capMapPairSph Y k))) k B) := by
  rw [pushChain_comp (TopCat.of (Y × MBall k)) (TopCat.of ↥(Sph Y (k + 1)))
    (TopCat.of (Y × EuclideanSpace ℝ (Fin (k + 1))))
    (TopCat.ofHom ((sphFlat Y k).comp (capMapPairSph Y k)))
    (subtypeIncl (TopCat.of (Y × EuclideanSpace ℝ (Fin (k + 1)))) (Sph Y (k + 1))) k B]
  congr 1

/-- **The round trip** `sphUnflat ∘ sphFlat` on chains is the identity. -/
theorem sphUnflat_pushChain_sphFlat (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (c : (singularChains ℤ (TopCat.of (Y × MSph (k + 1)))).X k) :
    pushChain (TopCat.of ↥(Sph Y (k + 1))) (TopCat.of (Y × MSph (k + 1)))
        (TopCat.ofHom (sphUnflat Y k)) k
        (pushChain (TopCat.of (Y × MSph (k + 1))) (TopCat.of ↥(Sph Y (k + 1)))
          (TopCat.ofHom (sphFlat Y k)) k c) = c := by
  rw [pushChain_comp]
  have hmap : TopCat.ofHom (sphFlat Y k) ≫ TopCat.ofHom (sphUnflat Y k)
      = 𝟙 (TopCat.of (Y × MSph (k + 1))) := by
    apply TopCat.hom_ext
    exact sphUnflat_comp_sphFlat Y k
  rw [hmap, pushChain_id]


/-- The push-forward of a simplex of `A` is an `A`-small simplex of `X`. -/
theorem isSmall_subtypeIncl_app {X : TopCat} (A : Set X) {n : ℕ}
    (τ : Simplex (TopCat.of A) n) :
    IsSmall A (∅ : Set X)
      ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) τ) := by
  rw [isSmall_iff]
  left
  intro y
  rintro ⟨z, rfl⟩
  rw [sdMap_map]
  exact (sdMap n τ z).2

/-- **A cochain vanishing on the `A`-small generators is relative to `A`.** -/
theorem mem_relKern_of_genEval_zero {X : TopCat} (A : Set X) {n : ℕ}
    (u : Cochain ℤ (TopCat.toSSet.obj X) n)
    (h : ∀ σ : Simplex X n, IsSmall A (∅ : Set X) σ → u (gen X n σ) = 0) :
    u ∈ relKern ℤ X A n := by
  rw [relKern, LinearMap.mem_ker]
  have hgoal : (((restr ℤ X A).f n).hom u) = 0 := by
    apply genEval_ext
    intro τ
    show (show Cochain ℤ (TopCat.toSSet.obj (TopCat.of A)) n from ((restr ℤ X A).f n).hom u)
      (gen (TopCat.of A) n τ) = 0
    rw [show (show Cochain ℤ (TopCat.toSSet.obj (TopCat.of A)) n from ((restr ℤ X A).f n).hom u)
        = (show Cochain ℤ (TopCat.toSSet.obj X) n from u).comp
            ((chainMap ℤ (TopCat.of A) X (subtypeIncl X A)).f n).hom from rfl]
    rw [LinearMap.comp_apply]
    show (show Cochain ℤ (TopCat.toSSet.obj X) n from u)
      (pushChain (TopCat.of A) X (subtypeIncl X A) n (gen (TopCat.of A) n τ)) = 0
    rw [pushChain_gen]
    exact h _ (isSmall_subtypeIncl_app A τ)
  exact hgoal

/-- **The evaluation of the pushed cochain on a chain of the sphere bundle.** -/
theorem sphPushCochain_pushChain (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (z : Cochain ℤ (ssB (Y × MSph (k + 1))) k)
    (c : (singularChains ℤ (TopCat.of ↥(Sph Y (k + 1)))).X k) :
    (sphPushCochain Y k z) c
      = z (pushChain (TopCat.of ↥(Sph Y (k + 1))) (TopCat.of (Y × MSph (k + 1)))
          (TopCat.ofHom (sphUnflat Y k)) k c) := by
  have h := cochain_push_apply (TopCat.ofHom (sphUnflat Y k)) k z c
  exact h

/-- **The pushed cochain is relative to the band.** -/
theorem sphPushCochain_mem_relKern (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (z : Cochain ℤ (ssB (Y × MSph (k + 1))) k)
    (hz : z ∈ relKern ℤ (TopCat.of (Y × MSph (k + 1))) (SphB Y k) k) :
    (sphPushCochain Y k z) ∈ relKern ℤ (TopCat.of ↥(Sph Y (k + 1))) (BandInA Y k) k := by
  rw [relKern, LinearMap.mem_ker]
  have hgoal : (((restr ℤ (TopCat.of ↥(Sph Y (k + 1))) (BandInA Y k)).f k).hom
      (sphPushCochain Y k z)) = 0 := by
    apply genEval_ext
    intro τ
    show (show Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(BandInA Y k))) k from
        ((restr ℤ (TopCat.of ↥(Sph Y (k + 1))) (BandInA Y k)).f k).hom (sphPushCochain Y k z))
      (gen (TopCat.of ↥(BandInA Y k)) k τ) = 0
    rw [show (show Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(BandInA Y k))) k from
        ((restr ℤ (TopCat.of ↥(Sph Y (k + 1))) (BandInA Y k)).f k).hom (sphPushCochain Y k z))
        = (show Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Sph Y (k + 1)))) k from
            sphPushCochain Y k z).comp
            ((chainMap ℤ (TopCat.of (BandInA Y k)) (TopCat.of ↥(Sph Y (k + 1)))
              (subtypeIncl (TopCat.of ↥(Sph Y (k + 1))) (BandInA Y k))).f k).hom from rfl]
    rw [LinearMap.comp_apply]
    show (show Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Sph Y (k + 1)))) k from
        sphPushCochain Y k z)
      (pushChain (TopCat.of (BandInA Y k)) (TopCat.of ↥(Sph Y (k + 1)))
        (subtypeIncl (TopCat.of ↥(Sph Y (k + 1))) (BandInA Y k)) k
        (gen (TopCat.of (BandInA Y k)) k τ)) = 0
    rw [pushChain_gen]
    show (sphPushCochain Y k z) (gen (TopCat.of ↥(Sph Y (k + 1))) k
      ((TopCat.toSSet.map (subtypeIncl (TopCat.of ↥(Sph Y (k + 1))) (BandInA Y k))).app
        (Opposite.op ⦋k⦌) τ)) = 0
    rw [← pushChain_gen]
    rw [sphPushCochain_pushChain]
    rw [pushChain_comp]
    rw [pushChain_gen]
    have hσ' : IsSmall (SphB Y k) (∅ : Set (Y × MSph (k + 1)))
        ((TopCat.toSSet.map (subtypeIncl (TopCat.of ↥(Sph Y (k + 1))) (BandInA Y k) ≫
          TopCat.ofHom (sphUnflat Y k))).app (Opposite.op ⦋k⦌) τ) := by
      rw [isSmall_iff]
      left
      intro y
      rintro ⟨w, rfl⟩
      rw [sdMap_map]
      exact (sdMap k τ w).2
    obtain ⟨τ', hτ'⟩ := exists_simplex_subtypeIncl_of_isSmall hσ'
    rw [← hτ']
    show kronecker ℤ (ssB (Y × MSph (k + 1))) z
      (((ssB (Y × MSph (k + 1))).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        ((TopCat.toSSet.map (subtypeIncl (TopCat.of (Y × MSph (k + 1))) (SphB Y k))).app
          (Opposite.op ⦋k⦌) τ')).hom 1) = 0
    rw [kronecker_gen]
    exact genEval_eq_zero_of_mem_relKern ℤ (TopCat.of (Y × MSph (k + 1))) (SphB Y k) z hz τ'
  exact hgoal

/-- **The cap pull-back of the pushed cochain is relative to the disc boundary.** -/
theorem capMapPairSph_pull_mem_relKern (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (z : Cochain ℤ (ssB (Y × MSph (k + 1))) k)
    (hz : z ∈ relKern ℤ (TopCat.of (Y × MSph (k + 1))) (SphB Y k) k) :
    (((dualChainMap ℤ (TopCat.of (Y × MBall k)) (TopCat.of (Y × MSph (k + 1)))
      (TopCat.ofHom (capMapPairSph Y k))).f k).hom z)
      ∈ relKern ℤ (TopCat.of (Y × MBall k)) (DiscB Y k) k := by
  refine mem_relKern_of_genEval_zero (DiscB Y k)
    (show Cochain ℤ (TopCat.toSSet.obj (TopCat.of (Y × MBall k))) k from
      ((dualChainMap ℤ (TopCat.of (Y × MBall k)) (TopCat.of (Y × MSph (k + 1)))
        (TopCat.ofHom (capMapPairSph Y k))).f k).hom z) ?_
  intro σ hσ
  show (show Cochain ℤ (TopCat.toSSet.obj (TopCat.of (Y × MBall k))) k from
      ((dualChainMap ℤ (TopCat.of (Y × MBall k)) (TopCat.of (Y × MSph (k + 1)))
        (TopCat.ofHom (capMapPairSph Y k))).f k).hom z)
    (gen (TopCat.of (Y × MBall k)) k σ) = 0
  have hpull : (show Cochain ℤ (TopCat.toSSet.obj (TopCat.of (Y × MBall k))) k from
      ((dualChainMap ℤ (TopCat.of (Y × MBall k)) (TopCat.of (Y × MSph (k + 1)))
        (TopCat.ofHom (capMapPairSph Y k))).f k).hom z)
      (gen (TopCat.of (Y × MBall k)) k σ)
      = z (pushChain (TopCat.of (Y × MBall k)) (TopCat.of (Y × MSph (k + 1)))
          (TopCat.ofHom (capMapPairSph Y k)) k (gen (TopCat.of (Y × MBall k)) k σ)) := by
    show cochainLM ℤ (TopCat.of (Y × MBall k)) k
      (((dualChainMap ℤ (TopCat.of (Y × MBall k)) (TopCat.of (Y × MSph (k + 1)))
        (TopCat.ofHom (capMapPairSph Y k))).f k).hom z)
      (gen (TopCat.of (Y × MBall k)) k σ)
      = z (pushChain (TopCat.of (Y × MBall k)) (TopCat.of (Y × MSph (k + 1)))
          (TopCat.ofHom (capMapPairSph Y k)) k (gen (TopCat.of (Y × MBall k)) k σ))
    exact (cochain_push_apply (TopCat.ofHom (capMapPairSph Y k)) k z
      (gen (TopCat.of (Y × MBall k)) k σ)).symm
  rw [hpull, pushChain_gen]
  have hσ' : IsSmall (SphB Y k) (∅ : Set (Y × MSph (k + 1)))
      ((TopCat.toSSet.map (TopCat.ofHom (capMapPairSph Y k))).app (Opposite.op ⦋k⦌) σ) := by
    rw [isSmall_iff]
    left
    intro y
    rintro ⟨w, rfl⟩
    rw [sdMap_map]
    refine CleanA.capMapPairSph_mem_mLower k (sdMap k σ w) ?_
    rw [isSmall_iff] at hσ
    exact hσ.elim (fun h => h ⟨w, rfl⟩) (fun h => absurd ⟨w, rfl⟩ (fun hc => h hc))
  obtain ⟨τ, hτ⟩ := exists_simplex_subtypeIncl_of_isSmall hσ'
  rw [← hτ]
  show kronecker ℤ (ssB (Y × MSph (k + 1))) z
    (((ssB (Y × MSph (k + 1))).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      ((TopCat.toSSet.map (subtypeIncl (TopCat.of (Y × MSph (k + 1))) (SphB Y k))).app
        (Opposite.op ⦋k⦌) τ)).hom 1) = 0
  rw [kronecker_gen]
  exact genEval_eq_zero_of_mem_relKern ℤ (TopCat.of (Y × MSph (k + 1))) (SphB Y k) z hz τ

end

end Work.Whitney
