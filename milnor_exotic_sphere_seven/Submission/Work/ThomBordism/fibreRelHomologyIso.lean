import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.nfRead_ne_zero
import Submission.Work.Cohomology.euclideanLocalHomologyTop
import Submission.Work.Cohomology.relChainsHomeomorphCompat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative homology of the fibre pair of the normal bundle is `ℤ` in degree `k`

For an embedding `E : V ↪ ℝ^{8+k}` of the smooth `8`-manifold `V` and a point `x ∈ V`, the fibre of
the normal bundle over `x` is a `k`-dimensional real vector space `ν_x = (T_x)^⊥`, and the *fibre
pair* `(ν_x, ν_x ∖ 0)` is the pair `(ℤ^k, ℤ^k ∖ 0)` up to homeomorphism of pairs.  Its `k`-th
relative singular homology is therefore `ℤ`:

  `H_k(ν_x, ν_x ∖ 0; ℤ) ≅ ℤ`.

This is the base case of the Thom isomorphism in homology, and the homology companion of
`Work.ThomBordism.nfRelCohIso` (the same statement for relative *cohomology*).

The proof is a transport of `H_k(ℝ^k, ℝ^k∖0; ℤ) ≅ ℤ`
(`Work.Cohomology.euclideanLocalHomologyTop`) along an explicit homeomorphism of pairs: the fibre
`nfSet E x` of the normal total space over `x` is the normal space `ν_x` (via
`vec_mem_normalSpace_of_mem_nfSet`), which is `k`-dimensional (`Work.Tubular.finrank_normalSpace`),
hence linearly — and continuously — isomorphic to `EuclideanSpace ℝ (Fin k)`; the punctured fibre
`nfPunct E x` corresponds to `ℝ^k ∖ {0}` under that map.  Relative homology is invariant under a
homeomorphism of pairs (`Work.Cohomology.relChainsHomeomorphCompat`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism

theorem fibreRelHomologyIso {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Nonempty (↥((Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (Work.ThomBordism.nfPunct E x)).homology k) ≃ₗ[ℤ] ℤ) := by
  classical
  -- the normal space `ν_x` is `k`-dimensional, hence linearly isomorphic to `ℝ^k`
  obtain ⟨L⟩ : Nonempty (↥(Work.Tubular.normalSpace E x) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :=
    ⟨LinearEquiv.ofFinrankEq _ _ (by rw [Work.Tubular.finrank_normalSpace E x]; simp)⟩
  -- the fibre of the normal total space over `x` is the normal space `ν_x`
  let F : ↥(nfSet E x) → EuclideanSpace ℝ (Fin k) :=
    fun p => L ⟨Work.Tubular.NormalTotal.vec p.1, vec_mem_normalSpace_of_mem_nfSet E p⟩
  let G : EuclideanSpace ℝ (Fin k) → ↥(nfSet E x) :=
    fun v => ⟨⟨(x, (L.symm v).1), (L.symm v).2⟩, rfl⟩
  have hGF : Function.LeftInverse G F := by
    intro p
    apply Subtype.ext
    apply Work.Tubular.NormalTotal.ext
    show (x, (L.symm (L ⟨Work.Tubular.NormalTotal.vec p.1, _⟩)).1) = p.1.1
    rw [LinearEquiv.symm_apply_apply]
    exact Prod.ext (by simpa [Work.Tubular.NormalTotal.proj] using (p.2).symm) rfl
  have hFG : Function.RightInverse G F := by
    intro v
    show L ⟨(L.symm v).1, (L.symm v).2⟩ = v
    conv_lhs => rw [show (⟨(L.symm v).1, (L.symm v).2⟩ : ↥(Work.Tubular.normalSpace E x))
      = L.symm v from rfl]
    exact L.apply_symm_apply v
  have hFc : Continuous F :=
    (LinearMap.continuous_of_finiteDimensional L.toLinearMap).comp
      (Continuous.subtype_mk
        ((Work.Tubular.NormalTotal.continuous_vec E).comp continuous_subtype_val) _)
  have hGc : Continuous G := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    refine continuous_const.prodMk ?_
    exact continuous_subtype_val.comp
      (LinearMap.continuous_of_finiteDimensional L.symm.toLinearMap)
  let e : ↥(nfSet E x) ≃ₜ EuclideanSpace ℝ (Fin k) :=
    Homeomorph.mk ⟨F, G, hGF, hFG⟩ hFc hGc
  -- the punctured fibre corresponds to `ℝ^k ∖ {0}`
  have he' : ∀ p : ↥(nfSet E x),
      (e p ≠ 0) ↔ (Work.Tubular.NormalTotal.vec p.1 ≠ 0) := by
    intro p
    change ¬ (e p = 0) ↔ (Work.Tubular.NormalTotal.vec p.1 ≠ 0)
    rw [show e p = L ⟨Work.Tubular.NormalTotal.vec p.1,
      vec_mem_normalSpace_of_mem_nfSet E p⟩ from rfl]
    rw [not_congr (LinearEquiv.map_eq_zero_iff L)]
    constructor
    · intro h h0; exact h (Subtype.ext h0)
    · intro h h0; exact h (congrArg Subtype.val h0)
  have he : ∀ p : ↥(nfSet E x),
      p ∈ nfPunct E x ↔ e p ∈ ({v : EuclideanSpace ℝ (Fin k) | v ≠ 0}) :=
    fun p => (he' p).symm
  -- transport the homology computation of `(ℝ^k, ℝ^k∖0)`
  obtain ⟨h1⟩ := Work.Cohomology.relChainsHomeomorphCompat (↥(nfSet E x))
    (EuclideanSpace ℝ (Fin k)) (nfPunct E x) {v : EuclideanSpace ℝ (Fin k) | v ≠ 0} e he k
  obtain ⟨h2⟩ := Work.Cohomology.euclideanLocalHomologyTop k hk
  exact ⟨(h1 ≪≫ h2).toLinearEquiv⟩

end Work.ThomBordism
