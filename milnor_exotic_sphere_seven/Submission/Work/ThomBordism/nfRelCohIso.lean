import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.nfGenBasic
import Submission.Work.Thom.ATools
import Submission.Work.Thom.relCohomology_euclidean_punctured
import Submission.Work.Tubular.Rank

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre pair of the normal bundle has free relative cohomology of rank one in degree `k`

`Work.ThomBordism.nfRelCohIso` computes the relative cohomology of the *fibre pair* of the normal
bundle: for `p ∈ ν_x` the fibre of the normal bundle of an embedding `E : V ↪ ℝ^{8+k}` at the point
`x` of the `8`-manifold `V`,

  `H^k(ν_x, ν_x ∖ 0; ℤ) ≅ ℤ`,

the base case of the Thom isomorphism.  This is what makes the *oriented fibre generator*
`Work.ThomBordism.nfGen` (the pullback of `Work.ThomBordism.stdThomGen` along the frame reading
`Work.ThomBordism.nfRead`) a *basis*, hence the fibre comparisons of the last mile of
`Work.ThomBordism.thomRational` a comparison of numbers.

The proof is a transport of the already-computed `H^k(ℝ^k, ℝ^k∖0; ℤ) = ℤ`
(`Work.Thom.relCohomology_euclidean_punctured`) along an explicit homeomorphism of pairs:

* `℥(ν_x) := ↥(nfSet E x) ≅ ↥(normalSpace E x)`, `p ↦ vec p.1` (the fibre of the normal total space
  over `x` is exactly the normal space `ν_x = (T_x)^⊥`, cf.
  `Work.ThomBordism.vec_mem_normalSpace_of_mem_nfSet`);
* `↥(normalSpace E x) ≅ ℝ^k` by any `ℝ`-linear equivalence — one exists because
  `Module.finrank ℝ ν_x = k` (`Work.Tubular.finrank_normalSpace`), and linear maps between
  finite-dimensional spaces are continuous;
* the punctured fibre `nfPunct E x = {p | vec p.1 ≠ 0}` corresponds to `ℝ^k ∖ {0}`.

The transport of relative cohomology along a homeomorphism of pairs is bijective
(`Work.Thom.bijective_relCohMap_of_homeomorphA`), so it is a `ℤ`-linear equivalence; composing with
`H^k(ℝ^k, ℝ^k∖0) ≅ ℤ` gives the claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism

theorem nfRelCohIso {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Nonempty (Work.Thom.RelCoh ℤ k ↥(nfSet E x) (nfPunct E x) ≃ₗ[ℤ] ℤ) := by
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
      p ∈ nfPunct E x ↔ e p ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) :=
    fun p => (he' p).symm
  -- transport the computation of `H^k(ℝ^k, ℝ^k∖0) = ℤ`
  obtain ⟨eiso⟩ := Work.Thom.relCohomology_euclidean_punctured k hk k
  rw [if_pos rfl] at eiso
  have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA (nfPunct E x)
    ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) e he ℤ k
  exact ⟨(LinearEquiv.ofBijective _ hbij).symm.trans
    (eiso.toLinearEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ))⟩

end Work.ThomBordism
