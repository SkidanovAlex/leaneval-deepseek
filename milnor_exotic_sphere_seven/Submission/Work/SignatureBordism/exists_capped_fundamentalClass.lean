import Mathlib
import Submission.Work.Milnor.CappedManifold
import Submission.Work.Cohomology.capped_cupSquare_generates
import Submission.Work.Milnor.capped_generator_pairings

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.SignatureBordism

/-- If a `ℤ`-linear equivalence sends `y` to a generator of its source, then `e.symm y` generates
the target. -/
private lemma span_symm_singleton_eq_top {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) {y : N}
    (hy : Submodule.span ℤ {y} = ⊤) : Submodule.span ℤ {e.symm y} = ⊤ := by
  rw [Work.Cohomology.span_singleton_eq_top_iff] at hy ⊢
  intro z
  exact Work.Cohomology.exists_smul_of_surjective (e.symm : N →ₗ[ℤ] M) e.symm.surjective hy z

/-- `H₈(X;ℤ)` of the closed `8`-manifold `X = D(ξ) ∪_F D⁸` is `ℤ`
(`Work.Milnor.homology_capped_datum`), hence has a generator: the fundamental class. -/
theorem exists_capped_fundamentalClass (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) :
    ∃ c : (Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.Milnor.capped F hF))).homology 8,
      Submodule.span ℤ {c} = ⊤ := by
  obtain ⟨e⟩ := Work.Milnor.cgp_homology_linEquiv_one F hF (n := 8) (by norm_num)
  have hy : Submodule.span ℤ ({(1 : ℤ)} : Set ℤ) = ⊤ := by
    rw [Work.Cohomology.span_singleton_eq_top_iff]
    intro z
    exact ⟨z, by simp⟩
  exact ⟨e.symm 1, span_symm_singleton_eq_top e hy⟩

end Work.SignatureBordism
