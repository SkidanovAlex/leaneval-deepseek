import Submission.Work.Tubular.exists_relKronH_eval_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A primitive functional for the relative Kronecker pairing

`Work.Tubular.exists_relKronH_eval_iso` identifies `H^n(X,A;ℤ)` with the dual of `H_n(X,A;ℤ)`
through `Work.Tubular.relKronH`, whenever the relative homology is degreewise free.  This module
draws the consequence used by the local-degree route (README §24, step 2): for a rank-one
identification `e : H_n(X,A) ≃ₗ[ℤ] ℤ` there is a cohomology class `β` with

  `⟨β, e.symm 1⟩ = 1`,

i.e. the relative Kronecker pairing admits a *primitive* cohomology class against a generator.
-/

set_option autoImplicit false

open CategoryTheory

namespace Work.Tubular

noncomputable section

/-- **A primitive cohomology class for the relative Kronecker pairing.**  If the relative homology of
`(X,A)` is degreewise free and `e` identifies its degree-`n` part with `ℤ`, then the generator
`e.symm 1` pairs to `1` with some class of `H^n(X,A;ℤ)`. -/
theorem relKronH_exists_eval_one {X : Type} [TopologicalSpace X] {A : Set X} {n : ℕ}
    (hfree : ∀ j, Module.Free ℤ ↥((Work.Cohomology.relChains (TopCat.of X) A).homology j))
    (e : ↥((Work.Cohomology.relChains (TopCat.of X) A).homology n) ≃ₗ[ℤ] ℤ) :
    ∃ β : (Work.Cohomology.relComplex ℤ (TopCat.of X) A).homology n,
      relKronH (TopCat.of X) A n β (e.symm 1) = 1 := by
  obtain ⟨e', he'⟩ := exists_relKronH_eval_iso (TopCat.of X) A n hfree
  refine ⟨e'.symm (e.toLinearMap : ↥((Work.Cohomology.relChains (TopCat.of X) A).homology n) →ₗ[ℤ] ℤ),
    ?_⟩
  rw [← he', e'.apply_symm_apply]
  exact e.apply_symm_apply 1

end

end Work.Tubular
