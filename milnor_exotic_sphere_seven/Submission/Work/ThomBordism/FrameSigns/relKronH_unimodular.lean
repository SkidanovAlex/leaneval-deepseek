import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.Tubular.Unimodular

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.FrameSigns

/-- **The relative Kronecker pairing is unimodular on a cyclic generator and a primitive class.**

If the relative homology `H_*(X,A;ℤ)` is degreewise free, the relative Kronecker pairing
`relKronH : H^n(X,A;ℤ) →ₗ (H_n(X,A;ℤ) →ₗ ℤ)` is an isomorphism
(`Work.Tubular.exists_relKronH_eval_iso`).  Hence a cyclic generator `τ` of `H^n(X,A;ℤ)`
(`Submodule.span ℤ {τ} = ⊤`) is carried to a cyclic generator of the dual module, and pairing it
with a *primitive* class `σ ∈ H_n(X,A;ℤ)` (one admitting `φ` with `φ σ = 1`) gives a unit of `ℤ`. -/
theorem relKronH_unimodular (X : TopCat) (A : Set X) (n : ℕ)
    (hfree : ∀ j, Module.Free ℤ ↥((Work.Cohomology.relChains X A).homology j))
    (τ : Work.Thom.RelCoh ℤ n X A) (hτ : Submodule.span ℤ {τ} = ⊤)
    (σ : ↥((Work.Cohomology.relChains X A).homology n))
    (φ : ↥((Work.Cohomology.relChains X A).homology n) →ₗ[ℤ] ℤ) (hφ : φ σ = 1) :
    (Work.Tubular.relKronH X A n) τ σ = 1 ∨ (Work.Tubular.relKronH X A n) τ σ = -1 := by
  obtain ⟨e, he⟩ := Work.Tubular.exists_relKronH_eval_iso X A n hfree
  have h := Work.Tubular.eq_one_or_neg_one_of_linearEquiv_dual e τ σ φ hφ hτ
  rw [he τ σ] at h
  exact h

end Work.ThomBordism.FrameSigns
