import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.twistLayer
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **The twist is equivariant for conjugation by `G_ℚ` along the decomposition group of `A`.**
If the decomposition group `D_A` of `A` lies in `G_K` (`hDK`), then for `σ ∈ D_A` the value of the
twisted homomorphism at any conjugate `θ σ θ⁻¹` is the `ψ θ`-conjugate of its value at `σ`.

The proof has three ingredients:
* the (inhomogeneous) `1`-cocycle identity for `x`, which together with `res σ = 1` gives
  `x (θ σ θ⁻¹) = (res θ) • x σ` (`hkey`);
* the equivariance `gradeInl_conj` of the graded piece inside `Γ_{τ+1}`, which identifies the
  conjugation action of the lift `ψ θ` with the `Gal(K/ℚ)`-action;
* `ψ` being a homomorphism for the permutation of the `ψ`-factors. -/
theorem flowTwistE_conj_of_mem_decomp (p : ℕ)
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (x : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hψquot : ∀ σ, Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) n
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2 (ψ σ)
      = Work.SSGRoute.restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ)
    (A : ValuationSubring SSGRoute.QBar)
    (hDK : ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup)
    (θ σ : SSGRoute.GalQ) (hσ : σ ∈ SSGRoute.decomp ℚ A) :
    Work.SSGRoute.flowTwistE p K n i j x ψ (θ * σ * θ⁻¹)
      = ψ θ * Work.SSGRoute.flowTwistE p K n i j x ψ σ * (ψ θ)⁻¹ := by
  -- `σ` acts trivially on `K`
  have hres : restrict K σ = 1 := restrict_eq_one_of_mem_fixingSubgroup K (hDK σ hσ)
  -- the cocycle vanishes at `1`
  have hx1 : x 1 = 0 := by
    have h := hxmul 1 1
    simp only [mul_one, map_one, one_smul] at h
    exact add_left_cancel (h.symm.trans (add_zero (x 1)).symm)
  -- the coboundary identity at `θ⁻¹ θ`
  have hxθ : x θ + (restrict K θ) • x θ⁻¹ = 0 := by
    have h := hxmul θ θ⁻¹
    rw [mul_inv_cancel, hx1] at h
    exact h.symm
  -- the key cocycle computation: `x` is `res θ`-equivariant at `σ`
  have hkey : x (θ * σ * θ⁻¹) = (restrict K θ) • x σ := by
    have h1 := hxmul θ (σ * θ⁻¹)
    have h2 := hxmul σ θ⁻¹
    rw [← mul_assoc, h2, hres, one_smul] at h1
    rw [h1, smul_add, add_comm ((restrict K θ) • x σ) ((restrict K θ) • x θ⁻¹),
      ← add_assoc, hxθ, zero_add]
  -- conjugation by the lift `ψ θ` acts on the graded piece by `res θ`
  have hcl : gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul ((restrict K θ) • x σ))
      = ψ θ * gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (x σ)) * (ψ θ)⁻¹ :=
    (gradeInl_conj p K n i j ψ θ (hψquot θ) (Additive.toMul (x σ))).symm
  rw [flowTwistE, flowTwist, flowTwist, hkey, map_mul, map_mul, map_inv, hcl]
  group

end Work.SSGRoute
