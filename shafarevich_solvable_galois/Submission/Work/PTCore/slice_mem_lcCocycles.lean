import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PTCore

/-- The `σ`-slice `n ↦ F n σ` of a locally constant `2`-cocycle `F` on the decomposition group
`D_A` that is normalized on `I` (`F g n = 0` for `g ∈ D_A`, `n ∈ I`) is a locally constant
`1`-cocycle on any subgroup `I ≤ D_A` normalized by `σ`.

The `1`-cocycle identity and the `σ`-shift `F g (h σ) = F g σ` are both consequences of the
`2`-cocycle identity: the first at the triple `(g, h, σ)` and the second at `(g, σ, σ⁻¹ h σ)`,
where `σ⁻¹ h σ ∈ I` is exactly the normality hypothesis. -/
lemma slice_mem_lcCocycles
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (F : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hF : F ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A))
    (hFn : ∀ g ∈ SSGRoute.decomp k A, ∀ n ∈ I, F g n = 0) :
    (fun n => F n σ) ∈ Work.SSGRoute.lcCocycles p k Ω K M I := by
  simp only [Work.SSGRoute.mem_lcCocycles]
  refine ⟨?_, ?_⟩
  · -- the `1`-cocycle identity
    intro g hg h hh
    show F (g * h) σ = F g σ + SSGRoute.res k K g • F h σ
    have hgh : F g h = 0 := hFn g (hI hg) h hh
    have hnh : σ⁻¹ * h * σ ∈ I := hnorm2 h hh
    have hc1 := hF.1 g (hI hg) h (hI hh) σ hσ
    have hc2 := hF.1 g (hI hg) σ hσ (σ⁻¹ * h * σ) (hI hnh)
    have hsig : F σ (σ⁻¹ * h * σ) = 0 := hFn σ hσ (σ⁻¹ * h * σ) hnh
    have hgs : F (g * σ) (σ⁻¹ * h * σ) = 0 :=
      hFn (g * σ) (mul_mem (hI hg) hσ) (σ⁻¹ * h * σ) hnh
    have hconj : σ * (σ⁻¹ * h * σ) = h * σ := by group
    -- the `σ`-shift, from the cocycle identity at `(g, σ, σ⁻¹ h σ)`
    have h2 : F g (h * σ) = F g σ := by
      rw [hconj, hsig, hgs, smul_zero, zero_sub, neg_zero, zero_add] at hc2
      exact sub_eq_zero.mp hc2
    -- the cocycle identity at `(g, h, σ)`
    rw [hgh, h2, sub_zero] at hc1
    have hC : F g σ = F (g * h) σ - SSGRoute.res k K g • F h σ := by
      rw [eq_neg_of_add_eq_zero_right hc1, neg_sub]
    rw [hC, sub_add_cancel]
  · -- local constancy, inherited from `F` by freezing the second variable at `σ`
    obtain ⟨U, hUo, hU⟩ := hF.2
    refine ⟨U, hUo, ?_⟩
    intro g hg u hu huI
    have h := hU g (hI hg) σ hσ u hu 1 (one_mem U) (hI huI)
      (one_mem (SSGRoute.decomp k A))
    simpa using h

end Work.PTCore
