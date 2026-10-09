import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.kerSuccCocycle_naturality
import Submission.Work.SSGRoute.exists_hom_lift_of_section_coboundary
import Submission.Work.SSGRoute.isOpen_ker_of_invariant_open_subgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

theorem exists_continuous_lift_of_locconst_coboundary (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j n : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hopen : IsOpen (φ.ker : Set SSGRoute.GalQ))
    (s : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j →
      Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hs : ∀ x, Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s x) = x) (h1 : s 1 = 1)
    (hb : ∃ f : SSGRoute.GalQ → Additive ↥(Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker,
        SSGRoute.IsLocConstOn ⊤ f ∧
        ∀ σ τ : SSGRoute.GalQ,
          Work.SSGRoute.kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j φ s hs σ τ =
            Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
              (Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) (s (φ σ))
              (Additive.toMul (f τ))) - f (σ * τ) + f σ) :
    ∃ ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
      (Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).comp ψ = φ ∧
      IsOpen (ψ.ker : Set SSGRoute.GalQ) := by
  obtain ⟨f, hflc, hcob⟩ := hb
  -- The cocycle `kerSuccCocycle` is, up to an irrelevant proof component, the explicit section
  -- cocycle of the projection `flowGroupSucc`.
  have hmem : ∀ σ τ : SSGRoute.GalQ,
      (s (φ σ) * s (φ τ) * (s (φ (σ * τ)))⁻¹) ∈
        (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker := by
    intro σ τ
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hs, hs, hs]
    simp
  have hbridge : ∀ σ τ : SSGRoute.GalQ,
      kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j φ s hs σ τ =
        Additive.ofMul (⟨s (φ σ) * s (φ τ) * (s (φ (σ * τ)))⁻¹, hmem σ τ⟩ :
          (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) := by
    intro σ τ
    apply Additive.ext
    exact Subtype.ext rfl
  have hcob' : ∀ σ τ : SSGRoute.GalQ,
      Additive.ofMul (⟨s (φ σ) * s (φ τ) * (s (φ (σ * τ)))⁻¹, hmem σ τ⟩ :
          (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) =
        Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) (s (φ σ))
          (Additive.toMul (f τ))) - f (σ * τ) + f σ := by
    intro σ τ
    rw [← hbridge σ τ]
    exact hcob σ τ
  have hcomm : ∀ a b : (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker, a * b = b * a :=
    fun a b => (flowGroupSucc_ker_isMulCommutative p (K ≃ₐ[ℚ] K) n i j).is_comm.comm a b
  obtain ⟨ψ, hcomp, hψ⟩ := exists_hom_lift_of_section_coboundary
    (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) hcomm s hs h1 φ f hcob'
  refine ⟨ψ, hcomp, ?_⟩
  -- The local constancy of `f` and the openness of `ker φ` make `ψ` invariant under an open
  -- subgroup, hence `ker ψ` is open.
  obtain ⟨U, hUopen, hUinv⟩ := hflc
  refine isOpen_ker_of_invariant_open_subgroup ψ (U ⊓ φ.ker) ?_ ?_
  · rw [Subgroup.coe_inf]
    exact hUopen.inter hopen
  · intro σ u hu
    rw [Subgroup.mem_inf] at hu
    obtain ⟨huU, huK⟩ := hu
    have hf : f (σ * u) = f σ := hUinv σ (Subgroup.mem_top σ) u huU (Subgroup.mem_top u)
    have hφ : φ (σ * u) = φ σ := by
      rw [map_mul, MonoidHom.mem_ker.mp huK, mul_one]
    rw [hψ (σ * u), hψ σ, hf, hφ]

end Work.SSGRoute
