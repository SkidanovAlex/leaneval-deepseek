import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.LTDDefs.H2locAux
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LTDDefs.H2loc

theorem restrictFun2_mem_B2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M} (hc : c ∈ lcCocycles2 p k Ω K M H)
    (hb : c ∈ coboundaries2 p k Ω K M H) :
    restrictFun2 H c ∈ Work.AbsoluteKummer.B2 ↥H M := by
  rw [Work.AbsoluteKummer.mem_B2_iff]
  have hb' : SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c := hb
  obtain ⟨b, hbloc, hbeq⟩ := hb'
  refine ⟨fun h : ↥H => b (h : Ω ≃ₐ[k] Ω), ?_, ?_⟩
  · rw [Work.AbsoluteKummer.mem_C1c_iff]
    obtain ⟨U, hUo, hU⟩ := hbloc
    intro x
    refine ⟨{y : ↥H | (x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω) ∈ U}, ?_, ?_, ?_⟩
    · exact hUo.preimage (continuous_const.mul continuous_subtype_val)
    · show (x : Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω) ∈ U
      rw [inv_mul_cancel]
      exact U.one_mem
    · intro y hy
      show b (y : Ω ≃ₐ[k] Ω) = b (x : Ω ≃ₐ[k] Ω)
      have hyH : (x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω) ∈ H :=
        H.mul_mem (H.inv_mem x.2) y.2
      have hthis := hU (x : Ω ≃ₐ[k] Ω) x.2 ((x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) hy hyH
      have hxy : (x : Ω ≃ₐ[k] Ω) * ((x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) =
          (y : Ω ≃ₐ[k] Ω) := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [← hxy, hthis]
  · funext q
    obtain ⟨g, h⟩ := q
    rw [Work.GroupCohomology.d1_apply, restrictFun2_apply]
    rw [hcompat g (b (h : Ω ≃ₐ[k] Ω)), Subgroup.coe_mul, ← hbeq (g : Ω ≃ₐ[k] Ω) g.2
      (h : Ω ≃ₐ[k] Ω) h.2]

end Work.SSGRoute.LTDDefs.H2loc
