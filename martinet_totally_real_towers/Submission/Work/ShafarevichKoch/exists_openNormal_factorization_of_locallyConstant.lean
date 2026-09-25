import Mathlib
import Submission.Work.HopfGaschutz.Profinite

namespace Work.ShafarevichKoch

open scoped Topology

/-- A locally constant function on a compact, totally disconnected topological group
factors through the quotient by an open normal subgroup.

The subgroup used is the normal core of `K = {x | ∀ g, f (g * x) = f g}`, which is open
because `K` is a neighborhood of `1` (compactness of `Γ` upgrades pointwise local constancy
to a uniform statement). -/
theorem exists_openNormal_factorization_of_locallyConstant
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [T2Space Γ] [TotallyDisconnectedSpace Γ]
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    (f : LocallyConstant Γ M) :
    ∃ U : OpenNormalSubgroup Γ, ∃ g : Γ ⧸ U.toSubgroup → M,
      ∀ σ : Γ, f σ = g (QuotientGroup.mk' U.toSubgroup σ) := by
  let K : Subgroup Γ :=
    { carrier := {x | ∀ g : Γ, f (g * x) = f g}
      mul_mem' := by
        intro a b ha hb g
        rw [← mul_assoc, hb (g * a), ha g]
      one_mem' := by intro g; rw [mul_one]
      inv_mem' := by
        intro a ha g
        have h := ha (g * a⁻¹)
        rw [mul_assoc, inv_mul_cancel, mul_one] at h
        exact h.symm }
  have hKmem : (K : Set Γ) ∈ 𝓝 (1 : Γ) := by
    have hmain : ∀ᶠ x in 𝓝 (1 : Γ), ∀ y ∈ (Set.univ : Set Γ), f (y * x) = f y := by
      refine IsCompact.eventually_forall_of_forall_eventually isCompact_univ ?_
      intro y _
      have h1 : ∀ᶠ z : Γ × Γ in 𝓝 ((1 : Γ), y), f (z.2 * z.1) = f y := by
        have hcont : Continuous fun z : Γ × Γ => z.2 * z.1 := by fun_prop
        have hlc : IsLocallyConstant (fun z : Γ × Γ => f (z.2 * z.1)) :=
          f.isLocallyConstant.comp_continuous hcont
        have := hlc.eventually_eq ((1 : Γ), y)
        simpa using this
      have h2 : ∀ᶠ z : Γ × Γ in 𝓝 ((1 : Γ), y), f z.2 = f y := by
        have := (continuous_snd.tendsto ((1 : Γ), y)).eventually
          (f.isLocallyConstant.eventually_eq y)
        simpa using this
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
    rw [Filter.eventually_iff] at hmain
    simpa [K] using hmain
  have hKopen : IsOpen (K : Set Γ) := Subgroup.isOpen_of_mem_nhds K hKmem
  have hKclosed : IsClosed (K : Set Γ) := Subgroup.isClosed_of_isOpen K hKopen
  have hqfin : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKopen
  have hKfin : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let U : OpenNormalSubgroup Γ :=
    { toSubgroup := K.normalCore
      isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex K.normalCore
        (K.normalCore_isClosed hKclosed)
      isNormal' := K.normalCore_normal }
  have hU : U.toSubgroup = K.normalCore := rfl
  refine ⟨U, ?_⟩
  refine ⟨fun q => q.liftOn' (fun σ : Γ => f σ) ?_, ?_⟩
  · intro a b hab
    rw [hU] at hab
    rw [QuotientGroup.leftRel_apply] at hab
    have hzK : a⁻¹ * b ∈ K := Subgroup.normalCore_le K hab
    have key : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b
    rw [← key]
    exact (hzK a).symm
  · intro σ
    simp [QuotientGroup.mk'_apply]

end Work.ShafarevichKoch
