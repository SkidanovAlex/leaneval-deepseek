import Mathlib
import Submission.Work.SSGRoute.HSRow.TransgressionDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

open scoped Pointwise

/-- Conjugation by a fixed element of a topological group is continuous, so the preimage of an
open subgroup under it is again open.  (This is the light substitute for the normal core of an
open subgroup: instead of enlarging a witness to be conjugation invariant, we pull back the
conjugation orbit of the witness point by point.) -/
lemma isOpen_comap_conj {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (γ : Γ) (W : Subgroup Γ) (hW : IsOpen (W : Set Γ)) :
    IsOpen ((Subgroup.comap ((MulAut.conj γ⁻¹ : MulAut Γ) : Γ →* Γ) W : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.coe_comap]
  refine hW.preimage ?_
  have hcont : Continuous (fun u : Γ => γ⁻¹ * u * γ) := by continuity
  convert hcont using 1
  funext u
  simp

/-- The transgression cochain `x ↦ tprim σ c β x - β x` (extended by `0` off `I`) is locally
constant on `I`.  Take the local-constancy witness `U` inside `ker (res k K)`, inside the preimage
of the witnesses of `hc` and `hβlc` under `u ↦ σ⁻¹ * u * σ` (or under the normal core of the
witness of `hc`, to make it conjugation invariant). -/
theorem tcoch_isLocConstOn
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (D I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hσ : σ ∈ D) (hI : I ≤ D) (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hc : Work.SSGRoute.IsLocConst2On p k Ω K M D c)
    (β : (Ω ≃ₐ[k] Ω) → M) (hβlc : SSGRoute.IsLocConstOn I β) :
    SSGRoute.IsLocConstOn I (tcoch p k Ω K M I σ c β) := by
  obtain ⟨Vc, hVc_open, hVc⟩ := hc
  obtain ⟨Vb, hVb_open, hVb⟩ := hβlc
  -- The witness: `u` must (a) be trivial under `res k K`, (b) have `σ⁻¹ * u * σ` inside the
  -- witnesses `Vc`, `Vb` of `hc`, `hβlc`, and (c) itself lie in `Vb` (to shift the argument of
  -- `β` on `I`).
  refine ⟨Subgroup.comap ((MulAut.conj σ⁻¹ : MulAut (Ω ≃ₐ[k] Ω)) :
      (Ω ≃ₐ[k] Ω) →* (Ω ≃ₐ[k] Ω)) (Vc ⊓ Vb) ⊓ Vb ⊓ (SSGRoute.res k K).ker, ?_, ?_⟩
  · -- openness: intersection of an open subgroup, an open subgroup, and `ker (res k K)`.
    have hcomap : IsOpen ((Subgroup.comap ((MulAut.conj σ⁻¹ : MulAut (Ω ≃ₐ[k] Ω)) :
        (Ω ≃ₐ[k] Ω) →* (Ω ≃ₐ[k] Ω)) (Vc ⊓ Vb) : Subgroup (Ω ≃ₐ[k] Ω)) :
        Set (Ω ≃ₐ[k] Ω)) := isOpen_comap_conj σ (Vc ⊓ Vb) (hVc_open.inter hVb_open)
    have hker : IsOpen (((SSGRoute.res k K).ker : Subgroup (Ω ≃ₐ[k] Ω)) :
        Set (Ω ≃ₐ[k] Ω)) := by
      rw [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl]
      rw [IntermediateField.restrictNormalHom_ker]
      exact IntermediateField.fixingSubgroup_isOpen K
    rw [Subgroup.coe_inf, Subgroup.coe_inf]
    exact (hcomap.inter hVb_open).inter hker
  · intro g hg u hu huI
    have huVc : σ⁻¹ * u * σ ∈ Vc := by
      have h : ((MulAut.conj σ⁻¹ : MulAut (Ω ≃ₐ[k] Ω)) :
          (Ω ≃ₐ[k] Ω) →* (Ω ≃ₐ[k] Ω)) u ∈ Vc ⊓ Vb := Subgroup.mem_comap.mp hu.1.1
      have h' : ((MulAut.conj σ⁻¹ : MulAut (Ω ≃ₐ[k] Ω)) u) ∈ Vc :=
        (Subgroup.mem_inf.mp h).1
      simpa using h'
    have huVb' : σ⁻¹ * u * σ ∈ Vb := by
      have h : ((MulAut.conj σ⁻¹ : MulAut (Ω ≃ₐ[k] Ω)) :
          (Ω ≃ₐ[k] Ω) →* (Ω ≃ₐ[k] Ω)) u ∈ Vc ⊓ Vb := Subgroup.mem_comap.mp hu.1.1
      have h' : ((MulAut.conj σ⁻¹ : MulAut (Ω ≃ₐ[k] Ω)) u) ∈ Vb :=
        (Subgroup.mem_inf.mp h).2
      simpa using h'
    have huVb : u ∈ Vb := hu.1.2
    have huk : SSGRoute.res k K u = 1 := MonoidHom.mem_ker.mp hu.2
    have hguI : g * u ∈ I := I.mul_mem hg huI
    -- the group identities putting the `u`-part of each argument on the right
    have h1 : σ⁻¹ * (g * u) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * u * σ) := by group
    have h2 : (g * u) * σ = (g * σ) * (σ⁻¹ * u * σ) := by group
    have hmI : σ⁻¹ * g * σ ∈ I := hnorm2 g hg
    have hnI : σ⁻¹ * u * σ ∈ I := hnorm2 u huI
    -- the four local-constancy rewrites (two for `β`, two for `c`)
    have hβ1 : β (g * u) = β g := hVb g hg u huVb huI
    have hβ2 : β ((σ⁻¹ * g * σ) * (σ⁻¹ * u * σ)) = β (σ⁻¹ * g * σ) :=
      hVb (σ⁻¹ * g * σ) hmI (σ⁻¹ * u * σ) huVb' hnI
    have hc1 : c σ ((σ⁻¹ * g * σ) * (σ⁻¹ * u * σ)) = c σ (σ⁻¹ * g * σ) :=
      hVc σ hσ (σ⁻¹ * g * σ) (hI hmI) 1 Vc.one_mem (σ⁻¹ * u * σ) huVc D.one_mem (hI hnI)
    have hc2 : c ((g * σ) * (σ⁻¹ * u * σ)) σ⁻¹ = c (g * σ) σ⁻¹ :=
      hVc (g * σ) (D.mul_mem (hI hg) hσ) σ⁻¹ (D.inv_mem hσ) (σ⁻¹ * u * σ) huVc 1 Vc.one_mem
        (hI hnI) D.one_mem
    have hres : SSGRoute.res k K (g * u) = SSGRoute.res k K g := by rw [map_mul, huk, mul_one]
    rw [tcoch_apply_of_mem p k Ω K M I σ c β hguI, tcoch_apply_of_mem p k Ω K M I σ c β hg,
      tprim_apply, tprim_apply, h1, h2, hβ1, hβ2, hres, hc1, hc2]

end Work.SSGRoute.HSRow
