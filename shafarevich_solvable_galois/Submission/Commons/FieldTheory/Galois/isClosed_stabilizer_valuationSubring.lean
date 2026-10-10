import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.FieldTheory.Galois.mem_stabilizer_valuationSubring_iff_forall_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

open scoped Pointwise _root_.Topology

/-- **The stabiliser of a valuation subring of a Galois extension is closed in the Krull
topology.**

Indeed, by `Commons.FieldTheory.Galois.mem_stabilizer_valuationSubring_iff_forall_restrict`, the
stabiliser of `A` is the intersection over the *finite* normal intermediate fields `L` of the
preimages of the stabilisers of `A ∩ L` under the restriction maps `Gal(K'/K) →* Gal(L/K)`.  The
latter take values in finite, hence discrete, groups, and are continuous because their kernels are
the open fixing subgroups (`IntermediateField.fixingSubgroup_isOpen`). -/
theorem isClosed_stabilizer_valuationSubring {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    [IsGalois K K'] (A : ValuationSubring K') :
    IsClosed ((MulAction.stabilizer (K' ≃ₐ[K] K') A : Set (K' ≃ₐ[K] K'))) := by
  rw [isClosed_iff_nhds]
  intro σ hσ
  change σ ∈ MulAction.stabilizer (K' ≃ₐ[K] K') A
  rw [MulAction.mem_stabilizer_iff]
  -- Key pointwise statement: `σ` agrees with some stabiliser element on each finite subextension,
  -- hence preserves membership in `A`.
  have hkey : ∀ z : K', z ∈ A ↔ σ z ∈ A := by
    intro z
    let E : IntermediateField K K' := IntermediateField.adjoin K {z}
    haveI : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional (IsGalois.integral K z)
    have hzE : z ∈ E := IntermediateField.mem_adjoin_simple_self K z
    have hopen : IsOpen (σ • (E.fixingSubgroup : Set (K' ≃ₐ[K] K'))) :=
      (IntermediateField.fixingSubgroup_isOpen E).leftCoset σ
    have hmem : σ ∈ σ • (E.fixingSubgroup : Set (K' ≃ₐ[K] K')) := by
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_mul_cancel]
      exact E.fixingSubgroup.one_mem
    obtain ⟨τ, hτU, hτH⟩ := hσ _ (hopen.mem_nhds hmem)
    obtain ⟨g, hgE, hgτ⟩ := Set.mem_smul_set.mp hτU
    have hgz : g z = z := by
      change g ∈ E.fixingSubgroup at hgE
      rw [IntermediateField.mem_fixingSubgroup_iff] at hgE
      exact hgE z hzE
    have hτz : τ z = σ z := by
      rw [← hgτ, smul_eq_mul, AlgEquiv.mul_apply, hgz]
    have hτstab : τ • A = A := (MulAction.mem_stabilizer_iff).mp hτH
    constructor
    · intro hz
      have h1 : τ • z ∈ τ • A := ValuationSubring.smul_mem_pointwise_smul τ z A hz
      rw [hτstab] at h1
      rwa [AlgEquiv.smul_def, hτz] at h1
    · intro hz
      have h1 : τ • z ∈ A := by rw [AlgEquiv.smul_def, hτz]; exact hz
      have h2 : τ • z ∈ τ • A := by rwa [hτstab]
      exact (ValuationSubring.smul_mem_pointwise_smul_iff).mp h2
  apply ValuationSubring.ext
  intro z
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hkey (σ⁻¹ z)]
  simp

end Commons.FieldTheory.Galois