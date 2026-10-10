import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

/-- **Level-`K`-conjugate places have conjugate local groups.**  If `A` and `B` are level-`K`
conjugate (`Work.SSGRoute.KConj K A B`: `τ • A = B` for some `τ ∈ G_K = K.fixingSubgroup`) and two
cochains `z`, `w` are additive on `G_K` and agree on the local group `decomp k A ⊓ G_K` of `A`, then
they agree on the local group of `B`.

This is the elementary transport along `G_K`-conjugacy which lets a local condition imposed at one
representative of a level-`K` class be read off at every place of the class; it uses only that
`z (τ * u * τ⁻¹) = z u` for additive cochains (`Work.SSGRoute.zadd_conj`, `ZConstruction/ZDataGlue`).
The vanishing case (`w = 0`) and the case `w = y₁` (agreement with prescribed data) are the two
instances used by the §4 assembly.

Hints: get `τ ∈ G_K` with `τ • A = B`.  For `σ ∈ decomp k B ⊓ G_K` use
`SSGRoute.decomp_conj` (`Submission/Work/SSGRoute/place_basics.lean`) to write `σ = τ * σ' * τ⁻¹`
with `σ' ∈ decomp k A ⊓ G_K` (`σ' = τ⁻¹ * σ * τ`; subgroup closure only, no normality of `G_K` in
`G_k` is needed), then `zadd_conj` twice plus the hypothesis at `σ'`.  The special case `w = 0` is
already proved as `kills_decomp_of_smul` (`shafarevich_z_data_two.lean:1351`) and is the template. -/
theorem kConj_of_local_agree {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} {E : Type} [AddCommGroup E]
    {z w : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hwadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, w (g * h) = w g + w h)
    {A B : ValuationSubring Ω} (hAB : Work.SSGRoute.KConj K A B)
    (h : ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = w σ) :
    ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z σ = w σ := by
  obtain ⟨τ, hτK, hτA⟩ := hAB
  intro σ hσ
  obtain ⟨hσD, hσK⟩ := Subgroup.mem_inf.mp hσ
  have hτinv : τ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hτK
  -- the conjugate element `σ' = τ⁻¹ * σ * τ`
  have hσ'K : τ⁻¹ * σ * τ ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hτinv hσK) hτK
  have hσ'D : τ⁻¹ * σ * τ ∈ SSGRoute.decomp k A := by
    rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff] at hσD ⊢
    calc (τ⁻¹ * σ * τ) • A = τ⁻¹ • (σ • (τ • A)) := by simp only [mul_smul]
      _ = τ⁻¹ • B := by rw [hτA, hσD]
      _ = A := by rw [← hτA, inv_smul_smul]
  -- the hypothesis at the conjugate element
  have hconj : z (τ⁻¹ * σ * τ) = w (τ⁻¹ * σ * τ) :=
    h _ (Subgroup.mem_inf.mpr ⟨hσ'D, hσ'K⟩)
  -- `zadd_conj` at `τ` and `u = τ⁻¹ * σ * τ` recovers the value at `σ`
  have hτεq : τ * (τ⁻¹ * σ * τ) * τ⁻¹ = σ := by group
  have hz : z σ = z (τ⁻¹ * σ * τ) := by
    have hh := zadd_conj hzadd hτK hσ'K
    rwa [hτεq] at hh
  have hw : w σ = w (τ⁻¹ * σ * τ) := by
    have hh := zadd_conj hwadd hτK hσ'K
    rwa [hτεq] at hh
  rw [hz, hw, hconj]

end Work.SSGRoute.ZConstruction
