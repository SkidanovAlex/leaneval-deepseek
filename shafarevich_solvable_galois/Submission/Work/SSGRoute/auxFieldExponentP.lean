import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite normal extension killing a locally constant `𝔽_p`-valued homomorphism

Let `k` be a number field, `Ω` an algebraic closure of `k` and `K ⊆ Ω` a finite normal
subextension.  Let `E` be a module over `ZMod p` (`p` prime), so that `E` has exponent `p`, and
let `z : Ω ≃ₐ[k] Ω → E` be additive on `H = K.fixingSubgroup = Gal(Ω/K)`:

`z (g * h) = z g + z h` for `g, h ∈ H`,

and locally constant on `H` (`SSGRoute.IsLocConstOn H z`, i.e. `z` is continuous for the Krull
topology and the discrete topology on `E`).

Then `z` kills a finite *normal* extension of `K`: there is `L` with `K ≤ L`, `L/k` finite and
normal, such that `z` vanishes on `Gal(Ω/L) = L.fixingSubgroup`, and additionally
`Gal(Ω/L)` contains the `p`-th powers and the commutators of elements of `H = Gal(Ω/K)`.

The mathematical content: additivity of `z` on the group `H` with values in a group of exponent
`p` forces `z (g ^ p) = p · z g = 0` and `z (σ τ σ⁻¹ τ⁻¹) = 0`, while local constancy makes
`ker z ∩ H` an open subgroup of `H`.  Passing to the normal core of that open subgroup (an open
normal subgroup, using that `Kz` is open in the Krull topology) and taking its fixed field gives
the required `L`.
-/

namespace Work.SSGRoute

open scoped Pointwise

set_option linter.style.haveILetI false

theorem auxFieldExponentP (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [Normal k K]
    {E : Type} [AddCommGroup E] [Module (ZMod p) E]
    (z : (Ω ≃ₐ[k] Ω) → E)
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z) :
    ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧ Normal k L ∧ K ≤ L ∧
      (∀ σ ∈ L.fixingSubgroup, z σ = 0) ∧
      (∀ σ ∈ K.fixingSubgroup, σ ^ p ∈ L.fixingSubgroup) ∧
      (∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup,
        σ * τ * σ⁻¹ * τ⁻¹ ∈ L.fixingSubgroup) := by
  haveI : IsGalois k Ω := inferInstance
  -- `Gal(Ω/K)` is normal in `Gal(Ω/k)`, because `K/k` is normal.
  have hH_normal : K.fixingSubgroup.Normal := by
    rw [← IntermediateField.restrictNormalHom_ker K]
    infer_instance
  -- `z` is a homomorphism on `K.fixingSubgroup`; values in a group.
  have hz_one : z 1 = 0 := by
    have h1 : (1 : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := K.fixingSubgroup.one_mem
    have h : z (1 * 1) = z 1 + z 1 := hzadd 1 h1 1 h1
    rw [one_mul] at h
    exact (add_left_cancel (show z 1 + 0 = z 1 + z 1 by rw [add_zero]; exact h)).symm
  have hz_inv : ∀ g ∈ K.fixingSubgroup, z g⁻¹ = - z g := by
    intro g hg
    have h : z (g * g⁻¹) = z g + z g⁻¹ := hzadd g hg g⁻¹ (K.fixingSubgroup.inv_mem hg)
    rw [mul_inv_cancel, hz_one] at h
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)
  -- `z (g ^ n) = n • z g`; in particular `z (g ^ p) = 0` since `E` has exponent `p`.
  have hz_pow : ∀ (n : ℕ) (g : Ω ≃ₐ[k] Ω), g ∈ K.fixingSubgroup → z (g ^ n) = n • z g := by
    intro n
    induction n with
    | zero => intro g _; simp [hz_one]
    | succ n ih =>
      intro g hg
      have hgm : g ^ n ∈ K.fixingSubgroup := K.fixingSubgroup.pow_mem hg n
      rw [pow_succ, hzadd (g ^ n) hgm g hg, ih g hg]
      exact (succ_nsmul (z g) n).symm
  -- `z` kills commutators of `K.fixingSubgroup`, `E` being abelian.
  have hz_comm : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
      z (g * h * g⁻¹ * h⁻¹) = 0 := by
    intro g hg h hh
    have hg' : g⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hg
    have hh' : h⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hh
    have h1 : z (g * h * g⁻¹ * h⁻¹) = z (g * h) + z (g⁻¹ * h⁻¹) := by
      rw [mul_assoc (g * h) g⁻¹ h⁻¹]
      exact hzadd (g * h) (K.fixingSubgroup.mul_mem hg hh) (g⁻¹ * h⁻¹)
        (K.fixingSubgroup.mul_mem hg' hh')
    rw [h1, hzadd g hg h hh, hzadd g⁻¹ hg' h⁻¹ hh', hz_inv g hg, hz_inv h hh]
    abel
  -- The kernel of `z` inside `K.fixingSubgroup`, as a subgroup of `Gal(Ω/k)`.
  let Kz : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {x | x ∈ K.fixingSubgroup ∧ z x = 0}
      mul_mem' := fun {a b} ha hb => ⟨K.fixingSubgroup.mul_mem ha.1 hb.1,
        by rw [hzadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨K.fixingSubgroup.one_mem, hz_one⟩
      inv_mem' := fun {a} ha => ⟨K.fixingSubgroup.inv_mem ha.1,
        by rw [hz_inv a ha.1, ha.2, neg_zero]⟩ }
  have hKz_le : Kz ≤ K.fixingSubgroup := fun _ hx => hx.1
  -- `Kz` is open: local constancy gives an open subgroup `U` with `U ⊓ H ≤ Kz`.
  obtain ⟨U, hUopen, hUprop⟩ := hzloc
  have hKz_open : IsOpen (Kz : Set (Ω ≃ₐ[k] Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := U ⊓ K.fixingSubgroup) (H₂ := Kz) ?_ ?_
    · intro x hx
      exact ⟨hx.2, by
        have h := hUprop 1 K.fixingSubgroup.one_mem x hx.1 hx.2
        simpa [hz_one] using h⟩
    · exact hUopen.inter (IntermediateField.fixingSubgroup_isOpen K)
  -- An open normal subgroup contained in `Kz` (a finite Galois subextension of `Ω/k`).
  obtain ⟨M₀, hM₀⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (k := k) (K := Ω)
      (Kz : Set (Ω ≃ₐ[k] Ω))).mp (hKz_open.mem_nhds Kz.one_mem)
  have hB_le : M₀.fixingSubgroup ≤ Kz := hM₀
  have hB_open : IsOpen (M₀.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen M₀.toIntermediateField
  have hB_normal : M₀.fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois M₀.toIntermediateField).mpr inferInstance
  -- Its fixed field is the `L` we are looking for: the normal core of `Kz` is open and normal.
  have hcore_open : IsOpen ((Kz.normalCore : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isOpen_mono (Subgroup.normal_le_normalCore.mpr hB_le) hB_open
  have hcore_closed : IsClosed (Kz.normalCore : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isClosed_of_isOpen Kz.normalCore hcore_open
  have hfix : (IntermediateField.fixedField Kz.normalCore).fixingSubgroup = Kz.normalCore :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨Kz.normalCore, hcore_closed⟩
  refine ⟨IntermediateField.fixedField Kz.normalCore, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hfix]; exact hcore_open)
  · have hgal : IsGalois k (IntermediateField.fixedField Kz.normalCore) :=
      (InfiniteGalois.normal_iff_isGalois _).mp (by rw [hfix]; infer_instance)
    exact IsGalois.to_normal
  · rw [IntermediateField.le_iff_le]
    exact fun x hx => (Kz.normalCore_le hx).1
  · intro σ hσ
    rw [hfix] at hσ
    exact (Kz.normalCore_le hσ).2
  · -- `σ ^ p ∈ Kz.normalCore`: conjugate into `H`, where `z` vanishes on `p`-th powers.
    intro σ hσ
    rw [hfix]
    intro b
    have hb : b * σ ^ p * b⁻¹ = (b * σ * b⁻¹) ^ p :=
      (conj_pow (a := b) (b := σ) (i := p)).symm
    have hmem : b * σ * b⁻¹ ∈ K.fixingSubgroup := hH_normal.conj_mem σ hσ b
    refine ⟨?_, ?_⟩
    · rw [hb]; exact K.fixingSubgroup.pow_mem hmem p
    · rw [hb, hz_pow p (b * σ * b⁻¹) hmem,
        ← Nat.cast_smul_eq_nsmul (ZMod p) p (z (b * σ * b⁻¹)), ZMod.natCast_self, zero_smul]
  · -- `σ * τ * σ⁻¹ * τ⁻¹ ∈ Kz.normalCore`: conjugate to a commutator in `H`.
    intro σ hσ τ hτ
    rw [hfix]
    intro b
    have hmemσ : b * σ * b⁻¹ ∈ K.fixingSubgroup := hH_normal.conj_mem σ hσ b
    have hmemτ : b * τ * b⁻¹ ∈ K.fixingSubgroup := hH_normal.conj_mem τ hτ b
    have hb : b * (σ * τ * σ⁻¹ * τ⁻¹) * b⁻¹ =
        (b * σ * b⁻¹) * (b * τ * b⁻¹) * (b * σ * b⁻¹)⁻¹ * (b * τ * b⁻¹)⁻¹ := by
      group
    have hmem' : (b * σ * b⁻¹) * (b * τ * b⁻¹) * (b * σ * b⁻¹)⁻¹ * (b * τ * b⁻¹)⁻¹ ∈
        K.fixingSubgroup := by
      exact K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem
        (K.fixingSubgroup.mul_mem hmemσ hmemτ) (K.fixingSubgroup.inv_mem hmemσ))
        (K.fixingSubgroup.inv_mem hmemτ)
    refine ⟨?_, ?_⟩
    · rw [hb]; exact hmem'
    · rw [hb]
      exact hz_comm (b * σ * b⁻¹) hmemσ (b * τ * b⁻¹) hmemτ

end Work.SSGRoute
