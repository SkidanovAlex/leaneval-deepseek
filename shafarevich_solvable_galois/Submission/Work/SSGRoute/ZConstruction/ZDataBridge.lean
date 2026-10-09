import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.Work.SSGRoute.ZConstruction.SWData
import Submission.Work.SSGRoute.cyclic_transfer_of_vanishing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# From Schmidt--Wingberg's `z`-data to `Work.SSGRoute.shafarevich_z_construction`

The interface `Work.SSGRoute.shafarevich_z_construction_of_swData` (module
`Submission.Work.SSGRoute.ZConstruction.SWData`) derives the conclusion of
`Work.SSGRoute.shafarevich_z_construction` from Schmidt--Wingberg's local data for the auxiliary
class `z`, but triggers the sharpened condition (b) on the condition that `z` *does not vanish* on
the local group `decomp k B ⊓ G_K`.  The class constructed in the paper satisfies the condition
with the trigger "`z` is **ramified** at `B`" (non-trivial on the inertia): a local class can be
unramified and non-zero, and at such a place the cyclicity of the transfer holds for a different
reason --- the decomposition group modulo its inertia is pro-cyclic
(`Work.SSGRoute.decomp_mod_inertia_cyclic`).

This file proves the matching interface
`Work.SSGRoute.shafarevich_z_construction_of_zData`: the conclusion of
`shafarevich_z_construction` follows from a cochain `z` with

* `z` additive on `G_K = K.fixingSubgroup` (equivalently a `1`-cocycle for the trivial action) and
  locally constant;
* `z = y` on the decomposition groups of the places of `cs(S)` (conjunct (3));
* `z` kills the involutions of `G_K` (conjunct (4));
* `z` kills the inertia of every place outside `cs(S)` that is not split in `Λ` (conjunct (5));
* **Schmidt--Wingberg's (b) with the ramification trigger**: at every place `B ∉ cs(S)` split in
  `Λ` at which `z` is ramified (`∃ σ ∈ I_B ∩ G_K, z σ ≠ 0`), the image `z (decomp k B ⊓ G_K)` is
  cyclic and `z` vanishes on the local group of every conjugate of `B` that is not a
  `G_K`-conjugate of `B`.

This is *exactly* the conclusion of the `z`-data statements of the same development
(`Work.SSGRoute.z_data_mup_core`, `Work.SSGRoute.shafarevich_z_data_two`,
`Work.SSGRoute.sw_z_exists_odd_sketch`), so the remaining arithmetic obligation is precisely
Schmidt--Wingberg's §4 construction.

## Proof

Fix a finite place `B ∉ cs(S)` that is split in `Λ` (hence in `K`, so `decomp k B ≤ G_K` and the
action of `decomp k B` on `E` is trivial).  The transfer
`X δ = ∑_s s • z ((sec s)⁻¹ δ sec s)` is additive on `decomp k B`, so it suffices to produce
`g ∈ decomp k B` with `X (decomp k B) ⊆ ⟨X g⟩`.

* **No conjugate of `B` is ramified.**  Let `Z = {u ∈ G_K : z u = 0}` and let `U` be a normal open
  subgroup on which `z` vanishes (obtained from local constancy and
  `exists_finiteDimensional_normal_fixingSubgroup_le`).  Put
  `V = ⋂_{s ∈ Gal(K/k)} (sec s) (Z ⊔ U) (sec s)⁻¹`, an open subgroup (each factor contains `U`).
  The hypothesis says exactly that `I_B ⊆ V`, and `X` vanishes on `decomp k B ⊓ V`; the transfer is
  then cyclic by `Work.SSGRoute.cyclic_transfer_of_vanishing` (pro-cyclicity of
  `decomp k B / I_B`, `Work.SSGRoute.decomp_mod_inertia_cyclic`).

* **Some conjugate `Q = (sec s)⁻¹ • B` of `B` is ramified.**  By (b) at `Q`, `z` vanishes on the
  local group of every other conjugate of `Q`; distinct conjugates are never `G_K`-conjugate
  (`not_conj_conj_place`), so all terms of the transfer except the `s`-th vanish, and the `s`-th
  term is the composite of `δ ↦ (sec s)⁻¹ δ sec s` (an isomorphism
  `decomp k B ≅ decomp k Q ⊓ G_K`) with `z`, whose image on `decomp k Q ⊓ G_K` is cyclic by (b) at
  `Q`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section ZDataBridge

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)]
  {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]

/-- Integer multiples commute with the action of `Gal(K/k)` on `E`. -/
lemma smul_zsmul_group (s : K ≃ₐ[k] K) (m : ℤ) (x : E) : s • (m • x) = m • (s • x) := by
  have h := map_zsmul (DistribSMul.toAddMonoidHom E s) m x
  simpa using h

/-- **A normal open subgroup on which `z` vanishes**, obtained from local constancy. -/
lemma exists_normal_open_of_z_eq_zero (z : (Ω ≃ₐ[k] Ω) → E)
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧ U.Normal ∧
      ∀ u ∈ U, u ∈ K.fixingSubgroup → z u = 0 := by
  obtain ⟨U₀, hU₀open, hU₀c⟩ := hzloc
  obtain ⟨F, hFfin, hFnorm, hFle⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le (U := k) (L := Ω) U₀ hU₀open
  haveI := hFfin
  haveI := hFnorm
  haveI hFgal : IsGalois k ↥F := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  refine ⟨F.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen F,
    IsGalois.fixingSubgroup_normal_of_isGalois F, ?_⟩
  intro u hu huK
  have h := hU₀c 1 K.fixingSubgroup.one_mem u (hFle hu) huK
  rw [one_mul, z_one hzadd] at h
  exact h

/-- Two distinct conjugates of a place split in `K`, parametrised by a section of `res k K`, are
never `G_K`-conjugate: if `τ • ((sec s)⁻¹ • B) = (sec t)⁻¹ • B` with `τ ∈ G_K`, then
`(sec t) * τ * (sec s)⁻¹` stabilises `B`, so has trivial restriction to `K`, whence `t = s`. -/
lemma not_conj_conj_place {B : ValuationSubring Ω} (hsplitK : SSGRoute.IsSplitIn k K B)
    {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)} (hsec : ∀ s : K ≃ₐ[k] K, SSGRoute.res k K (sec s) = s)
    {s t : K ≃ₐ[k] K} (hst : s ≠ t) :
    ¬ ∃ τ ∈ K.fixingSubgroup, τ • ((sec s)⁻¹ • B) = (sec t)⁻¹ • B := by
  rintro ⟨τ, hτ, hτB⟩
  have hmem : (sec t) * τ * (sec s)⁻¹ ∈ SSGRoute.decomp k B := by
    rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff]
    calc ((sec t) * τ * (sec s)⁻¹) • B
        = (sec t) • (τ • ((sec s)⁻¹ • B)) := by rw [mul_smul, mul_smul]
      _ = (sec t) • ((sec t)⁻¹ • B) := by rw [hτB]
      _ = B := by rw [smul_inv_smul]
  have hres : SSGRoute.res k K ((sec t) * τ * (sec s)⁻¹) = 1 :=
    (res_eq_one_iff_mem_fixingSubgroup (K := K) _).mpr (hsplitK hmem)
  rw [map_mul, map_mul, map_inv, hsec t, hsec s, (res_eq_one_iff_mem_fixingSubgroup (K := K) τ).mpr hτ,
    mul_one] at hres
  exact hst (mul_inv_eq_one.mp hres).symm

/-- **The conclusion of `shafarevich_z_construction` from Schmidt--Wingberg's `z`-data**, with the
sharpened condition (b) triggered on ramification rather than on non-vanishing. -/
theorem shafarevich_z_construction_of_zData
    (hKΛ : K ≤ Λ) (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → E)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s : K ≃ₐ[k] K, SSGRoute.res k K (sec s) = s)
    (hzdata : ∃ z : (Ω ≃ₐ[k] Ω) → E,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            z δ ∈ AddSubgroup.zmultiples (z g)) ∧
        (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0))) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V,
            (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  obtain ⟨z, hzadd, hzloc, hzagree, hzinv, hzS, hzram⟩ := hzdata
  -- `z` is a `1`-cocycle for the trivial action of `G_K`
  have hzcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z := by
    intro g hg h hh
    rw [(res_eq_one_iff_mem_fixingSubgroup (K := K) g).mpr hg, one_smul]
    exact hzadd g hg h hh
  refine ⟨z, hzcoc, hzloc, hzagree, hzinv, hzS, ?_⟩
  intro B hBfin hnotconj hsplitΛ
  have hsplitK : SSGRoute.IsSplitIn k K B :=
    le_trans hsplitΛ (IntermediateField.fixingSubgroup_le hKΛ)
  -- the normal open subgroup on which `z` vanishes
  obtain ⟨U, hUopen, hUnorm, hUz⟩ := exists_normal_open_of_z_eq_zero z hzadd hzloc
  haveI := hUnorm
  -- the kernel of `z` on `G_K`
  let Z : Subgroup (Ω ≃ₐ[k] Ω) := kerOn K.fixingSubgroup z hzadd
  have hZmem : ∀ u : Ω ≃ₐ[k] Ω, u ∈ Z ↔ u ∈ K.fixingSubgroup ∧ z u = 0 := fun _ => Iff.rfl
  -- the intersection of the conjugates of `Z ⊔ U`
  let V : Subgroup (Ω ≃ₐ[k] Ω) := ⨅ s : K ≃ₐ[k] K, (Z ⊔ U).comap (MulAut.conj (sec s)⁻¹)
  have hVmem : ∀ u : Ω ≃ₐ[k] Ω, u ∈ V ↔ ∀ s : K ≃ₐ[k] K,
      (sec s)⁻¹ * u * (sec s) ∈ Z ⊔ U := by
    intro u
    rw [Subgroup.mem_iInf]
    exact forall_congr' (fun s => by simp [Subgroup.mem_comap, MulAut.conj_apply])
  have hVopen : IsOpen (V : Set (Ω ≃ₐ[k] Ω)) := by
    rw [Subgroup.coe_iInf]
    refine isOpen_iInter_of_finite (fun s => ?_)
    refine Subgroup.isOpen_mono ?_ hUopen
    intro u hu
    refine Subgroup.mem_comap.mpr (Subgroup.mem_sup_right ?_)
    simpa [MulAut.conj_apply] using hUnorm.conj_mem u hu (sec s)⁻¹
  -- it remains to show that the image of the transfer on `decomp k B` is cyclic
  suffices hcyc : ∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B,
      transfer z sec δ ∈ AddSubgroup.zmultiples (transfer z sec g) by
    obtain ⟨V', hV'o, hV'n, hV'c, hV'v⟩ :=
      exists_V_of_cyclic_transfer hsec hzadd hzloc B hsplitK hcyc
    exact ⟨V', hV'o, hV'n, hV'c, hV'v⟩
  by_cases hA : ∀ (s : K ≃ₐ[k] K) (σ : Ω ≃ₐ[k] Ω),
      SSGRoute.IsInertia k ((sec s)⁻¹ • B) σ → z σ = 0
  · -- case A: no conjugate of `B` is ramified
    have hI : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → σ ∈ V := by
      intro σ hσ
      rw [hVmem]
      intro s
      exact Subgroup.mem_sup_left ⟨conj_sec_mem_fixingSubgroup hsec s (hsplitK hσ.1),
        hA s ((sec s)⁻¹ * σ * (sec s)) ((isInertia_conj B (sec s)⁻¹ σ).mpr hσ)⟩
    have hVan : ∀ h ∈ SSGRoute.decomp k B ⊓ V, transfer z sec h = 0 := by
      intro h hh
      obtain ⟨hD, hV⟩ := Subgroup.mem_inf.mp hh
      unfold transfer
      refine Finset.sum_eq_zero (fun s _ => ?_)
      have hmem : (sec s)⁻¹ * h * (sec s) ∈
          ((Z ⊔ U : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := (hVmem h).mp hV s
      have hGK : (sec s)⁻¹ * h * (sec s) ∈ K.fixingSubgroup :=
        conj_sec_mem_fixingSubgroup hsec s (hsplitK hD)
      have hz0 : z ((sec s)⁻¹ * h * (sec s)) = 0 := by
        rw [Subgroup.mul_normal Z U] at hmem
        obtain ⟨a, haZ, b, hbU, hab⟩ := Set.mem_mul.mp hmem
        have haGK : a ∈ K.fixingSubgroup := ((hZmem a).mp haZ).1
        have hbGK : b ∈ K.fixingSubgroup := by
          have h1 : a * b ∈ K.fixingSubgroup := by rw [hab]; exact hGK
          have h2 : a⁻¹ * (a * b) ∈ K.fixingSubgroup :=
            K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem haGK) h1
          simpa using h2
        rw [← hab, hzadd a haGK b hbGK, ((hZmem a).mp haZ).2, hUz b hbU hbGK, add_zero]
      rw [hz0, smul_zero]
    exact cyclic_transfer_of_vanishing z sec hsec hzadd B hBfin hsplitK V hVopen hVan hI
  · -- case B: some conjugate of `B` is ramified
    push_neg at hA
    obtain ⟨s, σ, hσI, hσz⟩ := hA
    have hQfin : SSGRoute.IsFinPlace k ((sec s)⁻¹ • B) :=
      (isFinPlace_smul_iff B (sec s)⁻¹).mpr hBfin
    have hQconj : SSGRoute.IsConjPlace k B ((sec s)⁻¹ • B) := ⟨(sec s)⁻¹, rfl⟩
    have hQnotconj : ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A ((sec s)⁻¹ • B) := fun A hA' hc =>
      hnotconj A hA' (SSGRoute.isConjPlace_trans hc (SSGRoute.isConjPlace_symm hQconj))
    have hQsplitΛ : SSGRoute.IsSplitIn k Λ ((sec s)⁻¹ • B) := by
      haveI hnorm : (Λ.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois Λ
      exact (SSGRoute.isSplitIn_conj Λ hnorm B (sec s)⁻¹).mpr hsplitΛ
    have hQsplitK : SSGRoute.IsSplitIn k K ((sec s)⁻¹ • B) :=
      le_trans hQsplitΛ (IntermediateField.fixingSubgroup_le hKΛ)
    have hσGK : σ ∈ K.fixingSubgroup := hQsplitK hσI.1
    obtain ⟨hcycQ, hvanQ⟩ := hzram ((sec s)⁻¹ • B) hQfin hQnotconj hQsplitΛ ⟨σ, hσI, hσGK, hσz⟩
    -- every term of the transfer except the `s`-th vanishes
    have hkill : ∀ t : K ≃ₐ[k] K, t ≠ s → ∀ h ∈ SSGRoute.decomp k B,
        z ((sec t)⁻¹ * h * (sec t)) = 0 := by
      intro t ht h hh
      have hconj' : SSGRoute.IsConjPlace k ((sec s)⁻¹ • B) ((sec t)⁻¹ • B) :=
        ⟨(sec t)⁻¹ * sec s, by rw [mul_smul, smul_inv_smul]⟩
      have hnconj : ¬ ∃ τ ∈ K.fixingSubgroup,
          τ • ((sec s)⁻¹ • B) = (sec t)⁻¹ • B :=
        not_conj_conj_place hsplitK hsec (Ne.symm ht)
      refine hvanQ ((sec t)⁻¹ • B) hconj' hnconj _ ?_
      refine Subgroup.mem_inf.mpr ⟨?_, conj_sec_mem_fixingSubgroup hsec t (hsplitK hh)⟩
      rw [SSGRoute.decomp_conj]
      exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    have hsingle : ∀ h ∈ SSGRoute.decomp k B,
        transfer z sec h = s • z ((sec s)⁻¹ * h * (sec s)) := by
      intro h hh
      unfold transfer
      rw [Finset.sum_eq_single s]
      · intro t _ ht
        rw [hkill t ht h hh, smul_zero]
      · intro hs
        exact absurd (Finset.mem_univ s) hs
    -- pull the generator of the cyclic local group at `(sec s)⁻¹ • B` back to `decomp k B`
    obtain ⟨gQ, hgQ, hgQcyc⟩ := hcycQ
    obtain ⟨g, hgD, hgeq⟩ : ∃ g ∈ SSGRoute.decomp k B, (sec s)⁻¹ * g * (sec s) = gQ := by
      have h1 : gQ ∈ (SSGRoute.decomp k B).map (MulAut.conj (sec s)⁻¹).toMonoidHom := by
        rw [← SSGRoute.decomp_conj B (sec s)⁻¹]
        exact hgQ.1
      obtain ⟨g, hgD, hgeq⟩ := Subgroup.mem_map.mp h1
      exact ⟨g, hgD, by simpa [MulAut.conj_apply] using hgeq⟩
    refine ⟨g, hgD, fun δ hδ => ?_⟩
    rw [hsingle δ hδ, hsingle g hgD, hgeq]
    have hcsδ : (sec s)⁻¹ * δ * (sec s) ∈
        SSGRoute.decomp k ((sec s)⁻¹ • B) ⊓ K.fixingSubgroup := by
      refine Subgroup.mem_inf.mpr ⟨?_, conj_sec_mem_fixingSubgroup hsec s (hsplitK hδ)⟩
      rw [SSGRoute.decomp_conj]
      exact Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgQcyc _ hcsδ)
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
    rw [← hm, smul_zsmul_group]

end ZDataBridge

end Work.SSGRoute
