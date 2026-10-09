import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.ZConstruction.Reduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The remaining interface of `Work.SSGRoute.shafarevich_z_construction`

`Work.SSGRoute.shafarevich_z_construction_of_swData` shows that the conclusion of
`shafarevich_z_construction` follows from the existence of a cochain `z` with the *local* conditions
of Schmidt–Wingberg §4 (their (a) plus the sharpened (b): at every new ramification place `P`
outside `cs(S)` the image of `z` on the local group `decomp k P ⊓ G_K` is cyclic and `z` vanishes on
the local group of every *other* conjugate of `P`).

Everything in this file is elementary: no local field theory, no Chebotarev.  The point of the
sharpened (b) is exactly that it makes the transfer computable: for a place `B` outside `cs(S)` that
is split in `Λ`, at most one of the conjugates `(sec s)⁻¹ • B` contributes to the transfer, so the
image of the transfer on `decomp k B` is (up to the Galois action) the image of `z` on the local
group of that single conjugate — hence cyclic by (b).  The `∃ V`-form of the last conjunct of the
theorem is then supplied by `Work.SSGRoute.exists_V_of_cyclic_transfer`.
-/

open scoped Pointwise TensorProduct

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

section SWData

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)]

/-- The conjugates of `B` parametrised by the section: `(sec s)⁻¹ • B` is a conjugate of `B`. -/
lemma isConjPlace_conj_place {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)} (B : ValuationSubring Ω)
    (s : K ≃ₐ[k] K) : SSGRoute.IsConjPlace k B ((sec s)⁻¹ • B) :=
  ⟨(sec s)⁻¹, rfl⟩

/-- If `B` is split in `K`, the parametrisation `s ↦ (sec s)⁻¹ • B` of the conjugates of `B` is
injective. -/
lemma conj_place_injective {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)}
    (hsec : ∀ s : K ≃ₐ[k] K, SSGRoute.res k K (sec s) = s) {B : ValuationSubring Ω}
    (hsplitK : SSGRoute.IsSplitIn k K B) {s t : K ≃ₐ[k] K}
    (h : (sec s)⁻¹ • B = (sec t)⁻¹ • B) : s = t := by
  have hmem : ((sec t) * (sec s)⁻¹) ∈ SSGRoute.decomp k B := by
    rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff]
    rw [mul_smul, h, smul_inv_smul]
  have hGK : ((sec t) * (sec s)⁻¹) ∈ K.fixingSubgroup := hsplitK hmem
  have h1 : SSGRoute.res k K ((sec t) * (sec s)⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
    exact hGK
  rw [map_mul, map_inv, hsec t, hsec s] at h1
  exact (mul_inv_eq_one.mp h1).symm

/-- For `s ≠ 1` the conjugate `(sec s)⁻¹ • B` is different from `B`. -/
lemma conj_place_ne {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)}
    (hsec : ∀ s : K ≃ₐ[k] K, SSGRoute.res k K (sec s) = s) {B : ValuationSubring Ω}
    (hsplitK : SSGRoute.IsSplitIn k K B) {s : K ≃ₐ[k] K} (hs : s ≠ 1) :
    (sec s)⁻¹ • B ≠ B := by
  intro h
  have hmem : (sec s)⁻¹ ∈ SSGRoute.decomp k B := by
    rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff]
    exact h
  have h1 : SSGRoute.res k K (sec s)⁻¹ = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
    exact hsplitK hmem
  rw [map_inv, hsec s] at h1
  exact hs (inv_eq_one.mp h1)

/-- A conjugate of a place split in `K` is again split in `K`. -/
lemma isSplitIn_conj_place {B : ValuationSubring Ω} (hsplitK : SSGRoute.IsSplitIn k K B)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (s : K ≃ₐ[k] K) :
    SSGRoute.IsSplitIn k K ((sec s)⁻¹ • B) := by
  haveI hnorm : (K.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois K
  exact (SSGRoute.isSplitIn_conj K hnorm B (sec s)⁻¹).mpr hsplitK

end SWData

section Main

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)]
  {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]

open _root_.SSGRoute

/-- **The conclusion of `shafarevich_z_construction` from Schmidt–Wingberg's local data.**  If there
is a cochain `z` which is a locally constant `1`-cocycle on `G_K`, agrees with `y` on the
decomposition groups of the places of `cs(S)`, kills the involutions and the outside inertia, and
satisfies the sharpened cyclicity condition (b) of Schmidt–Wingberg §4 outside `cs(S)` — namely, at
every place `B` outside `cs(S)` split in `Λ` where `z` does not vanish on `decomp k B ⊓ G_K`, the
image of `z` on `decomp k B ⊓ G_K` is cyclic and `z` vanishes on the local group of every *other*
conjugate of `B` — then `z` satisfies all six conjuncts of `shafarevich_z_construction`. -/
theorem shafarevich_z_construction_of_swData
    (hKΛ : K ≤ Λ)
    (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → E)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω))
    (hsec : ∀ s : K ≃ₐ[k] K, SSGRoute.res k K (sec s) = s)
    (hSW : ∃ z : (Ω ≃ₐ[k] Ω) → E,
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
        (∃ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z δ ≠ 0) →
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
  obtain ⟨z, hzcoc, hzloc, hzagree, hzinv, hzS, hzram⟩ := hSW
  refine ⟨z, hzcoc, hzloc, hzagree, hzinv, hzS, ?_⟩
  intro B hBfin hconj hsplitΛ
  have hsplitK : SSGRoute.IsSplitIn k K B :=
    le_trans hsplitΛ (IntermediateField.fixingSubgroup_le hKΛ)
  -- `z` is additive on `G_K`
  have hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h := by
    intro g hg h hh
    have h2 : SSGRoute.res k K g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
      exact hg
    rw [hzcoc g hg h hh, h2, one_smul]
  -- the `s`-th conjugate of `B`, and the fact that the corresponding `z`-term is `0` unless
  -- `s = t`
  have hkill : ∀ t : K ≃ₐ[k] K,
      (∃ δ ∈ SSGRoute.decomp k ((sec t)⁻¹ • B) ⊓ K.fixingSubgroup, z δ ≠ 0) →
      ∀ s : K ≃ₐ[k] K, s ≠ t →
      ∀ τ ∈ SSGRoute.decomp k ((sec s)⁻¹ • B) ⊓ K.fixingSubgroup, z τ = 0 := by
    intro t hwit s hst τ hτ
    have hBtfin : SSGRoute.IsFinPlace k ((sec t)⁻¹ • B) :=
      (isFinPlace_smul_iff B (sec t)⁻¹).mpr hBfin
    have hBtconj : SSGRoute.IsConjPlace k B ((sec t)⁻¹ • B) := isConjPlace_conj_place B t
    have hBtconjS : ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A ((sec t)⁻¹ • B) := fun A hA hc =>
      hconj A hA (SSGRoute.isConjPlace_trans hc (SSGRoute.isConjPlace_symm hBtconj))
    have hBtsplit : SSGRoute.IsSplitIn k Λ ((sec t)⁻¹ • B) := by
      haveI hnorm : (Λ.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois Λ
      exact (SSGRoute.isSplitIn_conj Λ hnorm B (sec t)⁻¹).mpr hsplitΛ
    obtain ⟨-, hvan⟩ := hzram ((sec t)⁻¹ • B) hBtfin hBtconjS hBtsplit hwit
    refine hvan ((sec s)⁻¹ • B) ?_ ?_ τ hτ
    · exact ⟨(sec s)⁻¹ * sec t, by rw [mul_smul, smul_inv_smul]⟩
    · -- `(sec s)⁻¹ • B` is not a `G_K`-conjugate of `(sec t)⁻¹ • B` when `s ≠ t`
      rintro ⟨v, hv, hvv⟩
      have hv1 : SSGRoute.res k K v = 1 :=
        (res_eq_one_iff_mem_fixingSubgroup (K := K) v).mpr hv
      have h1 : v⁻¹ • ((sec s)⁻¹ • B) = (sec t)⁻¹ • B := by
        rw [← hvv, inv_smul_smul]
      have hw : (sec t) * v⁻¹ * (sec s)⁻¹ ∈ SSGRoute.decomp k B := by
        rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff]
        rw [mul_smul, mul_smul, h1, smul_inv_smul]
      have hres : SSGRoute.res k K ((sec t) * v⁻¹ * (sec s)⁻¹) = 1 :=
        (res_eq_one_iff_mem_fixingSubgroup (K := K) _).mpr (hsplitK hw)
      rw [map_mul, map_mul, map_inv, map_inv, hsec t, hsec s, hv1] at hres
      exact hst (mul_inv_eq_one.mp hres).symm
  -- the transfer at `B` is `0` unless the `t`-th conjugate carries a non-zero value
  have htrans : ∀ t : K ≃ₐ[k] K,
      (∃ δ ∈ SSGRoute.decomp k ((sec t)⁻¹ • B) ⊓ K.fixingSubgroup, z δ ≠ 0) →
      ∀ δ ∈ SSGRoute.decomp k B,
        transfer z sec δ = t • z ((sec t)⁻¹ * δ * sec t) := by
    intro t hwit δ hδ
    unfold transfer
    rw [Finset.sum_eq_single t]
    · intro s _ hs
      rw [hkill t hwit s hs _ (by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [SSGRoute.decomp_conj]
          exact Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩
        · exact conj_sec_mem_fixingSubgroup hsec s (hsplitK hδ)), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ t) h
  -- cyclicity of the transfer on `decomp k B`
  have hcycT : ∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B,
      transfer z sec δ ∈ AddSubgroup.zmultiples (transfer z sec g) := by
    by_cases ht : ∃ t : K ≃ₐ[k] K,
        ∃ δ ∈ SSGRoute.decomp k ((sec t)⁻¹ • B) ⊓ K.fixingSubgroup, z δ ≠ 0
    · obtain ⟨t, hwit⟩ := ht
      have hBtfin : SSGRoute.IsFinPlace k ((sec t)⁻¹ • B) :=
        (isFinPlace_smul_iff B (sec t)⁻¹).mpr hBfin
      have hBtconj : SSGRoute.IsConjPlace k B ((sec t)⁻¹ • B) := isConjPlace_conj_place B t
      have hBtconjS : ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A ((sec t)⁻¹ • B) := by
        intro A hA hc
        exact hconj A hA (SSGRoute.isConjPlace_trans hc (SSGRoute.isConjPlace_symm hBtconj))
      have hBtsplit : SSGRoute.IsSplitIn k Λ ((sec t)⁻¹ • B) := by
        haveI hnorm : (Λ.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois Λ
        exact (SSGRoute.isSplitIn_conj Λ hnorm B (sec t)⁻¹).mpr hsplitΛ
      obtain ⟨⟨g_t, hg_t, hcyc_t⟩, -⟩ := hzram ((sec t)⁻¹ • B) hBtfin hBtconjS hBtsplit hwit
      set g : Ω ≃ₐ[k] Ω := (sec t) * g_t * (sec t)⁻¹ with hg
      have hg_t_stab : g_t • ((sec t)⁻¹ • B) = (sec t)⁻¹ • B := by
        have h1 : g_t ∈ SSGRoute.decomp k ((sec t)⁻¹ • B) := (Subgroup.mem_inf.mp hg_t).1
        rwa [SSGRoute.decomp, MulAction.mem_stabilizer_iff] at h1
      have hgmem : g ∈ SSGRoute.decomp k B := by
        rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff]
        rw [hg, mul_smul, mul_smul, hg_t_stab, smul_inv_smul]
      have hgen : transfer z sec g = t • z g_t := by
        rw [htrans t hwit g hgmem, hg]
        congr 1
        group
      refine ⟨g, hgmem, fun δ hδ => ?_⟩
      rw [htrans t hwit δ hδ, hgen]
      have hconj : (sec t)⁻¹ * δ * sec t ∈ SSGRoute.decomp k ((sec t)⁻¹ • B) ⊓ K.fixingSubgroup := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [SSGRoute.decomp_conj]
          exact Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩
        · exact conj_sec_mem_fixingSubgroup hsec t (hsplitK hδ)
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hcyc_t _ hconj)
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
      rw [← smul_comm t (m : ℤ) (z g_t), hm]
    · push_neg at ht
      have hzero : ∀ δ ∈ SSGRoute.decomp k B, transfer z sec δ = 0 := by
        intro δ hδ
        unfold transfer
        refine Finset.sum_eq_zero fun s _ => ?_
        have hmem : (sec s)⁻¹ * δ * sec s ∈
            SSGRoute.decomp k ((sec s)⁻¹ • B) ⊓ K.fixingSubgroup := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · rw [SSGRoute.decomp_conj]
            exact Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩
          · exact conj_sec_mem_fixingSubgroup hsec s (hsplitK hδ)
        rw [ht s _ hmem, smul_zero]
      exact ⟨1, (SSGRoute.decomp k B).one_mem, fun δ hδ => by
        rw [hzero δ hδ, hzero 1 (SSGRoute.decomp k B).one_mem]
        exact AddSubgroup.zero_mem _⟩
  obtain ⟨V, hVo, hVn, hVc, hVv⟩ :=
    exists_V_of_cyclic_transfer hsec hzadd hzloc B hsplitK hcycT
  exact ⟨V, hVo, hVn, hVc, fun δ hδ => hVv δ hδ⟩

end Main

end Work.SSGRoute
