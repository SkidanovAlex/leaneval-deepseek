import Mathlib
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the two coordinates of `D_A = I ⋊ C`, with the missing closedness hypothesis

`Submission/Work/SSGRoute/HS/Setup.lean` provides, for a subgroup `I` normalised by
`D_A = decomp k A` and the procyclic closed subgroup `C = closure (zpowers σ)`, with
`D_A ≤ I ⊔ C` and `I ⊓ C = ⊥`, the two coordinates

* `HS.proj : ↥D_A → ↥C` (the `C`-coordinate, a group homomorphism, `HS.proj_mul`),
* `HS.ip : ↥D_A → ↥I` (the `I`-coordinate), with `HS.ip d * HS.proj d = d` (`HS.ip_mul_proj`).

`Submission/Work/SSGRoute/HSTwoRow/continuous_proj_ip.lean` states that these are continuous.
**As filed there, that statement is not provable**: the intended proof (this file's, and the one
sketched in that file's own docstring) exhibits `proj` as the inverse of the continuous bijection

  `Φ : ↥C → ↥D_A ⧸ ↥(I.subgroupOf D_A)`,  `γ ↦ γ · I`,

which is a homeomorphism because its domain is compact and its codomain Hausdorff — and the
codomain is Hausdorff only when `I` is closed (`QuotientGroup.instT2Space` needs
`IsClosed ↑(I.subgroupOf D_A)`).  The binder list of that file contains no `IsClosed I`, while its
docstring says "`↑I` is closed in `↥D_A` because `I` is closed in `Ω ≃ₐ[k] Ω`" — a hypothesis that
is not available.  Both consumers, `HSTwoRow.transgression_injective` and
`HSTwoRow.coker_injects_H2loc`, **do** carry `hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω))`, so the
corrected statement below is the one that is usable.

The statements are proved here in the namespace `Work.SSGRoute.HSRow`, with the coordinates and
subgroups of `HS.Setup`; the identification of `proj` with `ℓ.symm` uses only `HS.ip_mul_proj`
(no `Classical.choose`-independence is needed).
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The `C`-coordinate of `D_A = I ⋊ C` is continuous.**  (`IsClosed I` added: the statement as
filed in `HSTwoRow/continuous_proj_ip.lean` omits it, but the Hausdorffness of the relevant quotient
needs it, and both consumers carry it.) -/
theorem continuous_proj
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A)
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥)
    (hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω))) :
    Continuous (Work.SSGRoute.HS.proj A I σ hI hnorm
      (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup) := by
  classical
  have hCD : Subgroup.topologicalClosure (Subgroup.zpowers σ) ≤ SSGRoute.decomp k A :=
    Work.SSGRoute.HS.CC_le_DD A σ hσ
  haveI : CompactSpace ↥(SSGRoute.decomp k A) :=
    isCompact_iff_compactSpace.mp (Work.SSGRoute.HS.isClosed_decomp A).isCompact
  haveI : CompactSpace ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure _).isCompact
  have hIdc : IsClosed ((I.subgroupOf (SSGRoute.decomp k A) : Subgroup ↥(SSGRoute.decomp k A)) :
      Set ↥(SSGRoute.decomp k A)) := by
    rw [Subgroup.coe_subgroupOf]
    exact hIclosed.preimage continuous_subtype_val
  haveI : IsClosed ((I.subgroupOf (SSGRoute.decomp k A) : Subgroup ↥(SSGRoute.decomp k A)) :
      Set ↥(SSGRoute.decomp k A)) := hIdc
  haveI : T2Space (↥(SSGRoute.decomp k A) ⧸ (I.subgroupOf (SSGRoute.decomp k A))) :=
    QuotientGroup.instT2Space
  -- the continuous bijection `Φ`
  let Φ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →
      ↥(SSGRoute.decomp k A) ⧸ (I.subgroupOf (SSGRoute.decomp k A)) :=
    fun γ => QuotientGroup.mk (s := I.subgroupOf (SSGRoute.decomp k A))
      (⟨γ.1, hCD γ.2⟩ : ↥(SSGRoute.decomp k A))
  have hΦcont : Continuous Φ :=
    QuotientGroup.continuous_mk.comp (continuous_subtype_val.subtype_mk (fun γ => hCD γ.2))
  have hΦinj : Function.Injective Φ := by
    intro γ₁ γ₂ h
    have h' : (⟨γ₁.1, hCD γ₁.2⟩ : ↥(SSGRoute.decomp k A))⁻¹ *
        ⟨γ₂.1, hCD γ₂.2⟩ ∈ I.subgroupOf (SSGRoute.decomp k A) :=
      QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h'
    have hI' : γ₁.1⁻¹ * γ₂.1 ∈ I := h'
    have hC' : γ₁.1⁻¹ * γ₂.1 ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ γ₁.2) γ₂.2
    have hbot : γ₁.1⁻¹ * γ₂.1 ∈ (⊥ : Subgroup (Ω ≃ₐ[k] Ω)) := by
      rw [← hinf]
      exact Subgroup.mem_inf.mpr ⟨hI', hC'⟩
    have h1 : γ₁.1⁻¹ * γ₂.1 = 1 := Subgroup.mem_bot.mp hbot
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have hΦsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨d, rfl⟩ := Quotient.exists_rep x
    obtain ⟨i, hi, γ, hγ, hfac⟩ :=
      Work.SSGRoute.HS.exists_factor A I σ hI hnorm hCD hsup d.2
    refine ⟨⟨γ, hγ⟩, ?_⟩
    have hmem : (⟨γ, hCD hγ⟩ : ↥(SSGRoute.decomp k A))⁻¹ * d ∈
        I.subgroupOf (SSGRoute.decomp k A) := by
      rw [Subgroup.mem_subgroupOf]
      show γ⁻¹ * d.1 ∈ I
      rw [← hfac]
      have hconj := hnorm γ⁻¹ (hCD (Subgroup.inv_mem _ hγ)) i hi
      simpa [inv_inv, mul_assoc] using hconj
    exact QuotientGroup.eq.mpr hmem
  -- the homeomorphism `Φ`
  let e : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) ≃
      ↥(SSGRoute.decomp k A) ⧸ (I.subgroupOf (SSGRoute.decomp k A)) :=
    Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have he : Continuous (e : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) → _) := hΦcont
  let ℓ := Continuous.homeoOfEquivCompactToT2 (f := e) he
  -- `proj` is the inverse of `Φ`
  have hmem_proj : ∀ d : ↥(SSGRoute.decomp k A),
      (⟨(Work.SSGRoute.HS.proj A I σ hI hnorm
            (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω),
          hCD (Work.SSGRoute.HS.proj A I σ hI hnorm
            (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2⟩ : ↥(SSGRoute.decomp k A))⁻¹ * d ∈
        I.subgroupOf (SSGRoute.decomp k A) := by
    intro d
    rw [Subgroup.mem_subgroupOf]
    show ((Work.SSGRoute.HS.proj A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω))⁻¹ * (d : Ω ≃ₐ[k] Ω) ∈ I
    have hfac := Work.SSGRoute.HS.ip_mul_proj A I σ hI hnorm
      (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d
    have heq : ((Work.SSGRoute.HS.proj A I σ hI hnorm
            (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω))⁻¹ * (d : Ω ≃ₐ[k] Ω)
        = ((Work.SSGRoute.HS.proj A I σ hI hnorm
              (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω))⁻¹ *
            (Work.SSGRoute.HS.ip A I σ hI hnorm
              (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω) *
            (Work.SSGRoute.HS.proj A I σ hI hnorm
              (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω) := by
      rw [← hfac, mul_assoc]
    rw [heq]
    have hconj := hnorm (((Work.SSGRoute.HS.proj A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω)))⁻¹
      (hCD (Subgroup.inv_mem _ (Work.SSGRoute.HS.proj A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2))
      ((Work.SSGRoute.HS.ip A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω))
      (Work.SSGRoute.HS.ip A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2
    simpa [inv_inv] using hconj
  have hkey : (Work.SSGRoute.HS.proj A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup)
      = fun d : ↥(SSGRoute.decomp k A) =>
          ℓ.symm (QuotientGroup.mk (s := I.subgroupOf (SSGRoute.decomp k A)) d) := by
    funext d
    have h2 : ℓ (Work.SSGRoute.HS.proj A I σ hI hnorm
          (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d)
        = QuotientGroup.mk (s := I.subgroupOf (SSGRoute.decomp k A)) d := by
      show Φ (Work.SSGRoute.HS.proj A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d)
          = QuotientGroup.mk (s := I.subgroupOf (SSGRoute.decomp k A)) d
      exact QuotientGroup.eq.mpr (hmem_proj d)
    rw [← h2, Homeomorph.symm_apply_apply]
  rw [hkey]
  exact ℓ.symm.continuous.comp QuotientGroup.continuous_mk

/-- **The `I`-coordinate of `D_A = I ⋊ C` is continuous** (same `IsClosed I` correction as
`Work.SSGRoute.HSRow.continuous_proj`). -/
theorem continuous_ip
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A)
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥)
    (hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω))) :
    Continuous (Work.SSGRoute.HS.ip A I σ hI hnorm
      (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup) := by
  classical
  have hproj := continuous_proj k Ω A I σ hI hnorm hσ hsup hinf hIclosed
  have hmem : ∀ d : ↥(SSGRoute.decomp k A),
      (d : Ω ≃ₐ[k] Ω) * ((Work.SSGRoute.HS.proj A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω))⁻¹ ∈ I := by
    intro d
    have hfac := Work.SSGRoute.HS.ip_mul_proj A I σ hI hnorm
      (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d
    rw [← hfac]
    rw [mul_inv_cancel_right]
    exact (Work.SSGRoute.HS.ip A I σ hI hnorm
      (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2
  have hcont : Continuous (fun d : ↥(SSGRoute.decomp k A) =>
      (⟨(d : Ω ≃ₐ[k] Ω) * ((Work.SSGRoute.HS.proj A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω))⁻¹, hmem d⟩ : ↥I)) :=
    Continuous.subtype_mk (continuous_subtype_val.mul
      ((continuous_subtype_val.comp hproj).inv)) hmem
  refine hcont.congr ?_
  intro d
  exact Subtype.ext (by
    have hfac := Work.SSGRoute.HS.ip_mul_proj A I σ hI hnorm
      (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d
    show (d : Ω ≃ₐ[k] Ω) * ((Work.SSGRoute.HS.proj A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω))⁻¹
      = (Work.SSGRoute.HS.ip A I σ hI hnorm
        (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d : Ω ≃ₐ[k] Ω)
    rw [← hfac, mul_inv_cancel_right])

end

end Work.SSGRoute.HSRow

-- API probe (harmless)
#check @Quotient.exists_rep
#check @Homeomorph.symm_apply_apply
#check @inv_mul_eq_one
#check @mul_inv_cancel_right
#check @Continuous.congr
#check @Equiv.ofBijective
#check @QuotientGroup.eq
