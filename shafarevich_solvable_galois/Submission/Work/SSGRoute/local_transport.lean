import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of decomposition / inertia data between `ℚ` and a finite intermediate field

Let `K ⊆ ℚ̄` be a finite extension of `ℚ` and `A` a valuation subring of `ℚ̄` (a place above `ℚ`).
The map `K.fixingSubgroup ≃* Gal(ℚ̄/K)` (`IntermediateField.fixingSubgroupEquiv`) is the identity on
the underlying functions, so all the local data attached to a place transports along it:

* `local_transport_decomp` — an element of `K.fixingSubgroup` stabilises `A` seen over `K` iff it
  stabilises `A` seen over `ℚ` (`MulAction.stabilizer`, i.e. `SSGRoute.decomp`);
* `local_transport_isInertia` — the same for the inertia condition;
* `local_transport_isFinPlace` — the restriction of `A` to `K` is a nontrivial place of `K` iff its
  restriction to `ℚ` is a nontrivial place of `ℚ`.  Here integrality is used: a valuation subring is
  integrally closed, and `ℚ̄` is algebraic over `ℚ`, so a place of `ℚ̄` whose restriction to `ℚ` is
  trivial is the whole of `ℚ̄`;
* `local_transport_isRamifiedIn` — the corresponding statement for `SSGRoute.IsRamifiedIn`.

These are the four components of `Work.SSGRoute.local_transport`.
-/

open scoped Pointwise

namespace Work.SSGRoute

/-- An element `σ ∈ K.fixingSubgroup` stabilises `A` viewed as a place of `ℚ̄/↥K`
(i.e. the image of `σ` under `IntermediateField.fixingSubgroupEquiv K` lies in
`SSGRoute.decomp ↥K A`) if and only if `σ` stabilises `A` viewed as a place of `ℚ̄/ℚ`. -/
lemma local_transport_decomp (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (A : ValuationSubring SSGRoute.QBar) (σ : SSGRoute.GalQ) (hσ : σ ∈ K.fixingSubgroup) :
    ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ ∈ SSGRoute.decomp ↥K A) ↔
      σ ∈ SSGRoute.decomp ℚ A := by
  have hfun : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ : SSGRoute.QBar → SSGRoute.QBar)
      = ⇑σ := rfl
  -- The two actions agree because they only depend on the underlying function.
  have hsmul : (IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩ :
        SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) • A
      = (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) • A := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists,
      ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hfun]⟩
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hfun]⟩
  rw [SSGRoute.decomp, SSGRoute.decomp, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, hsmul]

/-- An element `σ ∈ K.fixingSubgroup` lies in the inertia group of `A` over `↥K`
(after transporting `σ` through `IntermediateField.fixingSubgroupEquiv K`) if and only if
it lies in the inertia group of `A` over `ℚ`. -/
lemma local_transport_isInertia (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (A : ValuationSubring SSGRoute.QBar) (σ : SSGRoute.GalQ) (hσ : σ ∈ K.fixingSubgroup) :
    SSGRoute.IsInertia ↥K A ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) ↔
      SSGRoute.IsInertia ℚ A σ := by
  have hfun : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ : SSGRoute.QBar → SSGRoute.QBar)
      = ⇑σ := rfl
  rw [SSGRoute.IsInertia, SSGRoute.IsInertia, local_transport_decomp K A σ hσ, hfun]

/-- The restriction of a place `A` of `ℚ̄` to the finite extension `K` is a nontrivial place
(a finite place) if and only if its restriction to `ℚ` is.

Indeed, if `A` contains `ℚ` then it contains `K`: a valuation subring is integrally closed in its
field of fractions, and `K ⊆ ℚ̄` is algebraic (even integral, being finite) over `ℚ`. -/
lemma local_transport_isFinPlace (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (A : ValuationSubring SSGRoute.QBar) :
    SSGRoute.IsFinPlace ↥K A ↔ SSGRoute.IsFinPlace ℚ A := by
  have hAlgClosure : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ
  have hAlgebraic : Algebra.IsAlgebraic ℚ SSGRoute.QBar := IsAlgClosure.isAlgebraic
  have hIntegral : Algebra.IsIntegral ℚ SSGRoute.QBar := Algebra.IsAlgebraic.isIntegral
  -- `A` is integrally closed in `ℚ̄`, and every element of `ℚ̄` is integral over `ℚ`; hence
  -- if `ℚ ⊆ A` then already `A = ⊤`.
  have nice : ∀ y : SSGRoute.QBar, (∀ r : ℚ, algebraMap ℚ SSGRoute.QBar r ∈ A) → y ∈ A := by
    intro y hq
    have hIC : IsIntegrallyClosedIn ↥A.toSubring SSGRoute.QBar :=
      Subring.isIntegrallyClosedIn_iff.mpr fun z hz =>
        LocalSubring.mem_of_isMax_of_isIntegral A.isMax_toLocalSubring hz
    have hle : (integralClosure ℚ SSGRoute.QBar).toSubring ≤ A.toSubring := by
      rw [Subring.integralClosure_le_iff]
      intro r
      rw [ValuationSubring.mem_toSubring]
      exact hq r
    exact hle ((mem_integralClosure_iff ℚ SSGRoute.QBar).mpr (Algebra.IsIntegral.isIntegral y))
  constructor
  · intro h hq
    have hq' : ∀ r : ℚ, algebraMap ℚ SSGRoute.QBar r ∈ A := fun r => by
      have : r ∈ A.comap (algebraMap ℚ SSGRoute.QBar) := by rw [hq]; trivial
      rwa [ValuationSubring.mem_comap] at this
    apply h
    rw [eq_top_iff]
    intro x _
    rw [ValuationSubring.mem_comap]
    exact nice (algebraMap ↥K SSGRoute.QBar x) hq'
  · intro h hk
    apply h
    rw [eq_top_iff]
    intro q _
    rw [ValuationSubring.mem_comap]
    have hmem : algebraMap ↥K SSGRoute.QBar (algebraMap ℚ ↥K q) ∈ A := by
      have : algebraMap ℚ ↥K q ∈ A.comap (algebraMap ↥K SSGRoute.QBar) := by rw [hk]; trivial
      rwa [ValuationSubring.mem_comap] at this
    rwa [IsScalarTower.algebraMap_apply ℚ ↥K SSGRoute.QBar]

/-- A place `A` of `ℚ̄` ramifies in an extension `N/↥K` (with `N` an intermediate field of
`ℚ̄/↥K`) if and only if there is an element `σ` of `Gal(ℚ̄/ℚ)` fixing `K`, lying in the inertia
group of `A` over `ℚ` and not fixing `N` pointwise. -/
lemma local_transport_isRamifiedIn (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (N : IntermediateField ↥K SSGRoute.QBar) (A : ValuationSubring SSGRoute.QBar) :
    SSGRoute.IsRamifiedIn ↥K N A ↔
      ∃ σ : SSGRoute.GalQ, σ ∈ K.fixingSubgroup ∧
        SSGRoute.IsInertia ℚ A σ ∧
        σ ∉ (N.restrictScalars ℚ).fixingSubgroup := by
  constructor
  · rintro ⟨τ, hτI, hτN⟩
    let u : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm τ
    have hueq : (IntermediateField.fixingSubgroupEquiv K) u = τ := MulEquiv.apply_symm_apply _ _
    have hcoe : ⇑((u : SSGRoute.GalQ)) = ⇑τ := funext fun _ => rfl
    refine ⟨(u : SSGRoute.GalQ), u.2, ?_, ?_⟩
    · rw [← local_transport_isInertia K A (u : SSGRoute.GalQ) u.2]
      rw [show (⟨(u : SSGRoute.GalQ), u.2⟩ : ↥(K.fixingSubgroup)) = u from rfl, hueq]
      exact hτI
    · intro h
      apply hτN
      rw [IntermediateField.mem_fixingSubgroup_iff] at h ⊢
      intro x hx
      have hx' : x ∈ IntermediateField.restrictScalars ℚ N := by
        rwa [IntermediateField.mem_restrictScalars ℚ]
      have h2 := h x hx'
      rw [hcoe] at h2
      exact h2
  · rintro ⟨σ, hσ, hI, hN⟩
    have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ :
        SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) = ⇑σ := funext fun _ => rfl
    refine ⟨(IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩, ?_, ?_⟩
    · exact (local_transport_isInertia K A σ hσ).mp hI
    · intro h
      apply hN
      rw [IntermediateField.mem_fixingSubgroup_iff] at h ⊢
      intro x hx
      have hx' : x ∈ N := by rwa [← IntermediateField.mem_restrictScalars ℚ]
      have h2 := h x hx'
      rw [hcoe] at h2
      exact h2

theorem local_transport (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] :
    (∀ (A : ValuationSubring SSGRoute.QBar) {σ : SSGRoute.GalQ} (hσ : σ ∈ K.fixingSubgroup),
      ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ ∈ SSGRoute.decomp ↥K A) ↔
        σ ∈ SSGRoute.decomp ℚ A) ∧
    (∀ (A : ValuationSubring SSGRoute.QBar) {σ : SSGRoute.GalQ} (hσ : σ ∈ K.fixingSubgroup),
      SSGRoute.IsInertia ↥K A ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) ↔
        SSGRoute.IsInertia ℚ A σ) ∧
    (∀ A : ValuationSubring SSGRoute.QBar,
      SSGRoute.IsFinPlace ↥K A ↔ SSGRoute.IsFinPlace ℚ A) ∧
    (∀ (N : IntermediateField ↥K SSGRoute.QBar) (A : ValuationSubring SSGRoute.QBar),
      SSGRoute.IsRamifiedIn ↥K N A ↔
        ∃ σ : SSGRoute.GalQ, σ ∈ K.fixingSubgroup ∧
          SSGRoute.IsInertia ℚ A σ ∧
          σ ∉ (N.restrictScalars ℚ).fixingSubgroup) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A σ hσ
    exact local_transport_decomp K A σ hσ
  · intro A σ hσ
    exact local_transport_isInertia K A σ hσ
  · intro A
    exact local_transport_isFinPlace K A
  · intro N A
    exact local_transport_isRamifiedIn K N A

end Work.SSGRoute
