import Mathlib
import Submission.Work.SSGRoute.step4_y_localdata
import Submission.Work.SSGRoute.twoOneFork.Step4YClauses
import Submission.Work.SSGRoute.local_transport
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.isLocConstOn_patchFun
import Submission.Work.SSGRoute.grunwald_distinct_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! TEMPORARY COPY (node lane, session 42) of `step4_yPrescribed_of_localData.lean`, with its import
of `step4_y_clauses` replaced by the *fork* `twoOneFork/Step4YClauses.lean` (whose body is identical
to `step4_y_clauses.lean`'s) so that the cone of `NodeS37.yExistsV2Node` does not contain both
`step4Helpers` and `twoOneFork.Step4Helpers` (the duplicate `Work.SSGRoute.Step4Input` clash).
The main theorem is renamed `step4_yPrescribed_of_localData_node`.  Delete once the fork is retired /
the duplicates renamed. -/

/-! # The clause verification `Step4YLocalData → Step4YPrescribed` of Step 4

This module turns the arithmetic output `Work.SSGRoute.Step4YLocalData D Tnew ηt` (a class `ε` on
`Gal(ℚ̄/↥K)` with the prescribed local behaviour) into the datum `Work.SSGRoute.Step4YPrescribed`
consumed by the node `Work.SSGRoute.step4_y_exists`: the function is `y := patchFun K ε`
(`ε` transported to `G_ℚ` and extended by `0` off `G_K`), and the ten clauses are the transports of
the local clauses of `ε` along

* `Work.SSGRoute.patchFun_of_mem` (values on `K.fixingSubgroup`),
* `Work.SSGRoute.local_transport_decomp` / `local_transport_isInertia` (`↥K` ↔ `ℚ` local data),
* `Work.SSGRoute.step4_conj_eq_of_additive_K` (conjugation invariance on the `↥K`-side, which makes
  the local data of `ε` depend only on the `K`-prime of a place).

The vanishing at the `ℚ`-conjugates `(D.sec s)⁻¹ • A` of the places of `Tnew` and of `D.T0`
(`s ≠ 1`) uses that those places have a `K`-prime distinct from all the `K`-primes of `Tnew`: an
`A ∈ Tnew` is completely split in `K`, so its conjugates are `↥K`-non-conjugate to it, and the
`ℚ`-non-conjugacy of the elements of `D.S` (`Step4CokerData.hSdisj`) upgrades this to
non-`↥K`-conjugacy with *every* element of `Tnew`. -/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking
open scoped Pointwise

set_option linter.unusedSectionVars false

/-! ## Small transport lemmas about places -/

/-- **`(-).valuation (p : ·) < 1` along a `comap`.**  A local copy of
`Work.SSGRoute.comap_valuation_lt_one_iff` (kept here so that this module only imports the light
dependencies). -/
theorem step4y_comap_valuation_lt_one {L₀ L : Type*} [Field L₀] [Field L] [Algebra L₀ L]
    (B : ValuationSubring L) (x : L₀) :
    (B.comap (algebraMap L₀ L)).valuation x < 1 ↔ B.valuation (algebraMap L₀ L x) < 1 := by
  have hsub : (B.comap (algebraMap L₀ L)).valuation.valuationSubring =
      (B.valuation.comap (algebraMap L₀ L)).valuationSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    ext y
    simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      ValuationSubring.valuation_le_one_iff, Valuation.comap_apply]
  have heq : (B.comap (algebraMap L₀ L)).valuation.IsEquiv
      (B.valuation.comap (algebraMap L₀ L)) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
  rw [Valuation.IsEquiv.lt_one_iff_lt_one heq]
  rfl

/-- Translating a place by an element of `G_ℚ` does not change whether it lies over `p`. -/
theorem step4y_smul_valuation_p_lt_one (p : ℕ) (B : ValuationSubring SSGRoute.QBar)
    (g : SSGRoute.GalQ) :
    (g • B).valuation (p : SSGRoute.QBar) < 1 ↔ B.valuation (p : SSGRoute.QBar) < 1 := by
  have h1 : ((g • B).comap (algebraMap ℚ SSGRoute.QBar)).valuation (p : ℚ) < 1 ↔
      (g • B).valuation (p : SSGRoute.QBar) < 1 := by
    simpa using (step4y_comap_valuation_lt_one (B := g • B) (x := (p : ℚ)))
  have h2 : ((B.comap (algebraMap ℚ SSGRoute.QBar)).valuation (p : ℚ) < 1) ↔
      B.valuation (p : SSGRoute.QBar) < 1 := by
    simpa using (step4y_comap_valuation_lt_one (B := B) (x := (p : ℚ)))
  rw [← h1, ← h2, comap_algebraMap_smul]

/-- The restriction to a finite normal intermediate field is trivial exactly on its fixing
subgroup. -/
theorem step4y_restrictNormalHom_eq_one_iff (K : IntermediateField ℚ SSGRoute.QBar) [hK : Normal ℚ K]
    (σ : SSGRoute.GalQ) :
    AlgEquiv.restrictNormalHom K σ = 1 ↔ σ ∈ K.fixingSubgroup := by
  rw [← MonoidHom.mem_ker]
  have h : (AlgEquiv.restrictNormalHom K).ker = K.fixingSubgroup :=
    @IntermediateField.restrictNormalHom_ker ℚ SSGRoute.QBar _ _ _ K hK
  rw [h]

/-- Conjugation by an element of `G_ℚ` preserves the fixing subgroup of a normal intermediate
field. -/
theorem step4y_conj_mem_fixingSubgroup (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    {g δ : SSGRoute.GalQ} (h : δ ∈ K.fixingSubgroup) : g * δ * g⁻¹ ∈ K.fixingSubgroup := by
  rw [← step4y_restrictNormalHom_eq_one_iff K]
  rw [map_mul, map_mul, map_inv, (step4y_restrictNormalHom_eq_one_iff K δ).mpr h]
  group

/-- Complete splitting in a normal extension `K/ℚ` is invariant under translating the place. -/
theorem step4y_isSplitIn_smul_iff (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (B : ValuationSubring SSGRoute.QBar) (g : SSGRoute.GalQ) :
    SSGRoute.IsSplitIn ℚ K (g • B) ↔ SSGRoute.IsSplitIn ℚ K B := by
  show SSGRoute.decomp ℚ (g • B) ≤ K.fixingSubgroup ↔
    SSGRoute.decomp ℚ B ≤ K.fixingSubgroup
  rw [decomp_conj, Subgroup.map_le_iff_le_comap]
  constructor
  · intro h δ hδ
    have h1 : g * δ * g⁻¹ ∈ K.fixingSubgroup := Subgroup.mem_comap.mp (h hδ)
    have hconj : g⁻¹ * (g * δ * g⁻¹) * (g⁻¹)⁻¹ ∈ K.fixingSubgroup :=
      step4y_conj_mem_fixingSubgroup K h1
    simpa using hconj
  · intro h δ hδ
    rw [Subgroup.mem_comap]
    exact step4y_conj_mem_fixingSubgroup K (h hδ)

/-- The `G_ℚ`-element underlying `(fixingSubgroupEquiv K).symm δ` is the restriction of scalars of
`δ`; in particular the two have the same underlying function. -/
theorem step4y_coe_symm_fixingSubgroupEquiv (K : IntermediateField ℚ SSGRoute.QBar)
    (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) :
    ⇑(((IntermediateField.fixingSubgroupEquiv K).symm δ : ↥(K.fixingSubgroup)) : SSGRoute.GalQ) =
      ⇑δ := rfl

/-- Inertia on the `↥K`-side transports to inertia over `ℚ` along `fixingSubgroupEquiv`. -/
theorem step4y_isInertia_symm_iff (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (A : ValuationSubring SSGRoute.QBar) (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) :
    SSGRoute.IsInertia ℚ A
        (((IntermediateField.fixingSubgroupEquiv K).symm δ : ↥(K.fixingSubgroup)) :
          SSGRoute.GalQ) ↔
      SSGRoute.IsInertia ↥K A δ := by
  have hmem : (((IntermediateField.fixingSubgroupEquiv K).symm δ : ↥(K.fixingSubgroup)) :
      SSGRoute.GalQ) ∈ K.fixingSubgroup :=
    ((IntermediateField.fixingSubgroupEquiv K).symm δ).2
  have h5 : (⟨(((IntermediateField.fixingSubgroupEquiv K).symm δ : ↥(K.fixingSubgroup)) :
        SSGRoute.GalQ), hmem⟩ : ↥(K.fixingSubgroup)) =
      (IntermediateField.fixingSubgroupEquiv K).symm δ := Subtype.ext rfl
  have h := local_transport_isInertia K A
    (((IntermediateField.fixingSubgroupEquiv K).symm δ : ↥(K.fixingSubgroup)) : SSGRoute.GalQ) hmem
  rw [h5, MulEquiv.apply_symm_apply] at h
  exact h.symm

/-- Translating a place of `ℚ̄` by an element of `K.fixingSubgroup` (viewed as a `ℚ`-algebra
automorphism) commutes with the `↥K`-component. -/
theorem step4y_smul_of_coe_symm (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    [Normal ℚ K]
    (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) (A : ValuationSubring SSGRoute.QBar) :
    (((IntermediateField.fixingSubgroupEquiv K).symm δ : ↥(K.fixingSubgroup)) : SSGRoute.GalQ) •
        A = δ • A := by
  exact (smul_congr K (x := δ) (step4y_coe_symm_fixingSubgroupEquiv K δ).symm).symm

/-! ## The auxiliary clauses -/

/-- **Vanishing at the places which are not `↥K`-conjugate to a `Tnew`-place.**  If `B` is a finite
place which is `ℚ`-conjugate to an element of `D.S`, but not `↥K`-conjugate to any element of
`Tnew`, then `ε` vanishes on the whole decomposition group of `B` (the `↥K`-side of `hzero`, with
the local data propagated along `↥K`-conjugacy of places). -/
theorem step4y_eps_zero_of_not_conj_Tnew (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (ηt : (A : ValuationSubring SSGRoute.QBar) → A ∈ Tnew →
      SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j)
    (hL : Step4YLocalData D Tnew ηt)
    (B : ValuationSubring SSGRoute.QBar) (hBfin : SSGRoute.IsFinPlace ℚ B)
    (hBconj : ∃ A ∈ D.S, SSGRoute.IsConjPlace ℚ A B)
    (hnew : ∀ A₀ ∈ Tnew, ¬ SSGRoute.IsConjPlace ↥K A₀ B) :
    ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, δ ∈ SSGRoute.decomp ↥K B → hL.ε δ = 0 := by
  intro δ hδ
  obtain ⟨A, hA, hconjAB⟩ := hL.hScover B hBfin hBconj
  obtain ⟨ρ, hρ⟩ := hconjAB
  have hzero : ∀ δ' : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar,
      δ' ∈ SSGRoute.decomp ↥K A → hL.ε δ' = 0 :=
    hL.hzero A hA (fun A₀ hA₀ hc =>
      hnew A₀ hA₀ (isConjPlace_trans (isConjPlace_symm hc) ⟨ρ, hρ⟩))
  have hmap : SSGRoute.decomp ↥K A =
      (SSGRoute.decomp ↥K B).map (MulAut.conj ρ⁻¹).toMonoidHom := by
    have hBA : ρ⁻¹ • B = A := by rw [← hρ, inv_smul_smul]
    rw [← hBA, decomp_conj B ρ⁻¹]
  have hmem : ρ⁻¹ * δ * ρ ∈ SSGRoute.decomp ↥K A := by
    rw [hmap]
    exact Subgroup.mem_map.mpr ⟨δ, hδ, by simp [MulAut.conj]⟩
  have h1 : hL.ε (ρ⁻¹ * δ * ρ) = 0 := hzero _ hmem
  have h2 : hL.ε (ρ⁻¹ * δ * ρ) = hL.ε δ := by
    have hh := step4_conj_eq_of_additive_K hL.ε hL.hadd (a := ρ⁻¹) (b := δ)
    rwa [inv_inv] at hh
  rw [← h2, h1]

/-- **Vanishing on the inertia of a `↥K`-conjugate of a `Tnew`-place.**  There `ε` is the local
target `ηt`, which vanishes on the inertia group by hypothesis. -/
theorem step4y_eps_zero_of_isInertia_of_conj_Tnew (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (ηt : (A : ValuationSubring SSGRoute.QBar) → A ∈ Tnew →
      SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j)
    (hηtinert : ∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
      ∀ σ, SSGRoute.IsInertia ℚ A σ → ηt A hA σ = 0)
    (hL : Step4YLocalData D Tnew ηt)
    (B : ValuationSubring SSGRoute.QBar)
    (h : ∃ A₀ ∈ Tnew, SSGRoute.IsConjPlace ↥K A₀ B) :
    ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, δ ∈ SSGRoute.decomp ↥K B →
      SSGRoute.IsInertia ↥K B δ → hL.ε δ = 0 := by
  intro δ hδ hδI
  obtain ⟨A₀, hA₀, hc⟩ := h
  obtain ⟨ρ, hρ⟩ := hc
  have hBA : ρ⁻¹ • B = A₀ := by rw [← hρ, inv_smul_smul]
  have hmap : SSGRoute.decomp ↥K A₀ =
      (SSGRoute.decomp ↥K B).map (MulAut.conj ρ⁻¹).toMonoidHom := by
    rw [← hBA, decomp_conj B ρ⁻¹]
  have hmem : ρ⁻¹ * δ * ρ ∈ SSGRoute.decomp ↥K A₀ := by
    rw [hmap]
    exact Subgroup.mem_map.mpr ⟨δ, hδ, by simp [MulAut.conj]⟩
  have hI' : SSGRoute.IsInertia ↥K A₀ (ρ⁻¹ * δ * ρ) := by
    have h2 := (isInertia_conj B ρ⁻¹ δ).mpr hδI
    rwa [inv_inv, hBA] at h2
  have hIℚ : SSGRoute.IsInertia ℚ A₀
      (((IntermediateField.fixingSubgroupEquiv K).symm (ρ⁻¹ * δ * ρ) : ↥(K.fixingSubgroup)) :
        SSGRoute.GalQ) :=
    (step4y_isInertia_symm_iff K A₀ (ρ⁻¹ * δ * ρ)).mpr hI'
  have hzero : ηt A₀ hA₀
      (((IntermediateField.fixingSubgroupEquiv K).symm (ρ⁻¹ * δ * ρ) : ↥(K.fixingSubgroup)) :
        SSGRoute.GalQ) = 0 :=
    hηtinert A₀ hA₀ _ hIℚ
  have hconjinv : hL.ε δ = hL.ε (ρ⁻¹ * δ * ρ) := by
    have hh := step4_conj_eq_of_additive_K hL.ε hL.hadd (a := ρ⁻¹) (b := δ)
    rw [inv_inv] at hh
    exact hh.symm
  rw [hconjinv, hL.hpres A₀ hA₀ (ρ⁻¹ * δ * ρ) hmem, hzero]

/-- **Complete splitting is inherited by a `↥K`-conjugate.** -/
theorem step4y_isSplitIn_of_conj_Tnew (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K]
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (hTnewsplit : ∀ A ∈ Tnew, SSGRoute.IsSplitIn ℚ K A)
    (B : ValuationSubring SSGRoute.QBar)
    (h : ∃ A₀ ∈ Tnew, SSGRoute.IsConjPlace ↥K A₀ B) :
    SSGRoute.IsSplitIn ℚ K B := by
  obtain ⟨A₀, hA₀, ⟨ρ, hρ⟩⟩ := h
  have hsmul : (((IntermediateField.fixingSubgroupEquiv K).symm ρ : ↥(K.fixingSubgroup)) :
      SSGRoute.GalQ) • A₀ = B := (step4y_smul_of_coe_symm K ρ A₀).trans hρ
  rw [← hsmul]
  exact (step4y_isSplitIn_smul_iff K A₀ _).mpr (hTnewsplit A₀ hA₀)

/-- **Lying over `p` is inherited by a `↥K`-conjugate.** -/
theorem step4y_not_val_p_lt_one_of_conj_Tnew (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K]
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (hTnewnotp : ∀ A ∈ Tnew, ¬ A.valuation (p : SSGRoute.QBar) < 1)
    (B : ValuationSubring SSGRoute.QBar)
    (h : ∃ A₀ ∈ Tnew, SSGRoute.IsConjPlace ↥K A₀ B) :
    ¬ B.valuation (p : SSGRoute.QBar) < 1 := by
  obtain ⟨A₀, hA₀, ⟨ρ, hρ⟩⟩ := h
  have hsmul : (((IntermediateField.fixingSubgroupEquiv K).symm ρ : ↥(K.fixingSubgroup)) :
      SSGRoute.GalQ) • A₀ = B := (step4y_smul_of_coe_symm K ρ A₀).trans hρ
  rw [← hsmul]
  intro hlt
  exact hTnewnotp A₀ hA₀ ((step4y_smul_valuation_p_lt_one p A₀ _).mp hlt)

/-- **The places of `D.T0` are not `↥K`-conjugate to a `Tnew`-place.** -/
theorem step4y_not_conj_T0_Tnew (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (hTnewS : ∀ A ∈ Tnew, A ∈ D.S)
    (hT0Tnew : ∀ A ∈ D.T0, A ∉ Tnew)
    (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ D.T0) :
    ¬ ∃ A₀ ∈ Tnew, SSGRoute.IsConjPlace ↥K A₀ A := by
  rintro ⟨A₀, hA₀, hc⟩
  have h4 : A₀ = A := D.hSdisj A₀ (hTnewS A₀ hA₀) A (D.hT0S A hA)
    (isConjPlace_of_isConjPlace_over_K hc)
  exact hT0Tnew A hA (h4 ▸ hA₀)

/-- **The conjugates of the `D.T0`-places are not `↥K`-conjugate to a `Tnew`-place.** -/
theorem step4y_not_conj_T0_conj (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (hTnewS : ∀ A ∈ Tnew, A ∈ D.S)
    (hT0Tnew : ∀ A ∈ D.T0, A ∉ Tnew)
    (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ D.T0)
    (s : K ≃ₐ[ℚ] K) :
    ∀ A₀ ∈ Tnew, ¬ SSGRoute.IsConjPlace ↥K A₀ ((D.sec s)⁻¹ • A) := by
  intro A₀ hA₀ hc
  have h1 : SSGRoute.IsConjPlace ℚ A₀ ((D.sec s)⁻¹ • A) :=
    isConjPlace_of_isConjPlace_over_K hc
  have h2 : SSGRoute.IsConjPlace ℚ A ((D.sec s)⁻¹ • A) := ⟨(D.sec s)⁻¹, rfl⟩
  have h3 : SSGRoute.IsConjPlace ℚ A₀ A := isConjPlace_trans h1 (isConjPlace_symm h2)
  have h4 : A₀ = A := D.hSdisj A₀ (hTnewS A₀ hA₀) A (D.hT0S A hA) h3
  exact hT0Tnew A hA (h4 ▸ hA₀)

/-- **The conjugates of the `Tnew`-places are not `↥K`-conjugate to a `Tnew`-place.**  This is
where the complete splitting of the places of `Tnew` enters: the conjugate
`(D.sec s)⁻¹ • A` (`s ≠ 1`) has a different `K`-prime from `A` itself. -/
theorem step4y_not_conj_Tnew_conj (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (hTnewS : ∀ A ∈ Tnew, A ∈ D.S)
    (hTnewsplit : ∀ A ∈ Tnew, SSGRoute.IsSplitIn ℚ K A)
    (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew)
    (s : K ≃ₐ[ℚ] K) (hs : s ≠ 1) :
    ∀ A₀ ∈ Tnew, ¬ SSGRoute.IsConjPlace ↥K A₀ ((D.sec s)⁻¹ • A) := by
  intro A₀ hA₀ hc
  have h1 : SSGRoute.IsConjPlace ℚ A₀ ((D.sec s)⁻¹ • A) :=
    isConjPlace_of_isConjPlace_over_K hc
  have h2 : SSGRoute.IsConjPlace ℚ A ((D.sec s)⁻¹ • A) := ⟨(D.sec s)⁻¹, rfl⟩
  have h3 : SSGRoute.IsConjPlace ℚ A₀ A := isConjPlace_trans h1 (isConjPlace_symm h2)
  have h4 : A₀ = A := D.hSdisj A₀ (hTnewS A₀ hA₀) A (hTnewS A hA) h3
  rw [h4] at hc
  -- `A` and `(D.sec s)⁻¹ • A` have the same `K`-prime; `A` being completely split forces `s = 1`
  obtain ⟨ρ, hρ⟩ := hc
  set σ : SSGRoute.GalQ :=
    (((IntermediateField.fixingSubgroupEquiv K).symm ρ : ↥(K.fixingSubgroup)) :
      SSGRoute.GalQ) with hσdef
  have hσK : σ ∈ K.fixingSubgroup := by
    rw [hσdef]
    exact ((IntermediateField.fixingSubgroupEquiv K).symm ρ).2
  have hσsmul : σ • A = (D.sec s)⁻¹ • A := by
    rw [hσdef]
    exact (step4y_smul_of_coe_symm K ρ A).trans hρ
  have hmem : (D.sec s) * σ ∈ SSGRoute.decomp ℚ A := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hσsmul, smul_inv_smul]
  have hmemK : (D.sec s) * σ ∈ K.fixingSubgroup := hTnewsplit A hA hmem
  have hsecK : D.sec s ∈ K.fixingSubgroup := by
    have h5 : ((D.sec s) * σ) * σ⁻¹ ∈ K.fixingSubgroup :=
      K.fixingSubgroup.mul_mem hmemK (K.fixingSubgroup.inv_mem hσK)
    simpa [mul_assoc] using h5
  have h6 : AlgEquiv.restrictNormalHom K (D.sec s) = 1 :=
    (step4y_restrictNormalHom_eq_one_iff K (D.sec s)).mpr hsecK
  rw [D.hsec s] at h6
  exact hs h6

/-- **Ramification of `D.phi` at a `↥K`-conjugate of a `Tnew`-place is impossible.** -/
theorem step4y_not_phi_ramified_of_conj_Tnew (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (hTnewφ : ∀ A ∈ Tnew, ∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1)
    (B : ValuationSubring SSGRoute.QBar)
    (h : ∃ A₀ ∈ Tnew, SSGRoute.IsConjPlace ↥K A₀ B) :
    ¬ ∃ σ, SSGRoute.IsInertia ℚ B σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1 := by
  rintro ⟨σ, hIσ, -, hφσ⟩
  obtain ⟨A₀, hA₀, ⟨ρ, hρ⟩⟩ := h
  set τ : SSGRoute.GalQ :=
    (((IntermediateField.fixingSubgroupEquiv K).symm ρ : ↥(K.fixingSubgroup)) :
      SSGRoute.GalQ) with hτdef
  have hτsmul : τ • A₀ = B := by
    rw [hτdef]
    exact (step4y_smul_of_coe_symm K ρ A₀).trans hρ
  have hBA : τ⁻¹ • B = A₀ := by rw [← hτsmul, inv_smul_smul]
  have hI' : SSGRoute.IsInertia ℚ A₀ (τ⁻¹ * σ * τ) := by
    have h2 := (isInertia_conj B τ⁻¹ σ).mpr hIσ
    rwa [inv_inv, hBA] at h2
  have hφ1 : D.phi (τ⁻¹ * σ * τ) = 1 := hTnewφ A₀ hA₀ _ hI'.1
  have hconj : D.phi (τ⁻¹ * σ * τ) = (D.phi τ)⁻¹ * D.phi σ * D.phi τ := by
    rw [map_mul, map_mul, map_inv]
  have heq : (D.phi τ)⁻¹ * D.phi σ * D.phi τ = 1 := by rw [← hconj]; exact hφ1
  have h3 : D.phi τ * ((D.phi τ)⁻¹ * D.phi σ * D.phi τ) * (D.phi τ)⁻¹ = 1 := by
    rw [heq, mul_one, mul_inv_cancel]
  have h4 : D.phi τ * ((D.phi τ)⁻¹ * D.phi σ * D.phi τ) * (D.phi τ)⁻¹ = D.phi σ := by
    group
  rw [h4] at h3
  exact hφσ h3

/-! ## The clause verification -/

theorem step4_yPrescribed_of_localData_node (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (ηt : (A : ValuationSubring SSGRoute.QBar) → A ∈ Tnew →
      SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j)
    (hTnewS : ∀ A ∈ Tnew, A ∈ D.S)
    (hT0Tnew : ∀ A ∈ D.T0, A ∉ Tnew)
    (hTnewfin : ∀ A ∈ Tnew, SSGRoute.IsFinPlace ℚ A)
    (hTnewnotp : ∀ A ∈ Tnew, ¬ A.valuation (p : SSGRoute.QBar) < 1)
    (hTnewφ : ∀ A ∈ Tnew, ∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1)
    (hTnewsplit : ∀ A ∈ Tnew, SSGRoute.IsSplitIn ℚ K A)
    (hηtinert : ∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
      ∀ σ, SSGRoute.IsInertia ℚ A σ → ηt A hA σ = 0)
    (hL : Step4YLocalData D Tnew ηt) :
    Step4YPrescribed D Tnew ηt := by
  classical
  refine ⟨patchFun K hL.ε, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `y` is supported on `G_K`
    intro σ hσ
    simp only [patchFun, dif_neg hσ]
  · -- additivity on `G_K`
    intro σ hσ τ hτ
    rw [patchFun_of_mem K hL.ε σ hσ, patchFun_of_mem K hL.ε τ hτ,
      patchFun_of_mem K hL.ε (σ * τ) (K.fixingSubgroup.mul_mem hσ hτ)]
    have h1 : ((IntermediateField.fixingSubgroupEquiv K)
          ⟨σ * τ, K.fixingSubgroup.mul_mem hσ hτ⟩) =
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) *
          ((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) := by
      rw [← map_mul]; rfl
    rw [h1]
    exact hL.hadd _ _
  · -- local constancy
    exact isLocConstOn_patchFun K hL.ε hL.hloc
  · -- clause 3: the escape clause (places outside `cs(S)` not split in `Λ`)
    intro B hBfin hBnotconj hBnotsplit σ hσK hI
    rw [patchFun_of_mem K hL.ε σ hσK]
    refine hL.hesc B ((local_transport_isFinPlace K B).mpr hBfin) ?_ hBnotsplit _ ?_
    · intro A hA hconj
      obtain ⟨A₀, hA₀S, hconj₀⟩ := hL.hSconj A hA
      exact hBnotconj A₀ hA₀S
        (isConjPlace_trans hconj₀ (isConjPlace_of_isConjPlace_over_K hconj))
    · exact (local_transport_isInertia K B σ hσK).mp hI
  · -- clause 4: the inertia of the places of `cs(S)`
    intro B hBfin hBconj σ hσK hI
    rw [patchFun_of_mem K hL.ε σ hσK]
    by_cases hcase : ∃ A₀ ∈ Tnew, SSGRoute.IsConjPlace ↥K A₀ B
    · exact step4y_eps_zero_of_isInertia_of_conj_Tnew p K n i j D Tnew ηt hηtinert hL B hcase _
        ((local_transport_decomp K B σ hσK).mpr hI.1)
        ((local_transport_isInertia K B σ hσK).mp hI)
    · exact step4y_eps_zero_of_not_conj_Tnew p K n i j D Tnew ηt hL B hBfin hBconj
        (fun A₀ hA₀ hc => hcase ⟨A₀, hA₀, hc⟩) _
        ((local_transport_decomp K B σ hσK).mpr hI.1)
  · -- clause 5
    intro B hBfin hBconj hcase σ hσK hσB
    rw [patchFun_of_mem K hL.ε σ hσK]
    by_cases hnew : ∃ A₀ ∈ Tnew, SSGRoute.IsConjPlace ↥K A₀ B
    · -- `B` is `↥K`-conjugate to a `Tnew`-place: all three alternatives are impossible
      have hsplit := step4y_isSplitIn_of_conj_Tnew K Tnew hTnewsplit B hnew
      have hval := step4y_not_val_p_lt_one_of_conj_Tnew p K Tnew hTnewnotp B hnew
      have hphi := step4y_not_phi_ramified_of_conj_Tnew p K n i j D Tnew hTnewφ B hnew
      rcases hcase with h | h | h
      · exact absurd hsplit h
      · exact absurd h hval
      · exact absurd h hphi
    · exact step4y_eps_zero_of_not_conj_Tnew p K n i j D Tnew ηt hL B hBfin hBconj
        (fun A₀ hA₀ hc => hnew ⟨A₀, hA₀, hc⟩) _
        ((local_transport_decomp K B σ hσK).mpr hσB)
  · -- clause 6: the places of `D.T0`
    intro A hA σ hσK hσB
    rw [patchFun_of_mem K hL.ε σ hσK]
    have hBfin : SSGRoute.IsFinPlace ℚ A := D.hSfin A (D.hT0S A hA)
    have hBconj : ∃ A' ∈ D.S, SSGRoute.IsConjPlace ℚ A' A :=
      ⟨A, D.hT0S A hA, isConjPlace_refl (k := ℚ) A⟩
    by_cases hnew : ∃ A₀ ∈ Tnew, SSGRoute.IsConjPlace ↥K A₀ A
    · exact absurd hnew (step4y_not_conj_T0_Tnew p K n i j D Tnew hTnewS hT0Tnew A hA)
    · exact step4y_eps_zero_of_not_conj_Tnew p K n i j D Tnew ηt hL A hBfin hBconj
        (fun A₀ hA₀ hc => hnew ⟨A₀, hA₀, hc⟩) _
        ((local_transport_decomp K A σ hσK).mpr hσB)
  · -- clause 7: the agreement at the places of `Tnew`
    intro A hA σ hσK hσB
    rw [patchFun_of_mem K hL.ε σ hσK]
    rw [hL.hpres A hA _ ((local_transport_decomp K A σ hσK).mpr hσB)]
    congr 1
  · -- clause 8: the conjugates of the `Tnew`-places
    intro A hA s hs σ hσK hσB
    rw [patchFun_of_mem K hL.ε σ hσK]
    have hBfin : SSGRoute.IsFinPlace ℚ ((D.sec s)⁻¹ • A) :=
      (isFinPlace_smul_iff A (D.sec s)⁻¹).mpr (D.hSfin A (hTnewS A hA))
    have hBconj : ∃ A' ∈ D.S, SSGRoute.IsConjPlace ℚ A' ((D.sec s)⁻¹ • A) :=
      ⟨A, hTnewS A hA, ⟨(D.sec s)⁻¹, rfl⟩⟩
    exact step4y_eps_zero_of_not_conj_Tnew p K n i j D Tnew ηt hL _ hBfin hBconj
      (step4y_not_conj_Tnew_conj p K n i j D Tnew hTnewS hTnewsplit A hA s hs) _
      ((local_transport_decomp K _ σ hσK).mpr hσB)
  · -- clause 9: the conjugates of the `D.T0`-places
    intro A hA s hs σ hσK hσB
    rw [patchFun_of_mem K hL.ε σ hσK]
    have hBfin : SSGRoute.IsFinPlace ℚ ((D.sec s)⁻¹ • A) :=
      (isFinPlace_smul_iff A (D.sec s)⁻¹).mpr (D.hSfin A (D.hT0S A hA))
    have hBconj : ∃ A' ∈ D.S, SSGRoute.IsConjPlace ℚ A' ((D.sec s)⁻¹ • A) :=
      ⟨A, D.hT0S A hA, ⟨(D.sec s)⁻¹, rfl⟩⟩
    exact step4y_eps_zero_of_not_conj_Tnew p K n i j D Tnew ηt hL _ hBfin hBconj
      (step4y_not_conj_T0_conj p K n i j D Tnew hTnewS hT0Tnew A hA s) _
      ((local_transport_decomp K _ σ hσK).mpr hσB)

end Work.SSGRoute
