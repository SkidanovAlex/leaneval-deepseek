import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.RamifiedPlacesAux
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.twistLayer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking
open scoped Pointwise

/-! ## Helper lemmas for `step4_transport_of_sha13` -/

section GenericCocycle

variable {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- A `1`-cocycle takes the value `0` at `1`. -/
theorem step4_cocycle_apply_one {act : Γ →* G} {x : Γ → M} (hx : IsCocycleOn act ⊤ x) :
    x 1 = 0 := by
  have h := hx 1 (Subgroup.mem_top 1) 1 (Subgroup.mem_top 1)
  simpa using h

/-- **Conjugation identity for a `1`-cocycle.** -/
theorem step4_cocycle_conj {act : Γ →* G} {x : Γ → M} (hx : IsCocycleOn act ⊤ x)
    (g γ : Γ) :
    x (g * γ * g⁻¹) = x g + act g • x γ - act (g * γ * g⁻¹) • x g := by
  have hx1 : x 1 = 0 := step4_cocycle_apply_one hx
  have hginv : x g⁻¹ = - (act g⁻¹ • x g) := by
    have h := hx g⁻¹ (Subgroup.mem_top _) g (Subgroup.mem_top _)
    rw [inv_mul_cancel, hx1] at h
    have h' : x g⁻¹ + act g⁻¹ • x g = 0 := h.symm
    calc x g⁻¹ = x g⁻¹ + act g⁻¹ • x g - act g⁻¹ • x g := by abel
      _ = 0 - act g⁻¹ • x g := by rw [h']
      _ = - (act g⁻¹ • x g) := by rw [zero_sub]
  have hsplit : x (g * γ * g⁻¹) = x (g * γ) + act (g * γ) • x g⁻¹ := by
    simpa only [mul_assoc] using hx (g * γ) (Subgroup.mem_top _) g⁻¹ (Subgroup.mem_top _)
  have hmul : x (g * γ) = x g + act g • x γ :=
    hx g (Subgroup.mem_top _) γ (Subgroup.mem_top _)
  rw [hsplit, hmul, hginv, smul_neg]
  rw [show act (g * γ) • (act g⁻¹ • x g) = act (g * γ * g⁻¹) • x g from by
    rw [← mul_smul, ← map_mul]]
  abel

/-- A map that vanishes on a subgroup is a coboundary on it. -/
theorem step4_coboundary_of_eq_zero {act : Γ →* G} {H : Subgroup Γ} {f : Γ → M}
    (hf : ∀ g ∈ H, f g = 0) : IsCoboundaryOn act H f :=
  ⟨0, fun g hg => by rw [hf g hg, smul_zero, sub_zero]⟩

end GenericCocycle

section PlaceHelpers

/-- The restriction to a finite normal intermediate field is trivial exactly on its fixing
subgroup. -/
theorem step4_restrict_eq_one_iff (K : IntermediateField ℚ SSGRoute.QBar) [hK : Normal ℚ K]
    (σ : SSGRoute.GalQ) :
    AlgEquiv.restrictNormalHom K σ = 1 ↔ σ ∈ K.fixingSubgroup := by
  rw [← MonoidHom.mem_ker]
  have h : (AlgEquiv.restrictNormalHom K).ker = K.fixingSubgroup :=
    @IntermediateField.restrictNormalHom_ker ℚ SSGRoute.QBar _ _ _ K hK
  rw [h]

/-- Conjugation by an element of `G_ℚ` preserves the fixing subgroup of a normal intermediate
field (no normality of the fixing subgroup is needed: the restriction is a group homomorphism). -/
theorem step4_conj_mem_fixingSubgroup (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    {g δ : SSGRoute.GalQ} (h : δ ∈ K.fixingSubgroup) : g * δ * g⁻¹ ∈ K.fixingSubgroup := by
  rw [← step4_restrict_eq_one_iff K]
  rw [map_mul, map_mul, map_inv, (step4_restrict_eq_one_iff K δ).mpr h]
  group

/-- Complete splitting in a normal extension `K/ℚ` is invariant under translating the place. -/
theorem step4_isSplitIn_smul (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (B : ValuationSubring SSGRoute.QBar) (g : SSGRoute.GalQ) :
    IsSplitIn ℚ K (g • B) ↔ IsSplitIn ℚ K B := by
  show decomp ℚ (g • B) ≤ K.fixingSubgroup ↔ decomp ℚ B ≤ K.fixingSubgroup
  rw [decomp_conj, Subgroup.map_le_iff_le_comap]
  constructor
  · intro h δ hδ
    have h1 : g * δ * g⁻¹ ∈ K.fixingSubgroup := Subgroup.mem_comap.mp (h hδ)
    have hconj : g⁻¹ * (g * δ * g⁻¹) * (g⁻¹)⁻¹ ∈ K.fixingSubgroup :=
      step4_conj_mem_fixingSubgroup K h1
    simpa using hconj
  · intro h δ hδ
    rw [Subgroup.mem_comap]
    exact step4_conj_mem_fixingSubgroup K (h hδ)

/-- Conjugation by the section `sec s` preserves `K.fixingSubgroup`. -/
theorem step4_conj_sec_mem_fixingSubgroup (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ)
    (hsec : ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s)
    (s : K ≃ₐ[ℚ] K) {δ : SSGRoute.GalQ} (hδ : δ ∈ K.fixingSubgroup) :
    (sec s)⁻¹ * δ * sec s ∈ K.fixingSubgroup := by
  have h1 : AlgEquiv.restrictNormalHom K ((sec s)⁻¹ * δ * sec s) = 1 := by
    rw [map_mul, map_mul, map_inv, hsec, (step4_restrict_eq_one_iff K δ).mpr hδ]
    simp
  exact (step4_restrict_eq_one_iff K _).mp h1

/-- Translating a place of `ℚ̄` by an element of `G_ℚ` preserves the property of lying over the
prime `p`. -/
theorem step4_smul_valuation_p_lt_one (p : ℕ) (B : ValuationSubring SSGRoute.QBar)
    (g : SSGRoute.GalQ) :
    (g • B).valuation (p : SSGRoute.QBar) < 1 ↔ B.valuation (p : SSGRoute.QBar) < 1 := by
  have h1 : ((g • B).comap (algebraMap ℚ SSGRoute.QBar)).valuation (p : ℚ) < 1 ↔
      (g • B).valuation (p : SSGRoute.QBar) < 1 := by
    simpa using (comap_valuation_lt_one_iff (B := g • B) (x := (p : ℚ)))
  have h2 : ((B.comap (algebraMap ℚ SSGRoute.QBar)).valuation (p : ℚ) < 1) ↔
      B.valuation (p : SSGRoute.QBar) < 1 := by
    simpa using (comap_valuation_lt_one_iff (B := B) (x := (p : ℚ)))
  rw [← h1, ← h2, comap_algebraMap_smul]

/-- **Summands of the formal corestriction vanish at a place over `p` conjugate to `S`.** -/
theorem step4_sum_smul_y_eq_zero_of_over_p (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (S : Finset (ValuationSubring SSGRoute.QBar))
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ)
    (hsec : ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hy0 : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∃ A ∈ S, IsConjPlace ℚ A B) →
      (¬ IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp ℚ B → y σ = 0)
    (B : ValuationSubring SSGRoute.QBar) (hB : IsFinPlace ℚ B)
    (hc : ∃ A ∈ S, IsConjPlace ℚ A B) (hval : B.valuation (p : SSGRoute.QBar) < 1)
    (δ : SSGRoute.GalQ) (hδK : δ ∈ K.fixingSubgroup) (hδD : δ ∈ decomp ℚ B) :
    (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)) = 0 := by
  refine Finset.sum_eq_zero (fun s _ => ?_)
  obtain ⟨A₀, hA₀S, hA₀conj⟩ := hc
  have hBs : IsFinPlace ℚ ((sec s)⁻¹ • B) := (isFinPlace_smul_iff B (sec s)⁻¹).mpr hB
  have hcs : ∃ A ∈ S, IsConjPlace ℚ A ((sec s)⁻¹ • B) :=
    ⟨A₀, hA₀S, isConjPlace_smul hA₀conj (sec s)⁻¹⟩
  have hvals : ((sec s)⁻¹ • B).valuation (p : SSGRoute.QBar) < 1 :=
    (step4_smul_valuation_p_lt_one p B (sec s)⁻¹).mpr hval
  have hmem : (sec s)⁻¹ * δ * sec s ∈ K.fixingSubgroup :=
    step4_conj_sec_mem_fixingSubgroup K sec hsec s hδK
  have hD : (sec s)⁻¹ * δ * sec s ∈ decomp ℚ ((sec s)⁻¹ • B) := by
    rw [decomp_conj]
    refine Subgroup.mem_map.mpr ⟨δ, hδD, ?_⟩
    simp
  rw [hy0 _ hBs hcs (Or.inr hvals) _ hmem hD, smul_zero]

/-- **Summands of the formal corestriction vanish on the inertia of a place conjugate to `S`.** -/
theorem step4_sum_smul_y_eq_zero_of_inertia (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (S : Finset (ValuationSubring SSGRoute.QBar))
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ)
    (hsec : ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hyT : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∃ A ∈ S, IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia ℚ B σ → y σ = 0)
    (B : ValuationSubring SSGRoute.QBar) (hB : IsFinPlace ℚ B)
    (hc : ∃ A ∈ S, IsConjPlace ℚ A B)
    (δ : SSGRoute.GalQ) (hδK : δ ∈ K.fixingSubgroup) (hδI : IsInertia ℚ B δ) :
    (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)) = 0 := by
  refine Finset.sum_eq_zero (fun s _ => ?_)
  obtain ⟨A₀, hA₀S, hA₀conj⟩ := hc
  have hBs : IsFinPlace ℚ ((sec s)⁻¹ • B) := (isFinPlace_smul_iff B (sec s)⁻¹).mpr hB
  have hcs : ∃ A ∈ S, IsConjPlace ℚ A ((sec s)⁻¹ • B) :=
    ⟨A₀, hA₀S, isConjPlace_smul hA₀conj (sec s)⁻¹⟩
  have hmem : (sec s)⁻¹ * δ * sec s ∈ K.fixingSubgroup :=
    step4_conj_sec_mem_fixingSubgroup K sec hsec s hδK
  have hI : IsInertia ℚ ((sec s)⁻¹ • B) ((sec s)⁻¹ * δ * sec s) :=
    (isInertia_conj B (sec s)⁻¹ δ).mpr hδI
  rw [hyT _ hBs hcs _ hmem hI, smul_zero]

end PlaceHelpers

/-- Transport of the local clauses of `SSGRoute.shafarevich_theorem13` at the places of a set `S`
(one per prime, containing the places over `Ram(Λ/ℚ)` and over `p`) to *arbitrary* places, and the
derivation of the two global conditions on `x` used by Step 4 of Theorem 15: `x` is a coboundary on
the decomposition group of every place over `Ram(K/ℚ) ∪ {p}`, and `x` ramifies over `K` only at
places completely decomposed in `Λ/ℚ` (where `φ` is the level-`τ` solution with kernel `G_Λ`). -/
theorem step4_transport_of_sha13 (p : ℕ) [Fact p.Prime]
    (K Λ : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    [FiniteDimensional ℚ Λ] [Normal ℚ Λ] (hKΛ : K ≤ Λ) (n i j : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hΛker : φ.ker = Λ.fixingSubgroup)
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, IsFinPlace ℚ A)
    (hSram : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) → ∃ A ∈ S, IsConjPlace ℚ A B)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hyT : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∃ A ∈ S, IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia ℚ B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∃ A ∈ S, IsConjPlace ℚ A B) → (¬ IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp ℚ B → y σ = 0)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxcoc : SSGRoute.IsCocycleOn (AlgEquiv.restrictNormalHom K) ⊤ x)
    (hxsplit : ∀ A ∈ S, IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A)
        (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (hxnot : ∀ A ∈ S, ¬ IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A) x)
    (hxinertia : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ IsConjPlace ℚ A B) → ¬ IsSplitIn ℚ Λ B →
      ∀ σ : SSGRoute.GalQ, IsInertia ℚ B σ → x σ = 0) :
    (∀ A : ValuationSubring SSGRoute.QBar, IsT1Place p K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A) x) ∧
    (∀ A : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) →
      ∀ σ ∈ decomp ℚ A, φ σ = 1) := by
  -- ramification in `K` implies ramification in `Λ`
  have hram_mono : ∀ B : ValuationSubring SSGRoute.QBar,
      IsRamifiedIn ℚ K B → IsRamifiedIn ℚ Λ B := by
    rintro B ⟨σ, hI, hσ⟩
    exact ⟨σ, hI, fun hmem => hσ (IntermediateField.fixingSubgroup_le hKΛ hmem)⟩
  -- every `T¹`-place is conjugate to an element of `S`
  have hT1_conj : ∀ B : ValuationSubring SSGRoute.QBar, IsT1Place p K B →
      ∃ A ∈ S, IsConjPlace ℚ A B := by
    rintro B ⟨hBfin, hval | hram⟩
    · exact hSram B hBfin (Or.inr hval)
    · exact hSram B hBfin (Or.inl (hram_mono B hram))
  refine ⟨?_, ?_⟩
  · -- ## Part 1: `x` is a coboundary on the decomposition group of every place of `T¹`
    intro A hA
    obtain ⟨hAfin, hAcond⟩ := hA
    obtain ⟨A', hA'S, τ, hτ⟩ := hT1_conj A ⟨hAfin, hAcond⟩
    -- a coboundary on `D_{A'}` transports to the conjugate place `A = τ • A'`
    have transfer : IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A') x →
        IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A) x := by
      intro hcob
      have h := isCoboundaryOn_map_conj (AlgEquiv.restrictNormalHom K) (decomp ℚ A') τ x
        hxcoc hcob
      rw [← decomp_conj A' τ, hτ] at h
      exact h
    by_cases hsplit : IsSplitIn ℚ K A'
    · -- `A'` splits completely in `K`: `x` and the formal corestriction agree on `D_{A'}`
      have hsplitA : IsSplitIn ℚ K A := hτ ▸ (step4_isSplitIn_smul K A' τ).mpr hsplit
      have hnotram : ¬ IsRamifiedIn ℚ K A := by
        rintro ⟨σ, hσI, hσK⟩
        exact hσK (hsplitA hσI.1)
      have hvalA : A.valuation (p : SSGRoute.QBar) < 1 :=
        hAcond.elim id (fun h => absurd h hnotram)
      have hvalA' : A'.valuation (p : SSGRoute.QBar) < 1 :=
        (step4_smul_valuation_p_lt_one p A' τ).mp (hτ.symm ▸ hvalA)
      have hxzero : ∀ δ ∈ decomp ℚ A', x δ = 0 := by
        obtain ⟨m, hm⟩ := hxsplit A' hA'S hsplit
        intro δ hδ
        have h1 : x δ - (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s))
            = AlgEquiv.restrictNormalHom K δ • m - m := hm δ hδ
        have hact : AlgEquiv.restrictNormalHom K δ = 1 :=
          (step4_restrict_eq_one_iff K δ).mpr (hsplit hδ)
        have hX0 : (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)) = 0 :=
          step4_sum_smul_y_eq_zero_of_over_p p K n i j S sec hsec y hy0 A' (hSfin A' hA'S)
            ⟨A', hA'S, isConjPlace_refl A'⟩ hvalA' δ (hsplit hδ) hδ
        rw [hact, one_smul, hX0, sub_zero, sub_self] at h1
        exact h1
      exact transfer (step4_coboundary_of_eq_zero hxzero)
    · -- `A'` does not split completely in `K`
      exact transfer (hxnot A' hA'S hsplit)
  · -- ## Part 2: `x` can only ramify over `K` at places split completely in `Λ/ℚ`
    intro A hAfin hram σ hσ
    obtain ⟨σ₀, hσ₀I, hσ₀K, hσ₀ne⟩ := hram
    have hσ₀D : σ₀ ∈ decomp ℚ A := hσ₀I.1
    have hσ₀act : AlgEquiv.restrictNormalHom K σ₀ = 1 :=
      (step4_restrict_eq_one_iff K σ₀).mpr hσ₀K
    have hsplitΛ : IsSplitIn ℚ Λ A := by
      by_contra hnsplit
      by_cases hconj : ∃ A' ∈ S, IsConjPlace ℚ A' A
      · obtain ⟨A', hA'S, τ, hτ⟩ := hconj
        by_cases hsplitK : IsSplitIn ℚ K A'
        · -- `x` agrees with the formal corestriction on `D_{A'}`, which kills the inertia of `A'`
          have hgrp : τ * (τ⁻¹ * σ₀ * τ) * τ⁻¹ = σ₀ := by group
          have hXi : ∀ δ ∈ decomp ℚ A', IsInertia ℚ A' δ →
              (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)) = 0 :=
            fun δ hδ hI => step4_sum_smul_y_eq_zero_of_inertia p K n i j S sec hsec y hyT
              A' (hSfin A' hA'S) ⟨A', hA'S, isConjPlace_refl A'⟩ δ (hsplitK hδ) hI
          obtain ⟨m, hm⟩ := hxsplit A' hA'S hsplitK
          have hxX : ∀ δ ∈ decomp ℚ A',
              x δ = ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s) := by
            intro δ hδ
            have h1 : x δ - (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s))
                = AlgEquiv.restrictNormalHom K δ • m - m := hm δ hδ
            have hact : AlgEquiv.restrictNormalHom K δ = 1 :=
              (step4_restrict_eq_one_iff K δ).mpr (hsplitK hδ)
            rw [hact, one_smul, sub_self] at h1
            exact sub_eq_zero.mp h1
          -- the conjugate `τ⁻¹ σ₀ τ` lies in the inertia of `A'`, where `x` vanishes
          have hbI : IsInertia ℚ A' (τ⁻¹ * σ₀ * τ) :=
            (isInertia_conj A' τ (τ⁻¹ * σ₀ * τ)).mp (by rw [hgrp, hτ]; exact hσ₀I)
          have hxb : x (τ⁻¹ * σ₀ * τ) = 0 := by
            rw [hxX _ hbI.1, hXi _ hbI.1 hbI]
          have hkey : x σ₀ = x τ + AlgEquiv.restrictNormalHom K τ • x (τ⁻¹ * σ₀ * τ)
              - AlgEquiv.restrictNormalHom K σ₀ • x τ := by
            have h := step4_cocycle_conj hxcoc τ (τ⁻¹ * σ₀ * τ)
            rwa [hgrp] at h
          have hzero : x σ₀ = 0 := by
            rw [hkey]
            simp [hxb, hσ₀act]
          exact hσ₀ne hzero
        · -- `A'` does not split in `K`: `hxnot` gives a coboundary on the conjugate `D_A`
          have hcobA : IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A') x :=
            hxnot A' hA'S hsplitK
          have hcob : IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A) x := by
            have h := isCoboundaryOn_map_conj (AlgEquiv.restrictNormalHom K) (decomp ℚ A') τ x
              hxcoc hcobA
            rw [← decomp_conj A' τ, hτ] at h
            exact h
          obtain ⟨m, hm⟩ := hcob
          have h1 : x σ₀ = AlgEquiv.restrictNormalHom K σ₀ • m - m := hm σ₀ hσ₀D
          rw [hσ₀act, one_smul] at h1
          exact hσ₀ne (by rw [sub_self] at h1; exact h1)
      · exact hσ₀ne (hxinertia A hAfin (fun A' hA' hc => hconj ⟨A', hA', hc⟩) hnsplit σ₀ hσ₀I)
    have hσΛ : σ ∈ Λ.fixingSubgroup := hsplitΛ hσ
    have h1 : σ ∈ φ.ker := by rw [hΛker]; exact hσΛ
    exact MonoidHom.mem_ker.mp h1

end Work.SSGRoute
