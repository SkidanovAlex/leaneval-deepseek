import Submission.Work.SSGRoute.ZVocab
import Submission.Work.SSGRoute.ZConstruction.Reduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The codimension-one induction step of Schmidt--Wingberg §4 (pp. 18--19)

This file proves the general-`A` half of Theorem 13 of Schmidt--Wingberg, in the form in which
`Work.SSGRoute.z_data_general` states it: the `z`-data for a coefficient module `E = E₀ ⊕ 𝔽_p`
follows from the `z`-data for `E₀` at the *same* pair `(Λ,S)` together with the `z`-data for the
one-dimensional summand `𝔽_p` at the *auxiliary* pair `(Λ₀,T₀)`, where `L ≤ Λ₀` is an extension of
`k` (in the paper, the Galois closure over `k` of the field cut out by the `E₀`-class) on whose
fixing subgroup the `E₀`-class `zE` vanishes.

Two observations make the induction reach *every* finite coefficient module (and not only direct
sums of one-dimensional modules):

* every clause of the `z`-data lives over `G_K = K.fixingSubgroup`, where the action of `Gal(K|k)`
  is trivial; so no equivariance of the splitting `E = E₀ ⊕ 𝔽_p` is needed, and one may take an
  arbitrary linear decomposition;
* at a place `B` at which the `𝔽_p`-summand is ramified, the cases `B ∈ T₀` and `B ∉ T₀` are handled
  by the vanishing of the auxiliary class at the new places and by the confinement of the
  ramification of the `E₀`-class to the primes ramified in `L` (clause (5) of its own `z`-data,
  applied at the auxiliary pair), respectively.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Transport

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {K Λ : IntermediateField k Ω}

/-- **Transport of the `z`-data along a `𝔽_p`-linear map.** -/
theorem IsZData.map {E F : Type} [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    [AddCommGroup F] [Module (ZMod p) F] [DistribMulAction (K ≃ₐ[k] K) F]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) F]
    {S : Finset (ValuationSubring Ω)} {y z : (Ω ≃ₐ[k] Ω) → E}
    (h : IsZData p K Λ S y z) (φ : E →ₗ[ZMod p] F) :
    IsZData p K Λ S (fun σ => φ (y σ)) (fun σ => φ (z σ)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg hh hhh
    show φ (z (g * hh)) = φ (z g) + φ (z hh)
    rw [h1 g hg hh hhh, map_add]
  · obtain ⟨U, hU, hc⟩ := h2
    exact ⟨U, hU, fun g hg u hu hgu => by
      show φ (z (g * u)) = φ (z g)
      rw [hc g hg u hu hgu]⟩
  · intro B hB hconj σ hσG hσD
    show φ (z σ) = φ (y σ)
    rw [h3 B hB hconj σ hσG hσD]
  · intro c hc hc2
    show φ (z c) = 0
    rw [h4 c hc hc2, map_zero]
  · intro B hB hnot hns σ hσG hσI
    show φ (z σ) = 0
    rw [h5 B hB hnot hns σ hσG hσI, map_zero]
  · intro B hB hnot hsplit htrig
    obtain ⟨σ, hσI, hσG, hσne⟩ := htrig
    have htrig' : ∃ σ, IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0 := by
      refine ⟨σ, hσI, hσG, fun h0 => hσne ?_⟩
      show φ (z σ) = 0
      rw [h0, map_zero]
    obtain ⟨hcyc, hvan⟩ := h6 B hB hnot hsplit htrig'
    refine ⟨?_, ?_⟩
    · obtain ⟨g, hg, hgz⟩ := hcyc
      refine ⟨g, hg, fun δ hδ => ?_⟩
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgz δ hδ)
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
      show m • φ (z g) = φ (z δ)
      rw [← map_zsmul, hm]
    · intro Q hQ hnc τ hτ
      show φ (z τ) = 0
      rw [hvan Q hQ hnc τ hτ, map_zero]

/-- **Replacement of the datum** by a function agreeing with it on the local groups of the places
of `S`.  Only clause (3) of the `z`-data mentions the datum. -/
theorem IsZData.congr {E : Type} [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    {S : Finset (ValuationSubring Ω)} {y y' z : (Ω ≃ₐ[k] Ω) → E}
    (h : IsZData p K Λ S y z)
    (hag : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y σ = y' σ) :
    IsZData p K Λ S y' z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, ?_, h4, h5, h6⟩
  intro B hB hconj σ hσG hσD
  rw [h3 B hB hconj σ hσG hσD, hag B hB hconj σ hσG hσD]

end Transport

section Monotone

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {K Λ : IntermediateField k Ω}
variable {E : Type} [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]

/-- **Passage from the auxiliary pair `(Λ₀,T₀)` down to `(Λ,T)`**, given that the class vanishes on
the local groups of the places of `T₀` that are not conjugate to a place of `T`. -/
theorem IsZData.at_le {S S₀ : Finset (ValuationSubring Ω)} {y z : (Ω ≃ₐ[k] Ω) → E}
    {Λ₀ : IntermediateField k Ω} (hΛΛ₀ : Λ ≤ Λ₀)
    (hsub : ∀ A ∈ S, ∃ A' ∈ S₀, IsConjPlace k A A')
    (hz : IsZData p K Λ₀ S₀ y z)
    (hvan : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S₀, IsConjPlace k A B) →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → z σ = 0) :
    IsZData p K Λ S y z := by
  obtain ⟨hz1, hz2, hz3, hz4, hz5, hz6⟩ := hz
  have hfix : Λ₀.fixingSubgroup ≤ Λ.fixingSubgroup := IntermediateField.fixingSubgroup_le hΛΛ₀
  refine ⟨hz1, hz2, ?_, hz4, ?_, ?_⟩
  · -- clause (3): the places of `S` are conjugate to places of `S₀`
    intro B hB hconj σ hσG hσD
    obtain ⟨A, hA, hAB⟩ := hconj
    obtain ⟨A', hA', hAA'⟩ := hsub A hA
    exact hz3 B hB ⟨A', hA', isConjPlace_trans (isConjPlace_symm hAA') hAB⟩ σ hσG hσD
  · -- clause (5)
    intro B hB hnot hnsplit σ hσG hσI
    by_cases hB0 : ∃ A ∈ S₀, IsConjPlace k A B
    · exact hvan B hB hB0 hnot σ hσG hσI.1
    · refine hz5 B hB (fun A hA hc => hB0 ⟨A, hA, hc⟩) ?_ σ hσG hσI
      exact fun h => hnsplit (le_trans h hfix)
  · -- clause (6)
    intro B hB hnot hsplit htrig
    by_cases hB0 : ∃ A ∈ S₀, IsConjPlace k A B
    · obtain ⟨σ, hσI, hσG, hσne⟩ := htrig
      exact absurd (hvan B hB hB0 hnot σ hσG hσI.1) hσne
    · obtain ⟨σ, hσI, hσG, hσne⟩ := htrig
      have hsplit₀ : IsSplitIn k Λ₀ B := by
        by_contra hns
        exact hσne (hz5 B hB (fun A hA hc => hB0 ⟨A, hA, hc⟩) hns σ hσG hσI)
      exact hz6 B hB (fun A hA hc => hB0 ⟨A, hA, hc⟩) hsplit₀ ⟨σ, hσI, hσG, hσne⟩

end Monotone

section Split

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
variable {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)]
variable [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The codimension-one induction step.** -/
theorem IsZData.split (hKΛ : K ≤ Λ)
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → E)
    (ρ : E →ₗ[ZMod p] ZMod p) (z₀ : E) (hρz₀ : ρ z₀ = 1)
    (zE : (Ω ≃ₐ[k] Ω) → E)
    (hzE : IsZData p K Λ S (fun σ => y σ - (ρ (y σ)) • z₀) zE)
    (L Λ₀ : IntermediateField k Ω) [FiniteDimensional k Λ₀] [IsGalois k Λ₀]
    (hLΛ₀ : L ≤ Λ₀) (hΛΛ₀ : Λ ≤ Λ₀)
    (hLvan : ∀ σ ∈ L.fixingSubgroup, zE σ = 0)
    (S₀ : Finset (ValuationSubring Ω))
    (hsub : ∀ A ∈ S, ∃ A' ∈ S₀, IsConjPlace k A A')
    (hS₀ramL : ∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k L B →
      ∃ A ∈ S₀, IsConjPlace k A B)
    (ytilde zF : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hreal : IsYRealisation p K Λ₀ S S₀ (fun B σ => ρ (y σ)) ytilde)
    (hzmu : IsZData p K Λ₀ S₀ ytilde zF) :
    IsZData p K Λ S y (fun σ => zE σ + (zF σ) • z₀) := by
  classical
  have hz₀ne : z₀ ≠ 0 := by
    intro h0
    have h1 : (1 : ZMod p) = 0 := by rw [← hρz₀, h0, map_zero]
    exact one_ne_zero h1
  have hsmul_ne : ∀ c : ZMod p, c • z₀ ≠ 0 → c ≠ 0 := by
    intro c hc h0
    exact hc (by rw [h0, zero_smul])
  -- (1) the auxiliary data, transported into `E` along `c ↦ c • z₀`
  have hzmuE : IsZData p K Λ₀ S₀ (fun σ => (ytilde σ) • z₀) (fun σ => (zF σ) • z₀) := by
    simpa only [LinearMap.toSpanSingleton_apply] using
      (IsZData.map hzmu (LinearMap.toSpanSingleton (ZMod p) E z₀))
  obtain ⟨hm1, hm2, hm3, hm4, hm5, hm6⟩ := hzmu
  -- (2) the auxiliary class vanishes on the local groups of the new places
  have hvanS₀ : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S₀, IsConjPlace k A B) →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B →
      (zF σ) • z₀ = 0 := by
    intro B hB hB0 hBnotS σ hσG hσD
    have hyt : ytilde σ = 0 :=
      IsYRealisation.vanishes_new p hreal hB hB0 hBnotS hσG hσD
    rw [hm3 B hB hB0 σ hσG hσD, hyt, zero_smul]
  -- (3) hence the auxiliary data is `z`-data at `(Λ,S)` as well
  have hzmu' : IsZData p K Λ S (fun σ => (ytilde σ) • z₀) (fun σ => (zF σ) • z₀) :=
    IsZData.at_le hΛΛ₀ hsub hzmuE hvanS₀
  -- (4) the datum of the auxiliary data agrees with the `𝔽_p`-component of `y` at the places of `S`
  have hag₂ : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → ytilde σ = ρ (y σ) := by
    intro B hB hconj σ hσG hσD
    obtain ⟨m, hm⟩ := hreal.2.2.1 B hconj
    have hval : ytilde σ - (fun B σ => ρ (y σ)) B σ = res k K σ • m - m := hm σ ⟨hσD, hσG⟩
    have hres : res k K σ = 1 :=
      (res_eq_one_iff_mem_fixingSubgroup (K := K) σ).mpr hσG
    rw [hres, one_smul, sub_self, sub_eq_zero] at hval
    exact hval
  have hzmu'' : IsZData p K Λ S (fun σ => (ρ (y σ)) • z₀) (fun σ => (zF σ) • z₀) :=
    IsZData.congr hzmu' (fun B hB hconj σ hσG hσD => by
      show (ytilde σ) • z₀ = (ρ (y σ)) • z₀
      rw [hag₂ B hB hconj σ hσG hσD])
  -- (5) the ramification of the two summands is disjoint
  have hdisj : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → IsSplitIn k Λ B →
      ((∃ σ, IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ zE σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, IsConjPlace k B Q →
          ∀ τ ∈ decomp k Q ⊓ K.fixingSubgroup, (zF τ) • z₀ = 0) ∧
      ((∃ σ, IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ (zF σ) • z₀ ≠ 0) →
        ∀ Q : ValuationSubring Ω, IsConjPlace k B Q →
          ∀ τ ∈ decomp k Q ⊓ K.fixingSubgroup, zE τ = 0) := by
    intro B hB hnot hsplit
    refine ⟨?_, ?_⟩
    · -- the `E₀`-class is ramified at `B`: then `B` is one of the new places
      rintro ⟨σ, hσI, hσG, hσne⟩ Q hQ τ hτ
      have hσnotL : σ ∉ L.fixingSubgroup := fun h => hσne (hLvan σ h)
      have hramL : IsRamifiedIn k L B := ⟨σ, hσI, hσnotL⟩
      obtain ⟨A, hA, hAB⟩ := hS₀ramL B hB hramL
      have hAQ : IsConjPlace k A Q := isConjPlace_trans hAB hQ
      have hQfin : IsFinPlace k Q := by
        obtain ⟨σ', hσ'⟩ := hQ
        rw [← hσ']
        exact (isFinPlace_smul_iff B σ').mpr hB
      have hnotQ : ∀ A' ∈ S, ¬ IsConjPlace k A' Q := fun A' hA' hc =>
        hnot A' hA' (isConjPlace_trans hc (isConjPlace_symm hQ))
      have hτG : τ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hτ).2
      have hτD : τ ∈ decomp k Q := (Subgroup.mem_inf.mp hτ).1
      have hyt : ytilde τ = 0 :=
        IsYRealisation.vanishes_new p hreal hQfin ⟨A, hA, hAQ⟩ hnotQ hτG hτD
      rw [hm3 Q hQfin ⟨A, hA, hAQ⟩ τ hτG hτD, hyt, zero_smul]
    · -- the auxiliary class is ramified at `B`
      rintro ⟨σ, hσI, hσG, hσne⟩ Q hQ τ hτ
      have hσD : σ ∈ decomp k B := hσI.1
      have hzFne : zF σ ≠ 0 := hsmul_ne (zF σ) hσne
      by_cases hB0 : ∃ A ∈ S₀, IsConjPlace k A B
      · -- `B` is a new place, where the auxiliary class vanishes identically
        have hyt : ytilde σ = 0 :=
          IsYRealisation.vanishes_new p hreal hB hB0 hnot hσG hσD
        exact absurd (by rw [hm3 B hB hB0 σ hσG hσD, hyt] : zF σ = 0) hzFne
      · -- `B` is outside the auxiliary pair: the auxiliary class is unramified there, so `B`
        -- splits in `Λ₀`, hence in `L`, and the `E₀`-class vanishes on the local groups there
        have hsplit₀ : IsSplitIn k Λ₀ B := by
          by_contra hns
          exact hzFne (hm5 B hB (fun A hA hc => hB0 ⟨A, hA, hc⟩) hns σ hσG hσI)
        have hnorm : (Λ₀.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois Λ₀
        obtain ⟨σ', hσ'⟩ := hQ
        have hDQ : decomp k Q ≤ Λ₀.fixingSubgroup := by
          rw [← hσ', decomp_conj B σ']
          intro y' hy'
          obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy'
          rw [← hxy]
          change MulAut.conj σ' x ∈ Λ₀.fixingSubgroup
          rw [MulAut.conj_apply]
          exact hnorm.conj_mem x (hsplit₀ hx) σ'
        have hτD : τ ∈ decomp k Q := (Subgroup.mem_inf.mp hτ).1
        exact hLvan τ (IntermediateField.fixingSubgroup_le hLΛ₀ (hDQ hτD))
  -- (6) the two summands combine
  have hprod := IsZData.prod p K Λ S (fun σ => y σ - (ρ (y σ)) • z₀)
    (fun σ => (ρ (y σ)) • z₀) zE (fun σ => (zF σ) • z₀) hzE hzmu'' hdisj
  have hsum := IsZData.map hprod
    (LinearMap.fst (ZMod p) E E + LinearMap.snd (ZMod p) E E)
  refine IsZData.congr hsum fun B hB hconj σ hσG hσD => ?_
  show ((LinearMap.fst (ZMod p) E E + LinearMap.snd (ZMod p) E E)
    (y σ - (ρ (y σ)) • z₀, (ρ (y σ)) • z₀)) = y σ
  rw [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  exact sub_add_cancel (y σ) _

end Split

end Work.SSGRoute
