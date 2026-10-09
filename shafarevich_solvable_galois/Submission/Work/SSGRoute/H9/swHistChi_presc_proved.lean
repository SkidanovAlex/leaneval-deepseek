import Mathlib
import Submission.Work.SSGRoute.H9.swZSixOfHistK
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open scoped Pointwise

/-- **The prescription at the siblings of the first escape prime** (Schmidt–Wingberg's condition (3)
with the corrected sign).  For two stages `i < j` of a `HistK`-history and every place `Q`
`k`-conjugate to `Q_i` but not `K`-conjugate to it, the sum `χ_{b_i} + χ_{b_j}` vanishes on the local
group of `Q`.  This is the `hpresc` input of `Work.SSGRoute.H9.ZSix_of_histK`.

Proof: `kleadReps_covers` gives a block `A ∈ kleadReps K {Q_i} ⊆ histPlacesK j f` `K`-conjugate to
`Q`, and `A` is not `K`-conjugate to `Q_i` (else `Q` would be).  At `A` the stage-`j` realisation
clause reads `χ_{b_j} = ½y + histDatum_j(A)`; in the accumulated datum the term `l = i` is the
*sibling* branch of `correctionDatum`, namely `−χ_{b_i} − ½y`, and every other term vanishes since
`IsConjPlace k Q_l A` would make `Q_l` `k`-conjugate to `Q_i`, contradicting
`Work.SSGRoute.H9.histK_escape_kdisj`.  Hence `χ_{b_i} + χ_{b_j} = 0` on `decomp k A`, and
`Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj` transports this to `decomp k Q`.  The two `½y`
terms cancel, so no side hypothesis on `y` is needed. -/
theorem swHistChi_presc_proved {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (hf : Work.SSGRoute.H9.HistK (p := p) K N ζ hζ hζK S y f) (i j : ℕ) (hij : i < j) :
    ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k ((f i).1) Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • ((f i).1) = Q) →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        Work.SSGRoute.H9.histChi K ζ hζK hζ f i τ
          + Work.SSGRoute.H9.histChi K ζ hζK hζ f j τ = 0 := by
  classical
  intro Q hQ hnotK τ hτ
  -- the realisation clause of the oracle at stage `j`
  have hpres := hf.2.2.2.2.1
  -- one representative `A` of the `K`-class of `Q` above the `k`-place of `Q_i`
  obtain ⟨A, hA, ρ, hρK, hρA⟩ :=
    Work.SSGRoute.ZDataMup.kleadReps_covers K ({((f i).1)} : Finset (ValuationSubring Ω))
      (Finset.mem_singleton_self _) hQ
  -- `A` is a *sibling* of `Q_i`: `k`-conjugate but not `K`-conjugate
  have hA_conjQ : SSGRoute.IsConjPlace k ((f i).1) A := by
    obtain ⟨σ, hσ⟩ := hQ
    exact ⟨ρ⁻¹ * σ, by rw [mul_smul, hσ, ← hρA, inv_smul_smul]⟩
  have hnotKQi : ¬ Work.SSGRoute.gesKConj K ((f i).1) A := by
    rintro ⟨τ', hτ'K, hτ'A⟩
    exact hnotK ⟨ρ * τ', K.fixingSubgroup.mul_mem hρK hτ'K, by rw [mul_smul, hτ'A, hρA]⟩
  -- `A` is a block of the stage-`j` place set (`T_j ⊇ kleadReps K {Q_i}`)
  have hAhist : A ∈ histPlacesK (p := p) K S ζ hζK hζ j f := by
    simp only [histPlacesK, Work.SSGRoute.ZDataMup.histPlaces, histClass,
      Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨⟨i, hij⟩, hA⟩
  -- the accumulated datum at the sibling `A` is the stage-`i` sibling correction `−χ_i − ½y`
  have hdatum : ∀ ρ' : Ω ≃ₐ[k] Ω,
      histDatumK (p := p) K ζ hζK hζ S y j f A ρ'
        = - histChi K ζ hζK hζ f i ρ' - (2 : ZMod p)⁻¹ * y ρ' := by
    intro ρ'
    have hcol : histDatumK (p := p) K ζ hζK hζ S y j f A ρ'
        = Work.SSGRoute.ZDataMup.correctionDatum K (fun σ => (2 : ZMod p)⁻¹ * y σ)
            (histChi K ζ hζK hζ f i) ((f i).1) A ρ' := by
      show (Finset.univ.sum (fun l : Fin j => Work.SSGRoute.ZDataMup.correctionDatum K
          (fun σ => (2 : ZMod p)⁻¹ * y σ) (histChi K ζ hζK hζ f (↑l)) ((f (↑l)).1) A ρ'))
        = Work.SSGRoute.ZDataMup.correctionDatum K (fun σ => (2 : ZMod p)⁻¹ * y σ)
            (histChi K ζ hζK hζ f i) ((f i).1) A ρ'
      refine Finset.sum_eq_single (⟨i, hij⟩ : Fin j) ?_ ?_
      · -- every other stage's correction vanishes: its escape prime is not `k`-conjugate to `A`
        intro l _ hl
        have hnotconj : ¬ SSGRoute.IsConjPlace k ((f (↑l : ℕ)).1) A := by
          intro hc
          have hc2 : SSGRoute.IsConjPlace k ((f (↑l : ℕ)).1) ((f i).1) :=
            isConjPlace_trans hc (isConjPlace_symm hA_conjQ)
          rcases lt_trichotomy (↑l : ℕ) i with h | h | h
          · exact absurd hc2 (histK_escape_kdisj K N ζ hζ hζK S y f hf h)
          · exact absurd (Fin.ext h) hl
          · exact absurd (isConjPlace_symm hc2) (histK_escape_kdisj K N ζ hζ hζK S y f hf h)
        rw [Work.SSGRoute.ZDataMup.correctionDatum_eq_zero_of_not_conjPlace K
          (fun σ => (2 : ZMod p)⁻¹ * y σ) (histChi K ζ hζK hζ f (↑l : ℕ)) ((f (↑l : ℕ)).1)
          A hnotconj]
        rfl
      · intro hmem
        exact absurd (Finset.mem_univ (⟨i, hij⟩ : Fin j)) hmem
    rw [hcol]
    unfold Work.SSGRoute.ZDataMup.correctionDatum
    rw [if_neg hnotKQi, if_pos hA_conjQ]
  -- transport to the local group of `Q` along `ρ`: `σ' := ρ⁻¹ τ ρ`
  set σ' : Ω ≃ₐ[k] Ω := ρ⁻¹ * (τ : Ω ≃ₐ[k] Ω) * ρ with hσ'def
  have hτQ : (τ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k Q := (Subgroup.mem_inf.mp hτ).1
  have hτK : (τ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hτ).2
  have hσ'K : σ' ∈ K.fixingSubgroup := by
    rw [hσ'def]
    exact (IsGalois.fixingSubgroup_normal_of_isGalois K).conj_mem (τ : Ω ≃ₐ[k] Ω) hτK ρ⁻¹
  have hσ'A : σ' ∈ SSGRoute.decomp k A := by
    rw [MulAction.mem_stabilizer_iff, hσ'def, mul_smul, mul_smul, hρA,
      MulAction.mem_stabilizer_iff.mp hτQ, ← hρA, inv_smul_smul]
  have hσ'mem : σ' ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup :=
    Subgroup.mem_inf.mpr ⟨hσ'A, hσ'K⟩
  -- the realisation at `A` reads `χ_j = ½y + datum = −χ_i`
  have hreal := hpres j A hAhist σ' hσ'mem
  have hvalj : histChi K ζ hζK hζ f j σ' = - histChi K ζ hζK hζ f i σ' := by
    show Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f j).2 σ' = - _
    rw [hreal, hdatum σ']
    ring
  have hsum : histChi K ζ hζK hζ f i σ' + histChi K ζ hζK hζ f j σ' = 0 := by
    rw [hvalj]; ring
  -- conjugation invariance transports the vanishing back to `decomp k Q`
  have hconj_eq : ρ * σ' * ρ⁻¹ = (τ : Ω ≃ₐ[k] Ω) := by rw [hσ'def]; group
  have htransport (m : ℕ) : histChi K ζ hζK hζ f m (τ : Ω ≃ₐ[k] Ω)
      = histChi K ζ hζK hζ f m σ' := by
    show Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2 (τ : Ω ≃ₐ[k] Ω)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2 σ'
    rw [← hconj_eq]
    exact Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK (f m).2 hρK σ'
  rw [htransport i, htransport j]
  exact hsum

end Work.SSGRoute.H9
