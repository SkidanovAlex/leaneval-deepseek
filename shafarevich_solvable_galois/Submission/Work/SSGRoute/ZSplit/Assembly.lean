import Submission.Work.SSGRoute.ZVocab
import Submission.Work.SSGRoute.ZSplit.Auxiliary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The general coefficient module of Schmidt--Wingberg's Theorem 13

`Work.SSGRoute.z_data_general` is stated for an arbitrary finite `𝔽_p[Gal(K|k)]`-module `E`.  This
file proves it (in the `z`-data form `Work.SSGRoute.IsZData`) from two inputs:

* `Work.SSGRoute.IsMupZData`: the one-dimensional case (`dim_{𝔽_p} E ≤ 1`) at *every* pair
  `(Λ,S)` — the "`A = μ_p`" case which Schmidt--Wingberg prove first; and
* `Work.SSGRoute.IsAuxiliaryZData`: the auxiliary/realisation input of the paper's induction, i.e.
  the existence of the class `yt` (with the prescribed local components at `S` and zero at the new
  places of `S₀ ⊇ S`) together with the one-dimensional `z`-data for it.

The induction on `dim_{𝔽_p} E` uses a *linear* (not `Gal(K|k)`-equivariant) decomposition
`E = ker ρ ⊕ ⟨z₀⟩`: all clauses of the `z`-data live over `G_K`, where the action of `Gal(K|k)` is
trivial, so no equivariance is needed.  The passage from the `ker ρ`-valued class to `E` is
`Work.SSGRoute.IsZData.map`, and the combination of the two summands is
`Work.SSGRoute.IsZData.split`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false


section Assembly

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)]
variable [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The general coefficient module of the `z`-construction, from the one-dimensional case and the
auxiliary realisation input** (induction on `dim_{𝔽_p} E`, Schmidt--Wingberg §4 pp. 18--19). -/
theorem z_data_general_of_mup_and_aux_zsplit (hμ : IsMupZData p k Ω K)
    (haux : IsAuxiliaryZData p k Ω K) :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
      (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, IsFinPlace k A)
      (hSdisj : ∀ A ∈ S, ∀ B ∈ S, IsConjPlace k A B → A = B)
      (hSram : ∀ B : ValuationSubring Ω, IsFinPlace k B →
        (IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, IsConjPlace k A B)
      (y : (Ω ≃ₐ[k] Ω) → E)
      (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
      (hyc : IsLocConstOn K.fixingSubgroup y)
      (hyS : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
        ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0)
      (hyT : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0)
      (hy0 : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y σ = 0)
      (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0),
      ∃ z, IsZData p K Λ S y z := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Module.finrank (ZMod p) E = n →
      ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ], K ≤ Λ →
      ∀ (S : Finset (ValuationSubring Ω)), (∀ A ∈ S, IsFinPlace k A) →
      (∀ A ∈ S, ∀ B ∈ S, IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B →
        (IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, IsConjPlace k A B) →
      ∀ (y : (Ω ≃ₐ[k] Ω) → E),
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h) →
      IsLocConstOn K.fixingSubgroup y →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
        ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y σ = 0) →
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) →
      ∃ z, IsZData p K Λ S y z
  have key : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n' ih
    intro E instE instMod instAct instSMC instFin hfin Λ instΛf instΛg hKΛ S hSfin hSdisj hSram
      y hy hyc hyS hyT hy0 hyinf
    by_cases hsmall : Module.finrank (ZMod p) E ≤ 1
    · exact hμ E hsmall Λ hKΛ S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf
    · have h2 : 2 ≤ Module.finrank (ZMod p) E := by omega
      obtain ⟨ρ, z₀, hρz₀, hker⟩ := exists_linearFunctional_finrank_ker p h2
      -- the codimension-one piece, with the trivial action (all the `z`-data lives over `G_K`)
      let E₀ := ↥(LinearMap.ker ρ)
      letI : SMul (K ≃ₐ[k] K) E₀ := ⟨fun _ x => x⟩
      letI : MulAction (K ≃ₐ[k] K) E₀ :=
        { smul := fun _ x => x, one_smul := fun x => rfl, mul_smul := fun g h x => rfl }
      letI : DistribMulAction (K ≃ₐ[k] K) E₀ :=
        { smul := fun _ x => x, one_smul := fun x => rfl, mul_smul := fun g h x => rfl,
          smul_zero := fun g => rfl, smul_add := fun g x x' => rfl }
      letI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₀ := ⟨fun g c x => rfl⟩
      -- the datum `y⁰ = π ∘ y` of the codimension-one piece
      have hmem : ∀ σ, ρ (y σ - (ρ (y σ)) • z₀) = 0 := by
        intro σ
        rw [map_sub, map_smul, hρz₀, smul_eq_mul, mul_one, sub_self]
      let y₀ : (Ω ≃ₐ[k] Ω) → E₀ := fun σ => ⟨y σ - (ρ (y σ)) • z₀, hmem σ⟩
      have hy₀ : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y₀ (g * h) = y₀ g + y₀ h := by
        intro g hg h hh
        refine Subtype.ext ?_
        show y (g * h) - (ρ (y (g * h))) • z₀
          = (y g - (ρ (y g)) • z₀) + (y h - (ρ (y h)) • z₀)
        rw [hy g hg h hh, map_add]
        module
      have hyc₀ : IsLocConstOn K.fixingSubgroup y₀ := by
        obtain ⟨U, hUopen, hUc⟩ := hyc
        refine ⟨U, hUopen, fun g hg u hu hgu => ?_⟩
        refine Subtype.ext ?_
        show y (g * u) - (ρ (y (g * u))) • z₀ = y g - (ρ (y g)) • z₀
        rw [hUc g hg u hu hgu]
      have hyS₀ : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
          ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y₀ σ = 0 := by
        intro B hB hnot hns σ hσG hσI
        refine Subtype.ext ?_
        show y σ - (ρ (y σ)) • z₀ = 0
        rw [hyS B hB hnot hns σ hσG hσI, map_zero, zero_smul, sub_zero]
      have hyT₀ : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
          ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y₀ σ = 0 := by
        intro B hB hconj σ hσG hσI
        refine Subtype.ext ?_
        show y σ - (ρ (y σ)) • z₀ = 0
        rw [hyT B hB hconj σ hσG hσI, map_zero, zero_smul, sub_zero]
      have hy0₀ : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
          (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
          ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y₀ σ = 0 := by
        intro B hB hconj hd σ hσG hσD
        refine Subtype.ext ?_
        show y σ - (ρ (y σ)) • z₀ = 0
        rw [hy0 B hB hconj hd σ hσG hσD, map_zero, zero_smul, sub_zero]
      have hyinf₀ : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y₀ c = 0 := by
        intro c hc hc2
        refine Subtype.ext ?_
        show y c - (ρ (y c)) • z₀ = 0
        rw [hyinf c hc hc2, map_zero, zero_smul, sub_zero]
      -- the induction hypothesis at the codimension-one piece
      have hlt : Module.finrank (ZMod p) ↥(LinearMap.ker ρ) < n' := by
        have h := hker
        rw [hfin] at h
        omega
      obtain ⟨z₀', hz₀'⟩ := ih (Module.finrank (ZMod p) ↥(LinearMap.ker ρ)) hlt
        ↥(LinearMap.ker ρ) rfl Λ hKΛ S hSfin hSdisj hSram y₀ hy₀ hyc₀ hyS₀ hyT₀ hy0₀ hyinf₀
      -- transport it back to `E` along the inclusion
      let zE : (Ω ≃ₐ[k] Ω) → E := fun σ => (z₀' σ : E)
      have hzE : IsZData p K Λ S (fun σ => y σ - (ρ (y σ)) • z₀) zE := by
        have hmapped := IsZData.map hz₀' (Submodule.subtype (LinearMap.ker ρ))
        simpa [zE, y₀] using hmapped
      -- the field cut out by `z⁰`
      obtain ⟨L, hLfin, hLnorm, hLvan'⟩ :=
        exists_normal_fixingSubgroup_vanishing p k Ω K z₀' hz₀'.1 hz₀'.2.1
      haveI := hLfin
      haveI := hLnorm
      have hLvan : ∀ σ ∈ L.fixingSubgroup, zE σ = 0 := by
        intro σ hσ
        show (z₀' σ : E) = 0
        rw [hLvan' σ hσ]
        rfl
      -- the auxiliary place set
      obtain ⟨S₀, hS₀fin, hS₀disj, hS₀sub, hS₀ramL⟩ :=
        exists_auxiliary_placeSet k Ω L S hSfin hSdisj
      -- the auxiliary pair
      let Λ₀ : IntermediateField k Ω := L ⊔ Λ
      haveI hΛ₀fd : FiniteDimensional k Λ₀ := inferInstance
      haveI hLgal : IsGalois k L :=
        Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
      haveI hΛ₀gal : IsGalois k Λ₀ := inferInstance
      have hLΛ₀ : L ≤ Λ₀ := le_sup_left
      have hΛΛ₀ : Λ ≤ Λ₀ := le_sup_right
      have hKΛ₀ : K ≤ Λ₀ := le_trans hKΛ hΛΛ₀
      -- `S₀` contains the places over `p` and the places ramified in `Λ₀`
      have hS₀ramΛ₀ : ∀ B : ValuationSubring Ω, IsFinPlace k B →
          (IsRamifiedIn k Λ₀ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S₀, IsConjPlace k A B := by
        intro B hB h
        rcases h with hram | hp
        · rcases isRamifiedIn_sup (L := L) (Λ := Λ) hram with hL | hΛ
          · exact hS₀ramL B hB hL
          · obtain ⟨A, hA, hAB⟩ := hSram B hB (Or.inl hΛ)
            obtain ⟨A', hA', hA'A⟩ := hS₀sub A hA
            exact ⟨A', hA', isConjPlace_trans (isConjPlace_symm hA'A) hAB⟩
        · obtain ⟨A, hA, hAB⟩ := hSram B hB (Or.inr hp)
          obtain ⟨A', hA', hA'A⟩ := hS₀sub A hA
          exact ⟨A', hA', isConjPlace_trans (isConjPlace_symm hA'A) hAB⟩
      -- the hypotheses for the auxiliary input
      have hadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
          (fun σ => ρ (y σ)) (g * h) = (fun σ => ρ (y σ)) g + (fun σ => ρ (y σ)) h := by
        intro g hg h hh
        show ρ (y (g * h)) = ρ (y g) + ρ (y h)
        rw [hy g hg h hh, map_add]
      have hloc : IsLocConstOn K.fixingSubgroup (fun σ => ρ (y σ)) := by
        obtain ⟨U, hUopen, hUc⟩ := hyc
        exact ⟨U, hUopen, fun g hg u hu hgu => by
          show ρ (y (g * u)) = ρ (y g)
          rw [hUc g hg u hu hgu]⟩
      have hνS : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
          ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ →
          (fun σ => ρ (y σ)) σ = 0 := by
        intro B hB hnot hns σ hσG hσI
        show ρ (y σ) = 0
        rw [hyS B hB hnot hns σ hσG hσI, map_zero]
      have hνT : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
          ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → (fun σ => ρ (y σ)) σ = 0 := by
        intro B hB hconj σ hσG hσI
        show ρ (y σ) = 0
        rw [hyT B hB hconj σ hσG hσI, map_zero]
      have hν0 : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
          (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
          ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → (fun σ => ρ (y σ)) σ = 0 := by
        intro B hB hconj hd σ hσG hσD
        show ρ (y σ) = 0
        rw [hy0 B hB hconj hd σ hσG hσD, map_zero]
      have hνinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → (fun σ => ρ (y σ)) c = 0 := by
        intro c hc hc2
        show ρ (y c) = 0
        rw [hyinf c hc hc2, map_zero]
      obtain ⟨f, hf, yt, zF, hreal, hzmu⟩ := haux Λ hKΛ Λ₀ hΛΛ₀ hKΛ₀ L hLΛ₀ S₀ hS₀ramL
        hS₀fin hS₀disj S hSfin hS₀ramΛ₀ (fun σ => ρ (y σ)) hadd hloc hνS hνT hν0 hνinf
      have hreal' : IsYRealisation p K Λ₀ S S₀ (fun B σ => ρ (y σ)) yt :=
        IsYRealisation.congr_datum hreal (fun A hA => hf A hA)
      exact ⟨fun σ => zE σ + (zF σ) • z₀,
        IsZData.split hKΛ S y ρ z₀ hρz₀ zE hzE L Λ₀ hLΛ₀ hΛΛ₀ hLvan S₀ hS₀sub hS₀ramL
          yt zF hreal' hzmu⟩
  intro E instE instMod instAct instSMC instFin Λ instΛf instΛg hKΛ S hSfin hSdisj hSram y hy hyc hyS
    hyT hy0 hyinf
  exact key (Module.finrank (ZMod p) E) E rfl Λ hKΛ S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf

end Assembly

end Work.SSGRoute
