import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.AuxRealisationGate
import Submission.Work.SSGRoute.ZDG.exists_level_zData_confinement
import Submission.Work.SSGRoute.ZSplit.Auxiliary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The general coefficient module of Schmidt--Wingberg's Theorem 13, from the one-dimensional
case and the Grünwald-with-escape realisation

`Work.SSGRoute.IsMupZData p k Ω K` is the one-dimensional (`dim_{𝔽_p} A ≤ 1`, i.e. `A = μ_p`) case
of the `z`-data of Schmidt--Wingberg's Theorem 13 at *every* pair `(Λ,S)`.  This file proves the
general case

  `∀ E, IsZData p K Λ S y z`

by the induction on `dim_{𝔽_p} E` of the paper (§4, pp. 18--19), the auxiliary class of the
induction step being supplied by the Grünwald-with-escape realisation
`Work.SSGRoute.isAuxiliaryZData_of_grunwald_v2` instead of the (over-strong) Poitou--Tate input
`Work.SSGRoute.IsAuxiliaryZData`.

The two structural inputs of the induction step are consequences of the definitions:

* the auxiliary field `L₂ = K̃` of the paper is the level of the `E₀`-valued class `z₀` which
  contains the `p`-th powers, the commutators of `G_K` and the inertia of the prescribed places `S`
  (`Work.SSGRoute.ZDG.exists_level_zData_confinement`);
* the enlarged place set `T' ⊇ T` may be chosen with its new places split completely in `Λ`, because
  the same lemma confines the ramification of that level, outside the conjugates of `S`, to the
  places at which the class `z₀` is ramified, and those split in `Λ` by the fifth clause of the
  `z`-data of `z₀` (`exists_placeSet_cover_split` below).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataGen

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **The confinement of the ramification, at a place outside the conjugates of `S`.**

This is `Work.SSGRoute.ZConstruction.isSplitIn_of_ramified_explained` with the covering hypothesis
required only at the places outside the conjugates of `S` — the form in which the confinement of the
ramification of a level below `Λ` is available. -/
theorem isSplitIn_of_ramified_explained_notS {K Λ N : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)}
    (hNorm : (Λ.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal)
    {E : Type} [AddCommGroup E] {y z : (Ω ≃ₐ[k] Ω) → E}
    (h : HasZData K Λ S y z)
    (hcov : ∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k N B →
      (∀ A ∈ S, ¬ IsConjPlace k A B) →
      ∃ Q : ValuationSubring Ω, IsConjPlace k B Q ∧
        ∃ σ ∈ K.fixingSubgroup, IsInertia k Q σ ∧ z σ ≠ 0)
    {B : ValuationSubring Ω} (hB : IsFinPlace k B)
    (hram : IsRamifiedIn k N B) (hnotS : ∀ A ∈ S, ¬ IsConjPlace k A B) :
    IsSplitIn k Λ B := by
  obtain ⟨Q, hBQ, hQram⟩ := hcov B hB hram hnotS
  have hQfin : IsFinPlace k Q := by
    obtain ⟨σ, rfl⟩ := hBQ
    rwa [isFinPlace_smul_iff]
  have hnotS' : ∀ A ∈ S, ¬ IsConjPlace k A Q := by
    intro A hA hAQ
    exact hnotS A hA (isConjPlace_trans hAQ (isConjPlace_symm hBQ))
  have hQ : IsSplitIn k Λ Q :=
    ZConstruction.hasZData_ramification_confined h hQfin hQram hnotS'
  obtain ⟨τ, hτ⟩ := hBQ
  exact (isSplitIn_conj Λ hNorm B τ).mp (by rw [hτ]; exact hQ)

/-- **The enlarged place set `T'` of the induction step, with the new places split in `Λ`.**

Given a finite Galois level `N` over `k` and the *confinement* of the ramification of `N` outside
the conjugates of `S` to the places split completely in `Λ`, there is a finite set `S₀ ⊇ S` of
pairwise non-conjugate finite places such that

* every finite place ramified in `N` is conjugate into `S₀`;
* every place of `S₀ ∖ S` splits completely in `Λ`.

The new places of `S₀` are a set of representatives of the ramification of `N` outside the
conjugates of `S` (finitely many by `Work.SSGRoute.PT.ramifiedPlaces_finite_k_aux`); the
confinement makes them split in `Λ`. -/
theorem exists_placeSet_cover_split (N Λ : IntermediateField k Ω)
    [FiniteDimensional k N] [IsGalois k N]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k N B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B) :
    ∃ S₀ : Finset (ValuationSubring Ω),
      (∀ A ∈ S₀, SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ S₀, ∀ B ∈ S₀, SSGRoute.IsConjPlace k A B → A = B) ∧
      S ⊆ S₀ ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k N B →
        ∃ A ∈ S₀, SSGRoute.IsConjPlace k A B) ∧
      (∀ A ∈ S₀, A ∉ S → SSGRoute.IsSplitIn k Λ A) := by
  classical
  have hNnorm : (N.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal := by
    rw [← IntermediateField.restrictNormalHom_ker N]
    exact MonoidHom.normal_ker _
  obtain ⟨R, hRfin, hRdisj, hRcov⟩ := Work.SSGRoute.PT.ramifiedPlaces_finite_k_aux k Ω N
  refine ⟨S ∪ R.filter (fun A => (∀ B ∈ S, ¬ SSGRoute.IsConjPlace k B A) ∧
      SSGRoute.IsSplitIn k Λ A), ?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact hSfin A hA
    · exact hRfin A (Finset.mem_of_mem_filter A hA)
  · intro A hA B hB hconj
    rcases Finset.mem_union.mp hA with hA | hA <;> rcases Finset.mem_union.mp hB with hB | hB
    · exact hSdisj A hA B hB hconj
    · exact absurd hconj ((Finset.mem_filter.mp hB).2.1 A hA)
    · exact absurd (SSGRoute.isConjPlace_symm hconj) ((Finset.mem_filter.mp hA).2.1 B hB)
    · exact hRdisj A (Finset.mem_of_mem_filter A hA) B (Finset.mem_of_mem_filter B hB) hconj
  · intro A hA
    exact Finset.mem_union_left _ hA
  · intro B hBfin hram
    obtain ⟨A₀, hA₀R, hA₀B⟩ := hRcov B hBfin hram
    by_cases hcs : ∃ B' ∈ S, SSGRoute.IsConjPlace k B' A₀
    · obtain ⟨B', hB'S, hB'A₀⟩ := hcs
      exact ⟨B', Finset.mem_union_left _ hB'S, SSGRoute.isConjPlace_trans hB'A₀ hA₀B⟩
    · push Not at hcs
      have hA₀fin : SSGRoute.IsFinPlace k A₀ := hRfin A₀ hA₀R
      have hA₀ram : SSGRoute.IsRamifiedIn k N A₀ := by
        obtain ⟨τ, hτ⟩ := hA₀B
        exact (SSGRoute.isRamifiedIn_conj N hNnorm A₀ τ).mp (by rw [hτ]; exact hram)
      have hsplit : SSGRoute.IsSplitIn k Λ A₀ :=
        hconf A₀ hA₀fin hA₀ram (fun B' hB' hc => hcs B' hB' hc)
      exact ⟨A₀, Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hA₀R, fun B' hB' hc => hcs B' hB' hc, hsplit⟩), hA₀B⟩
  · intro A hA hAnotS
    rcases Finset.mem_union.mp hA with hA | hA
    · exact absurd hA hAnotS
    · exact (Finset.mem_filter.mp hA).2.2

theorem zDataGeneralOfMupAndZetaGen (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hreal : Work.SSGRoute.ZConstruction.AuxRealisationGate (p := p) (K := K) (ζ := ζ)
      (hζ := hζ) (hζK := hζK))
    (hμ : Work.SSGRoute.IsMupZData p k Ω K) :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
      (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
      (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
      (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
        ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
      (y : (Ω ≃ₐ[k] Ω) → E)
      (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
      (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
      (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
      (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
      (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
      (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0),
      ∃ z, Work.SSGRoute.IsZData p K Λ S y z := by
  classical
  -- ## The one-dimensional gate, for the coefficient module `ZMod p` (the case `A = μ_p`)
  have hgate : ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ], K ≤ Λ →
      ∀ (S : Finset (ValuationSubring Ω)), (∀ A ∈ S, SSGRoute.IsFinPlace k A) →
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
        ∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ (y : (Ω ≃ₐ[k] Ω) → ZMod p),
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h) →
      SSGRoute.IsLocConstOn K.fixingSubgroup y →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0) →
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) →
      ∃ z, IsZData p K Λ S y z := by
    intro Λ _ _ hKΛ S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf
    exact hμ (ZMod p) (le_of_eq (Module.finrank_self (ZMod p))) Λ hKΛ S hSfin hSdisj hSram
      y hy hyc hyS hyT hy0 hyinf
  -- ## The strong induction on `dim_{𝔽_p} E`
  let P : ℕ → Prop := fun n =>
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Module.finrank (ZMod p) E = n →
      ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ], K ≤ Λ →
      ∀ (S : Finset (ValuationSubring Ω)), (∀ A ∈ S, SSGRoute.IsFinPlace k A) →
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
        ∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ (y : (Ω ≃ₐ[k] Ω) → E),
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h) →
      SSGRoute.IsLocConstOn K.fixingSubgroup y →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0) →
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
      -- the codimension-one piece, with the trivial action (the `z`-data lives over `G_K`)
      let E₀ := ↥(LinearMap.ker ρ)
      letI : SMul (K ≃ₐ[k] K) E₀ := ⟨fun _ x => x⟩
      letI : MulAction (K ≃ₐ[k] K) E₀ :=
        { smul := fun _ x => x, one_smul := fun x => rfl, mul_smul := fun g h x => rfl }
      letI : DistribMulAction (K ≃ₐ[k] K) E₀ :=
        { smul := fun _ x => x, one_smul := fun x => rfl, mul_smul := fun g h x => rfl,
          smul_zero := fun g => rfl, smul_add := fun g x x' => rfl }
      letI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₀ := ⟨fun g c x => rfl⟩
      -- the datum `y₀ = π ∘ y` of the codimension-one piece
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
      have hzE' : HasZData K Λ S (fun σ => y σ - (ρ (y σ)) • z₀) zE := hzE
      -- the auxiliary field `L₂ = K̃`: the level of `z₀'` containing the `p`-th powers, the
      -- commutators of `G_K` and the inertia of the places of `S`
      have hIlevel : ∀ B : ValuationSubring Ω, (∃ A ∈ S, IsConjPlace k A B) →
          ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → z₀' σ = 0 := by
        intro B hB σ hσK hσI
        have hBfin : IsFinPlace k B := by
          obtain ⟨A, hA, hAB⟩ := hB
          obtain ⟨τ, hτ⟩ := hAB
          rw [← hτ]
          exact (isFinPlace_smul_iff A τ).mpr (hSfin A hA)
        have h1 : zE σ = y σ - (ρ (y σ)) • z₀ := hzE.2.2.1 B hBfin hB σ hσK hσI.1
        have h2 : (y σ - (ρ (y σ)) • z₀ : E) = 0 :=
          congrArg Subtype.val (hyT₀ B hBfin hB σ hσK hσI)
        have hval : zE σ = 0 := by rw [h1, h2]
        exact Subtype.ext hval
      obtain ⟨L, hLfin, hLnorm, hKL, hLvan₀, hLexp, hLcomm, hLiner, hLconf⟩ :=
        Work.SSGRoute.ZDG.exists_level_zData_confinement p k Ω K z₀' hz₀'.1 hz₀'.2.1 S hIlevel
      haveI : FiniteDimensional k L := hLfin
      haveI : Normal k L := hLnorm
      haveI hLgal : IsGalois k L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
      have hLvan : ∀ σ ∈ L.fixingSubgroup, zE σ = 0 := by
        intro σ hσ
        show ((z₀' σ : E)) = 0
        rw [hLvan₀ σ hσ]
        rfl
      -- the auxiliary pair `(Λ₀, S₀)` with `Λ₀ = Λ ⊔ L`
      let Λ₀ : IntermediateField k Ω := Λ ⊔ L
      haveI : FiniteDimensional k Λ₀ := inferInstance
      haveI : IsGalois k Λ₀ := inferInstance
      have hΛΛ₀ : Λ ≤ Λ₀ := le_sup_left
      have hLΛ₀ : L ≤ Λ₀ := le_sup_right
      have hΛLsup : Λ ⊔ L = Λ₀ := rfl
      have hNormΛ : (Λ.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal := by
        rw [← IntermediateField.restrictNormalHom_ker Λ]
        exact MonoidHom.normal_ker _
      -- ramification of `K` is inside the conjugates of `S`
      have hramKΛ : ∀ B : ValuationSubring Ω, IsRamifiedIn k K B → IsRamifiedIn k Λ B := by
        intro B ⟨σ, hσI, hσ⟩
        exact ⟨σ, hσI, fun hmem => hσ (IntermediateField.fixingSubgroup_le hKΛ hmem)⟩
      have hnotK_of_notS : ∀ B : ValuationSubring Ω, IsFinPlace k B →
          (∀ A ∈ S, ¬ IsConjPlace k A B) → ¬ IsRamifiedIn k K B := by
        intro B hB hnotS hK
        obtain ⟨A, hA, hAB⟩ := hSram B hB (Or.inl (hramKΛ B hK))
        exact hnotS A hA hAB
      -- the confinement of the ramification of `L` outside `S` to the places split in `Λ`
      have hconf : ∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k L B →
          (∀ A ∈ S, ¬ IsConjPlace k A B) → IsSplitIn k Λ B := by
        intro B hBfin hram hnotS
        exact isSplitIn_of_ramified_explained_notS hNormΛ hz₀'
          (fun B' hB' hram' hnotS' => hLconf B' hB' (hnotK_of_notS B' hB' hnotS') hnotS' hram')
          hBfin hram hnotS
      -- the enlarged place set
      obtain ⟨S₀, hS₀fin, hS₀disj, hSS₀, hS₀cov, hS₀new⟩ :=
        exists_placeSet_cover_split L Λ S hSfin hSdisj hconf
      have hS₀ramΛ : ∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k Λ B →
          ∃ A ∈ S₀, IsConjPlace k A B := by
        intro B hB hram
        obtain ⟨A, hA, hAB⟩ := hSram B hB (Or.inl hram)
        exact ⟨A, hSS₀ hA, hAB⟩
      have hS₀ramΛ₀ : ∀ B : ValuationSubring Ω, IsFinPlace k B →
          (IsRamifiedIn k Λ₀ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S₀, IsConjPlace k A B := by
        intro B hB hc
        rcases hc with hram | hp
        · rcases isRamifiedIn_sup Λ L hram with hΛ | hL
          · exact hS₀ramΛ B hB hΛ
          · exact hS₀cov B hB hL
        · obtain ⟨A, hA, hAB⟩ := hSram B hB (Or.inr hp)
          exact ⟨A, hSS₀ hA, hAB⟩
      -- the datum `ν = ρ ∘ y` and its hypotheses
      have hνadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
          (fun σ => ρ (y σ)) (g * h) = (fun σ => ρ (y σ)) g + (fun σ => ρ (y σ)) h := by
        intro g hg h hh
        show ρ (y (g * h)) = ρ (y g) + ρ (y h)
        rw [hy g hg h hh, map_add]
      have hνc : IsLocConstOn K.fixingSubgroup (fun σ => ρ (y σ)) := by
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
      -- the auxiliary realisation at `(Λ₀, S₀)`
      obtain ⟨f, hf, yt, zF, hreal, hzmu⟩ :=
        hreal hgate
          Λ hKΛ Λ₀ hΛΛ₀ (le_trans hKΛ hΛΛ₀) L hLΛ₀ S₀ hS₀cov hS₀fin hS₀disj hS₀ramΛ₀
          S hSfin hSS₀ hS₀new L hKL hΛLsup hLexp hLcomm
          (fun A hA σ hσK hσI => hLiner A ⟨A, hA, isConjPlace_refl A⟩ σ hσK hσI)
          hS₀ramΛ hS₀cov
          (fun σ => ρ (y σ)) hνadd hνc hνS hνT hν0 hνinf
      have hreal' : IsYRealisation p K Λ₀ S S₀ (fun B σ => ρ (y σ)) yt :=
        IsYRealisation.congr_datum hreal (fun A hA => hf A hA)
      -- the assembly
      exact ⟨fun σ => zE σ + (zF σ) • z₀,
        IsZData.split hKΛ S y ρ z₀ hρz₀ zE hzE L Λ₀ hLΛ₀ hΛΛ₀ hLvan S₀
          (fun A hA => ⟨A, hSS₀ hA, isConjPlace_refl A⟩) hS₀cov
          yt zF hreal' hzmu⟩
  intro E instE instMod instAct instSMC instFin Λ instΛf instΛg hKΛ S hSfin hSdisj hSram
    y hy hyc hyS hyT hy0 hyinf
  exact key (Module.finrank (ZMod p) E) E rfl Λ hKΛ S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf

end Work.SSGRoute.ZDataGen
