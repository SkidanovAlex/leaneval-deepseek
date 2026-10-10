import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.ZConstruction.mem_localNormSubgroup_of_mem_powRange
import Submission.Work.SSGRoute.ZDataMup.hLocalFactor_eq_one_ofInfinite
import Submission.Work.SSGRoute.ZDataMup.isUnramifiedIn_of_inertia_subset_fixingSubgroup
import Submission.Work.SSGRoute.ZDataMup.mupOddRecipAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The odd-`p` local factor is trivial away from the one-sided set `T'`

This file proves `Work.SSGRoute.ZDataMup.OddForm.oTheta_eq_one_of_ne_oddPrime`: for an odd prime
`p ≠ 2`, two cocycles `a`, `b` attached (through their Kummer characters) to global elements
`α, β ∈ ↥Kˣ` and vanishing on the inertia of every finite place of `Ω` outside the one-sided finite
set `T'`, the level-`α` local factor `oTheta α β v` of the global abelian Artin map is trivial at
every place `v` of `↥K` that does not lie below an element of `T'`.

* at a finite place `v = 𝔭`: a place `A` of `Ω` over `𝔭` exists
  (`NK.ReconstructField.exists_finitePlace_of_prime_level`); it is not conjugate to any element of
  `T'` (its prime below is `𝔭`, and `hv` excludes this), so `hunr` makes `χ_α` and `χ_β` vanish on
  its inertia.  Vanishing of `χ_β` makes the local image of `β` a `p`-th power times a local unit
  (`kummerChar_zero_on_inertia_imp_mem_unramified`), and both factors are local norms at `𝔭`:
  `p`-th powers because `Gal(↥K(α^{1/p})/↥K)` has order `p`, local units because `𝔭` is unramified
  in `↥K(α^{1/p})` (`isUnramifiedIn_of_inertia_subset_fixingSubgroup`, using the vanishing of
  `χ_α`).  Hence the one-place idèle is a norm idèle and the local factor is `1`
  (`oddArtin_onePlace`).
* at an archimedean place: local degrees are at most `2` and the degree `p` is odd, so the local
  norm group is everything (`localNormSubgroup_ofInfinite_eq_top_of_odd_finrank`) — this is where
  `p ≠ 2` enters.

The only degenerate case is `α ∈ (↥Kˣ)^p`, where the Kummer level is `↥K` itself and `oTheta` lands
in the trivial group.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataMup.OddForm

open Work.SSGRoute.ZDataMup.LTRecFamHonest

noncomputable section

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- **The prime of `↥K` below a place of `Ω` is invariant under the fixing subgroup of `↥K`.** -/
theorem comap_smul_eq_comap_of_mem_fixingSubgroup (A : ValuationSubring Ω) (τ : Ω ≃ₐ[k] Ω)
    (hτ : τ ∈ K.fixingSubgroup) :
    (τ • A).comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
  have hfix : ∀ x : ↥K, (τ⁻¹ : Ω ≃ₐ[k] Ω) • (algebraMap ↥K Ω x) = algebraMap ↥K Ω x := by
    intro x
    rw [AlgEquiv.smul_def]
    exact (IntermediateField.mem_fixingSubgroup_iff K (τ⁻¹ : Ω ≃ₐ[k] Ω)).mp
      (K.fixingSubgroup.inv_mem hτ) _ x.2
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hfix x]

/-- **A place of `Ω` that is finite over `↥K` is finite over `k`.** -/
theorem isFinPlace_of_isFinPlace_level (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace ↥K A) : SSGRoute.IsFinPlace k A := by
  haveI : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  intro htop
  have hAtop : A = ⊤ :=
    Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top A
      (IsSepClosure.separable (k := k) (K := Ω)).isAlgebraic htop
  exact hA (by rw [hAtop]; ext x; simp)

/-- **Places of `Ω` conjugate over `↥K` have the same prime of `↥K` below them** (the converse of
`exists_conj_of_oddPrime_eq`). -/
theorem oddPrime_eq_of_exists_conj {A B : ValuationSubring Ω} (hA : SSGRoute.IsFinPlace k A)
    (hB : SSGRoute.IsFinPlace k B)
    (h : ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) :
    oddPrime (K := K) A hA = oddPrime (K := K) B hB := by
  obtain ⟨τ, hτ, hconj⟩ := h
  have hBA : B = τ • A := by
    refine ValuationSubring.ext B (τ • A) fun x => ?_
    rw [hconj x, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hcomap : B.comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
    rw [hBA]
    exact comap_smul_eq_comap_of_mem_fixingSubgroup (K := K) A τ hτ
  apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
  rw [← oddPrime_spec (K := K) hA, ← oddPrime_spec (K := K) hB, hcomap]

theorem oTheta_eq_one_of_ne_oddPrime {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (a b : (Ω ≃ₐ[k] Ω) → ZMod p) (α β : (↥K)ˣ)
    (hα : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      a σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ α
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (hβ : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      b σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (T' : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T', SSGRoute.IsFinPlace k A)
    (hunr : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T', ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0)
    (v : NK.GlobalCFT.Place ↥K)
    (hv : ∀ A ∈ T'.attach,
      NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A.1
        (hTfin A.1 A.2)) ≠ v) :
    Work.SSGRoute.ZDataMup.OddForm.oTheta (K := K) (p := p) ζ hζ α β v = 1 := by
  by_cases hαpow : α ∈ NK.LocalAnabelian.powSubgroup p ↥K
  · -- Degenerate case: the Kummer level of `α` is `↥K` itself, so the target group is trivial.
    have hbot : hLevel (K := K) (Ω := Ω) (p := p) α = ⊥ :=
      NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := Ω) (k := ↥K) p
        Fact.out hζ hαpow
    haveI : Subsingleton (↥(hLevel (K := K) (Ω := Ω) (p := p) α) ≃ₐ[↥K]
        ↥(hLevel (K := K) (Ω := Ω) (p := p) α)) := by
      rw [hbot]
      refine ⟨fun x y => AlgEquiv.ext fun z => ?_⟩
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp z.2
      have hz : z = algebraMap ↥K ↥(⊥ : IntermediateField ↥K Ω) c := (Subtype.ext hc).symm
      rw [hz, AlgEquiv.commutes, AlgEquiv.commutes]
    exact Subsingleton.elim _ _
  · haveI hfdL : FiniteDimensional ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) α) :=
      hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α
    haveI hgalL : IsGalois ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) α) :=
      hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ α
    haveI hnfL : NumberField ↥(hLevel (K := K) (Ω := Ω) (p := p) α) :=
      hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ α
    have hcardL : Nat.card (↥(hLevel (K := K) (Ω := Ω) (p := p) α) ≃ₐ[↥K]
        ↥(hLevel (K := K) (Ω := Ω) (p := p) α)) = p := by
      rw [IsGalois.card_aut_eq_finrank,
        (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) (k := ↥K) p
          Fact.out hζ α hαpow).2]
    -- The one-place idèle of `β` is a norm idèle; then `oddArtin_onePlace` finishes.
    have hmem : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v β ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
          (L := ↥(hLevel (K := K) (Ω := Ω) (p := p) α)) v := by
      rcases v with w | 𝔭
      · -- Archimedean place: the local norm group is everything because `p` is odd.
        have hodd : ¬ 2 ∣ Module.finrank ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) α) := by
          rw [← IsGalois.card_aut_eq_finrank ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) α), hcardL]
          exact (Nat.Prime.odd_of_ne_two Fact.out hp).not_two_dvd_nat
        rw [Work.SSGRoute.ZDataMup.localNormSubgroup_ofInfinite_eq_top_of_odd_finrank
          (K := ↥K) (L := ↥(hLevel (K := K) (Ω := Ω) (p := p) α)) w hodd]
        exact Subgroup.mem_top _
      · -- Finite place `𝔭` of `↥K`.
        -- A place `A` of `Ω` above `𝔭`.
        obtain ⟨A, hApart⟩ := NK.ReconstructField.exists_finitePlace_of_prime_level
          (K₁ := k) (K₁' := Ω) K 𝔭
        -- `A` is not conjugate to any element of `T'`: that would put `𝔭` below a `T'`-element.
        have hnc : ∀ A' ∈ T', ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A.1 ↔
            (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A' := by
          intro A' hA' hconj
          have hprime := oddPrime_eq_of_exists_conj (K := K) (A := A') (B := A.1)
            (hTfin A' hA') A.2 hconj
          have hA'p : oddPrime (K := K) A.1 A.2 = 𝔭 := by
            apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
            rw [← oddPrime_spec (K := K) (A := A.1) A.2, hApart]
          exact hv ⟨A', hA'⟩ (Finset.mem_attach T' _) (by rw [hprime, hA'p])
        -- The Kummer character of `β` vanishes on the inertia of `A`.
        have hchiβ : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
            SSGRoute.IsInertia k A.1 σ →
            Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β
              ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) = 0 :=
          fun σ hσ hI => (hβ σ hσ).symm.trans (hunr A.1 A.2 hnc σ hI).2
        -- hence the local image of `β` at `𝔭` is a `p`-th power times a local unit
        obtain ⟨γ, u, hu, hβeq⟩ :=
          Work.SSGRoute.ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified
            p k Ω K ζ hζ A.1 A.2 𝔭 hApart β hchiβ
        have hloc : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
            (NK.GlobalCFT.Place.ofFinite 𝔭) β = γ ^ p * u := by
          rw [show NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
              (NK.GlobalCFT.Place.ofFinite 𝔭) β =
              Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)) β from rfl]
          exact hβeq
        -- `𝔭` is unramified in the Kummer level of `α`
        have hunrlvl : NK.HeckeL.IsUnramifiedIn (K := ↥K)
            (L := ↥(hLevel (K := K) (Ω := Ω) (p := p) α)) 𝔭 := by
          refine Work.SSGRoute.ZDataMup.isUnramifiedIn_of_inertia_subset_fixingSubgroup
            (K := ↥K) (Ω := Ω) (hLevel (K := K) (Ω := Ω) (p := p) α) 𝔭 ?_
          intro B hB hBp σ hI
          have hBk : SSGRoute.IsFinPlace k B := isFinPlace_of_isFinPlace_level (K := K) B hB
          have hncB : ∀ A' ∈ T', ¬ ∃ τ ∈ K.fixingSubgroup,
              ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A' := by
            intro A' hA' hconj
            have hprime := oddPrime_eq_of_exists_conj (K := K) (A := A') (B := B)
              (hTfin A' hA') hBk hconj
            have hBp' : oddPrime (K := K) B hBk = 𝔭 := by
              apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
              rw [← oddPrime_spec (K := K) (A := B) hBk, hBp]
            exact hv ⟨A', hA'⟩ (Finset.mem_attach T' _) (by rw [hprime, hBp'])
          have hτmem : σ.restrictScalars k ∈ K.fixingSubgroup := by
            rw [IntermediateField.mem_fixingSubgroup_iff]
            intro x hx
            exact σ.commutes ⟨x, hx⟩
          have heq : (IntermediateField.fixingSubgroupEquiv K)
              ⟨σ.restrictScalars k, hτmem⟩ = σ := by
            ext x
            rfl
          have hIfin : SSGRoute.IsInertia k B (σ.restrictScalars k) :=
            (Work.SSGRoute.isInertia_baseChange k Ω K B (σ.restrictScalars k) hτmem).mp
              (by rw [heq]; exact hI)
          have hχ : Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ α σ = 0 := by
            have h0 := (hunr B hBk hncB (σ.restrictScalars k) hIfin).1
            rw [hα (σ.restrictScalars k) hτmem, heq] at h0
            exact h0
          exact (Work.SSGRoute.ZDataMup.OddForm.odd_kummerCharZMod_eq_zero_iff_mem_fixingSubgroup
            (K := K) ζ hζ α σ).mp hχ
        rw [hloc]
        refine Subgroup.mul_mem _ ?_ ?_
        · exact Work.SSGRoute.ZConstruction.mem_localNormSubgroup_of_mem_powRange
            (K := ↥K) (L := ↥(hLevel (K := K) (Ω := Ω) (p := p) α)) hcardL
            (NK.GlobalCFT.Place.ofFinite 𝔭) (γ ^ p) ⟨γ, by rw [powMonoidHom_apply]⟩
        · exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
            (K := ↥K) (L := ↥(hLevel (K := K) (Ω := Ω) (p := p) α)) 𝔭 hunrlvl hu
    unfold oTheta
    exact (Work.SSGRoute.ZDataMup.oddArtin_onePlace (K := K)
      (hLevel (K := K) (Ω := Ω) (p := p) α)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) ζ hζ α) v
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v β)).mpr hmem

end

end Work.SSGRoute.ZDataMup.OddForm
