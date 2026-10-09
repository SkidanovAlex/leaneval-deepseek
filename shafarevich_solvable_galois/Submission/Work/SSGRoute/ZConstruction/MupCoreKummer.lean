import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.Work.SSGRoute.ZConstruction.ZDataGeneral
import Submission.Work.SSGRoute.z_data_mup_odd_of_grunwald
import Submission.Work.SSGRoute.ZDataMup.sw_odd_kummer_core
import Submission.Work.SSGRoute.H9.sw_odd_kummer_core_proved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The odd `μ_p` core from the `H9` lane's Kummer core (the live route)

`Work.SSGRoute.z_data_mup_core` (`z_data_mup_core.lean`, session of 2026-09-26) obtains the odd-`p`
one-dimensional `z`-data from the *sketch* `Work.SSGRoute.sw_z_exists_odd_sketch`
(`z_data_mup_arith.lean`), whose four sorries (the Tate--Poitou degree-one realisation, the
Chebotarev--Frobenius step, the local Tate system product formula, and the §4 construction itself)
have not been touched since 2026-09-26: that route is stale.

This file is a *copy* of `Work.SSGRoute.z_data_mup_core`'s proof, character for character except for
that single arithmetic input, which is replaced by the **live** route of the `H9`/`ZDataMup` lanes:

* `Work.SSGRoute.H9.sw_odd_kummer_core_proved` (whose statement is verbatim that of
  `Work.SSGRoute.ZDataMup.sw_odd_kummer_core`) --- the odd Kummer core of Schmidt--Wingberg §4 (the
  Kummer element `b ∈ Kˣ` realising a prescribed datum `y : G_K → ZMod p`), which is the statement
  the `H9` lane's chain (`Work.SSGRoute.H9.sw_odd_kummer_core_proved`,
  `H9.swHistChi_chain*_proved`, `ZDataMup.swChainValue`) is filling; and
* `Work.SSGRoute.z_data_mup_odd_of_grunwald_of_kummerCore` --- the *proved*, axiom-clean bridge from
  that Kummer core to the class form `z = χ_b` (the shape the transport below consumes).

Consequently `Work.SSGRoute.isMupZData_of_kummerCore` (below) is the one-dimensional gate
`Work.SSGRoute.IsMupZData p k Ω K` for odd `p` in terms of the `H9` lane's obligation only --- so that
the node `Work.SSGRoute.shafarevich_z_construction` is unblocked as soon as that lane's chain lands,
with no dependence on the stale `z_data_mup_arith.lean` sketches.  (`ZConstruction/ZDataFinal.lean`
uses this gate in the odd-`p` branch of `Work.SSGRoute.z_data_general_of_ramified`.)
-/

set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.SSGRoute

theorem z_data_mup_core_of_kummerCore (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (h1 : Module.finrank (ZMod p) E ≤ 1)
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
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
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
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            z δ ∈ AddSubgroup.zmultiples (z g)) ∧
        (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)) := by
  classical
  have hres : ∀ g ∈ K.fixingSubgroup, SSGRoute.res k K g = 1 := by
    intro g hg
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hg
  by_cases hram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0
  · -- ## The hard case: `y` is ramified somewhere outside `cs(S)`.
    -- This is the case in which the Schmidt–Wingberg class `z` has to be constructed.
    obtain ⟨B₀, hB₀fin, hB₀conj, σ₀, hσ₀K, hI₀, hσ₀ne⟩ := hram
    haveI : Nontrivial E := ⟨⟨0, y σ₀, fun h => hσ₀ne h.symm⟩⟩
    have hfr : Module.finrank (ZMod p) E = 1 := by
      have hpos : 0 < Module.finrank (ZMod p) E := Module.finrank_pos_iff.mpr ‹Nontrivial E›
      omega
    let φ : E ≃ₗ[ZMod p] ZMod p :=
      LinearEquiv.ofFinrankEq E (ZMod p) (by rw [hfr, Module.finrank_self])
    have hyp : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
        (fun σ => φ (y σ)) (g * h) = (fun σ => φ (y σ)) g + (fun σ => φ (y σ)) h := by
      intro g hg h hh
      show φ (y (g * h)) = φ (y g) + φ (y h)
      rw [hy g hg h hh, map_add]
    have hypc : SSGRoute.IsLocConstOn K.fixingSubgroup (fun σ => φ (y σ)) := by
      obtain ⟨U, hUopen, hU⟩ := hyc
      exact ⟨U, hUopen, fun g hg u hu huH => by
        show φ (y (g * u)) = φ (y g)
        rw [hU g hg u hu huH]⟩
    have hypS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → (fun σ => φ (y σ)) σ = 0 := by
      intro B hB hconj hsp σ hσK hσI
      show φ (y σ) = 0
      rw [hyS B hB hconj hsp σ hσK hσI, map_zero]
    have hypram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ (fun σ => φ (y σ)) σ ≠ 0 := by
      refine ⟨B₀, hB₀fin, hB₀conj, σ₀, hσ₀K, hI₀, ?_⟩
      show φ (y σ₀) ≠ 0
      intro h0
      exact hσ₀ne (φ.injective (by rw [h0, map_zero]))
    have hypT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → (fun σ => φ (y σ)) σ = 0 := by
      intro B hB hconj σ hσK hσI
      show φ (y σ) = 0
      rw [hyT B hB hconj σ hσK hσI, map_zero]
    have hyp0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → (fun σ => φ (y σ)) σ = 0 := by
      intro B hB hconj hsp σ hσK hσd
      show φ (y σ) = 0
      rw [hy0 B hB hconj hsp σ hσK hσd, map_zero]
    have hypinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → (fun σ => φ (y σ)) c = 0 := by
      intro c hc hc2
      show φ (y c) = 0
      rw [hyinf c hc hc2, map_zero]
    -- THE ONLY CHANGE W.R.T. `Work.SSGRoute.z_data_mup_core`: the arithmetic input.  Instead of the
    -- (stale, still entirely sketched) `Work.SSGRoute.sw_z_exists_odd_sketch` of
    -- `z_data_mup_arith.lean`, the datum `φ ∘ y` (with values in `ZMod p`) is fed to the *live*
    -- route: the Kummer core `Work.SSGRoute.H9.sw_odd_kummer_core_proved` of the `H9` lane, i.e. the
    -- Kummer element `b ∈ Kˣ` realising it, converted into the class form `z = χ_b` by the (proved,
    -- axiom-clean) bridge `Work.SSGRoute.z_data_mup_odd_of_grunwald_of_kummerCore`.
    haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
    obtain ⟨zp, hzadd, hzlc, hzagree, hzinv, hzspl, hzsharp⟩ :=
      z_data_mup_odd_of_grunwald_of_kummerCore p hp k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram
        (fun σ => φ (y σ)) hyp hypc hypS hypram hypT hyp0 hypinf
        (H9.sw_odd_kummer_core_proved p hp k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram
          (fun σ => φ (y σ)) hyp hypc hypS hypram hypT hyp0 hypinf)
    refine ⟨fun σ => φ.symm (zp σ), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg h hh
      show φ.symm (zp (g * h)) = φ.symm (zp g) + (SSGRoute.res k K g) • φ.symm (zp h)
      rw [hzadd g hg h hh, map_add, hres g hg, one_smul]
    · obtain ⟨U, hUopen, hU⟩ := hzlc
      exact ⟨U, hUopen, fun g hg u hu huH => by
        show φ.symm (zp (g * u)) = φ.symm (zp g)
        rw [hU g hg u hu huH]⟩
    · intro B hB hconj σ hσK hσd
      show φ.symm (zp σ) = y σ
      rw [hzagree B hB hconj σ hσK hσd]
      exact φ.symm_apply_apply (y σ)
    · intro c hc hc2
      show φ.symm (zp c) = 0
      rw [hzinv c hc hc2, map_zero]
    · intro B hB hconj hsp σ hσK hσI
      show φ.symm (zp σ) = 0
      rw [hzspl B hB hconj hsp σ hσK hσI, map_zero]
    · intro B hB hconj hsplit htrig
      have hztrig : ∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ zp σ ≠ 0 := by
        obtain ⟨σ, hI, hσK, hne⟩ := htrig
        exact ⟨σ, hI, hσK, fun h0 => hne (by
          show φ.symm (zp σ) = 0
          rw [h0, map_zero])⟩
      refine ⟨?_, fun Q hQ hne τ hτ => by
        show φ.symm (zp τ) = 0
        rw [hzsharp B hB hconj hsplit hztrig Q hQ hne τ hτ, map_zero]⟩
      · by_cases hex : ∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, φ.symm (zp g) ≠ 0
        · obtain ⟨g, hg, hgne⟩ := hex
          exact ⟨g, hg, fun δ hδ => zmultiples_eq_top_of_finrank_le_one h1 hgne (φ.symm (zp δ))⟩
        · push_neg at hex
          exact ⟨1, (SSGRoute.decomp k B ⊓ K.fixingSubgroup).one_mem, fun δ hδ => by
            show φ.symm (zp δ) ∈ AddSubgroup.zmultiples (φ.symm (zp 1))
            rw [hex δ hδ, hex 1 (Subgroup.one_mem _)]
            exact AddSubgroup.zero_mem _⟩
  · -- ## The easy case: `y` is unramified at every finite place outside `cs(S)`.
    -- Then `z := y` itself satisfies all the conditions.
    have hyun : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0 := by
      intro B hB hconj σ hσK hσI
      by_contra hne
      exact hram ⟨B, hB, hconj, σ, hσK, hσI, hne⟩
    refine ⟨y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg h hh
      rw [hy g hg h hh, hres g hg, one_smul]
    · exact hyc
    · intro B hB hconj σ hσK hσd
      rfl
    · exact hyinf
    · intro B hB hconj hsp σ hσK hσI
      exact hyun B hB hconj σ hσK hσI
    · intro B hB hconj hsplit htrig
      exact absurd htrig (by
        rintro ⟨σ, hI, hσK, hne⟩
        exact hne (hyun B hB hconj σ hσK hI))

/-- **The one-dimensional gate `Work.SSGRoute.IsMupZData` for odd `p`, from the `H9` lane's Kummer
core.**  Same conversion of "additive on `G_K`" into the `1`-cocycle identity as
`Work.SSGRoute.isMupZData_of_core_odd` (`ZConstruction/ZDataGeneral.lean`). -/
theorem isMupZData_of_kummerCore {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (hp : p ≠ 2) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K) : IsMupZData p k Ω K := by
  intro E _instE _instMod _instAct _instSMC _instFin h1 Λ _instΛf _instΛg hKΛ S hSfin hSdisj hSram
    y hy hyc hyS hyT hy0 hyinf
  obtain ⟨z, hcoc, hloc, h3, h4, h5, h6⟩ :=
    z_data_mup_core_of_kummerCore p hp k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram y hy hyc
      hyS hyT hy0 hyinf
  exact ⟨z, (isCocycleOn_fixingSubgroup_iff_additive z).mp hcoc, hloc, h3, h4, h5, h6⟩

end Work.SSGRoute
