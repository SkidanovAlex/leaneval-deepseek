/-
# The twins endgame (session 30)

The node `Work.SSGRoute.shafarevich_z_construction` needs the two `mu_p` cores.  The fleet has
"twins" of both, proved / being proved in the lanes' own files:

* `Work.SSGRoute.H9.sw_odd_kummer_core_proved`  (`H9/sw_odd_kummer_core_proved.lean`)  -- the odd-`p`
  Kummer core, with the same statement as `Work.SSGRoute.sw_odd_kummer_core`
  (`z_data_mup_odd_of_grunwald.lean`);
* `Work.SSGRoute.H9.shafarevich_z_data_two_kummerCore_proved`
  (`H9/shafarevich_z_data_two_kummerCore_proved.lean`) -- the `p = 2` Kummer core, with the same
  statement as `Work.SSGRoute.shafarevich_z_data_two_kummerCore`.

The lanes' own files still route through their own `sorry`-carrying copies, so *nothing is gained
automatically*.  This module converts the twins into the two cores **in the node's own lane**, so
that the node closes as soon as the twins are sorry-free -- no edit to any other lane's file.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.z_data_mup_odd_of_grunwald
import Submission.Work.SSGRoute.shafarevich_z_data_two
import Submission.Work.SSGRoute.H9.sw_odd_kummer_core_proved
import Submission.Work.SSGRoute.H9.shafarevich_z_data_two_kummerCore_proved
import Submission.Work.SSGRoute.ZConstruction.ZDataReduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The odd-`p` Kummer core, from the H9 twin.**  One call to the lane's own assembly
`Work.SSGRoute.z_data_mup_odd_of_grunwald_of_kummerCore` with the twin as its Kummer-core input. -/
theorem zDataOdd_of_H9 (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [Fintype (K ≃ₐ[k] K)] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)  := by
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  exact
    Work.SSGRoute.z_data_mup_odd_of_grunwald_of_kummerCore p hp k Ω K N hKN ζ hζ hζK S hSfin
      hSdisj hSram y hy hyc hyS hyram hyT hy0 hyinf
      (Work.SSGRoute.H9.sw_odd_kummer_core_proved p hp k Ω K N hKN ζ hζ hζK S hSfin hSdisj
        hSram y hy hyc hyS hyram hyT hy0 hyinf)


/-! ## The two `mu_p` cores, from the twins -/

/-- **The odd-`p` one-dimensional `z`-data, from the H9 twin.**  Verbatim the body of
`Work.SSGRoute.z_data_mup_core` (`z_data_mup_core.lean`), with its single arithmetic call
`Work.SSGRoute.sw_z_exists_odd_sketch` replaced by `zDataOdd_of_H9` above. -/
theorem z_data_mup_core_H9 (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
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
    obtain ⟨zp, hzadd, hzlc, hzagree, hzinv, hzspl, hzsharp⟩ :=
      zDataOdd_of_H9 p hp k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram
        (fun σ => φ (y σ)) hyp hypc hypS hypram hypT hyp0 hypinf
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


/-- **The `p = 2` one-dimensional `z`-data, from the H9 twin.**  Verbatim the body of
`Work.SSGRoute.shafarevich_z_data_two` (`shafarevich_z_data_two.lean`), with its single arithmetic
call `Work.SSGRoute.shafarevich_z_data_two_kummerCore` replaced by the H9 twin. -/
theorem shafarevich_z_data_two_H9 (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (k Ω : Type) [Field k]
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
  subst hp2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  exact shafarevich_z_data_two_of_kummerCore k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram
    y hy hyc hyS hyT hy0 hyinf
    (fun y' hy' hyc' hyS' hyT' hy0' hyinf' =>
      Work.SSGRoute.H9.shafarevich_z_data_two_kummerCore_proved k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram
        y' hy' hyc' hyS' hyT' hy0' hyinf')



/-! ## The one-dimensional gate `MupGate` -/

open scoped Pointwise

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
  [Algebra k Ω] [IsAlgClosure k Ω]

/-- **`Work.SSGRoute.MupGate`, from the twins.**  Verbatim `Work.SSGRoute.mupGate_of_cores`
(`ZConstruction/MupGate.lean`) with the two cores replaced by the twins' versions above. -/
theorem mupGate_of_cores_H9 {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] : MupGate (p := p) K := by
  intro Λ _instΛf _instΛg S hAmb E _instE _instM _instF h1 y hy
  obtain ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩ := hAmb
  -- the trivial action of `Gal(K|k)` makes the arithmetic cores applicable
  letI : DistribMulAction (K ≃ₐ[k] K) E :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  haveI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) E := ⟨fun _ _ _ => rfl⟩
  rcases eq_or_ne p 2 with hp2 | hp2
  · haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
    obtain ⟨z, hz⟩ := shafarevich_z_data_two_H9 p hp2 k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram y
      hy.add hy.locconst hy.hyS hy.hyT hy.hy0 hy.hyinf
    exact ⟨z, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2⟩
  · obtain ⟨z, hz⟩ := z_data_mup_core_H9 p hp2 k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram y
      hy.add hy.locconst hy.hyS hy.hyT hy.hy0 hy.hyinf
    exact ⟨z, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2⟩


end Work.SSGRoute.ZConstruction
