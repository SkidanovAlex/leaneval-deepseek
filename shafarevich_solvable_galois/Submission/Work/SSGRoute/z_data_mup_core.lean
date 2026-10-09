import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.Work.SSGRoute.z_data_mup_arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `z`-data of Schmidt–Wingberg §4 in the one-dimensional (`μ_p`) case

The statement `Work.SSGRoute.z_data_mup_core` is Schmidt–Wingberg §4, first half, in the case of a
one-dimensional coefficient module (`dim_{𝔽_p} E ≤ 1`, i.e. `A = μ_p`).

This file assembles it from

* the arithmetic core `Work.SSGRoute.sw_z_exists_odd_sketch` (module
  `Submission.Work.SSGRoute.z_data_mup_arith`), which is the construction of the class `z` in SW §4
  over the odd prime `p` with coefficients in the trivial `𝔽_p`-module `ZMod p`, and
* elementary algebra: a finite `𝔽_p`-module of `𝔽_p`-dimension `≤ 1` is trivial or isomorphic to
  `ZMod p` (so the arithmetic output can be transported along `E ≃ₗ[𝔽_p] ZMod p`), the coincidence
  of "additive on `G_K`" with the `1`-cocycle identity for the trivial action of `G_K = K.fixingSubgroup`
  on `E`, and the cyclicity of every subgroup of `E` (from `dim E ≤ 1`).

Concretely, if `E` is trivial then `z := 0` works; otherwise `E ≅ ZMod p`, the transport of the
arithmetic class gives the first five conjuncts, the cyclicity half of the sixth conjunct is
`Work.SSGRoute.zmultiples_eq_top_of_finrank_le_one`, and the sharpened vanishing half of the sixth
conjunct is exactly Schmidt–Wingberg's `z_{σP} = 0` for `σ ≠ 1` supplied by the arithmetic.
-/

set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.SSGRoute

/-- The pointwise action on valuation subrings, unfolded in terms of membership: translating the
place `B` by `τ` gives `Q` exactly when `Q` is the set of `x` with `τ⁻¹ x ∈ B`. -/
lemma conjPlace_eq_iff_mem (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (τ : Ω ≃ₐ[k] Ω) (B Q : ValuationSubring Ω) :
    (τ • B = Q) ↔ ∀ x : Ω, x ∈ Q ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ B := by
  rw [SetLike.ext_iff]
  constructor
  · intro h x
    rw [← h x, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  · intro h x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, h x]

theorem z_data_mup_core (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
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
      sw_z_exists_odd_sketch p hp k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram
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
