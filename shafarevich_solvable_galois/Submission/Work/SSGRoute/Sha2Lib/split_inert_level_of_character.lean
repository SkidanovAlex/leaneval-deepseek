import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.Sha2Lib.level_char_inert_at_place
import Submission.Work.SSGRoute.Sha2Lib.level_char_split_at_places
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open scoped Pointwise NumberField

set_option maxHeartbeats 4000000

theorem split_inert_level_of_character
    (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Ss : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (χ : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hadd : ∀ a b : Ω ≃ₐ[k] Ω, χ (a * b) = χ a + χ b)
    (hcont : ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧ ∀ x ∈ U, χ x = 0)
    (hsurj : ∃ x : Ω ≃ₐ[k] Ω, χ x ≠ 0)
    (hsplit : ∀ 𝔭 ∈ Ss, ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 →
      ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A → χ σ = 0)
    (Aq : ValuationSubring Ω) (hAq : SSGRoute.IsFinPlace k Aq)
    (hAqover : Aq.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k q)
    (hqin : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω Aq → χ σ = 0)
    (hqne : ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k Aq ∧ χ σ ≠ 0) :
    ∃ (E : IntermediateField k Ω), ∃ (_ : NumberField ↥E) (_ : FiniteDimensional k ↥E),
      IsGalois k ↥E ∧ Module.finrank k ↥E = p ∧
      (∀ 𝔭 ∈ Ss, ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
        𝔮.asIdeal.LiesOver 𝔭.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
        𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 1) ∧
      (∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
        𝔮.asIdeal.LiesOver q.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
        𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = p) := by
  classical
  -- The additive character has value `0` at the identity, hence is a group homomorphism into
  -- the multiplicative group `Multiplicative (ZMod p)`.
  have hχ1 : χ 1 = 0 := by
    have h1 : χ 1 = χ 1 + χ 1 := by simpa using hadd 1 1
    exact add_left_cancel (show χ 1 + χ 1 = χ 1 + 0 by rw [add_zero, ← h1])
  let ψ : (Ω ≃ₐ[k] Ω) →* Multiplicative (ZMod p) :=
    { toFun := fun σ => Multiplicative.ofAdd (χ σ)
      map_one' := by rw [hχ1]; rfl
      map_mul' := fun a b => by rw [hadd a b]; rfl }
  have hψ : ∀ σ : Ω ≃ₐ[k] Ω, (ψ σ).toAdd = χ σ := fun σ => rfl
  -- `ker ψ` is open (it contains the given open subgroup).
  obtain ⟨U, hUopen, hUz⟩ := hcont
  have hUker : U ≤ ψ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    exact Multiplicative.ext (by rw [toAdd_one, hψ u]; exact hUz u hu)
  have hkeropen : IsOpen ((ψ.ker : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isOpen_mono hUker hUopen
  have hkerclosed : IsClosed ((ψ.ker : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isClosed_of_isOpen _ hkeropen
  haveI hgalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  -- The level `M` cut out by `ker ψ`.
  let H : ClosedSubgroup (Ω ≃ₐ[k] Ω) := ⟨ψ.ker, hkerclosed⟩
  let M : IntermediateField k Ω := IntermediateField.fixedField ψ.ker
  have hMfix : M.fixingSubgroup = ψ.ker := by
    change (IntermediateField.fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))).fixingSubgroup =
      (H : Subgroup (Ω ≃ₐ[k] Ω))
    exact InfiniteGalois.fixingSubgroup_fixedField H
  haveI hMgal : IsGalois k ↥M := IsGalois.of_fixedField_normal_subgroup ψ.ker
  have hMfd : FiniteDimensional k ↥M :=
    (InfiniteGalois.isOpen_iff_finite M).mp (by rw [hMfix]; exact hkeropen)
  haveI : FiniteDimensional k ↥M := hMfd
  have hMnf : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField M
  -- `ψ` is surjective, because `χ` (hence `ψ`) is non-zero somewhere.
  have hψsurj : Function.Surjective ψ := by
    obtain ⟨x, hx⟩ := hsurj
    have hx1 : ψ x ≠ 1 := by
      intro h
      apply hx
      have h' := congrArg Multiplicative.toAdd h
      rw [toAdd_one, hψ x] at h'
      exact h'
    have hcardM : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]
    have htop : Subgroup.zpowers (ψ x) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      have hdvd : Nat.card ↥(Subgroup.zpowers (ψ x)) ∣ Nat.card (Multiplicative (ZMod p)) :=
        Subgroup.card_subgroup_dvd_card _
      rw [hcardM] at hdvd
      have hne_bot : Subgroup.zpowers (ψ x) ≠ ⊥ := by
        intro h
        have hmem : ψ x ∈ (⊥ : Subgroup (Multiplicative (ZMod p))) := by
          rw [← h]; exact Subgroup.mem_zpowers _
        exact hx1 (by simpa using hmem)
      have h1 : 1 < Nat.card ↥(Subgroup.zpowers (ψ x)) := by
        by_contra hcon
        push Not at hcon
        have hpos : 0 < Nat.card ↥(Subgroup.zpowers (ψ x)) := Nat.card_pos
        exact hne_bot (Subgroup.card_eq_one.mp (by omega))
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with hd | hd
      · omega
      · rw [hd, hcardM]
    intro y
    have hy : y ∈ Subgroup.zpowers (ψ x) := by rw [htop]; exact Subgroup.mem_top y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨x ^ n, by rw [map_zpow, hn]⟩
  -- `Gal(M/k) ≅ G_k ⧸ ker ψ ≅ Multiplicative (ZMod p)`, so `[M : k] = p`.
  let eGal : (↥M ≃ₐ[k] ↥M) ≃* Multiplicative (ZMod p) :=
    (InfiniteGalois.normalAutEquivQuotient H).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  have hcard : Nat.card (↥M ≃ₐ[k] ↥M) = p := by
    rw [Nat.card_congr eGal.toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_eq_fintype_card, ZMod.card]
  have hfinrank : Module.finrank k ↥M = p := by
    rw [← IsGalois.card_aut_eq_finrank k ↥M]
    exact hcard
  -- Translate the hypotheses on `χ` into hypotheses on `ψ`.
  have hinn : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω Aq → ψ σ = 1 := by
    intro σ hσ
    exact Multiplicative.ext (by rw [toAdd_one, hψ σ]; exact hqin σ hσ)
  have hne : ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k Aq ∧ ψ σ ≠ 1 := by
    obtain ⟨σ, hσ, hneσ⟩ := hqne
    refine ⟨σ, hσ, fun h => hneσ ?_⟩
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_one, hψ σ] at h'
    exact h'
  have hsplitψ : ∀ 𝔭 ∈ Ss, ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 →
      ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A → ψ σ = 1 := by
    intro 𝔭 h𝔭 A hAfin hAcomap σ hσ
    exact Multiplicative.ext (by rw [toAdd_one, hψ σ]; exact hsplit 𝔭 h𝔭 A hAfin hAcomap σ hσ)
  -- Assemble: the level `M` is the required `E`.
  have hS := level_char_split_at_places p k Ω M ψ hMfix Ss hsplitψ
  have hQ := level_char_inert_at_place p k Ω q Aq hAqover M ψ hMfix hinn hne
  exact ⟨M, hMnf, hMfd, hMgal, hfinrank, hS, hQ⟩

end Work.SSGRoute.Sha2Lib
