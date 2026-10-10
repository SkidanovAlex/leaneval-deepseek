import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.Sha2Lib.aux_unramified_inert_level_of_character
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A level of prime degree which is inert at a prescribed place

Let `k` be a number field with algebraic closure `Ω`, `M ⊆ Ω` a finite Galois level with
`[M : k] = p` (realised as the fixed field of the kernel of a character
`ψ : G_k → Multiplicative (ZMod p)`, `p` prime).  If `ψ` vanishes on the inertia subgroup
`I_A` of a finite place `A` of `Ω` but is non-trivial on the decomposition group `D_A`, then
every prime `w` of `𝓞 M` above the prime `Q` of `𝓞 k` below `A` is unramified (`e = 1`) and
inert (`f = p`) over `k`.

Since `ker ψ = M.fixingSubgroup`, the quotient `G_k ⧸ ker ψ` has `p` elements, so
`Gal(M/k)` has cardinality `p` (`IsGalois.card_aut_eq_finrank` plus
`IntermediateField.finrank_eq_fixingSubgroup_index`).  The inertia of the level prime `P` below
`A` is the image of `I_A`, hence trivial by hypothesis; its decomposition group is the image of
`D_A`, hence everything since it contains the non-trivial element `ψ δ ≠ 1` and `Gal(M/k)` has
prime order.  Then `Work.SSGRoute.levelInertia_index_eq_inertiaDeg` gives `f = p`, and the
order of the inertia subgroup is the ramification index, giving `e = 1`.  Finally the Galois
action is transitive on the primes above `Q`, so the same holds for every such prime.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open scoped Pointwise NumberField

namespace Work.SSGRoute.Sha2Lib

open _root_.SSGRoute

theorem level_char_inert_at_place
    (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    (hA : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M] [NumberField ↥M]
    (ψ : (Ω ≃ₐ[k] Ω) →* Multiplicative (ZMod p))
    (hfix : M.fixingSubgroup = ψ.ker)
    (hinn : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω A → ψ σ = 1)
    (hne : ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A ∧ ψ σ ≠ 1) :
    ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
      w.asIdeal.LiesOver Q.asIdeal →
        w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
        w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = p := by
  classical
  haveI hGalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  -- `A` is a finite place of `Ω`
  have hAf : SSGRoute.IsFinPlace k A := by
    change A.comap (algebraMap k Ω) ≠ ⊤
    rw [hA]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top Q
  have hcardp : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
      Nat.card_eq_fintype_card, ZMod.card]
  -- ## `ψ` is surjective
  have hsurj : Function.Surjective ψ := by
    obtain ⟨δ, _hδD, hδψ⟩ := hne
    have hne_bot : Subgroup.zpowers (ψ δ) ≠ ⊥ := by
      intro h
      have : ψ δ ∈ (⊥ : Subgroup (Multiplicative (ZMod p))) := by
        rw [← h]; exact Subgroup.mem_zpowers _
      exact hδψ (by simpa using this)
    have htop : Subgroup.zpowers (ψ δ) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      have hdvd : Nat.card (Subgroup.zpowers (ψ δ)) ∣ Nat.card (Multiplicative (ZMod p)) :=
        Subgroup.card_subgroup_dvd_card _
      rw [hcardp] at hdvd
      have h1 : 1 < Nat.card (Subgroup.zpowers (ψ δ)) := by
        by_contra hcon
        push Not at hcon
        have hpos : 0 < Nat.card (Subgroup.zpowers (ψ δ)) := Nat.card_pos
        exact hne_bot (Subgroup.card_eq_one.mp (by omega))
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
      · omega
      · rw [h, hcardp]
    intro y
    have hy : y ∈ Subgroup.zpowers (ψ δ) := by rw [htop]; exact Subgroup.mem_top y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨δ ^ n, by rw [map_zpow, hn]⟩
  -- ## `Gal(M/k)` has `p` elements
  have hcardM : Nat.card (↥M ≃ₐ[k] ↥M) = p := by
    calc Nat.card (↥M ≃ₐ[k] ↥M)
        = Module.finrank k ↥M := IsGalois.card_aut_eq_finrank k ↥M
      _ = M.fixingSubgroup.index := IntermediateField.finrank_eq_fixingSubgroup_index Ω M
      _ = ψ.ker.index := by rw [hfix]
      _ = Nat.card ↥(⊤ : Subgroup (Multiplicative (ZMod p))) := by
            rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj]
      _ = p := by
            rw [Nat.card_congr (Subgroup.topEquiv).toEquiv, hcardp]
  -- ## the level prime below `A`
  let P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M) :=
    Work.SSGRoute.levelPrime k Ω A hAf M
  have hPliesQ : P.asIdeal.LiesOver Q.asIdeal := by
    have h1 : P.asIdeal.LiesOver (Submission.NeukirchUchida.primeOf A hAf).asIdeal :=
      NK.ResidueFrob.primeOfLevel_liesOver (K := k) (K' := Ω) ⟨A, hAf⟩ M
    have h2 : Submission.NeukirchUchida.primeOf A hAf = Q :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
        (by rw [← Submission.NeukirchUchida.primeOf_spec A hAf, hA])
    rwa [h2] at h1
  haveI hPliesI : P.asIdeal.LiesOver Q.asIdeal := hPliesQ
  haveI hPprime : P.asIdeal.IsPrime := P.isPrime
  haveI hQprime : Q.asIdeal.IsPrime := Q.isPrime
  -- ## the inertia of the level is trivial
  have hIbot : Work.SSGRoute.levelInertiaAt k Ω A hAf M = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro τ hτ
    have hτ' : τ ∈ (Work.SSGRoute.inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom M) := by
      rw [inertiaSub_image_eq_levelInertia k Ω A hAf M]
      exact hτ
    obtain ⟨σ, hσ, hστ⟩ := Subgroup.mem_map.mp hτ'
    have hσker : σ ∈ M.fixingSubgroup := by
      rw [hfix]; exact MonoidHom.mem_ker.mpr (hinn σ hσ)
    rw [← hστ]
    exact MonoidHom.mem_ker.mp (by rw [IntermediateField.restrictNormalHom_ker]; exact hσker)
  -- ## the decomposition group of the level is everything
  have hDtop : Work.SSGRoute.levelDecompAt k Ω A hAf M = ⊤ := by
    obtain ⟨δ, hδD, hδψ⟩ := hne
    have hδ1 : AlgEquiv.restrictNormalHom M δ ≠ 1 := by
      intro h
      apply hδψ
      have hker : δ ∈ (AlgEquiv.restrictNormalHom M).ker := MonoidHom.mem_ker.mpr h
      rw [IntermediateField.restrictNormalHom_ker] at hker
      rw [hfix] at hker
      exact MonoidHom.mem_ker.mp hker
    have hmem : AlgEquiv.restrictNormalHom M δ ∈ Work.SSGRoute.levelDecompAt k Ω A hAf M := by
      show AlgEquiv.restrictNormalHom M δ ∈
        MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hAf M).asIdeal
      rw [← Work.SSGRoute.range_restrictNormalHom_eq_stabilizer A hAf M]
      exact ⟨⟨δ, hδD⟩, rfl⟩
    have hne_bot : Work.SSGRoute.levelDecompAt k Ω A hAf M ≠ ⊥ := by
      intro h
      have : AlgEquiv.restrictNormalHom M δ ∈ (⊥ : Subgroup (↥M ≃ₐ[k] ↥M)) := by
        rw [← h]; exact hmem
      exact hδ1 (by simpa using this)
    apply Subgroup.eq_top_of_card_eq
    have hdvd : Nat.card (Work.SSGRoute.levelDecompAt k Ω A hAf M) ∣
        Nat.card (↥M ≃ₐ[k] ↥M) := Subgroup.card_subgroup_dvd_card _
    rw [hcardM] at hdvd
    have h1 : 1 < Nat.card (Work.SSGRoute.levelDecompAt k Ω A hAf M) := by
      by_contra hcon
      push Not at hcon
      have hpos : 0 < Nat.card (Work.SSGRoute.levelDecompAt k Ω A hAf M) := Nat.card_pos
      exact hne_bot (Subgroup.card_eq_one.mp (by omega))
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
    · omega
    · rw [h, hcardM]
  -- ## `f = p` at the level prime
  have hfind : P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = p := by
    have hind : ((Work.SSGRoute.levelInertiaAt k Ω A hAf M).subgroupOf
        (Work.SSGRoute.levelDecompAt k Ω A hAf M)).index =
        P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
      Work.SSGRoute.levelInertia_index_eq_inertiaDeg k Ω A hAf M
    rw [← hind, hIbot, hDtop, Subgroup.bot_subgroupOf, Subgroup.index_bot,
      Nat.card_congr (Subgroup.topEquiv :
        (⊤ : Subgroup (↥M ≃ₐ[k] ↥M)) ≃* (↥M ≃ₐ[k] ↥M)).toEquiv, hcardM]
  -- ## `e = 1` at the level prime
  haveI hperf : PerfectField Q.asIdeal.ResidueField :=
    Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum Q
  have heind : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    have hcard_in : Nat.card (P.asIdeal.inertia (↥M ≃ₐ[k] ↥M)) =
        Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥M) :=
      Ideal.card_inertia_eq_ramificationIdxIn (G := ↥M ≃ₐ[k] ↥M) Q.asIdeal P.asIdeal
    have hrIn : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥M) =
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) :=
      Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal P.asIdeal (↥M ≃ₐ[k] ↥M)
    have hbot : P.asIdeal.inertia (↥M ≃ₐ[k] ↥M) = ⊥ := hIbot
    have h1 : Nat.card (P.asIdeal.inertia (↥M ≃ₐ[k] ↥M)) = 1 :=
      Subgroup.card_eq_one.mpr hbot
    rw [← hrIn, ← hcard_in, h1]
  -- ## every prime above `Q`
  intro w hw
  haveI hwI : w.asIdeal.LiesOver Q.asIdeal := hw
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup Q.asIdeal P.asIdeal w.asIdeal
    (↥M ≃ₐ[k] ↥M)
  have h1 : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) =
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) := by
    rw [← hσ, Ideal.ramificationIdx_smul]
  have h2 : w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) =
      P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    rw [← hσ, Ideal.inertiaDeg_smul]
  exact ⟨by rw [h1, heind], by rw [h2, hfind]⟩

end Work.SSGRoute.Sha2Lib
