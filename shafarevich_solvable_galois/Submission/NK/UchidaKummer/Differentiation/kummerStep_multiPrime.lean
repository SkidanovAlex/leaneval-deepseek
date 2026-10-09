import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Differentiation.exists_kummerField_localDeg_eq_of_surjective
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer.Differentiation

set_option linter.style.haveILetI false

theorem kummerStep_multiPrime {B K' : Type*} [Field B] [NumberField B] [Field K'] [Algebra B K']
    [IsSepClosure B K'] (ℓ : ℕ) (hℓ : ℓ.Prime) {ζ : B} (hζ : IsPrimitiveRoot ζ ℓ)
    (R S T : Finset (NK.Chebotarev.PrimeIdeal B)) (hR : R.Nonempty)
    (hRT : ∀ 𝔮 ∈ R, 𝔮 ∈ T) (hST : ∀ 𝔮 ∈ S, 𝔮 ∈ T) (hRS : ∀ 𝔮 ∈ R, 𝔮 ∉ S)
    (hsurj : NK.UchidaKummer.IsKummerSurjective B ℓ T)
    (hnonpow : ∀ 𝔮 ∈ R, ∃ u : (𝔮.adicCompletion B)ˣ, ∀ b : (𝔮.adicCompletion B)ˣ, b ^ ℓ ≠ u)
    (hdich : NK.UchidaKummer.IsKummerLocalDichotomy B K' ℓ) :
    ∃ (E₁ : IntermediateField B K') (_ : FiniteDimensional B E₁) (_ : NumberField ↥E₁),
      (∀ 𝔮 ∈ R, ∀ P : NK.Chebotarev.PrimeIdeal ↥E₁, P.asIdeal.LiesOver 𝔮.asIdeal →
        NK.UchidaKummer.localDeg P 𝔮 = ℓ) ∧
      (∀ 𝔮 ∈ S, ∀ P : NK.Chebotarev.PrimeIdeal ↥E₁, P.asIdeal.LiesOver 𝔮.asIdeal →
        NK.UchidaKummer.localDeg P 𝔮 = 1) := by
  classical
  -- Choose, at every prime of `R`, a local unit which is not an `ℓ`-th power.
  have hchoice : ∀ 𝔮 : ↥R, ∃ u : (𝔮.1.adicCompletion B)ˣ,
      ∀ b : (𝔮.1.adicCompletion B)ˣ, b ^ ℓ ≠ u := fun 𝔮 => hnonpow 𝔮.1 𝔮.2
  choose u hu using hchoice
  -- The prescribed tuple of local `ℓ`-power classes: the class of `u 𝔮` at `𝔮 ∈ R`, trivial off `R`.
  let y : ∀ 𝔮 : T,
      (𝔮.1.adicCompletion B)ˣ ⧸ NK.UchidaKummer.ellPowSubgroup (𝔮.1.adicCompletion B) ℓ :=
    fun 𝔮 => if h : 𝔮.1 ∈ R then
      QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (𝔮.1.adicCompletion B) ℓ)
        (u ⟨𝔮.1, h⟩)
      else 1
  obtain ⟨b, hb⟩ := hsurj y
  -- The class of `b` at a prime of `R` is the class of `u`.
  have hbR : ∀ (𝔮 : NK.Chebotarev.PrimeIdeal B) (h𝔮 : 𝔮 ∈ R),
      NK.UchidaKummer.localPowClass B ℓ 𝔮 b =
        QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (𝔮.adicCompletion B) ℓ)
          (u ⟨𝔮, h𝔮⟩) := by
    intro 𝔮 h𝔮
    have h := hb ⟨𝔮, hRT 𝔮 h𝔮⟩
    simpa only [y, dif_pos h𝔮] using h
  -- The class of `b` at a prime of `S` is trivial.
  have hbS : ∀ (𝔮 : NK.Chebotarev.PrimeIdeal B) (h𝔮 : 𝔮 ∈ S),
      NK.UchidaKummer.localPowClass B ℓ 𝔮 b = 1 := by
    intro 𝔮 h𝔮
    have hne : ¬ (𝔮 ∈ R) := fun h => hRS 𝔮 h h𝔮
    have h := hb ⟨𝔮, hST 𝔮 h𝔮⟩
    simpa only [y, dif_neg hne] using h
  -- The chosen local units are not `ℓ`-th powers.
  have hu_notmem : ∀ (𝔮 : NK.Chebotarev.PrimeIdeal B) (h𝔮 : 𝔮 ∈ R),
      u ⟨𝔮, h𝔮⟩ ∉ NK.UchidaKummer.ellPowSubgroup (𝔮.adicCompletion B) ℓ := by
    intro 𝔮 h𝔮 hmem
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
    exact hu ⟨𝔮, h𝔮⟩ c hc
  -- `b` is not a local `ℓ`-th power at a prime of `R`.
  have hnotlocalpow : ∀ (𝔮 : NK.Chebotarev.PrimeIdeal B) (h𝔮 : 𝔮 ∈ R),
      ¬ ∃ c : (𝔮.adicCompletion B)ˣ,
        algebraMap B (𝔮.adicCompletion B) (b : B) = (c : 𝔮.adicCompletion B) ^ ℓ := by
    intro 𝔮 h𝔮 ⟨c, hc⟩
    have hmem : Units.map (algebraMap B (𝔮.adicCompletion B)).toMonoidHom b ∈
        NK.UchidaKummer.ellPowSubgroup (𝔮.adicCompletion B) ℓ :=
      ⟨c, (Units.ext (by simpa using hc)).symm⟩
    have h2 : QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (𝔮.adicCompletion B) ℓ)
        (u ⟨𝔮, h𝔮⟩) = 1 := by
      rw [← hbR 𝔮 h𝔮]
      rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    exact hu_notmem 𝔮 h𝔮
      ((QuotientGroup.eq_one_iff (N := NK.UchidaKummer.ellPowSubgroup (𝔮.adicCompletion B) ℓ)
        (u ⟨𝔮, h𝔮⟩)).mp (by rwa [QuotientGroup.mk'_apply] at h2))
  -- `b` is a local `ℓ`-th power at a prime of `S`.
  have hlocpowS : ∀ (𝔮 : NK.Chebotarev.PrimeIdeal B) (h𝔮 : 𝔮 ∈ S),
      ∃ c : (𝔮.adicCompletion B)ˣ,
        algebraMap B (𝔮.adicCompletion B) (b : B) = (c : 𝔮.adicCompletion B) ^ ℓ := by
    intro 𝔮 h𝔮
    have h1 : NK.UchidaKummer.localPowClass B ℓ 𝔮 b = 1 := hbS 𝔮 h𝔮
    have hmem : Units.map (algebraMap B (𝔮.adicCompletion B)).toMonoidHom b ∈
        NK.UchidaKummer.ellPowSubgroup (𝔮.adicCompletion B) ℓ := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
      simpa [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply] using h1
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
    exact ⟨c, by
      have h2 := congrArg (fun z : (𝔮.adicCompletion B)ˣ => (z : 𝔮.adicCompletion B)) hc
      simpa using h2.symm⟩
  -- `b` is not a global `ℓ`-th power.
  obtain ⟨𝔮₀, h𝔮₀⟩ := hR
  have hbglob : b ∉ NK.LocalAnabelian.powSubgroup ℓ B := by
    intro hmem2
    obtain ⟨e, he⟩ := MonoidHom.mem_range.mp hmem2
    have he' : e ^ ℓ = b := he
    have h2 : Units.map (algebraMap B (𝔮₀.adicCompletion B)).toMonoidHom b =
        (Units.map (algebraMap B (𝔮₀.adicCompletion B)).toMonoidHom e) ^ ℓ := by
      rw [← map_pow, he']
    refine hnotlocalpow 𝔮₀ h𝔮₀ ⟨Units.map (algebraMap B (𝔮₀.adicCompletion B)).toMonoidHom e, ?_⟩
    have h3 := congrArg (fun z : (𝔮₀.adicCompletion B)ˣ => (z : 𝔮₀.adicCompletion B)) h2
    simpa using h3
  -- The Kummer field of `b` is Galois of degree `ℓ` over `B`.
  set L : IntermediateField B K' := NK.LocalAnabelian.kummerField (K' := K') ℓ b with hL
  have hKL := NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := B) (K' := K')
    ℓ hℓ hζ b hbglob
  haveI hgal : IsGalois B ↥L := hKL.1
  have hfinrank : Module.finrank B ↥L = ℓ := hKL.2
  haveI hfin : FiniteDimensional B L :=
    FiniteDimensional.of_finrank_pos (by rw [hfinrank]; exact hℓ.pos)
  haveI hNF : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  refine ⟨L, hfin, hNF, ?_, ?_⟩
  · -- Local degree `ℓ` at the primes of `R`.
    intro 𝔮 h𝔮 P hP
    have hnotall : ¬ ∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver 𝔮.asIdeal →
        NK.UchidaKummer.localDeg P 𝔮 = 1 :=
      fun hall => hnotlocalpow 𝔮 h𝔮 ((hdich b L hfin hNF hL 𝔮).mp hall)
    exact localDeg_eq_of_finrank_eq_prime_of_not_forall_eq_one L ℓ hℓ hfinrank 𝔮 hnotall P hP
  · -- Local degree `1` at the primes of `S`.
    intro 𝔮 h𝔮 P hP
    exact ((hdich b L hfin hNF hL 𝔮).mpr (hlocpowS 𝔮 h𝔮)) P hP

end NK.UchidaKummer.Differentiation
