import Mathlib.RingTheory.Localization.AtPrime.Basic

set_option maxHeartbeats 800000

namespace Commons.RingTheory.Localization

open IsLocalization

/-- If `𝔭` is a maximal ideal and `Localization.AtPrime 𝔭` is a field, then the residue
ring `B ⧸ 𝔭` is isomorphic to `Localization.AtPrime 𝔭`. -/
theorem quotient_iso_atPrime {B : Type} [CommRing B] (𝔭 : Ideal B) [𝔭.IsPrime]
    (hmax : 𝔭.IsMaximal) (hfield : IsField (Localization.AtPrime 𝔭)) :
    Nonempty (B ⧸ 𝔭 ≃+* Localization.AtPrime 𝔭) := by
  -- Since the localization is local and a field, its maximal ideal is zero.
  have hmaxIdeal : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
  -- The image of `𝔭` in the localization is the maximal ideal, hence zero.
  have hmap : Ideal.map (algebraMap B (Localization.AtPrime 𝔭)) 𝔭 = ⊥ := by
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal, hmaxIdeal]
  -- Hence `𝔭` is contained in the kernel of the localization map.
  have hle : 𝔭 ≤ RingHom.ker (algebraMap B (Localization.AtPrime 𝔭)) := by
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.map_le_iff_le_comap.mp (le_of_eq hmap)
  -- Conversely the kernel is contained in `𝔭`, by primality of `𝔭`.
  have hle' : RingHom.ker (algebraMap B (Localization.AtPrime 𝔭)) ≤ 𝔭 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨m, hm⟩ :=
      (IsLocalization.map_eq_zero_iff 𝔭.primeCompl (Localization.AtPrime 𝔭) x).mp hx
    rcases (‹𝔭.IsPrime› : 𝔭.IsPrime).mem_or_mem
        (show (m : B) * x ∈ 𝔭 from by rw [hm]; exact 𝔭.zero_mem) with h | h
    · exact absurd h (Ideal.mem_primeCompl_iff.mp m.2)
    · exact h
  have hker : RingHom.ker (algebraMap B (Localization.AtPrime 𝔭)) = 𝔭 :=
    le_antisymm hle' hle
  have hqfield : IsField (B ⧸ 𝔭) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔭).mp hmax
  -- The localization map is surjective.
  have hsurj : Function.Surjective (algebraMap B (Localization.AtPrime 𝔭)) := by
    intro z
    obtain ⟨b, s, hs⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl z
    have hs0 : Ideal.Quotient.mk 𝔭 (s : B) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_primeCompl_iff.mp s.2
    obtain ⟨v, hv⟩ := hqfield.mul_inv_cancel hs0
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective v
    have hcl : (s : B) * c - 1 ∈ 𝔭 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hc, hv, sub_self]
    have hclk : (s : B) * c - 1 ∈ RingHom.ker (algebraMap B (Localization.AtPrime 𝔭)) := by
      rw [hker]; exact hcl
    have hphi1 : algebraMap B (Localization.AtPrime 𝔭) ((s : B) * c) = 1 := by
      have h := hclk
      rw [RingHom.mem_ker] at h
      rw [map_sub, map_one, sub_eq_zero] at h
      exact h
    have hphi' : algebraMap B (Localization.AtPrime 𝔭) c *
        algebraMap B (Localization.AtPrime 𝔭) (s : B) = 1 := by
      rw [← map_mul, mul_comm]; exact hphi1
    refine ⟨b * c, ?_⟩
    rw [← hs, eq_comm, IsLocalization.mk'_eq_iff_eq_mul, map_mul, mul_assoc, hphi', mul_one]
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)⟩

end Commons.RingTheory.Localization