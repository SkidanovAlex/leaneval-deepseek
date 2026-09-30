import Mathlib
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **Annihilator of a class modulo a `p`-saturated ideal is `p`.**

Let `p ≤ q` be primes, `I` a `p`-saturated ideal, `x ∉ I`, and `b ∈ R_q`. If `b * x ∈ I·R_q` then
`b ∈ p·R_q`.

Route. By `IsLocalization.surj` write `b * algebraMap R R_q t = algebraMap R R_q β` with `t ∉ q`.
Multiplying the hypothesis by `algebraMap R R_q t` gives `algebraMap R R_q (β * x) ∈ I·R_q`, so
`IsLocalization.algebraMap_mem_map_algebraMap_iff` produces `m ∉ q` with `m * (β * x) ∈ I`. If
`β ∉ p` then `m * β ∉ p` (as `m ∉ q ⊇ p` and `p` is prime), so `m * β` is a unit of `R_p` and
`(m * β) * x ∈ I ⊆ I·R_p` forces `x ∈ I·R_p`, hence `x ∈ I` by saturation (`hsatI`), contradicting
`hxI`. So `β ∈ p`, and `b = algebraMap R R_q β * (algebraMap R R_q t)⁻¹ ∈ p·R_q` because
`algebraMap R R_q t` is a unit. -/
theorem mem_map_prime_of_mul_mem_map {R : Type*} [CommRing R] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (hpq : p ≤ q) (I : Ideal R)
    (hsatI : ((I.map (algebraMap R (Localization.AtPrime p))).comap
      (algebraMap R (Localization.AtPrime p))) = I)
    (x : R) (hxI : x ∉ I) {b : Localization.AtPrime q}
    (hb : b * algebraMap R (Localization.AtPrime q) x ∈
      I.map (algebraMap R (Localization.AtPrime q))) :
    b ∈ p.map (algebraMap R (Localization.AtPrime q)) := by
  obtain ⟨⟨β, t⟩, hbt⟩ := IsLocalization.surj q.primeCompl b
  have h2 : algebraMap R (Localization.AtPrime q) (β * x) ∈
      I.map (algebraMap R (Localization.AtPrime q)) := by
    have hmem := Ideal.mul_mem_left (I.map (algebraMap R (Localization.AtPrime q)))
      (algebraMap R (Localization.AtPrime q) (t : R)) hb
    have hkey : algebraMap R (Localization.AtPrime q) (t : R) *
        (b * algebraMap R (Localization.AtPrime q) x) =
        algebraMap R (Localization.AtPrime q) β *
          algebraMap R (Localization.AtPrime q) x := by
      rw [← mul_assoc, mul_comm (algebraMap R (Localization.AtPrime q) (t : R)) b, hbt]
    rw [hkey] at hmem
    simpa only [map_mul] using hmem
  obtain ⟨m, hmq, hmI⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl
      (Localization.AtPrime q) I (β * x)).mp h2
  have hmq' : m ∉ q := by rwa [Ideal.mem_primeCompl_iff] at hmq
  by_cases hβp : β ∈ p
  · refine (IsLocalization.mem_map_algebraMap_iff q.primeCompl
      (Localization.AtPrime q)).mpr ⟨(⟨β, hβp⟩, t), ?_⟩
    simpa using hbt
  · exfalso
    have hmp' : m ∉ p := fun h => hmq' (hpq h)
    have hmβp : m * β ∈ p.primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      intro h
      rcases (inferInstance : p.IsPrime).mem_or_mem h with h' | h'
      · exact hmp' h'
      · exact hβp h'
    have hunit : IsUnit (algebraMap R (Localization.AtPrime p) (m * β)) :=
      IsLocalization.map_units (Localization.AtPrime p) ⟨m * β, hmβp⟩
    have hIm : (m * β) * x ∈ I := (mul_assoc m β x).symm ▸ hmI
    have hxmem : algebraMap R (Localization.AtPrime p) x ∈
        I.map (algebraMap R (Localization.AtPrime p)) := by
      have hmem := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) hIm
      rw [map_mul] at hmem
      obtain ⟨u, hu⟩ := hunit
      have heq : algebraMap R (Localization.AtPrime p) x =
          ↑(u⁻¹) * (algebraMap R (Localization.AtPrime p) (m * β) *
            algebraMap R (Localization.AtPrime p) x) := by
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
      rw [heq]
      exact Ideal.mul_mem_left _ _ hmem
    exact hxI (by rw [← hsatI, Ideal.mem_comap]; exact hxmem)

end Work.BW
