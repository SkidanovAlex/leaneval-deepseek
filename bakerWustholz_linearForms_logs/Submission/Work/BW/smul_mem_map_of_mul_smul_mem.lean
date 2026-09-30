import Mathlib
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem smul_mem_map_of_mul_smul_mem {R : Type*} [CommRing R] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (hpq : p ≤ q) (I : Ideal R)
    (hsatI : ((I.map (algebraMap R (Localization.AtPrime p))).comap
      (algebraMap R (Localization.AtPrime p))) = I)
    (P : R) (hPp : P ∉ p) {y : Localization.AtPrime q}
    (hy : algebraMap R (Localization.AtPrime q) P * y ∈
      I.map (algebraMap R (Localization.AtPrime q))) :
    y ∈ I.map (algebraMap R (Localization.AtPrime q)) := by
  obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.surj q.primeCompl y
  have h1 : algebraMap R (Localization.AtPrime q) (b * P) ∈
      I.map (algebraMap R (Localization.AtPrime q)) := by
    have hmem := Ideal.mul_mem_right (algebraMap R (Localization.AtPrime q) (t : R))
      (I.map (algebraMap R (Localization.AtPrime q))) hy
    rw [map_mul]
    rw [mul_assoc, hbt] at hmem
    rwa [mul_comm] at hmem
  obtain ⟨m, hmq, hmI⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl
      (Localization.AtPrime q) I (b * P)).mp h1
  have hmq' : m ∉ q := by rwa [Ideal.mem_primeCompl_iff] at hmq
  have hmp' : m ∉ p := fun h => hmq' (hpq h)
  have hmPp : m * P ∈ p.primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    intro h
    rcases (inferInstance : p.IsPrime).mem_or_mem h with h' | h'
    · exact hmp' h'
    · exact hPp h'
  have hunit : IsUnit (algebraMap R (Localization.AtPrime p) (m * P)) :=
    IsLocalization.map_units (Localization.AtPrime p) ⟨m * P, hmPp⟩
  have hbmpI : b * (m * P) ∈ I := by
    have h : b * (m * P) = m * (b * P) := by ring
    rw [h]; exact hmI
  have hbmp : algebraMap R (Localization.AtPrime p) b *
      algebraMap R (Localization.AtPrime p) (m * P) ∈
      I.map (algebraMap R (Localization.AtPrime p)) := by
    rw [← map_mul]
    exact Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) hbmpI
  have hgb : algebraMap R (Localization.AtPrime p) b ∈
      I.map (algebraMap R (Localization.AtPrime p)) := by
    obtain ⟨u, hu⟩ := hunit
    have h : algebraMap R (Localization.AtPrime p) b =
        (algebraMap R (Localization.AtPrime p) b *
          algebraMap R (Localization.AtPrime p) (m * P)) *
          ↑(u⁻¹ : (Localization.AtPrime p)ˣ) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [h]
    exact Ideal.mul_mem_right _ _ hbmp
  have hbI : b ∈ I := by
    rw [← hsatI]
    rw [Ideal.mem_comap]
    exact hgb
  exact (IsLocalization.mem_map_algebraMap_iff q.primeCompl (Localization.AtPrime q)).mpr
    ⟨(⟨b, hbI⟩, t), hbt⟩

end Work.BW
