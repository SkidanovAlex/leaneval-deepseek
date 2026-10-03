import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Support

open Work.ORTorsion

variable {K : Type*} [Field K] {G : Type*} [Group G] {H : Subgroup G}

/-- The coefficient at `h` of the degree-`b` part of `x` is the coefficient of `x` at `h`
when `φ h` has degree `b`, and `0` otherwise. -/
theorem coeff_degPart (φ : H →* Multiplicative ℤ) (x : MonoidAlgebra K H) (b : ℤ) (h : H) :
    (degPart φ b x).coeff h = if φ h = Multiplicative.ofAdd b then x.coeff h else 0 := by
  classical
  rw [degPart, MonoidAlgebra.coeff_ofCoeff, Finsupp.finsetSum_apply]
  by_cases hh : h ∈ x.coeff.support
  · rw [Finset.sum_eq_single h]
    · by_cases hc : φ h = Multiplicative.ofAdd b <;> simp [hc]
    · intro h' _ h'ne
      by_cases hc : φ h' = Multiplicative.ofAdd b <;>
        simp [hc, Finsupp.single_eq_of_ne (Ne.symm h'ne)]
    · intro hnot; exact absurd hh hnot
  · rw [Finset.sum_eq_zero]
    · rw [Finsupp.notMem_support_iff.mp hh]
      by_cases hc : φ h = Multiplicative.ofAdd b <;> simp [hc]
    · intro h' h'mem
      have hne : h ≠ h' := fun he => hh (he ▸ h'mem)
      by_cases hc : φ h' = Multiplicative.ofAdd b <;> simp [hc, Finsupp.single_eq_of_ne hne]

/-- The degree condition `φ h = ofAdd b` can be read as `b = deg φ h`. -/
theorem degPart_eq_ofAdd (φ : H →* Multiplicative ℤ) (h : H) (b : ℤ) :
    (φ h = Multiplicative.ofAdd b) ↔ (b = deg φ h) := by
  constructor
  · intro hh; simpa [deg] using (congrArg Multiplicative.toAdd hh).symm
  · intro hb; rw [hb]; simp [deg]

/-- `coeff_degPart` with the degree condition written as `b = deg φ h`. -/
theorem coeff_degPart' (φ : H →* Multiplicative ℤ) (x : MonoidAlgebra K H) (b : ℤ) (h : H) :
    (degPart φ b x).coeff h = if b = deg φ h then x.coeff h else 0 := by
  rw [coeff_degPart]
  by_cases hc : φ h = Multiplicative.ofAdd b
  · rw [if_pos hc, if_pos ((degPart_eq_ofAdd φ h b).mp hc)]
  · rw [if_neg hc, if_neg (fun hb => hc ((degPart_eq_ofAdd φ h b).mpr hb))]

theorem degPart_sum {K : Type*} [Field K] {G : Type*} [Group G] {H : Subgroup G}
    (φ : H →* Multiplicative ℤ) (x : MonoidAlgebra K H) :
    ∃ S : Finset ℤ, x = ∑ b ∈ S, degPart φ b x := by
  classical
  refine ⟨x.coeff.support.image (deg φ), ?_⟩
  ext h
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_degPart']
  by_cases hh : h ∈ x.coeff.support
  · have hS : deg φ h ∈ x.coeff.support.image (deg φ) := Finset.mem_image.mpr ⟨h, hh, rfl⟩
    rw [Finset.sum_ite_eq' _ _ (fun _ => x.coeff h), if_pos hS]
  · rw [Finset.sum_ite_eq' _ _ (fun _ => x.coeff h), Finsupp.notMem_support_iff.mp hh]
    by_cases hS : deg φ h ∈ x.coeff.support.image (deg φ) <;> simp [hS]

end Work.ORTorsion.Support
