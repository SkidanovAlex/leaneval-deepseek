import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial IsLocalRing
open scoped Polynomial

noncomputable section

namespace Commons.RingTheory.Henselian

/-- Hensel's lemma (simple-root lifting) specialized to the Kummer polynomial
`X^p - C u`: in a Henselian local ring `R`, if `u` is a unit, `(p : R)` is a
unit, and `β` in the residue field satisfies `β^p = residue u`, then there is
`b ∈ R` with `b^p = u` and `residue b = β`. -/
theorem kummer_root_lift {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianLocalRing R] (p : ℕ) {u : R} (hu : IsUnit u) (hp : IsUnit (p : R)) :
    ∀ β : IsLocalRing.ResidueField R,
      β ^ p = IsLocalRing.residue R u →
      ∃ b : R, b ^ p = u ∧ IsLocalRing.residue R b = β := by
  intro β hβ
  rcases IsLocalRing.residue_surjective β with ⟨a₀, ha₀⟩
  let f : R[X] := X ^ p - C u
  have hp0 : p ≠ 0 := by
    intro hp0
    exact IsUnit.ne_zero hp (by rw [hp0]; simp)
  have hfmonic : f.Monic := by
    dsimp [f]
    exact monic_X_pow_sub_C u hp0
  have h₁ : f.eval a₀ ∈ maximalIdeal R := by
    have hres : IsLocalRing.residue R (f.eval a₀) = 0 := by
      have hf : f.eval a₀ = a₀ ^ p - u := by
        simp [f]
      have hr : IsLocalRing.residue R (a₀ ^ p - u) = β ^ p - IsLocalRing.residue R u := by
        rw [← ha₀]
        simp [map_sub, map_pow]
      rw [hf, hr, hβ]
      simp
    exact (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal R) (a := f.eval a₀)).mp hres
  have h₂ : IsUnit (f.derivative.eval a₀) := by
    have hder : f.derivative.eval a₀ = (p : R) * a₀ ^ (p - 1) := by
      simp [f, derivative_X_pow]
    have hres2 : IsLocalRing.residue R (f.derivative.eval a₀) ≠ 0 := by
      have hβ0 : β ≠ 0 := by
        intro hβ0
        have hu' : IsLocalRing.residue R u ≠ 0 := by
          rcases hu with ⟨v, rfl⟩
          exact (Units.map (IsLocalRing.residue R).toMonoidHom v).ne_zero
        apply hu'
        rw [← hβ, hβ0]
        exact zero_pow hp0
      have hpbar : IsLocalRing.residue R (p : R) ≠ 0 := by
        exact (IsLocalRing.residue_ne_zero_iff_isUnit (R := R) (x := (p : R))).mpr hp
      have hres_p : IsLocalRing.residue R ((p : R) * a₀ ^ (p - 1)) =
          IsLocalRing.residue R (p : R) * β ^ (p - 1) := by
        rw [← ha₀]
        simp [map_mul, map_pow]
      rw [hder, hres_p]
      exact mul_ne_zero hpbar (pow_ne_zero (p - 1) hβ0)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (R := R) (x := f.derivative.eval a₀)).mp hres2
  rcases HenselianLocalRing.is_henselian f hfmonic a₀ h₁ h₂ with ⟨b, hb_root, hb_mod⟩
  refine ⟨b, ?_, ?_⟩
  · have hb : f.eval b = 0 := hb_root
    have hf : f.eval b = b ^ p - u := by simp [f]
    exact sub_eq_zero.mp (by simpa [f] using hb)
  · have hb' : IsLocalRing.residue R b = IsLocalRing.residue R a₀ := by
      have hm : b - a₀ ∈ maximalIdeal R := hb_mod
      have hz : IsLocalRing.residue R (b - a₀) = 0 := by
        exact (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal R) (a := b - a₀)).mpr hm
      rw [← sub_eq_zero]
      simpa [map_sub] using hz
    exact hb'.trans ha₀

end Commons.RingTheory.Henselian