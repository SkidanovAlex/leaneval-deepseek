import Mathlib
import Submission.Commons.FieldTheory.Polynomial.discr_ne_zero_of_separable

open Polynomial

noncomputable section

namespace Commons.FieldTheory.Polynomial

/-- Multiplying a monic polynomial by a nonzero constant scales the discriminant by the
`(2·natDegree - 2)`-th power of that constant. -/
lemma discr_C_mul_of_monic {F : Type*} [Field F] (g : F[X]) (a : F) (hg : g.Monic)
    (ha : a ≠ 0) :
    Polynomial.discr (C a * g) = a ^ (2 * g.natDegree - 2) * Polynomial.discr g := by
  classical
  by_cases hn0 : g.natDegree = 0
  · have hg1 : g = 1 := monic_eq_one_of_natDegree_eq_zero hg hn0
    rw [hg1]
    rw [mul_one, Polynomial.discr_C]
    rw [show (1 : F[X]) = C (1 : F) by simp]
    rw [Polynomial.discr_C]
    simp
  · have hpos : 0 < g.natDegree := Nat.pos_of_ne_zero hn0
    let f : F[X] := C a * g
    have hfdeg : 0 < f.degree := by
      dsimp [f]
      rw [Polynomial.degree_C_mul ha]
      exact (Polynomial.natDegree_pos_iff_degree_pos.mp hpos)
    have hndf : f.natDegree = g.natDegree := by
      dsimp [f]
      exact Polynomial.natDegree_C_mul ha
    have hderiv : f.derivative = C a * g.derivative := by
      dsimp [f]
      exact Polynomial.derivative_C_mul a g
    have hlc_f : f.leadingCoeff = a := by
      dsimp [f]
      rw [Polynomial.leadingCoeff, Polynomial.natDegree_C_mul ha, Polynomial.coeff_C_mul]
      rw [← Polynomial.leadingCoeff]
      rw [hg.leadingCoeff]
      simp
    have hRf := Polynomial.resultant_deriv (f := f) hfdeg
    have hRg := Polynomial.resultant_deriv (f := g)
      (by exact (Polynomial.natDegree_pos_iff_degree_pos.mp hpos) : 0 < g.degree)
    let s : ℕ := g.natDegree * (g.natDegree - 1) / 2
    have hRf' : (-1 : F) ^ s * a * f.discr =
        a ^ (g.natDegree - 1) * a ^ g.natDegree *
          (g.resultant g.derivative g.natDegree (g.natDegree - 1)) := by
      have hsig : f.natDegree * (f.natDegree - 1) / 2 = s := by
        dsimp [s]
        rw [hndf]
      calc
        (-1 : F) ^ s * a * f.discr
            = (-1 : F) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff * f.discr := by
              rw [hsig, hlc_f]
        _ = f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
              exact hRf.symm
        _ = (C a * g).resultant (C a * g.derivative) f.natDegree (f.natDegree - 1) := by
              rw [hderiv]
        _ = (C a * g).resultant (C a * g.derivative) g.natDegree (g.natDegree - 1) := by
              rw [hndf]
        _ = a ^ (g.natDegree - 1) * g.resultant (C a * g.derivative)
              g.natDegree (g.natDegree - 1) := by
              rw [Polynomial.resultant_C_mul_left]
        _ = a ^ (g.natDegree - 1) * (a ^ g.natDegree *
              g.resultant g.derivative g.natDegree (g.natDegree - 1)) := by
              rw [Polynomial.resultant_C_mul_right]
        _ = a ^ (g.natDegree - 1) * a ^ g.natDegree *
              (g.resultant g.derivative g.natDegree (g.natDegree - 1)) := by
              ring
    have hRg' : g.resultant g.derivative g.natDegree (g.natDegree - 1) = (-1 : F) ^ s * g.discr := by
      calc
        g.resultant g.derivative g.natDegree (g.natDegree - 1)
            = (-1 : F) ^ (g.natDegree * (g.natDegree - 1) / 2) * g.leadingCoeff * g.discr := hRg
        _ = (-1 : F) ^ s * g.discr := by
              dsimp [s]
              rw [hg.leadingCoeff]
              simp
    have hA : (-1 : F) ^ s * a * f.discr =
        (-1 : F) ^ s * a * (a ^ (2 * g.natDegree - 2) * g.discr) := by
      calc
        (-1 : F) ^ s * a * f.discr
            = a ^ (g.natDegree - 1) * a ^ g.natDegree *
              (g.resultant g.derivative g.natDegree (g.natDegree - 1)) := hRf'
        _ = a ^ (g.natDegree - 1) * a ^ g.natDegree * ((-1 : F) ^ s * g.discr) := by
              rw [hRg']
        _ = (-1 : F) ^ s * a * (a ^ (2 * g.natDegree - 2) * g.discr) := by
              have hpow1 : a ^ (g.natDegree - 1) * a ^ g.natDegree =
                  a ^ (g.natDegree - 1 + g.natDegree) := by rw [pow_add]
              rw [hpow1]
              have hdeg' : g.natDegree - 1 + g.natDegree = 1 + (2 * g.natDegree - 2) := by omega
              rw [hdeg']
              rw [pow_add]
              ring
    have hσa : (-1 : F) ^ s * a ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero s (by exact neg_ne_zero.mpr one_ne_zero)) ha
    have hmain : f.discr = a ^ (2 * g.natDegree - 2) * g.discr := by
      exact mul_left_cancel₀ hσa hA
    change Polynomial.discr (C a * g) = a ^ (2 * g.natDegree - 2) * Polynomial.discr g
    dsimp [f] at hmain
    exact hmain

/-- The discriminant of `c X^m + d` (with `c ≠ 0`, `d ≠ 0` and `m` nonzero in `F`) is nonzero. -/
theorem discr_C_mul_X_pow_add_C_ne_zero {F : Type*} [Field F] (m : ℕ) (c d : F)
    (hm : (m : F) ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    Polynomial.discr (C c * X ^ m + C d : F[X]) ≠ 0 := by
  classical
  have hmn : m ≠ 0 := by
    intro hm0
    apply hm
    simp [hm0]
  have he : c⁻¹ * d ≠ 0 := mul_ne_zero (inv_ne_zero hc) hd
  have hcd : c * (c⁻¹ * d) = d := by
    field_simp [hc]
  have hp_eq : (C c * X ^ m + C d : F[X]) = C c * (X ^ m + C (c⁻¹ * d)) := by
    rw [mul_add, ← Polynomial.C_mul, hcd]
  rw [hp_eq]
  let g : F[X] := X ^ m + C (c⁻¹ * d)
  change Polynomial.discr (C c * g) ≠ 0
  have hgmon : g.Monic := by
    dsimp [g]
    exact monic_X_pow_add_C (R := F) (a := c⁻¹ * d) (n := m) hmn
  have hgsep : g.Separable := by
    dsimp [g]
    have hse : ((X : F[X]) ^ m - C (-(c⁻¹ * d))).Separable := by
      refine separable_X_pow_sub_C_unit (R := F) (n := m) (u := Units.mk0 (-(c⁻¹ * d)) ?_) ?_
      · exact neg_ne_zero.mpr he
      · exact (isUnit_iff_ne_zero.mpr hm)
    simpa [sub_eq_add_neg] using hse
  have hdg : Polynomial.discr g ≠ 0 := discr_ne_zero_of_separable g hgmon hgsep
  rw [discr_C_mul_of_monic g c hgmon hc]
  exact mul_ne_zero (pow_ne_zero (2 * g.natDegree - 2) hc) hdg

end Commons.FieldTheory.Polynomial
