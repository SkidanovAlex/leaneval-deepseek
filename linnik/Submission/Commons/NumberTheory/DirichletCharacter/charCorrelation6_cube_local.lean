import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_criticalClasses
import Submission.Commons.NumberTheory.DirichletCharacter.chi_one_add_primePow_isPrimitiveRoot
import Submission.Commons.NumberTheory.DirichletCharacter.criticalClass_gaussSum_primePow
import Submission.Commons.NumberTheory.GaussSum.quadratic_gauss_primitive_root
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation_caseC_gcd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

/-! ## Digits of `r + u` modulo `p` and the resulting phase coordinates -/

/-- The low digit `(r + u) mod p`. -/
def cLow (p : ℕ) (r : ZMod p) (u : ℕ) : ℕ := (r.val + u) % p

/-- The high digit `(r + u) / p`. -/
def cHigh (p : ℕ) (r : ZMod p) (u : ℕ) : ℕ := (r.val + u) / p

/-- `x ↦ (x.val : ZMod (p^3))`, the canonical lift of a residue class. -/
def clift (p : ℕ) (x : ZMod p) : ZMod (p^3) := ((x.val : ℕ) : ZMod (p^3))

/-- The unit part `u_l` of the point `r + p z + u`. -/
def cUnit (p : ℕ) (r : ZMod p) (u : ℕ) : ZMod (p^3) := ((cLow p r u : ℕ) : ZMod (p^3))

/-- The point `r + p z + u` as an element of `ZMod (p^3)`. -/
def cPt (p : ℕ) (r : ZMod p) (u : ℕ) (z : ZMod p) : ZMod (p^3) :=
  (((r.val + p * z.val + u : ℕ)) : ZMod (p^3))

/-- The phase coordinate `α = (high + z) * (low)⁻¹ ∈ ZMod (p^3)`. -/
def cAlpha (p : ℕ) (r : ZMod p) (u : ℕ) (z : ZMod p) : ZMod (p^3) :=
  ((((cHigh p r u : ℕ) : ZMod (p^3)) + clift p z) * (cUnit p r u)⁻¹)

lemma cLow_cast (r : ZMod p) (u : ℕ) : ((cLow p r u : ℕ) : ZMod p) = r + (u : ZMod p) := by
  have h : ((cLow p r u : ℕ) : ZMod p) = ((r.val + u : ℕ) : ZMod p) := by
    rw [cLow]; exact ZMod.natCast_mod _ _
  rw [h, Nat.cast_add, ZMod.natCast_zmod_val]

lemma cUnit_isUnit (r : ZMod p) (u : ℕ) (h : (r + (u : ZMod p)) ≠ 0) :
    IsUnit (cUnit p r u) := by
  rw [cUnit]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) (by norm_num : 0 < 3)]
  intro hdvd
  apply h
  rw [← cLow_cast r u]
  exact (ZMod.natCast_eq_zero_iff _ p).mpr hdvd

lemma cPt_eq (r : ZMod p) (u : ℕ) (z : ZMod p) (hu : (r + (u : ZMod p)) ≠ 0) :
    cPt p r u z = cUnit p r u * (1 + (p : ZMod (p^3)) * cAlpha p r u z) := by
  have hdec : r.val + u = cLow p r u + p * cHigh p r u := by
    rw [cLow, cHigh]; exact (Nat.mod_add_div (r.val + u) p).symm
  have hkey : r.val + p * z.val + u = cLow p r u + p * (cHigh p r u + z.val) := by
    calc r.val + p * z.val + u = (r.val + u) + p * z.val := by ring
      _ = (cLow p r u + p * cHigh p r u) + p * z.val := by rw [hdec]
      _ = cLow p r u + p * (cHigh p r u + z.val) := by ring
  have hunit : (((cLow p r u : ℕ)) : ZMod (p^3)) * (((cLow p r u : ℕ)) : ZMod (p^3))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (cUnit_isUnit r u hu)
  simp only [cPt, cAlpha, cUnit, clift]
  rw [hkey]
  push_cast
  linear_combination (-((p : ZMod (p^3)) * (((cHigh p r u : ℕ) : ZMod (p^3))
      + ((z.val : ℕ) : ZMod (p^3))))) * hunit

/-! ## The products `P` and its expansion -/

/-- The product `∏_l (1 + p α_l) * (∏_l (1 + p α'_l))⁻¹`. -/
noncomputable def cPz (p : ℕ) (r : ZMod p) (a b : Fin 3 → ℕ) (z : ZMod p) : ZMod (p^3) :=
  ((1 + (p : ZMod (p^3)) * cAlpha p r (a 0) z) * (1 + (p : ZMod (p^3)) * cAlpha p r (a 1) z)
    * (1 + (p : ZMod (p^3)) * cAlpha p r (a 2) z))
  * (((1 + (p : ZMod (p^3)) * cAlpha p r (b 0) z) * (1 + (p : ZMod (p^3)) * cAlpha p r (b 1) z)
      * (1 + (p : ZMod (p^3)) * cAlpha p r (b 2) z)))⁻¹

/-- The first-order part `W = ∑ α_l - ∑ α'_l`. -/
noncomputable def cWz (p : ℕ) (r : ZMod p) (a b : Fin 3 → ℕ) (z : ZMod p) : ZMod (p^3) :=
  (cAlpha p r (a 0) z + cAlpha p r (a 1) z + cAlpha p r (a 2) z)
    - (cAlpha p r (b 0) z + cAlpha p r (b 1) z + cAlpha p r (b 2) z)

/-- The second-order part `Z`. -/
noncomputable def cZz (p : ℕ) (r : ZMod p) (a b : Fin 3 → ℕ) (z : ZMod p) : ZMod (p^3) :=
  (cAlpha p r (a 0) z * cAlpha p r (a 1) z + cAlpha p r (a 0) z * cAlpha p r (a 2) z
      + cAlpha p r (a 1) z * cAlpha p r (a 2) z)
    + (cAlpha p r (b 0) z ^ 2 + cAlpha p r (b 1) z ^ 2 + cAlpha p r (b 2) z ^ 2)
    + (cAlpha p r (b 0) z * cAlpha p r (b 1) z + cAlpha p r (b 0) z * cAlpha p r (b 2) z
      + cAlpha p r (b 1) z * cAlpha p r (b 2) z)
    - ((cAlpha p r (a 0) z + cAlpha p r (a 1) z + cAlpha p r (a 2) z)
        * (cAlpha p r (b 0) z + cAlpha p r (b 1) z + cAlpha p r (b 2) z))

lemma p_cube_eq_zero : ((p : ZMod (p^3))) ^ 3 = 0 := by
  rw [show ((p : ZMod (p^3))) ^ 3 = ((p^3 : ℕ) : ZMod (p^3)) by push_cast; ring]
  exact ZMod.natCast_self _

lemma prod_expand {R : Type*} [CommRing R] (P X0 X1 X2 : R) (h3 : P ^ 3 = 0) :
    (1 + P * X0) * (1 + P * X1) * (1 + P * X2)
      = 1 + P * (X0 + X1 + X2) + P ^ 2 * (X0 * X1 + X0 * X2 + X1 * X2) := by
  have h : (1 + P * X0) * (1 + P * X1) * (1 + P * X2)
      = 1 + P * (X0 + X1 + X2) + P ^ 2 * (X0 * X1 + X0 * X2 + X1 * X2)
        + P ^ 3 * (X0 * X1 * X2) := by ring
  rw [h, h3, zero_mul, add_zero]

lemma quad_expand {R : Type*} [CommRing R] (P Y0 Y1 Y2 : R) (h3 : P ^ 3 = 0) :
    (1 - P * Y0 + P ^ 2 * Y0 ^ 2) * (1 - P * Y1 + P ^ 2 * Y1 ^ 2)
        * (1 - P * Y2 + P ^ 2 * Y2 ^ 2)
      = 1 - P * (Y0 + Y1 + Y2)
        + P ^ 2 * (Y0 ^ 2 + Y1 ^ 2 + Y2 ^ 2 + Y0 * Y1 + Y0 * Y2 + Y1 * Y2) := by
  have h4 : P ^ 4 = 0 := by rw [show P ^ 4 = P ^ 3 * P by ring, h3, zero_mul]
  have h5 : P ^ 5 = 0 := by rw [show P ^ 5 = P ^ 3 * P ^ 2 by ring, h3, zero_mul]
  have h6 : P ^ 6 = 0 := by rw [show P ^ 6 = P ^ 3 * P ^ 3 by ring, h3, zero_mul]
  ring_nf
  rw [h4, h5, h6]
  ring_nf
  rw [h3]
  ring

lemma inv_one_add (Y : ZMod (p^3)) :
    (1 + (p : ZMod (p^3)) * Y)⁻¹ = 1 - (p : ZMod (p^3)) * Y + (p : ZMod (p^3)) ^ 2 * Y ^ 2 := by
  have h3 : ((p : ZMod (p^3)) * Y) ^ 3 = 0 := by rw [mul_pow, p_cube_eq_zero, zero_mul]
  refine ZMod.inv_eq_of_mul_eq_one _ _ _ ?_
  have h : (1 + (p : ZMod (p^3)) * Y)
      * (1 - (p : ZMod (p^3)) * Y + (p : ZMod (p^3)) ^ 2 * Y ^ 2)
      = 1 + ((p : ZMod (p^3)) * Y) ^ 3 := by ring
  rw [h, h3, add_zero]

lemma one_add_mul_inv_self (Y : ZMod (p^3)) :
    (1 + (p : ZMod (p^3)) * Y) * (1 + (p : ZMod (p^3)) * Y)⁻¹ = 1 := by
  rw [inv_one_add Y]
  have h3 : ((p : ZMod (p^3)) * Y) ^ 3 = 0 := by rw [mul_pow, p_cube_eq_zero, zero_mul]
  have h : (1 + (p : ZMod (p^3)) * Y)
      * (1 - (p : ZMod (p^3)) * Y + (p : ZMod (p^3)) ^ 2 * Y ^ 2)
      = 1 + ((p : ZMod (p^3)) * Y) ^ 3 := by ring
  rw [h, h3, add_zero]

lemma inv_prod_three (Y0 Y1 Y2 : ZMod (p^3)) :
    ((1 + (p : ZMod (p^3)) * Y0) * (1 + (p : ZMod (p^3)) * Y1)
      * (1 + (p : ZMod (p^3)) * Y2))⁻¹
      = 1 - (p : ZMod (p^3)) * (Y0 + Y1 + Y2)
        + (p : ZMod (p^3)) ^ 2 * (Y0 ^ 2 + Y1 ^ 2 + Y2 ^ 2 + Y0 * Y1 + Y0 * Y2 + Y1 * Y2) := by
  have hprod : ((1 + (p : ZMod (p^3)) * Y0) * (1 + (p : ZMod (p^3)) * Y1)
      * (1 + (p : ZMod (p^3)) * Y2))⁻¹
      = (1 + (p : ZMod (p^3)) * Y0)⁻¹ * (1 + (p : ZMod (p^3)) * Y1)⁻¹
        * (1 + (p : ZMod (p^3)) * Y2)⁻¹ := by
    rw [show ((1 + (p : ZMod (p^3)) * Y0) * (1 + (p : ZMod (p^3)) * Y1)
        * (1 + (p : ZMod (p^3)) * Y2))⁻¹
        = (1 + (p : ZMod (p^3)) * Y0)⁻¹ * (1 + (p : ZMod (p^3)) * Y1)⁻¹
          * (1 + (p : ZMod (p^3)) * Y2)⁻¹ from
      ZMod.inv_eq_of_mul_eq_one _ _ _ (by
        rw [show (1 + (p : ZMod (p^3)) * Y0) * (1 + (p : ZMod (p^3)) * Y1)
            * (1 + (p : ZMod (p^3)) * Y2)
            * ((1 + (p : ZMod (p^3)) * Y0)⁻¹ * (1 + (p : ZMod (p^3)) * Y1)⁻¹
              * (1 + (p : ZMod (p^3)) * Y2)⁻¹)
          = ((1 + (p : ZMod (p^3)) * Y0) * (1 + (p : ZMod (p^3)) * Y0)⁻¹)
            * ((1 + (p : ZMod (p^3)) * Y1) * (1 + (p : ZMod (p^3)) * Y1)⁻¹)
            * ((1 + (p : ZMod (p^3)) * Y2) * (1 + (p : ZMod (p^3)) * Y2)⁻¹) by ring]
        rw [one_add_mul_inv_self, one_add_mul_inv_self, one_add_mul_inv_self]
        ring)]
  rw [hprod, inv_one_add Y0, inv_one_add Y1, inv_one_add Y2]
  exact quad_expand _ _ _ _ p_cube_eq_zero

lemma cPz_expand (r : ZMod p) (a b : Fin 3 → ℕ) (z : ZMod p) :
    cPz p r a b z = 1 + (p : ZMod (p^3)) * cWz p r a b z
      + (p : ZMod (p^3)) ^ 2 * cZz p r a b z := by
  have hf := prod_expand (R := ZMod (p^3)) (p : ZMod (p^3)) (cAlpha p r (a 0) z)
    (cAlpha p r (a 1) z) (cAlpha p r (a 2) z) p_cube_eq_zero
  have hi := inv_prod_three (p := p) (cAlpha p r (b 0) z) (cAlpha p r (b 1) z) (cAlpha p r (b 2) z)
  rw [cPz, hf, hi, cWz, cZz]
  have h4 : (p : ZMod (p^3)) ^ 4 = 0 := by
    rw [show (p : ZMod (p^3)) ^ 4 = (p:ZMod (p^3))^3 * p by ring, p_cube_eq_zero, zero_mul]
  ring_nf
  rw [h4]
  ring_nf
  rw [p_cube_eq_zero]
  ring

/-! ## Reduction modulo `p` of the phase coordinates -/

/-- The reduction of `α` modulo `p`. -/
noncomputable def cBeta (p : ℕ) (r : ZMod p) (u : ℕ) (z : ZMod p) : ZMod p :=
  (((cHigh p r u : ℕ) : ZMod p) + z) * ((((cLow p r u : ℕ) : ZMod p)))⁻¹

/-- The reduction of the second order part `Z` modulo `p`. -/
noncomputable def cQ (p : ℕ) (r : ZMod p) (a b : Fin 3 → ℕ) (z : ZMod p) : ZMod p :=
  (cBeta p r (a 0) z * cBeta p r (a 1) z + cBeta p r (a 0) z * cBeta p r (a 2) z
      + cBeta p r (a 1) z * cBeta p r (a 2) z)
    + (cBeta p r (b 0) z ^ 2 + cBeta p r (b 1) z ^ 2 + cBeta p r (b 2) z ^ 2)
    + (cBeta p r (b 0) z * cBeta p r (b 1) z + cBeta p r (b 0) z * cBeta p r (b 2) z
      + cBeta p r (b 1) z * cBeta p r (b 2) z)
    - ((cBeta p r (a 0) z + cBeta p r (a 1) z + cBeta p r (a 2) z)
        * (cBeta p r (b 0) z + cBeta p r (b 1) z + cBeta p r (b 2) z))

/-- The sum of inverses `∑_l (r + a_l)⁻¹` over a triple. -/
noncomputable def cDsum (p : ℕ) (r : ZMod p) (u : Fin 3 → ℕ) : ZMod p :=
  ((((cLow p r (u 0) : ℕ) : ZMod p)))⁻¹ + ((((cLow p r (u 1) : ℕ) : ZMod p)))⁻¹
    + ((((cLow p r (u 2) : ℕ) : ZMod p)))⁻¹

/-- The sum of squares of inverses `∑_l (r + a_l)⁻²` over a triple. -/
noncomputable def cDsq (p : ℕ) (r : ZMod p) (u : Fin 3 → ℕ) : ZMod p :=
  ((((cLow p r (u 0) : ℕ) : ZMod p)))⁻¹ ^ 2 + ((((cLow p r (u 1) : ℕ) : ZMod p)))⁻¹ ^ 2
    + ((((cLow p r (u 2) : ℕ) : ZMod p)))⁻¹ ^ 2

lemma castHom_natCast (h : p ∣ p ^ 3) (n : ℕ) :
    ZMod.castHom h (ZMod p) (((n : ℕ) : ZMod (p^3))) = ((n : ℕ) : ZMod p) := by
  rw [ZMod.castHom_apply]
  exact ZMod.cast_natCast h n

lemma castHom_cUnit (h : p ∣ p ^ 3) (r : ZMod p) (u : ℕ) :
    ZMod.castHom h (ZMod p) (cUnit p r u) = (((cLow p r u : ℕ)) : ZMod p) := by
  rw [cUnit, castHom_natCast]

lemma castHom_clift (h : p ∣ p ^ 3) (z : ZMod p) :
    ZMod.castHom h (ZMod p) (clift p z) = z := by
  rw [clift, castHom_natCast, ZMod.natCast_zmod_val]

lemma castHom_cAlpha (h : p ∣ p ^ 3) (r : ZMod p) (u : ℕ) (z : ZMod p)
    (hu : (r + (u : ZMod p)) ≠ 0) :
    ZMod.castHom h (ZMod p) (cAlpha p r u z) = cBeta p r u z := by
  have hx : ZMod.castHom h (ZMod p) ((cUnit p r u)⁻¹)
      = (ZMod.castHom h (ZMod p) (cUnit p r u))⁻¹ := by
    refine Eq.symm ?_
    refine ZMod.inv_eq_of_mul_eq_one _ _ _ ?_
    rw [← map_mul, ZMod.mul_inv_of_unit _ (cUnit_isUnit r u hu), map_one]
  rw [cAlpha, map_mul, map_add, hx, castHom_cUnit, cBeta, castHom_natCast, castHom_clift]

lemma castHom_cZz (h : p ∣ p ^ 3) (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0) (z : ZMod p) :
    ZMod.castHom h (ZMod p) (cZz p r a b z) = cQ p r a b z := by
  simp only [cZz, cQ, map_add, map_sub, map_mul, map_pow]
  rw [castHom_cAlpha h r (a 0) z (hu 0), castHom_cAlpha h r (a 1) z (hu 1),
    castHom_cAlpha h r (a 2) z (hu 2), castHom_cAlpha h r (b 0) z (hv 0),
    castHom_cAlpha h r (b 1) z (hv 1), castHom_cAlpha h r (b 2) z (hv 2)]

lemma cBeta_eq (r : ZMod p) (u : ℕ) (z : ZMod p) :
    cBeta p r u z = ((cHigh p r u : ℕ) : ZMod p) * ((((cLow p r u : ℕ) : ZMod p)))⁻¹
      + z * ((((cLow p r u : ℕ) : ZMod p)))⁻¹ := by
  rw [cBeta]; ring

lemma cQ_second_diff_gen (r : ZMod p) (a b : Fin 3 → ℕ) (z w : ZMod p) :
    cQ p r a b (z + w) - cQ p r a b z - cQ p r a b w + cQ p r a b 0
      = (z * w) * ((cDsum p r a - cDsum p r b) ^ 2 - (cDsq p r a - cDsq p r b)) := by
  simp only [cQ, cBeta_eq, cDsum, cDsq]
  ring

lemma cQ_second_diff (r : ZMod p) (a b : Fin 3 → ℕ)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) (z w : ZMod p) :
    cQ p r a b (z + w) - cQ p r a b z - cQ p r a b w + cQ p r a b 0
      = -(cDsq p r a - cDsq p r b) * (z * w) := by
  rw [cQ_second_diff_gen]
  have hδ : cDsum p r a = cDsum p r b := by
    rw [cDsum, cDsum, Fin.sum_univ_three, Fin.sum_univ_three] at *
    rw [cLow_cast r (a 0), cLow_cast r (a 1), cLow_cast r (a 2),
      cLow_cast r (b 0), cLow_cast r (b 1), cLow_cast r (b 2)]
    exact hcrit
  rw [hδ, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_sub]
  ring

/-! ## The unit-sum difference `S` and the affine structure of `W` -/

/-- The difference of the unit sums `∑_l (r+a_l)⁻¹ - ∑_l (r+b_l)⁻¹`. -/
noncomputable def cS (p : ℕ) (r : ZMod p) (a b : Fin 3 → ℕ) : ZMod (p^3) :=
  ((cUnit p r (a 0))⁻¹ + (cUnit p r (a 1))⁻¹ + (cUnit p r (a 2))⁻¹)
    - ((cUnit p r (b 0))⁻¹ + (cUnit p r (b 1))⁻¹ + (cUnit p r (b 2))⁻¹)

lemma clift_zero (p : ℕ) : clift p (0 : ZMod p) = 0 := by
  rw [clift, ZMod.val_zero, Nat.cast_zero]

lemma cWz_affine (r : ZMod p) (a b : Fin 3 → ℕ) (z : ZMod p) :
    cWz p r a b z = cWz p r a b 0 + clift p z * cS p r a b := by
  simp only [cWz, cAlpha, cS, Fin.sum_univ_three]
  rw [clift_zero]
  ring

lemma castHom_inv (h : p ∣ p ^ 3) (r : ZMod p) (u : ℕ) (hu : (r + (u : ZMod p)) ≠ 0) :
    ZMod.castHom h (ZMod p) ((cUnit p r u)⁻¹)
      = ((((cLow p r u : ℕ) : ZMod p)))⁻¹ := by
  refine Eq.symm ?_
  refine ZMod.inv_eq_of_mul_eq_one _ _ _ ?_
  rw [← castHom_cUnit h r u, ← map_mul, ZMod.mul_inv_of_unit _ (cUnit_isUnit r u hu), map_one]

lemma castHom_cS (h : p ∣ p ^ 3) (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0) :
    ZMod.castHom h (ZMod p) (cS p r a b) = cDsum p r a - cDsum p r b := by
  simp only [cS, cDsum, map_sub, map_add, Fin.sum_univ_three]
  rw [castHom_inv h r (a 0) (hu 0), castHom_inv h r (a 1) (hu 1), castHom_inv h r (a 2) (hu 2),
    castHom_inv h r (b 0) (hv 0), castHom_inv h r (b 1) (hv 1), castHom_inv h r (b 2) (hv 2)]

lemma cDsum_congr (r : ZMod p) (a b : Fin 3 → ℕ)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) :
    cDsum p r a = cDsum p r b := by
  rw [cDsum, cDsum, Fin.sum_univ_three, Fin.sum_univ_three] at *
  rw [cLow_cast r (a 0), cLow_cast r (a 1), cLow_cast r (a 2),
    cLow_cast r (b 0), cLow_cast r (b 1), cLow_cast r (b 2)]
  exact hcrit

lemma cDsq_congr (r : ZMod p) (a b : Fin 3 → ℕ) :
    cDsq p r a - cDsq p r b
      = (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
        - (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2) := by
  simp only [cDsq, Fin.sum_univ_three]
  rw [cLow_cast r (a 0), cLow_cast r (a 1), cLow_cast r (a 2),
    cLow_cast r (b 0), cLow_cast r (b 1), cLow_cast r (b 2)]

lemma cS_dvd (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) :
    p ∣ (cS p r a b).val := by
  have h0 : ZMod.castHom (show p ∣ p^3 by norm_num) (ZMod p) (cS p r a b) = 0 := by
    rw [castHom_cS _ r a b hu hv, cDsum_congr r a b hcrit, sub_self]
  have h2 := congrArg ZMod.val h0
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ZMod.val_zero] at h2
  exact Nat.dvd_of_mod_eq_zero h2

lemma cS_eq_p_mul (r : ZMod p) (a b : Fin 3 → ℕ) (hS : p ∣ (cS p r a b).val) :
    ∃ S' : ZMod (p^3), cS p r a b = (p : ZMod (p^3)) * S' := by
  obtain ⟨k, hk⟩ := hS
  refine ⟨((k : ℕ) : ZMod (p^3)), ?_⟩
  rw [← ZMod.natCast_zmod_val (cS p r a b), hk]
  push_cast
  ring

lemma clift_add_carry (z w : ZMod p) :
    clift p (z + w) = clift p z + clift p w
      - (p : ZMod (p^3)) * (((z.val + w.val) / p : ℕ) : ZMod (p^3)) := by
  have hmod : (z + w).val = (z.val + w.val) % p := ZMod.val_add z w
  rw [clift, clift, clift, hmod]
  have hle : p * ((z.val + w.val) / p) ≤ z.val + w.val := by
    rw [mul_comm]; exact Nat.div_mul_le_self _ _
  rw [show (z.val + w.val) % p = z.val + w.val - p * ((z.val + w.val) / p) by
    rw [Nat.mod_eq_sub_mul_div, mul_comm]]
  rw [Nat.cast_sub hle]
  push_cast
  ring

/-! ## The cocycle identity for `cPz` -/

/-- The first two orders of the phase: `X = W + p Z`. -/
noncomputable def cX (p : ℕ) (r : ZMod p) (a b : Fin 3 → ℕ) (z : ZMod p) : ZMod (p^3) :=
  cWz p r a b z + (p : ZMod (p^3)) * cZz p r a b z

/-- The second order remainder `F` of the four-term product expansion. -/
noncomputable def cF (p : ℕ) (r : ZMod p) (a b : Fin 3 → ℕ) (z w : ZMod p) : ZMod (p^3) :=
  (cX p r a b w) ^ 2 - cX p r a b (z + w) * cX p r a b w
    + (cX p r a b z) ^ 2 - cX p r a b z * cX p r a b 0
    + (cX p r a b (z + w) - cX p r a b w) * (cX p r a b 0 - cX p r a b z)

lemma exists_factor_of_castHom_eq_zero (h : p ∣ p ^ 3) (X : ZMod (p^3))
    (hX : ZMod.castHom h (ZMod p) X = 0) : ∃ Y : ZMod (p^3), X = (p : ZMod (p^3)) * Y := by
  have h2 := congrArg ZMod.val hX
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ZMod.val_zero] at h2
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h2
  refine ⟨((k : ℕ) : ZMod (p^3)), ?_⟩
  rw [← ZMod.natCast_zmod_val X, hk]
  push_cast
  ring

lemma cPz_expand' (r : ZMod p) (a b : Fin 3 → ℕ) (z : ZMod p) :
    cPz p r a b z = 1 + (p : ZMod (p^3)) * cX p r a b z := by
  rw [cPz_expand, cX]; ring

lemma cWz_diff (r : ZMod p) (a b : Fin 3 → ℕ) (S' : ZMod (p^3))
    (hS : cS p r a b = (p : ZMod (p^3)) * S') (z w : ZMod p) :
    cWz p r a b (z + w) - cWz p r a b w + cWz p r a b 0 - cWz p r a b z
      = - (p : ZMod (p^3)) ^ 2 * ((((z.val + w.val) / p : ℕ) : ZMod (p^3)) * S') := by
  rw [cWz_affine r a b (z + w), cWz_affine r a b w, cWz_affine r a b 0,
    cWz_affine r a b z, clift_zero, zero_mul, add_zero, hS, clift_add_carry]
  ring

lemma castHom_cWz_eq (h : p ∣ p ^ 3) (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) (z : ZMod p) :
    ZMod.castHom h (ZMod p) (cWz p r a b z) = ZMod.castHom h (ZMod p) (cWz p r a b 0) := by
  rw [cWz_affine r a b z, map_add, map_mul, castHom_clift, castHom_cS h r a b hu hv,
    cDsum_congr r a b hcrit, sub_self, mul_zero, add_zero]

lemma castHom_cX_eq (h : p ∣ p ^ 3) (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) (z : ZMod p) :
    ZMod.castHom h (ZMod p) (cX p r a b z) = ZMod.castHom h (ZMod p) (cX p r a b 0) := by
  rw [cX, cX, map_add, map_add, map_mul, map_mul,
    show ZMod.castHom h (ZMod p) (p : ZMod (p^3)) = 0 by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
      rw [show (p : ZMod (p^3)).val = p by
        rw [ZMod.val_natCast]
        exact Nat.mod_eq_of_lt (by
          calc p = p ^ 1 := (pow_one p).symm
            _ < p ^ 3 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num))]
      exact ZMod.natCast_self p,
    zero_mul, zero_mul, add_zero, add_zero]
  exact castHom_cWz_eq h r a b hu hv hcrit z

lemma castHom_cF (h : p ∣ p ^ 3) (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) (z w : ZMod p) :
    ZMod.castHom h (ZMod p) (cF p r a b z w) = 0 := by
  have h1 := castHom_cX_eq h r a b hu hv hcrit (z + w)
  have h2 := castHom_cX_eq h r a b hu hv hcrit w
  have h3 := castHom_cX_eq h r a b hu hv hcrit z
  have h4 := castHom_cX_eq h r a b hu hv hcrit 0
  simp only [cF, map_add, map_sub, map_mul, map_pow]
  rw [h1, h2, h3, h4]
  ring

lemma cF_dvd (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) (z w : ZMod p) :
    ∃ F' : ZMod (p^3), cF p r a b z w = (p : ZMod (p^3)) * F' :=
  exists_factor_of_castHom_eq_zero (show p ∣ p^3 by norm_num) _
    (castHom_cF (show p ∣ p^3 by norm_num) r a b hu hv hcrit z w)

lemma cZz_diff_mod (h : p ∣ p ^ 3) (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) (z w : ZMod p) :
    ZMod.castHom h (ZMod p)
      (cZz p r a b (z + w) - cZz p r a b w + cZz p r a b 0 - cZz p r a b z
        + clift p ((cDsq p r a - cDsq p r b) * z * w)) = 0 := by
  simp only [map_add, map_sub]
  rw [castHom_clift,
    castHom_cZz h r a b hu hv (z + w), castHom_cZz h r a b hu hv w,
    castHom_cZz h r a b hu hv 0, castHom_cZz h r a b hu hv z]
  rw [show cQ p r a b (z + w) - cQ p r a b w + cQ p r a b 0 - cQ p r a b z
      + (cDsq p r a - cDsq p r b) * z * w
      = (cQ p r a b (z + w) - cQ p r a b z - cQ p r a b w + cQ p r a b 0)
        + (cDsq p r a - cDsq p r b) * z * w by ring,
    cQ_second_diff r a b hcrit z w]
  ring

lemma cZz_diff_dvd (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) (z w : ZMod p) :
    ∃ Y : ZMod (p^3),
      cZz p r a b (z + w) - cZz p r a b w + cZz p r a b 0 - cZz p r a b z
        + clift p ((cDsq p r a - cDsq p r b) * z * w) = (p : ZMod (p^3)) * Y :=
  exists_factor_of_castHom_eq_zero (show p ∣ p^3 by norm_num) _
    (cZz_diff_mod (show p ∣ p^3 by norm_num) r a b hu hv hcrit z w)

lemma cF_eq (r : ZMod p) (a b : Fin 3 → ℕ) (z w : ZMod p) :
    cF p r a b z w = ((cX p r a b w) ^ 2 - cX p r a b (z + w) * cX p r a b w
      + (cX p r a b z) ^ 2 - cX p r a b z * cX p r a b 0
      + (cX p r a b (z + w) - cX p r a b w) * (cX p r a b 0 - cX p r a b z)) := rfl

lemma four_term_expand (A B C D : ZMod (p^3)) :
    (1 + (p : ZMod (p^3)) * A) * (1 + (p : ZMod (p^3)) * B)⁻¹
        * (1 + (p : ZMod (p^3)) * C)⁻¹ * (1 + (p : ZMod (p^3)) * D)
      = 1 + (p : ZMod (p^3)) * ((A - B + D - C)
          + (p : ZMod (p^3)) * ((B ^ 2 - A * B) + (C ^ 2 - C * D)
            + (A - B) * (D - C))) := by
  rw [inv_one_add B, inv_one_add C]
  have h4 : (p : ZMod (p^3)) ^ 4 = 0 := by
    rw [show (p : ZMod (p^3)) ^ 4 = (p : ZMod (p^3)) ^ 3 * p by ring, p_cube_eq_zero, zero_mul]
  have h5 : (p : ZMod (p^3)) ^ 5 = 0 := by
    rw [show (p : ZMod (p^3)) ^ 5 = (p : ZMod (p^3)) ^ 3 * (p : ZMod (p^3)) ^ 2 by ring,
      p_cube_eq_zero, zero_mul]
  have h6 : (p : ZMod (p^3)) ^ 6 = 0 := by
    rw [show (p : ZMod (p^3)) ^ 6 = (p : ZMod (p^3)) ^ 3 * (p : ZMod (p^3)) ^ 3 by ring,
      p_cube_eq_zero, zero_mul]
  ring_nf
  rw [h4, h5, h6]
  ring_nf
  rw [p_cube_eq_zero]
  ring

theorem cPz_cocycle (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) (z w : ZMod p) :
    cPz p r a b (z + w) * (cPz p r a b w)⁻¹ * (cPz p r a b z)⁻¹ * cPz p r a b 0
      = 1 - (p : ZMod (p^3)) ^ 2 * clift p ((cDsq p r a - cDsq p r b) * z * w) := by
  obtain ⟨S', hS⟩ := cS_eq_p_mul r a b (cS_dvd r a b hu hv hcrit)
  obtain ⟨Y, hY⟩ := cZz_diff_dvd r a b hu hv hcrit z w
  obtain ⟨F', hF⟩ := cF_dvd r a b hu hv hcrit z w
  have hE1 : cWz p r a b (z + w) - cWz p r a b w + cWz p r a b 0 - cWz p r a b z
      = - (p : ZMod (p^3)) ^ 2 * ((((z.val + w.val) / p : ℕ) : ZMod (p^3)) * S') :=
    cWz_diff r a b S' hS z w
  have hE2 : cZz p r a b (z + w) - cZz p r a b w + cZz p r a b 0 - cZz p r a b z
      = (p : ZMod (p^3)) * Y - clift p ((cDsq p r a - cDsq p r b) * z * w) := by
    rw [← hY]; ring
  have hF' : ((cX p r a b w) ^ 2 - cX p r a b (z + w) * cX p r a b w)
        + ((cX p r a b z) ^ 2 - cX p r a b z * cX p r a b 0)
        + (cX p r a b (z + w) - cX p r a b w) * (cX p r a b 0 - cX p r a b z)
      = (p : ZMod (p^3)) * F' := by
    rw [show ((cX p r a b w) ^ 2 - cX p r a b (z + w) * cX p r a b w)
            + ((cX p r a b z) ^ 2 - cX p r a b z * cX p r a b 0)
            + (cX p r a b (z + w) - cX p r a b w) * (cX p r a b 0 - cX p r a b z)
          = ((cX p r a b w) ^ 2 - cX p r a b (z + w) * cX p r a b w
            + (cX p r a b z) ^ 2 - cX p r a b z * cX p r a b 0
            + (cX p r a b (z + w) - cX p r a b w) * (cX p r a b 0 - cX p r a b z)) by ring,
      ← cF_eq]
    exact hF
  have hE1' : (cWz p r a b (z + w) + (p : ZMod (p^3)) * cZz p r a b (z + w))
        - (cWz p r a b w + (p : ZMod (p^3)) * cZz p r a b w)
        + (cWz p r a b 0 + (p : ZMod (p^3)) * cZz p r a b 0)
        - (cWz p r a b z + (p : ZMod (p^3)) * cZz p r a b z)
      = - (p : ZMod (p^3)) ^ 2 * ((((z.val + w.val) / p : ℕ) : ZMod (p^3)) * S')
        + (p : ZMod (p^3)) * ((p : ZMod (p^3)) * Y
          - clift p ((cDsq p r a - cDsq p r b) * z * w)) := by
    rw [← hE1, ← hE2]; ring
  have hstep : (p : ZMod (p^3)) * ((cX p r a b (z + w) - cX p r a b w + cX p r a b 0
          - cX p r a b z)
        + (p : ZMod (p^3)) * (((cX p r a b w) ^ 2 - cX p r a b (z + w) * cX p r a b w)
            + ((cX p r a b z) ^ 2 - cX p r a b z * cX p r a b 0)
            + (cX p r a b (z + w) - cX p r a b w) * (cX p r a b 0 - cX p r a b z))
        + (p : ZMod (p^3)) * clift p ((cDsq p r a - cDsq p r b) * z * w)) = 0 := by
    simp only [cX] at hF' ⊢
    rw [hE1', hF']
    ring_nf
    rw [p_cube_eq_zero]
    ring
  rw [cPz_expand' r a b (z + w), cPz_expand' r a b w, cPz_expand' r a b z,
    cPz_expand' r a b 0, four_term_expand]
  set E := cX p r a b (z + w) - cX p r a b w + cX p r a b 0 - cX p r a b z with hE
  set F := ((cX p r a b w) ^ 2 - cX p r a b (z + w) * cX p r a b w)
      + ((cX p r a b z) ^ 2 - cX p r a b z * cX p r a b 0)
      + (cX p r a b (z + w) - cX p r a b w) * (cX p r a b 0 - cX p r a b z) with hFdef
  set Q := clift p ((cDsq p r a - cDsq p r b) * z * w) with hQ
  have hstep2 : (p : ZMod (p^3)) * (E + (p : ZMod (p^3)) * F + (p : ZMod (p^3)) * Q) = 0 := by
    rw [hE, hFdef, hQ]
    exact hstep
  refine sub_eq_zero.mp ?_
  have h2 : (1 + (p : ZMod (p^3)) * (E + (p : ZMod (p^3)) * F))
      - (1 - (p : ZMod (p^3)) ^ 2 * Q)
      = (p : ZMod (p^3)) * (E + (p : ZMod (p^3)) * F + (p : ZMod (p^3)) * Q) := by ring
  rw [h2, hstep2]

/-! ## The character of the phase product and the second moment -/

lemma isUnit_one_add_pmul (Y : ZMod (p^3)) :
    IsUnit (1 + (p : ZMod (p^3)) * Y) := by
  refine isUnit_iff_exists_inv.mpr ⟨1 - (p : ZMod (p^3)) * Y + (p : ZMod (p^3)) ^ 2 * Y ^ 2, ?_⟩
  have h3 : ((p : ZMod (p^3)) * Y) ^ 3 = 0 := by rw [mul_pow, p_cube_eq_zero, zero_mul]
  have h : (1 + (p : ZMod (p^3)) * Y)
      * (1 - (p : ZMod (p^3)) * Y + (p : ZMod (p^3)) ^ 2 * Y ^ 2)
      = 1 + ((p : ZMod (p^3)) * Y) ^ 3 := by ring
  rw [h, h3, add_zero]

lemma isUnit_inv_of_unit {x : ZMod (p^3)} (hx : IsUnit x) : IsUnit x⁻¹ :=
  isUnit_iff_exists_inv.mpr ⟨x, by rw [mul_comm, ZMod.mul_inv_of_unit x hx]⟩

lemma cPz_isUnit (r : ZMod p) (a b : Fin 3 → ℕ) (z : ZMod p) :
    IsUnit (cPz p r a b z) := by
  rw [cPz]
  refine IsUnit.mul ?_ ?_
  · exact IsUnit.mul (IsUnit.mul (isUnit_one_add_pmul _) (isUnit_one_add_pmul _))
      (isUnit_one_add_pmul _)
  · exact isUnit_inv_of_unit (IsUnit.mul (IsUnit.mul (isUnit_one_add_pmul _)
      (isUnit_one_add_pmul _)) (isUnit_one_add_pmul _))

lemma norm_chi_cPz (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p) (a b : Fin 3 → ℕ)
    (z : ZMod p) : ‖χ (cPz p r a b z)‖ = 1 := by
  rw [← IsUnit.unit_spec (cPz_isUnit r a b z)]
  exact norm_apply_unit χ _

lemma one_add_psq_pow (m : ℕ) :
    (1 + (p : ZMod (p^3)) ^ 2) ^ m = 1 + (m : ZMod (p^3)) * (p : ZMod (p^3)) ^ 2 := by
  have h4 : (p : ZMod (p^3)) ^ 4 = 0 := by
    rw [show (p : ZMod (p^3)) ^ 4 = (p : ZMod (p^3)) ^ 3 * p by ring, p_cube_eq_zero, zero_mul]
  induction m with
  | zero => simp
  | succ n ih =>
      have hstep : (1 + (p : ZMod (p^3)) ^ 2) ^ (n + 1)
          = (1 + (p : ZMod (p^3)) ^ 2) ^ n * (1 + (p : ZMod (p^3)) ^ 2) :=
        pow_succ _ _
      have h6 : (p : ZMod (p^3)) ^ 6 = 0 := by
        rw [show (p : ZMod (p^3)) ^ 6 = (p : ZMod (p^3)) ^ 4 * (p : ZMod (p^3)) ^ 2 by ring,
          h4, zero_mul]
      rw [hstep, ih]
      push_cast
      ring_nf
      rw [h4]
      ring

lemma chi_one_sub_psq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (p^3)) (hχ : χ.IsPrimitive) (q : ZMod p) :
    χ (1 - (p : ZMod (p^3)) ^ 2 * clift p q)
      = ((χ (((1 + p ^ 2 : ℕ)) : ZMod (p^3))))⁻¹ ^ q.val := by
  set ξ : ℂ := χ (((1 + p ^ 2 : ℕ)) : ZMod (p^3)) with hξdef
  have hroot : IsPrimitiveRoot ξ p := by
    rw [hξdef]
    have h := chi_one_add_primePow_isPrimitiveRoot p 3 hp2 (by norm_num) χ hχ
    simpa using h
  have hξp : ξ ^ p = 1 := hroot.pow_eq_one
  have hξp2 : ξ ^ (p ^ 2) = 1 := by
    have h1 : ξ ^ (p * p) = 1 := by rw [pow_mul, hξp, one_pow]
    rwa [show p ^ 2 = p * p by ring]
  have hle : q.val ≤ p ^ 2 := by
    have h1 : q.val < p := ZMod.val_lt q
    have h2 : p ≤ p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ 2 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by norm_num)
    omega
  have hcast : χ (1 - (p : ZMod (p^3)) ^ 2 * clift p q) = ξ ^ (p ^ 2 - q.val) := by
    rw [hξdef, ← map_pow]
    congr 1
    rw [show (((1 + p ^ 2 : ℕ)) : ZMod (p^3)) = 1 + (p : ZMod (p^3)) ^ 2 by push_cast; ring,
      one_add_psq_pow (p ^ 2 - q.val), clift]
    push_cast
    rw [Nat.cast_sub hle]
    have h4 : (p : ZMod (p^3)) ^ 4 = 0 := by
      rw [show (p : ZMod (p^3)) ^ 4 = (p : ZMod (p^3)) ^ 3 * p by ring, p_cube_eq_zero, zero_mul]
    push_cast
    linear_combination -h4
  have hsplit : ξ ^ (p ^ 2 - q.val) * ξ ^ q.val = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hle, hξp2]
  rw [hcast, inv_pow]
  exact eq_inv_of_mul_eq_one_left hsplit

lemma chi_inv_eq {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ (p^3))
    {y : ZMod (p^3)} (hy : IsUnit y) : χ y⁻¹ = (χ y)⁻¹ := by
  have h : χ y * χ y⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit _ hy, map_one]
  have hχy : χ y ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  calc χ y⁻¹ = χ y⁻¹ * (χ y * (χ y)⁻¹) := by rw [mul_inv_cancel₀ hχy, mul_one]
    _ = (χ y⁻¹ * χ y) * (χ y)⁻¹ := by ring
    _ = (χ y)⁻¹ := by rw [mul_comm (χ y⁻¹) (χ y), h, one_mul]

lemma cocycle_chi {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ (p^3))
    (hχ : χ.IsPrimitive) (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) (z w : ZMod p) :
    χ (cPz p r a b (z + w)) * (χ (cPz p r a b w))⁻¹ * (χ (cPz p r a b z))⁻¹
        * χ (cPz p r a b 0)
      = ((χ (((1 + p ^ 2 : ℕ)) : ZMod (p^3))))⁻¹ ^ ((cDsq p r a - cDsq p r b) * z * w).val := by
  have h := cPz_cocycle r a b hu hv hcrit z w
  have h1 : χ (cPz p r a b (z + w) * (cPz p r a b w)⁻¹ * (cPz p r a b z)⁻¹ * cPz p r a b 0)
      = χ (1 - (p : ZMod (p^3)) ^ 2 * clift p ((cDsq p r a - cDsq p r b) * z * w)) := by
    rw [h]
  have h2 : χ (cPz p r a b (z + w) * (cPz p r a b w)⁻¹ * (cPz p r a b z)⁻¹ * cPz p r a b 0)
      = χ (cPz p r a b (z + w)) * (χ (cPz p r a b w))⁻¹ * (χ (cPz p r a b z))⁻¹
        * χ (cPz p r a b 0) := by
    rw [map_mul, map_mul, map_mul, chi_inv_eq χ (cPz_isUnit r a b w),
      chi_inv_eq χ (cPz_isUnit r a b z)]
  calc χ (cPz p r a b (z + w)) * (χ (cPz p r a b w))⁻¹ * (χ (cPz p r a b z))⁻¹
        * χ (cPz p r a b 0)
      = χ (cPz p r a b (z + w) * (cPz p r a b w)⁻¹ * (cPz p r a b z)⁻¹ * cPz p r a b 0) := h2.symm
    _ = χ (1 - (p : ZMod (p^3)) ^ 2 * clift p ((cDsq p r a - cDsq p r b) * z * w)) := h1
    _ = ((χ (((1 + p ^ 2 : ℕ)) : ZMod (p^3))))⁻¹ ^ ((cDsq p r a - cDsq p r b) * z * w).val :=
        chi_one_sub_psq hp2 χ hχ _

/-! ## The summand decomposition and the second moment -/

/-- The correlation summand at the point `r + p z`. -/
noncomputable def cSummand (p : ℕ) (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p)
    (a b : Fin 3 → ℕ) (z : ZMod p) : ℂ :=
  χ (∏ l : Fin 3, cPt p r (a l) z) * (starRingEnd ℂ) (χ (∏ l : Fin 3, cPt p r (b l) z))

lemma cSummand_eq (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0) (z : ZMod p) :
    cSummand p χ r a b z
      = χ ((∏ l : Fin 3, cUnit p r (a l)) * ((∏ l : Fin 3, cUnit p r (b l)))⁻¹)
        * χ (cPz p r a b z) := by
  have hA : (∏ l : Fin 3, cPt p r (a l) z)
      = (∏ l : Fin 3, cUnit p r (a l))
        * (∏ l : Fin 3, (1 + (p : ZMod (p^3)) * cAlpha p r (a l) z)) := by
    rw [Finset.prod_congr rfl (fun l _ => cPt_eq (r := r) (u := a l) (z := z) (hu := hu l)),
      Finset.prod_mul_distrib]
  have hB : (∏ l : Fin 3, cPt p r (b l) z)
      = (∏ l : Fin 3, cUnit p r (b l))
        * (∏ l : Fin 3, (1 + (p : ZMod (p^3)) * cAlpha p r (b l) z)) := by
    rw [Finset.prod_congr rfl (fun l _ => cPt_eq (r := r) (u := b l) (z := z) (hu := hv l)),
      Finset.prod_mul_distrib]
  have hUnitA : IsUnit (∏ l : Fin 3, cUnit p r (a l)) :=
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      (fun l _ => cUnit_isUnit r (a l) (hu l))
  have hUnitB : IsUnit (∏ l : Fin 3, cUnit p r (b l)) :=
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      (fun l _ => cUnit_isUnit r (b l) (hv l))
  have hUnitPa : IsUnit (∏ l : Fin 3, (1 + (p : ZMod (p^3)) * cAlpha p r (a l) z)) :=
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      (fun l _ => isUnit_one_add_pmul _)
  have hUnitPb : IsUnit (∏ l : Fin 3, (1 + (p : ZMod (p^3)) * cAlpha p r (b l) z)) :=
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      (fun l _ => isUnit_one_add_pmul _)
  have hcpz : cPz p r a b z
      = (∏ l : Fin 3, (1 + (p : ZMod (p^3)) * cAlpha p r (a l) z))
        * ((∏ l : Fin 3, (1 + (p : ZMod (p^3)) * cAlpha p r (b l) z)))⁻¹ := by
    rw [cPz, Fin.prod_univ_three, Fin.prod_univ_three]
  have h1 : χ (∏ l : Fin 3, cPt p r (a l) z)
      = χ (∏ l : Fin 3, cUnit p r (a l))
        * χ (∏ l : Fin 3, (1 + (p : ZMod (p^3)) * cAlpha p r (a l) z)) := by
    rw [hA, map_mul]
  have h2 : (starRingEnd ℂ) (χ (∏ l : Fin 3, cPt p r (b l) z))
      = (starRingEnd ℂ) (χ (∏ l : Fin 3, cUnit p r (b l)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (1 + (p : ZMod (p^3)) * cAlpha p r (b l) z))) := by
    rw [hB, map_mul, map_mul]
  rw [cSummand, h1, h2, star_chi_eq_chi_inv χ _ hUnitB, star_chi_eq_chi_inv χ _ hUnitPb,
    hcpz, map_mul, map_mul]
  ring

lemma sum_zmod_eta_pow {p : ℕ} [Fact p.Prime] {η : ℂ} (hη : IsPrimitiveRoot η p) (a : ZMod p) :
    (∑ z : ZMod p, η ^ ((a * z).val)) = if a = 0 then (p : ℂ) else 0 := by
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    simp only [zero_mul, ZMod.val_zero, pow_zero, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
  · rw [if_neg ha]
    have hηp : η ^ p = 1 := hη.pow_eq_one
    have hterm : ∀ z : ZMod p, η ^ ((a * z).val) = (η ^ a.val) ^ z.val := by
      intro z
      rw [ZMod.val_mul, ← pow_eq_pow_mod (a.val * z.val) hηp, pow_mul]
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    have hζ : (η ^ a.val) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hηp, one_pow]
    rw [sum_zmod_pow_eq p hζ]
    have hne : η ^ a.val ≠ 1 := by
      intro h1
      have hdvd : p ∣ a.val := (hη.pow_eq_one_iff_dvd a.val).mp h1
      have hlt : a.val < p := ZMod.val_lt a
      have hzero : a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      exact ha (ZMod.val_eq_zero a |>.mp hzero)
    rw [if_neg hne]

lemma cSummand_sum_bound {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ (p^3))
    (hχ : χ.IsPrimitive) (r : ZMod p) (a b : Fin 3 → ℕ)
    (hu : ∀ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) ≠ 0)
    (hv : ∀ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹))
    (hnd : cDsq p r a ≠ cDsq p r b) :
    ‖∑ z : ZMod p, cSummand p χ r a b z‖ ≤ 2 * Real.sqrt p := by
  set η : ℂ := ((χ (((1 + p ^ 2 : ℕ)) : ZMod (p^3))))⁻¹ with hηdef
  have hηroot : IsPrimitiveRoot η p := by
    rw [hηdef]
    have h := chi_one_add_primePow_isPrimitiveRoot p 3 hp2 (by norm_num) χ hχ
    simpa using h.inv
  have hcocy : ∀ z w : ZMod p, χ (cPz p r a b (z + w)) * (χ (cPz p r a b w))⁻¹
      * (χ (cPz p r a b z))⁻¹ * χ (cPz p r a b 0)
      = η ^ ((cDsq p r a - cDsq p r b) * z * w).val := by
    intro z w
    rw [hηdef]
    exact cocycle_chi hp2 χ hχ r a b hu hv hcrit z w
  have hne0 : ∀ z : ZMod p, χ (cPz p r a b z) ≠ 0 := by
    intro z hzero
    have h := norm_chi_cPz χ r a b z
    rw [hzero, norm_zero] at h
    exact one_ne_zero h.symm
  -- the shifted cocycle
  have hshift : ∀ z w : ZMod p, χ (cPz p r a b (z + w)) * (χ (cPz p r a b z))⁻¹
      = η ^ ((cDsq p r a - cDsq p r b) * w * z).val
        * (χ (cPz p r a b w) * (χ (cPz p r a b 0))⁻¹) := by
    intro z w
    have h := hcocy z w
    have h1 : χ (cPz p r a b (z + w)) * (χ (cPz p r a b z))⁻¹
        * (χ (cPz p r a b w) * (χ (cPz p r a b 0))⁻¹)⁻¹
        = η ^ ((cDsq p r a - cDsq p r b) * z * w).val := by
      rw [show χ (cPz p r a b (z + w)) * (χ (cPz p r a b z))⁻¹
            * (χ (cPz p r a b w) * (χ (cPz p r a b 0))⁻¹)⁻¹
          = χ (cPz p r a b (z + w)) * (χ (cPz p r a b w))⁻¹ * (χ (cPz p r a b z))⁻¹
            * χ (cPz p r a b 0) by
        rw [mul_inv_rev, inv_inv]; ring]
      exact h
    have hne : (χ (cPz p r a b w) * (χ (cPz p r a b 0))⁻¹) ≠ 0 :=
      mul_ne_zero (hne0 w) (inv_ne_zero (hne0 0))
    have hcomm : ((cDsq p r a - cDsq p r b) * z * w).val
        = ((cDsq p r a - cDsq p r b) * w * z).val := by
      congr 1; ring
    calc χ (cPz p r a b (z + w)) * (χ (cPz p r a b z))⁻¹
        = (χ (cPz p r a b (z + w)) * (χ (cPz p r a b z))⁻¹
            * (χ (cPz p r a b w) * (χ (cPz p r a b 0))⁻¹)⁻¹)
          * (χ (cPz p r a b w) * (χ (cPz p r a b 0))⁻¹) := by
          rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
      _ = η ^ ((cDsq p r a - cDsq p r b) * z * w).val
          * (χ (cPz p r a b w) * (χ (cPz p r a b 0))⁻¹) := by rw [h1]
      _ = η ^ ((cDsq p r a - cDsq p r b) * w * z).val
          * (χ (cPz p r a b w) * (χ (cPz p r a b 0))⁻¹) := by rw [hcomm]
  -- the second moment
  have hS : ‖∑ z : ZMod p, χ (cPz p r a b z)‖ ^ 2 = (p : ℝ) := by
    set S : ℂ := ∑ z : ZMod p, χ (cPz p r a b z) with hSdef
    have hconj : (starRingEnd ℂ) S = ∑ z : ZMod p, (χ (cPz p r a b z))⁻¹ := by
      rw [hSdef, map_sum]
      exact Finset.sum_congr rfl (fun z _ => (Complex.inv_eq_conj (norm_chi_cPz χ r a b z)).symm)
    have hdouble : (starRingEnd ℂ) S * S
        = ∑ z : ZMod p, ∑ w : ZMod p,
            χ (cPz p r a b (z + w)) * (χ (cPz p r a b z))⁻¹ := by
      rw [hconj, hSdef, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (-z))
        (fun z' => (χ (cPz p r a b z))⁻¹ * χ (cPz p r a b z'))
        (fun w => χ (cPz p r a b (z + w)) * (χ (cPz p r a b z))⁻¹) (fun z' => ?_)
      rw [Equiv.coe_addRight, show z + (z' + -z) = z' by ring]
      ring
    have hmain : (starRingEnd ℂ) S * S = (p : ℂ) := by
      rw [hdouble]
      have hstep : (∑ z : ZMod p, ∑ w : ZMod p,
              χ (cPz p r a b (z + w)) * (χ (cPz p r a b z))⁻¹)
          = ∑ w : ZMod p, (χ (cPz p r a b w) * (χ (cPz p r a b 0))⁻¹)
              * ∑ z : ZMod p, η ^ ((cDsq p r a - cDsq p r b) * w * z).val := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.sum_congr rfl (fun z _ => hshift z w), ← Finset.sum_mul, mul_comm]
      rw [hstep]
      rw [Finset.sum_congr rfl (fun w _ => by
        rw [sum_zmod_eta_pow hηroot ((cDsq p r a - cDsq p r b) * w)])]
      rw [Finset.sum_eq_single 0]
      · rw [if_pos (by simp), mul_inv_cancel₀ (hne0 0), one_mul]
      · intro w _ hw
        rw [if_neg, mul_zero]
        intro hc
        exact hw (mul_eq_zero.mp hc |>.resolve_left (sub_ne_zero.mpr hnd))
      · intro h
        exact absurd (Finset.mem_univ 0) h
    have hnormSq : Complex.normSq S = (p : ℝ) := by
      have h1 : (Complex.normSq S : ℂ) = (p : ℂ) := by
        rw [← Complex.mul_conj, mul_comm]; exact hmain
      exact_mod_cast h1
    rw [hSdef, ← Complex.normSq_eq_norm_sq]
    exact hnormSq
  -- the constant factor
  have hconst : ‖χ ((∏ l : Fin 3, cUnit p r (a l))
      * ((∏ l : Fin 3, cUnit p r (b l)))⁻¹)‖ = 1 := by
    have h1 : IsUnit ((∏ l : Fin 3, cUnit p r (a l))
        * ((∏ l : Fin 3, cUnit p r (b l)))⁻¹) :=
      IsUnit.mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        (fun l _ => cUnit_isUnit r (a l) (hu l)))
        (isUnit_inv_of_unit (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul)
          isUnit_one (fun l _ => cUnit_isUnit r (b l) (hv l))))
    rw [← IsUnit.unit_spec h1]
    exact norm_apply_unit χ _
  have hdecomp : (∑ z : ZMod p, cSummand p χ r a b z)
      = χ ((∏ l : Fin 3, cUnit p r (a l)) * ((∏ l : Fin 3, cUnit p r (b l)))⁻¹)
        * ∑ z : ZMod p, χ (cPz p r a b z) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => cSummand_eq χ r a b hu hv z)
  rw [hdecomp, norm_mul, hconst, one_mul]
  have hnorm : ‖∑ z : ZMod p, χ (cPz p r a b z)‖ = Real.sqrt p :=
    ((Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg p) (norm_nonneg _)).mpr hS.symm).symm
  rw [hnorm]
  have hp0 : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
  linarith

/-! ## The inner sum in the form of `charCorrelation6_criticalClasses` -/

/-- The inner correlation summand, as a function of the digit `n`. -/
noncomputable def cSummandNat (p : ℕ) (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p)
    (a b : Fin 3 → ℕ) (n : ℕ) : ℂ :=
  χ (∏ l : Fin 3, ((((r.val + p * n + a l : ℕ)) : ZMod (p^3))))
    * (starRingEnd ℂ) (χ (∏ l : Fin 3, ((((r.val + p * n + b l : ℕ)) : ZMod (p^3)))))

lemma cSummand_eq_nat (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p) (a b : Fin 3 → ℕ)
    (z : ZMod p) :
    cSummand p χ r a b z = cSummandNat p χ r a b z.val := by
  simp only [cSummand, cSummandNat, cPt, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]

lemma criticalArg_eq (r : ZMod p) (u : ℕ) (z : ZMod (p ^ (3 - 2))) :
    (((r.val : ℕ) : ZMod (p^3)) + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3))
        + ((u : ℕ) : ZMod (p^3)))
      = ((((r.val + p * z.val + u : ℕ)) : ZMod (p^3))) := by
  push_cast
  ring

lemma criticalSummand_eq_nat (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p) (a b : Fin 3 → ℕ)
    (z : ZMod (p ^ (3 - 2))) :
    χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3)) + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3))
        + ((a l : ℕ) : ZMod (p^3))))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
        + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))
      = cSummandNat p χ r a b z.val := by
  simp only [cSummandNat]
  rw [Finset.prod_congr rfl (fun l _ => criticalArg_eq (p := p) r (a l) z),
    Finset.prod_congr rfl (fun l _ => criticalArg_eq (p := p) r (b l) z)]

lemma sum_zmod_val_eq {M : Type*} [AddCommMonoid M] (q : ℕ) [NeZero q] (f : ℕ → M) :
    (∑ z : ZMod q, f z.val) = ∑ i ∈ Finset.range q, f i := by
  have h1 : (∑ z : ZMod q, f z.val) = ∑ z : ZMod q, (fun w : ZMod q => f w.val) z := rfl
  rw [h1, CaseC.zmod_sum_univ_eq_sum_range' q (fun w : ZMod q => f w.val)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]

lemma sum_val_zmod_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ z : ZMod (p ^ (3 - 2)), f z.val) = ∑ z : ZMod p, f z.val := by
  haveI : NeZero (p ^ (3 - 2)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [sum_zmod_val_eq (p ^ (3 - 2)) f, sum_zmod_val_eq p f]
  rw [show p ^ (3 - 2) = p by norm_num]

lemma sum_criticalSummand_eq (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p) (a b : Fin 3 → ℕ) :
    (∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
          + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
          + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3))))))
      = ∑ z : ZMod p, cSummand p χ r a b z := by
  rw [show (∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
          + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
          + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3))))))
      = ∑ z : ZMod (p ^ (3 - 2)), cSummandNat p χ r a b z.val from
    Finset.sum_congr rfl (fun z _ => criticalSummand_eq_nat χ r a b z)]
  rw [sum_val_zmod_eq (p := p) (fun n => cSummandNat p χ r a b n)]
  exact Finset.sum_congr rfl (fun z _ => (cSummand_eq_nat χ r a b z).symm)

/-! ## Vanishing at the bad classes and the trivial bound -/

lemma cSummandNat_eq_zero_of_bad (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p)
    (a b : Fin 3 → ℕ) (n : ℕ)
    (hbad : (∃ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) = 0)
      ∨ (∃ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) = 0)) :
    cSummandNat p χ r a b n = 0 := by
  rcases hbad with ⟨l, hl⟩ | ⟨l, hl⟩
  · have hfac : ¬ IsUnit ((((r.val + p * n + a l : ℕ)) : ZMod (p^3))) := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) (by norm_num : 0 < 3)]
      intro hndvd
      apply hndvd
      have h0 : ((r.val + p * n + a l : ℕ) : ZMod p) = 0 := by
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero, hl]
      exact (ZMod.natCast_eq_zero_iff _ p).mp h0
    have hprod : ¬ IsUnit (∏ l : Fin 3, ((((r.val + p * n + a l : ℕ)) : ZMod (p^3)))) := by
      intro hcon
      have hsplit := Finset.prod_erase_mul (Finset.univ : Finset (Fin 3))
        (fun l' : Fin 3 => ((((r.val + p * n + a l' : ℕ)) : ZMod (p^3)))) (Finset.mem_univ l)
      rw [← hsplit] at hcon
      exact hfac (IsUnit.mul_iff.mp hcon).2
    rw [cSummandNat, MulChar.map_nonunit χ hprod, zero_mul]
  · have hfac : ¬ IsUnit ((((r.val + p * n + b l : ℕ)) : ZMod (p^3))) := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) (by norm_num : 0 < 3)]
      intro hndvd
      apply hndvd
      have h0 : ((r.val + p * n + b l : ℕ) : ZMod p) = 0 := by
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero, hl]
      exact (ZMod.natCast_eq_zero_iff _ p).mp h0
    have hprod : ¬ IsUnit (∏ l : Fin 3, ((((r.val + p * n + b l : ℕ)) : ZMod (p^3)))) := by
      intro hcon
      have hsplit := Finset.prod_erase_mul (Finset.univ : Finset (Fin 3))
        (fun l' : Fin 3 => ((((r.val + p * n + b l' : ℕ)) : ZMod (p^3)))) (Finset.mem_univ l)
      rw [← hsplit] at hcon
      exact hfac (IsUnit.mul_iff.mp hcon).2
    rw [cSummandNat, MulChar.map_nonunit χ hprod, map_zero, mul_zero]

lemma cSummand_eq_zero_of_bad (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p) (a b : Fin 3 → ℕ)
    (z : ZMod p)
    (hbad : (∃ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) = 0)
      ∨ (∃ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) = 0)) :
    cSummand p χ r a b z = 0 := by
  rw [cSummand_eq_nat, cSummandNat_eq_zero_of_bad χ r a b z.val hbad]

lemma sum_cSummand_norm_le (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p) (a b : Fin 3 → ℕ) :
    ‖∑ z : ZMod p, cSummand p χ r a b z‖ ≤ (p : ℝ) := by
  calc ‖∑ z : ZMod p, cSummand p χ r a b z‖
      ≤ ∑ z : ZMod p, ‖cSummand p χ r a b z‖ := norm_sum_le _ _
    _ ≤ ∑ _z : ZMod p, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        rw [cSummand_eq_nat, cSummandNat, norm_mul, Complex.norm_conj]
        have h1 := DirichletCharacter.norm_le_one χ (∏ l : Fin 3, ((((r.val + p * z.val + a l : ℕ)) : ZMod (p^3))))
        have h2 := DirichletCharacter.norm_le_one χ (∏ l : Fin 3, ((((r.val + p * z.val + b l : ℕ)) : ZMod (p^3))))
        nlinarith [norm_nonneg (χ (∏ l : Fin 3, ((((r.val + p * z.val + a l : ℕ)) : ZMod (p^3))))),
          norm_nonneg (χ (∏ l : Fin 3, ((((r.val + p * z.val + b l : ℕ)) : ZMod (p^3)))))]
    _ = (p : ℝ) := by
        simp [Finset.sum_const, ZMod.card]

/-! ## The critical polynomial and its root count -/

/-- The monic cubic `∏_l (X + a_l)` over `ZMod p`. -/
noncomputable def cA (p : ℕ) (a : Fin 3 → ℕ) : Polynomial (ZMod p) :=
  ∏ l : Fin 3, (Polynomial.X + Polynomial.C (((a l : ℕ) : ZMod p)))

/-- The critical polynomial `A' * B - B' * A`. -/
noncomputable def cH (p : ℕ) (a b : Fin 3 → ℕ) : Polynomial (ZMod p) :=
  Polynomial.derivative (cA p a) * cA p b - Polynomial.derivative (cA p b) * cA p a

lemma deriv_prod_three (r : ZMod p) (c : Fin 3 → ZMod p) (hc : ∀ l, r + c l ≠ 0) :
    (Polynomial.derivative (∏ l : Fin 3, (Polynomial.X + Polynomial.C (c l)))).eval r
      = (∏ l : Fin 3, (r + c l)) * (∑ l : Fin 3, (r + c l)⁻¹) := by
  simp only [Fin.prod_univ_three, Fin.sum_univ_three]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, add_zero, mul_one, one_mul]
  field_simp [hc 0, hc 1, hc 2]

lemma crit_imp_H_zero (r : ZMod p) (a b : Fin 3 → ℕ)
    (ha : ∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
    (hb : ∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)) :
    (cH p a b).eval r = 0 := by
  rw [cH, cA, cA, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
    deriv_prod_three (p := p) r (fun l => ((a l : ℕ) : ZMod p)) ha,
    deriv_prod_three (p := p) r (fun l => ((b l : ℕ) : ZMod p)) hb, hcrit]
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  ring

lemma natDegree_cA_le (a : Fin 3 → ℕ) : (cA p a).natDegree ≤ 3 := by
  rw [cA, Fin.prod_univ_three]
  compute_degree!

lemma natDegree_cH_le (a b : Fin 3 → ℕ) : (cH p a b).natDegree ≤ 6 := by
  rw [cH]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    have h1 : (Polynomial.derivative (cA p a)).natDegree ≤ (cA p a).natDegree :=
      le_trans (Polynomial.natDegree_derivative_le _) (Nat.sub_le _ _)
    have h2 := natDegree_cA_le (p := p) a
    have h3 := natDegree_cA_le (p := p) b
    omega
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    have h1 : (Polynomial.derivative (cA p b)).natDegree ≤ (cA p b).natDegree :=
      le_trans (Polynomial.natDegree_derivative_le _) (Nat.sub_le _ _)
    have h2 := natDegree_cA_le (p := p) a
    have h3 := natDegree_cA_le (p := p) b
    omega

lemma card_roots_eval_le (H : Polynomial (ZMod p)) (hH : H ≠ 0) :
    ((Finset.univ : Finset (ZMod p)).filter (fun r => H.eval r = 0)).card ≤ H.natDegree := by
  calc ((Finset.univ : Finset (ZMod p)).filter (fun r => H.eval r = 0)).card
      ≤ H.roots.toFinset.card := by
        refine Finset.card_le_card ?_
        intro r hr
        rw [Finset.mem_filter] at hr
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hH]
        exact hr.2
    _ ≤ H.roots.card := Multiset.toFinset_card_le _
    _ ≤ H.natDegree := Polynomial.card_roots' H

lemma crit_nonbad_card_le (a b : Fin 3 → ℕ) (hH : cH p a b ≠ 0) :
    ((Finset.univ : Finset (ZMod p)).filter (fun r => (∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
        ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
        ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
          = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹))).card ≤ 6 := by
  calc ((Finset.univ : Finset (ZMod p)).filter (fun r => (∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
        ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
        ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
          = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹))).card
      ≤ ((Finset.univ : Finset (ZMod p)).filter (fun r => (cH p a b).eval r = 0)).card := by
        refine Finset.card_le_card ?_
        intro r hr
        rw [Finset.mem_filter] at hr ⊢
        exact ⟨Finset.mem_univ r, crit_imp_H_zero r a b hr.2.1 hr.2.2.1 hr.2.2.2⟩
    _ ≤ (cH p a b).natDegree := card_roots_eval_le _ hH
    _ ≤ 6 := natDegree_cH_le a b

/-! ## The doubly degenerate case: the gcd weight is at least `p` -/

lemma cA_eval_eq_zero_iff (a : Fin 3 → ℕ) (x : ZMod p) :
    (cA p a).eval x = 0 ↔ ∃ l : Fin 3, x + ((a l : ℕ) : ZMod p) = 0 := by
  rw [cA, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨l, _, hl⟩
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hl
    exact ⟨l, by linear_combination hl⟩
  · rintro ⟨l, hl⟩
    exact ⟨l, Finset.mem_univ l, by
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; linear_combination hl⟩

lemma cA_eval_neg (a : Fin 3 → ℕ) (l0 : Fin 3) :
    (cA p a).eval (-(((a l0 : ℕ) : ZMod p))) = 0 := by
  rw [cA_eval_eq_zero_iff]
  exact ⟨l0, by ring⟩

lemma cA_deriv_eval_neg (a : Fin 3 → ℕ) (l0 : Fin 3) :
    (Polynomial.derivative (cA p a)).eval (-(((a l0 : ℕ) : ZMod p)))
      = ∏ l ∈ Finset.univ.erase l0, (-(((a l0 : ℕ) : ZMod p)) + ((a l : ℕ) : ZMod p)) := by
  have hfact : (∏ l : Fin 3, (Polynomial.X + Polynomial.C (((a l : ℕ) : ZMod p))))
      = (∏ l ∈ Finset.univ.erase l0, (Polynomial.X + Polynomial.C (((a l : ℕ) : ZMod p))))
        * (Polynomial.X + Polynomial.C (((a l0 : ℕ) : ZMod p))) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ l0)).symm
  rw [cA, hfact]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_X,
    Polynomial.derivative_C, add_zero, mul_one, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_prod,
    neg_add_cancel, mul_zero, zero_add, one_mul]

lemma exists_other_root_of_deriv_zero (a : Fin 3 → ℕ) (l0 : Fin 3)
    (h : (Polynomial.derivative (cA p a)).eval (-(((a l0 : ℕ) : ZMod p))) = 0) :
    ∃ l : Fin 3, l ≠ l0 ∧ ((a l : ℕ) : ZMod p) = ((a l0 : ℕ) : ZMod p) := by
  rw [cA_deriv_eval_neg] at h
  obtain ⟨l, hl, hl0⟩ := Finset.prod_eq_zero_iff.mp h
  rw [Finset.mem_erase] at hl
  exact ⟨l, hl.1, by linear_combination hl0⟩

/-- **The coincidence alternative at a root of `A`.** -/
lemma coincidence_a (a b : Fin 3 → ℕ) (l0 : Fin 3) (hH : cH p a b = 0) :
    (∃ l : Fin 3, l ≠ l0 ∧ ((a l : ℕ) : ZMod p) = ((a l0 : ℕ) : ZMod p))
      ∨ (∃ l : Fin 3, ((b l : ℕ) : ZMod p) = ((a l0 : ℕ) : ZMod p)) := by
  have hx : (cH p a b).eval (-(((a l0 : ℕ) : ZMod p))) = 0 := by
    rw [hH]; exact Polynomial.eval_zero
  have hAB : (Polynomial.derivative (cA p a)).eval (-(((a l0 : ℕ) : ZMod p)))
      * (cA p b).eval (-(((a l0 : ℕ) : ZMod p))) = 0 := by
    rw [cH, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, cA_eval_neg a l0,
      mul_zero, sub_zero] at hx
    exact hx
  rcases mul_eq_zero.mp hAB with h1 | h1
  · exact Or.inl (exists_other_root_of_deriv_zero a l0 h1)
  · exact Or.inr (by obtain ⟨l, hl⟩ := (cA_eval_eq_zero_iff b _).mp h1; exact ⟨l, by linear_combination hl⟩)

/-- **The coincidence alternative at a root of `B`.** -/
lemma coincidence_b (a b : Fin 3 → ℕ) (l0 : Fin 3) (hH : cH p a b = 0) :
    (∃ l : Fin 3, ((a l : ℕ) : ZMod p) = ((b l0 : ℕ) : ZMod p))
      ∨ (∃ l : Fin 3, l ≠ l0 ∧ ((b l : ℕ) : ZMod p) = ((b l0 : ℕ) : ZMod p)) := by
  have hx : (cH p a b).eval (-(((b l0 : ℕ) : ZMod p))) = 0 := by
    rw [hH]; exact Polynomial.eval_zero
  rw [cH, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, cA_eval_neg b l0,
    mul_zero, zero_sub, neg_eq_zero] at hx
  rcases mul_eq_zero.mp hx with h1 | h1
  · exact Or.inr (exists_other_root_of_deriv_zero b l0 h1)
  · exact Or.inl (by obtain ⟨l, hl⟩ := (cA_eval_eq_zero_iff a _).mp h1; exact ⟨l, by linear_combination hl⟩)

/-- The index of the `a`-part of the six-tuple. -/
def idxA (l : Fin 3) : Fin 6 := ⟨l.val, by omega⟩

/-- The index of the `b`-part of the six-tuple. -/
def idxB (l : Fin 3) : Fin 6 := ⟨3 + l.val, by omega⟩

lemma vec6_idxA (a b : Fin 3 → ℕ) (l : Fin 3) :
    ![a 0, a 1, a 2, b 0, b 1, b 2] (idxA l) = a l := by
  fin_cases l <;> rfl

lemma vec6_idxB (a b : Fin 3 → ℕ) (l : Fin 3) :
    ![a 0, a 1, a 2, b 0, b 1, b 2] (idxB l) = b l := by
  fin_cases l <;> rfl

lemma eq_idxA_or_idxB (i : Fin 6) : (∃ l : Fin 3, i = idxA l) ∨ (∃ l : Fin 3, i = idxB l) := by
  fin_cases i
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inl ⟨2, rfl⟩
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨1, rfl⟩
  · exact Or.inr ⟨2, rfl⟩

lemma exists_coincidence_of_H_zero (a b : Fin 3 → ℕ) (i : Fin 6) (hH : cH p a b = 0) :
    ∃ j : Fin 6, j ≠ i ∧ ((![a 0, a 1, a 2, b 0, b 1, b 2] j : ℕ) : ZMod p)
      = ((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℕ) : ZMod p) := by
  rcases eq_idxA_or_idxB i with ⟨l0, rfl⟩ | ⟨l0, rfl⟩
  · rcases coincidence_a a b l0 hH with ⟨l, hlne, hle⟩ | ⟨l, hle⟩
    · refine ⟨idxA l, ?_, ?_⟩
      · intro hcon
        exact hlne (Fin.ext (by simpa [idxA] using congrArg Fin.val hcon))
      · simpa [vec6_idxA] using hle
    · refine ⟨idxB l, ?_, ?_⟩
      · intro hcon
        have h1 := congrArg Fin.val hcon
        simp only [idxA, idxB, Fin.val_mk] at h1
        omega
      · simpa [vec6_idxA, vec6_idxB] using hle
  · rcases coincidence_b a b l0 hH with ⟨l, hle⟩ | ⟨l, hlne, hle⟩
    · refine ⟨idxA l, ?_, ?_⟩
      · intro hcon
        have h1 := congrArg Fin.val hcon
        simp only [idxA, idxB, Fin.val_mk] at h1
        omega
      · simpa [vec6_idxA, vec6_idxB] using hle
    · refine ⟨idxB l, ?_, ?_⟩
      · intro hcon
        exact hlne (Fin.ext (by simpa [idxB] using congrArg Fin.val hcon))
      · simpa [vec6_idxB] using hle

lemma prod_gcd_ge_of_H_zero (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → (![a 0, a 1, a 2, b 0, b 1, b 2] i)
        ≠ (![a 0, a 1, a 2, b 0, b 1, b 2] j))
    (hH : cH p a b = 0) :
    p ≤ ∏ j ∈ Finset.univ.erase i,
          Nat.gcd (p ^ 3) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
            - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) := by
  obtain ⟨j, hjne, hjmod⟩ := exists_coincidence_of_H_zero a b i hH
  have hjdvd : p ∣ (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
      - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) := by
    have h2 : (![a 0, a 1, a 2, b 0, b 1, b 2] j) ≡ (![a 0, a 1, a 2, b 0, b 1, b 2] i) [MOD p] :=
      (ZMod.natCast_eq_natCast_iff _ _ p).mp hjmod
    have h4 : (p : ℤ) ∣ (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℕ) : ℤ)
        - ((![a 0, a 1, a 2, b 0, b 1, b 2] j : ℕ) : ℤ)) := Nat.ModEq.dvd h2
    obtain ⟨k, hk⟩ := h4
    exact ⟨k.natAbs, by rw [hk, Int.natAbs_mul, Int.natAbs_natCast]⟩
  have hgcd : p ≤ Nat.gcd (p ^ 3) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
      - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) := by
    have h1 : p ∣ p ^ 3 := ⟨p ^ 2, by ring⟩
    have h2 : p ∣ Nat.gcd (p ^ 3) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
        - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) := Nat.dvd_gcd h1 hjdvd
    have h3 : 0 < Nat.gcd (p ^ 3) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
        - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) :=
      Nat.gcd_pos_of_pos_left _ (pow_pos (Fact.out : p.Prime).pos 3)
    exact Nat.le_of_dvd h3 h2
  refine le_trans hgcd (Finset.single_le_prod'
    (f := fun j => Nat.gcd (p ^ 3) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
      - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs))
    (fun j _ => Nat.succ_le_iff.mpr (Nat.gcd_pos_of_pos_left _
      (pow_pos (Fact.out : p.Prime).pos 3))) (Finset.mem_erase.mpr ⟨hjne, Finset.mem_univ j⟩))

/-! ## The local bound on the critical classes and the main theorem -/

lemma sum_ite_pair {p : ℕ} [NeZero p] (P Q : ZMod p → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, Q x → ¬ P x) (c d : ℝ) :
    (∑ x : ZMod p, (if P x then c else if Q x then d else 0))
      = c * ((Finset.univ.filter P).card : ℝ) + d * ((Finset.univ.filter Q).card : ℝ) := by
  have hQ : (Finset.univ.filter (fun x => ¬ P x)).filter Q = Finset.univ.filter Q := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro x _
    constructor
    · exact fun hx => hx.2
    · intro hx; exact ⟨h x hx, hx⟩
  rw [Finset.sum_ite, Finset.sum_ite, hQ, Finset.sum_const, Finset.sum_const,
    Finset.sum_const_zero, add_zero, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- The bad predicate for a residue class. -/
def cBad (p : ℕ) (r : ZMod p) (a b : Fin 3 → ℕ) : Prop :=
  (∃ l : Fin 3, (r + ((a l : ℕ) : ZMod p)) = 0)
    ∨ (∃ l : Fin 3, (r + ((b l : ℕ) : ZMod p)) = 0)

lemma inner_eq_zero_of_bad (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p) (a b : Fin 3 → ℕ)
    (hbad : cBad p r a b) :
    (∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
          + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
          + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))) = 0 := by
  rw [sum_criticalSummand_eq]
  exact Finset.sum_eq_zero (fun z _ => cSummand_eq_zero_of_bad χ r a b z hbad)

lemma inner_norm_le_p (χ : DirichletCharacter ℂ (p^3)) (r : ZMod p) (a b : Fin 3 → ℕ) :
    ‖∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
          + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
          + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))‖
      ≤ (p : ℝ) := by
  rw [sum_criticalSummand_eq]
  exact sum_cSummand_norm_le χ r a b

lemma inner_norm_le_of_nondeg {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (p^3)) (hχ : χ.IsPrimitive) (r : ZMod p) (a b : Fin 3 → ℕ)
    (ha : ∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
    (hb : ∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
      = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹))
    (hnd : (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
      ≠ (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2)) :
    ‖∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
          + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
          + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))‖
      ≤ 2 * Real.sqrt p := by
  rw [sum_criticalSummand_eq]
  refine cSummand_sum_bound hp2 χ hχ r a b ha hb hcrit ?_
  intro hcon
  refine hnd (sub_eq_zero.mp ?_)
  have h := cDsq_congr (p := p) r a b
  rw [hcon, sub_self] at h
  exact h.symm

lemma critical_sum_bound {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ (p^3))
    (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) :
    ‖∑ r : ZMod p, (if (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
        - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
      then ∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
            + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
            + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))
      else 0)‖
      ≤ 2 * Real.sqrt p
          * ((Finset.univ.filter (fun r : ZMod p => (∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
              ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
              ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
                  - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
              ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
                  ≠ (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))).card : ℝ)
        + (p : ℝ)
          * ((Finset.univ.filter (fun r : ZMod p => (∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
              ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
              ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
                  - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
              ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
                  = (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))).card : ℝ) := by
  have hpoint : ∀ r : ZMod p,
      ‖if (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
        then ∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
              + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
              + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))
        else 0‖
      ≤ (if ((∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
              ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
              ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
                  - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
              ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
                  ≠ (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))
        then 2 * Real.sqrt p
        else if ((∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
              ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
              ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
                  - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
              ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
                  = (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))
        then (p : ℝ) else 0) := by
    intro r
    by_cases hbad : cBad p r a b
    · have hnb : ¬ ((∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
          ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)) := by
        rcases hbad with ⟨l, hl⟩ | ⟨l, hl⟩
        · intro h; exact h.1 l hl
        · intro h; exact h.2 l hl
      have hz : (if (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
            - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
          then ∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
                + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
              * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
                + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))
          else 0) = 0 := by
        rw [inner_eq_zero_of_bad χ r a b hbad]
        split <;> rfl
      rw [hz, norm_zero,
        if_neg (fun h => hnb ⟨h.1, h.2.1⟩), if_neg (fun h => hnb ⟨h.1, h.2.1⟩)]
    · simp only [cBad] at hbad
      push_neg at hbad
      by_cases hcrit : (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
      · by_cases hdg : (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
            = (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2)
        · rw [if_pos hcrit, if_neg (fun h => h.2.2.2 hdg),
            if_pos ⟨hbad.1, hbad.2, hcrit, hdg⟩]
          exact inner_norm_le_p χ r a b
        · rw [if_pos hcrit, if_pos ⟨hbad.1, hbad.2, hcrit, hdg⟩]
          exact inner_norm_le_of_nondeg hp2 χ hχ r a b hbad.1 hbad.2 (sub_eq_zero.mp hcrit) hdg
      · rw [if_neg hcrit, if_neg (fun h => hcrit h.2.2.1), if_neg (fun h => hcrit h.2.2.1)]
        simp
  have hcond : ∀ r : ZMod p,
      ((∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
          ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
          ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
              - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
          ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
              = (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2)) →
        ¬ ((∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
          ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
          ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
              - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
          ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
              ≠ (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2)) := by
    intro r h1 h2
    exact h2.2.2.2 h1.2.2.2
  calc ‖∑ r : ZMod p, (if (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
        - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
      then ∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
            + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
            + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))
      else 0)‖
      ≤ ∑ r : ZMod p, ‖(if (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
            - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
          then ∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
                + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
              * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
                + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))
          else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ r : ZMod p, (if ((∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
              ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
              ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
                  - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
              ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
                  ≠ (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))
        then 2 * Real.sqrt p
        else if ((∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
              ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
              ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
                  - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
              ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
                  = (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))
        then (p : ℝ) else 0) := Finset.sum_le_sum (fun r _ => hpoint r)
    _ = 2 * Real.sqrt p
          * ((Finset.univ.filter (fun r : ZMod p => (∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
              ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
              ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
                  - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
              ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
                  ≠ (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))).card : ℝ)
        + (p : ℝ)
          * ((Finset.univ.filter (fun r : ZMod p => (∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
              ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
              ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
                  - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
              ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
                  = (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))).card : ℝ) :=
        sum_ite_pair _ _ hcond _ _

/-- The `F₁`-filter of `critical_sum_bound`. -/
noncomputable def cF1 (p : ℕ) [NeZero p] (a b : Fin 3 → ℕ) : Finset (ZMod p) :=
  Finset.univ.filter (fun r : ZMod p => (∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
      ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
      ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
      ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
          ≠ (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))

/-- The `F₂`-filter of `critical_sum_bound`. -/
noncomputable def cF2 (p : ℕ) [NeZero p] (a b : Fin 3 → ℕ) : Finset (ZMod p) :=
  Finset.univ.filter (fun r : ZMod p => (∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
      ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
      ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
      ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
          = (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))

/-- The set of non-bad critical classes (in equality form). -/
noncomputable def cCcrit (p : ℕ) [NeZero p] (a b : Fin 3 → ℕ) : Finset (ZMod p) :=
  Finset.univ.filter (fun r : ZMod p => (∀ l : Fin 3, r + ((a l : ℕ) : ZMod p) ≠ 0)
      ∧ (∀ l : Fin 3, r + ((b l : ℕ) : ZMod p) ≠ 0)
      ∧ (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
          = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹))

lemma cF1_card_le_crit (a b : Fin 3 → ℕ) : (cF1 p a b).card ≤ (cCcrit p a b).card := by
  refine Finset.card_le_card ?_
  intro r hr
  rw [cF1, Finset.mem_filter] at hr
  rw [cCcrit, Finset.mem_filter]
  exact ⟨Finset.mem_univ r, hr.2.1, hr.2.2.1, sub_eq_zero.mp hr.2.2.2.1⟩

lemma cF2_card_le_K (a b : Fin 3 → ℕ) :
    (cF2 p a b).card ≤ ((Finset.univ : Finset (ZMod p)).filter (fun r : ZMod p =>
      (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
          = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)
      ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
          = (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))).card := by
  refine Finset.card_le_card ?_
  intro r hr
  rw [cF2, Finset.mem_filter] at hr
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ r, sub_eq_zero.mp hr.2.2.2.1, hr.2.2.2.2⟩

/-- **Local cubic correlation bound at a cube prime power `p^3`, with the doubly degenerate
correction.**

For an odd prime `p`, a primitive non-trivial `χ` mod `p^3`, and shifts `a b : Fin 3 → ℕ` whose
six values `v = ![](a0,a1,a2,b0,b1,b2)` have `v i` occurring exactly once, the cubic
correlation is bounded by `100 p^{3/2} ∏_{j ≠ i} gcd p^3 |v_i - v_j|  +  100 p^2 · K`, where
`K` is the number of *doubly degenerate* critical classes `r : ZMod p`, i.e. those with
`∑_l (r+a_l)⁻¹ = ∑_l (r+b_l)⁻¹` and `∑_l ((r+a_l)⁻¹)^2 = ∑_l ((r+b_l)⁻¹)^2` in `ZMod p`.

Route: `charCorrelation6_criticalClasses` (with `e = 3`) writes the correlation as
`p · ∑_{r : ZMod p} [crit(r)] · I(r)` with `I(r) = ∑_{z : ZMod p} χ(∏(x+a_l)) conj χ(∏(x+b_l))`,
`x = r + p z`.  Writing `x + u = u_l (1 + p α_l)` with `α_l = (high_l + z) u_l⁻¹`, the product
`P = ∏(1+pα_l)(∏(1+pα'_l))⁻¹` has the expansion `P = 1 + p W + p² Z`, and one shows
`P(z+w)P(z)⁻¹P(w)⁻¹P(0) = 1 - p²·C·z·w` where `C = ∑ u_l^{-2} - ∑ u'_l{}^{-2}` (the
non-degeneracy invariant): the `p`-level coefficient cancels by the criticality and the
`p²`-level coefficient is the second difference of the reduced quadratic `Z mod p`.  Applying
`χ` turns this into the exact twisted-cocycle relation for `Φ(z) = χ(P(z))` with
`ξ = χ(1+p²)` a primitive `p`-th root of unity, and the second moment
`|∑_z Φ(z)|² = Σ_{z,w} Φ(z+w)Φ(z)⁻¹` collapses by the geometric sum over `ZMod p` to `p`,
giving `|I(r)| ≤ 2√p` for non-degenerate critical classes, while the trivial bound `|I(r)| ≤ p`
always holds.  Bad classes (`p | r + a_l` or `p | r + b_l`) contribute nothing.
At most `6` non-bad classes are critical unless the critical polynomial `A'B - B'A` vanishes
identically, in which case the evaluation at a root of `A` (or `B`) exhibits a coincident pair
`v_i ≡ v_j (mod p)`, whence `∏_{j ≠ i} gcd p^3 |v_i - v_j| ≥ p`. -/
theorem charCorrelation6_cube_local {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (p ^ 3)) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1)
    (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → (![a 0, a 1, a 2, b 0, b 1, b 2] i)
        ≠ (![a 0, a 1, a 2, b 0, b 1, b 2] j)) :
    ‖∑ x : ZMod (p ^ 3), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ 3)))) *
        (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ 3)))))‖
      ≤ 100 * ((p : ℝ) * Real.sqrt (p : ℝ)) * ∏ j ∈ Finset.univ.erase i,
            (((Nat.gcd (p ^ 3) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
               - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ)
        + 100 * (p : ℝ) ^ 2 *
            (((Finset.univ : Finset (ZMod p)).filter (fun r : ZMod p =>
              (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹)
              ∧ (∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹)^2) = (∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹)^2))).card : ℝ) := by
  have hcc := charCorrelation6_criticalClasses (p := p) hp2 3 (by norm_num) χ hχ a b
  rw [hcc, norm_mul, Complex.norm_natCast]
  set PG : ℝ := ∏ j ∈ Finset.univ.erase i,
      (((Nat.gcd (p ^ 3) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
        - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) with hPG
  set KZ : ℝ := (((Finset.univ : Finset (ZMod p)).filter (fun r : ZMod p =>
      (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹) = (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹)
      ∧ (∑ l : Fin 3, ((r + ((a l : ℕ) : ZMod p))⁻¹) ^ 2)
          = (∑ l : Fin 3, ((r + ((b l : ℕ) : ZMod p))⁻¹) ^ 2))).card : ℝ) with hKZ
  have hbnd : ‖∑ r : ZMod p, (if (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
        - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
      then ∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
            + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
            + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))
      else 0)‖
      ≤ 2 * Real.sqrt p * ((cF1 p a b).card : ℝ) + (p : ℝ) * ((cF2 p a b).card : ℝ) :=
    critical_sum_bound hp2 χ hχ a b
  have hK2 : ((cF2 p a b).card : ℝ) ≤ KZ := by
    rw [hKZ]
    exact_mod_cast cF2_card_le_K a b
  have hpg1 : (1 : ℝ) ≤ PG := by
    rw [hPG]
    refine Finset.one_le_prod₀ (fun j _ => ?_)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.gcd_ne_zero_left (pow_ne_zero 3 (Fact.out : p.Prime).ne_zero))
  have hsq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  by_cases hH : cH p a b = 0
  · have hpgp : (p : ℝ) ≤ PG := by
      have h1 : (p : ℝ) ≤ ((∏ j ∈ Finset.univ.erase i,
          Nat.gcd (p ^ 3) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
            - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) : ℕ) : ℝ) := by
        exact_mod_cast prod_gcd_ge_of_H_zero a b i hi hH
      refine le_trans h1 ?_
      rw [hPG]
      push_cast
      rfl
    have hm2 : ((cF1 p a b).card : ℝ) ≤ (p : ℝ) := by
      have h1 : (cF1 p a b).card ≤ Fintype.card (ZMod p) := Finset.card_le_univ _
      rw [ZMod.card] at h1
      exact_mod_cast h1
    calc (p : ℝ) * ‖∑ r : ZMod p, (if (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
        then ∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
              + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
              + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))
        else 0)‖
        ≤ (p : ℝ) * (2 * Real.sqrt p * ((cF1 p a b).card : ℝ) + (p : ℝ) * ((cF2 p a b).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hbnd (le_of_lt hp0)
      _ ≤ (p : ℝ) * (2 * Real.sqrt p * (p : ℝ) + (p : ℝ) * KZ) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hp0)
          have h2 := mul_le_mul_of_nonneg_left hm2 (by positivity : (0:ℝ) ≤ 2 * Real.sqrt p)
          nlinarith [h2, hK2, hs0]
      _ = 2 * (p : ℝ) ^ 2 * Real.sqrt p + (p : ℝ) ^ 2 * KZ := by ring
      _ ≤ 100 * ((p : ℝ) * Real.sqrt (p : ℝ)) * PG + 100 * (p : ℝ) ^ 2 * KZ := by
          have h3 : (100:ℝ) * ((p : ℝ) * Real.sqrt p) * (p : ℝ)
              ≤ 100 * ((p : ℝ) * Real.sqrt p) * PG :=
            mul_le_mul_of_nonneg_left hpgp (by positivity)
          nlinarith [h3, hs0, hp0, hsq]
  · have hm : ((cF1 p a b).card : ℝ) ≤ 6 := by
      have h1 : (cF1 p a b).card ≤ (cCcrit p a b).card := cF1_card_le_crit a b
      have h2 : (cCcrit p a b).card ≤ 6 := crit_nonbad_card_le a b hH
      exact_mod_cast le_trans h1 h2
    calc (p : ℝ) * ‖∑ r : ZMod p, (if (∑ l : Fin 3, (r + ((a l : ℕ) : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + ((b l : ℕ) : ZMod p))⁻¹) = 0
        then ∑ z : ZMod (p ^ (3 - 2)), χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
              + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((a l : ℕ) : ZMod (p^3))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^3))
              + (p : ZMod (p^3)) * ((z.val : ℕ) : ZMod (p^3)) + ((b l : ℕ) : ZMod (p^3)))))
        else 0)‖
        ≤ (p : ℝ) * (2 * Real.sqrt p * ((cF1 p a b).card : ℝ) + (p : ℝ) * ((cF2 p a b).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hbnd (le_of_lt hp0)
      _ ≤ (p : ℝ) * (2 * Real.sqrt p * 6 + (p : ℝ) * KZ) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hp0)
          nlinarith [hm, hK2, hs0]
      _ = 12 * (p : ℝ) * Real.sqrt p + (p : ℝ) ^ 2 * KZ := by ring
      _ ≤ 100 * ((p : ℝ) * Real.sqrt (p : ℝ)) * PG + 100 * (p : ℝ) ^ 2 * KZ := by
          have h3 : (100:ℝ) * ((p : ℝ) * Real.sqrt p) * (1:ℝ)
              ≤ 100 * ((p : ℝ) * Real.sqrt p) * PG :=
            mul_le_mul_of_nonneg_left hpg1 (by positivity)
          nlinarith [h3, hs0, hp0, hsq, hK2]

end Commons.NumberTheory.DirichletCharacter
