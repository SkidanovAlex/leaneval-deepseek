import Mathlib
import Submission.Work.MotK.TwCensus.ZTwist
import Submission.Work.MotK.ZAll.FiveTermTotalDegree
import Submission.Work.MotK.ZAll.NoLinearFactorCharFive
import Submission.Work.MotK.ZAll.NoQuadFactorCharFive
import Submission.Work.MotK.ZAll.ShapeLemmaCharNeFive
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZElim2IrredCharAll`

`Irreducible (ZElim2 a b h)` for arbitrary `a b h ≠ 0` with `a¹⁰ - 11 a⁵b⁵ - b¹⁰ ≠ 0`, over an
arbitrary field `K` (no characteristic restriction).

`ZElim2 a b h` is the five-term binary quintic
`A X⁵ + B X²Y + C XY³ + D Y⁵ + E` with
`A = ab⁷h²`, `B = -b³h(3a⁵+b⁵)`, `C = a³h(a⁵+2b⁵)`, `D = -a⁶b²h`, `E = a⁶b²`
(so `A, D, E ≠ 0` under the hypotheses).  The proof is the contrapositive of the two
"shape lemmas" for such a quintic (one for characteristic `≠ 5`, one for characteristic `5`),
combined with the ring identity

`C² - 5 D B = a⁶ h² (a¹⁰ - 11a⁵b⁵ - b¹⁰)`

(so the necessary condition `C² = 5DB` for reducibility contradicts the hypothesis).
-/

open MvPolynomial

namespace Work.MotK.TGen

/-- `ZElim2 a b h` in the standard shape of a five-term binary quintic. -/
private lemma ZElim2_eq_fiveTerm (K : Type) [Field K] (a b h : K) :
    Work.MotK.TwCensus.ZElim2 a b h
      = C (a * b ^ 7 * h ^ 2) * (X 0 : MvPolynomial (Fin 2) K) ^ 5
        + C (-(b ^ 3 * h * (3 * a ^ 5 + b ^ 5))) * (X 0 : MvPolynomial (Fin 2) K) ^ 2 * X 1
        + C (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) * X 0 * (X 1 : MvPolynomial (Fin 2) K) ^ 3
        + C (-(a ^ 6 * b ^ 2 * h)) * (X 1 : MvPolynomial (Fin 2) K) ^ 5
        + C (a ^ 6 * b ^ 2) := by
  simp only [Work.MotK.TwCensus.ZElim2, MvPolynomial.C_neg]
  ring_nf

/-- The Klein discriminant identity for the shape coefficients of `ZElim2`. -/
private lemma ZElim2_disc_identity (K : Type) [Field K] (a b h : K) :
    (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) ^ 2
        - 5 * (-(a ^ 6 * b ^ 2 * h)) * (-(b ^ 3 * h * (3 * a ^ 5 + b ^ 5)))
      = a ^ 6 * h ^ 2 * (a ^ 10 - 11 * a ^ 5 * b ^ 5 - b ^ 10) := by
  first | refl_ring1 | ring

/-- The five-term quintic is nonzero as soon as its `X₀⁵`-coefficient is. -/
private lemma fiveTerm_ne_zero (K : Type) [Field K] (a b c d e : K) (ha : a ≠ 0) :
    (C a * (X 0 : MvPolynomial (Fin 2) K) ^ 5
      + C b * (X 0 : MvPolynomial (Fin 2) K) ^ 2 * X 1
      + C c * (X 0 : MvPolynomial (Fin 2) K) * (X 1 : MvPolynomial (Fin 2) K) ^ 3
      + C d * (X 1 : MvPolynomial (Fin 2) K) ^ 5 + C e) ≠ 0 := by
  intro h0
  have hdeg := Work.MotK.ZAll.FiveTermTotalDegree a b c d e ha
  rw [h0, MvPolynomial.totalDegree_zero] at hdeg
  exact absurd hdeg (by norm_num)

/-- A nonzero constant polynomial is a unit. -/
private lemma isUnit_C_of_ne_zero {K : Type} [Field K] {r : K} (hr : r ≠ 0) :
    IsUnit (C r : MvPolynomial (Fin 2) K) :=
  isUnit_iff_exists_inv.mpr ⟨C r⁻¹, by rw [← map_mul, mul_inv_cancel₀ hr, map_one]⟩

/-- A nonzero polynomial of total degree zero is a unit. -/
private lemma isUnit_of_totalDegree_zero {K : Type} [Field K] {p : MvPolynomial (Fin 2) K}
    (hp0 : p ≠ 0) (hp : p.totalDegree = 0) : IsUnit p := by
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp
  have hr : p.coeff 0 ≠ 0 := fun h0 => hp0 (by rw [hC, h0, map_zero])
  rw [hC]
  exact isUnit_C_of_ne_zero hr

/-- **Characteristic `5` shape lemma.**  In characteristic `5` the five-term quintic
`a X₀⁵ + b X₀²X₁ + c X₀X₁³ + d X₁⁵ + e` with `a,d,e ≠ 0` can only be reducible if `c = 0`. -/
private lemma fiveTerm_shape_charFive (K : Type) [Field K] (h5 : (5 : K) = 0) (a b c d e : K)
    (ha : a ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hred : ¬ Irreducible (C a * (X 0 : MvPolynomial (Fin 2) K) ^ 5
      + C b * (X 0 : MvPolynomial (Fin 2) K) ^ 2 * X 1
      + C c * (X 0 : MvPolynomial (Fin 2) K) * (X 1 : MvPolynomial (Fin 2) K) ^ 3
      + C d * (X 1 : MvPolynomial (Fin 2) K) ^ 5 + C e)) :
    c ^ 2 = 5 * d * b := by
  have hne := fiveTerm_ne_zero K a b c d e ha
  have hdeg := Work.MotK.ZAll.FiveTermTotalDegree a b c d e ha
  have hnotunit : ¬ IsUnit (C a * (X 0 : MvPolynomial (Fin 2) K) ^ 5
      + C b * (X 0 : MvPolynomial (Fin 2) K) ^ 2 * X 1
      + C c * (X 0 : MvPolynomial (Fin 2) K) * (X 1 : MvPolynomial (Fin 2) K) ^ 3
      + C d * (X 1 : MvPolynomial (Fin 2) K) ^ 5 + C e) := by
    intro hu
    have hdiv : (C a * (X 0 : MvPolynomial (Fin 2) K) ^ 5
        + C b * (X 0 : MvPolynomial (Fin 2) K) ^ 2 * X 1
        + C c * (X 0 : MvPolynomial (Fin 2) K) * (X 1 : MvPolynomial (Fin 2) K) ^ 3
        + C d * (X 1 : MvPolynomial (Fin 2) K) ^ 5 + C e) ∣ 1 := by
      obtain ⟨u, hu_eq⟩ := hu
      exact ⟨↑u⁻¹, by rw [← hu_eq, Units.mul_inv]⟩
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv
      (one_ne_zero : (1 : MvPolynomial (Fin 2) K) ≠ 0)
    rw [MvPolynomial.totalDegree_one] at hle
    omega
  rcases irreducible_or_factor hnotunit with hirr | ⟨g, h, hgu, hhu, hgh⟩
  · exact absurd hirr hred
  · have hg0 : g ≠ 0 := fun h0 => hne (by rw [hgh, h0, zero_mul])
    have hh0 : h ≠ 0 := fun h0 => hne (by rw [hgh, h0, mul_zero])
    have hdeggh : g.totalDegree + h.totalDegree = 5 := by
      have hd := MvPolynomial.totalDegree_mul_of_isDomain hg0 hh0
      rw [← hgh, hdeg] at hd
      exact hd.symm
    have hc0 : c = 0 := by
      rcases le_total h.totalDegree g.totalDegree with hle | hle
      · -- `h` is the factor of smaller total degree
        have hhle : h.totalDegree ≤ 2 := by omega
        rcases Nat.eq_zero_or_pos h.totalDegree with hh0d | hhpos
        · exact absurd (isUnit_of_totalDegree_zero hh0 hh0d) hhu
        · rcases (by omega : h.totalDegree = 1 ∨ h.totalDegree = 2) with h1 | h2
          · exact Work.MotK.ZAll.NoLinearFactorCharFive h5 a b c d e ha hd he h g
              (by omega) (by omega) (by rw [mul_comm]; exact hgh.symm)
          · exact Work.MotK.ZAll.NoQuadFactorCharFive h5 a b c d e ha hd he h g
              (by omega) (by omega) (by rw [mul_comm]; exact hgh.symm)
      · have hgle : g.totalDegree ≤ 2 := by omega
        rcases Nat.eq_zero_or_pos g.totalDegree with hg0d | hgpos
        · exact absurd (isUnit_of_totalDegree_zero hg0 hg0d) hgu
        · rcases (by omega : g.totalDegree = 1 ∨ g.totalDegree = 2) with h1 | h2
          · exact Work.MotK.ZAll.NoLinearFactorCharFive h5 a b c d e ha hd he g h
              (by omega) (by omega) hgh.symm
          · exact Work.MotK.ZAll.NoQuadFactorCharFive h5 a b c d e ha hd he g h
              (by omega) (by omega) hgh.symm
    simp [hc0, h5]

theorem ZElim2IrredCharAll (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hdisc : a ^ 10 - 11 * a ^ 5 * b ^ 5 - b ^ 10 ≠ 0) :
    Irreducible (Work.MotK.TwCensus.ZElim2 a b h) := by
  rw [ZElim2_eq_fiveTerm K a b h]
  by_contra hred
  have hA : a * b ^ 7 * h ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha (pow_ne_zero 7 hb)) (pow_ne_zero 2 hh)
  have hD : -(a ^ 6 * b ^ 2 * h) ≠ 0 := by
    rw [neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 6 ha) (pow_ne_zero 2 hb)) hh
  have hE : a ^ 6 * b ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 6 ha) (pow_ne_zero 2 hb)
  -- the necessary condition for reducibility, from the shape lemma (in either characteristic)
  have hkey : (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) ^ 2
      = 5 * (-(a ^ 6 * b ^ 2 * h)) * (-(b ^ 3 * h * (3 * a ^ 5 + b ^ 5))) := by
    rcases eq_or_ne (5 : K) 0 with h5 | h5
    · exact fiveTerm_shape_charFive K h5 (a * b ^ 7 * h ^ 2) (-(b ^ 3 * h * (3 * a ^ 5 + b ^ 5)))
        (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) (-(a ^ 6 * b ^ 2 * h)) (a ^ 6 * b ^ 2) hA hD hE hred
    · exact Work.MotK.ZAll.ShapeLemmaCharNeFive K h5 (a * b ^ 7 * h ^ 2) (-(b ^ 3 * h * (3 * a ^ 5 + b ^ 5)))
        (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) (-(a ^ 6 * b ^ 2 * h)) (a ^ 6 * b ^ 2) hA hD hE hred
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 ha) (pow_ne_zero 2 hh)) hdisc)
    (by rw [← ZElim2_disc_identity K a b h, hkey, sub_self])

end Work.MotK.TGen
