import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotA.coheight_eq_one_iff
import Submission.Work.MotAS.Nodes.Fw3Aux
import Submission.Work.MotAS.Nodes.Fw3FwEq
import Submission.Work.MotAS.Nodes.Fw3Stop
import Submission.Work.MotAS.Nodes.Fw3Irred
import Submission.Work.MotK.TGen.TopFormMul

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fwVecAS2 a b g 3` does not vanish on a codimension-one component of `{sAS2 a b g = 0}`

`Work.MotAS.sAS2 a b g` is the source ruling quintic of the corrected AS (Artin--Schreier) chart of
the Crauder--Katz link, and `Work.MotAS.fwVecAS2 a b g 3` is the third component of the forward
chart map (the `w ≠ 0` denominator of the AS ruling parametrisation).  The two polynomials have no
common prime factor: every height-one prime of `K[X₀,X₁,X₂]` containing `sAS2 a b g` misses
`fwVecAS2 a b g 3`.

## The argument

By `Work.MotA.coheight_eq_one_iff` a height-one point `x` of `𝔸³` is `(p)` for a prime `p`, so it
suffices to rule out `p ∣ sAS2 a b g` together with `p ∣ fwVecAS2 a b g 3`.

* `Work.MotAS.Nodes.Fw3FwEq` gives the explicit factorisation
  `fwVecAS2 a b g 3 = C 4 · C A² · asH a b g`,  `A = a² − ab − b²`,
  where `asH` (`Work.MotAS.Nodes.Fw3.asH`) is a cubic that is linear in `X₀` over `K[X₁,X₂]` with
  coefficients `Work.MotAS.Nodes.Fw3.α = 2A·X₁ − 2A·X₂² + B` and `β`; since `C 4 · C A²` is a unit
  (`A ≠ 0`, char 5) and `α, β` are coprime (`Work.MotAS.Nodes.Fw3Irred`), `asH` is irreducible.
* Hence `p ∼ asH` and so `asH ∣ p ∣ sAS2 a b g`.
* But `Work.MotAS.Nodes.Fw3.topForm_asH` gives `topForm (asH) = −X₂·Q` and
  `Work.MotAS.Nodes.Fw3Stop` gives `topForm (sAS2 a b g) = C (A⁵)·Q⁵`, where
  `Q = Work.MotAS.Nodes.Fw3.asQ = A·(X₁² + 2X₀X₂) − 2B·X₂²` is the source conic.  Top forms are
  multiplicative (`Work.MotK.TGen.TopFormMul`), so `asH ∣ sAS2` would force `X₂ ∣ Q⁵`, hence
  `X₂ ∣ Q`, contradicting `Work.MotAS.Nodes.Fw3.not_dvd_X2_asQ`.

This is the generic (arbitrary coefficient field `K` of characteristic 5) version of
`Work.MotAS.Nodes.fwVecAS2ThreeNotMemXProof`, which is stated over `RatFunc 𝕜` with the Klein datum
furnishing `aK D, bK D` and `fAS 𝕜`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotC5N3

open MvPolynomial

/-- The top form of a divisor divides the top form. -/
theorem topForm_dvd_topForm {K : Type} [Field K] {p q : MvPolynomial (Fin 3) K}
    (hp : p ≠ 0) (hq : q ≠ 0) (h : p ∣ q) :
    Work.MotK.TGen.topForm p ∣ Work.MotK.TGen.topForm q := by
  obtain ⟨r, hr⟩ := h
  have hrne : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hq hr
  exact ⟨Work.MotK.TGen.topForm r, by
    rw [hr, Work.MotK.TGen.TopFormMul K p r hp hrne]⟩

/-- `4 ≠ 0` in a field of characteristic `5`. -/
theorem four_ne_zero (K : Type) [Field K] [CharP K 5] : (4 : K) ≠ 0 := by
  intro h
  have hd : (5 : ℕ) ∣ 4 := (CharP.cast_eq_zero_iff K 5 4).mp h
  norm_num at hd

theorem fwVecAS2_three_notMem_x_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g)
    (x : Work.MotA.polySpec K 3) (hcoh : Order.coheight x = 1)
    (hx : Work.MotAS.sAS2 a b g ∈ x.asIdeal) :
    Work.MotAS.fwVecAS2 a b g 3 ∉ x.asIdeal := by
  obtain ⟨p, hpprime, hp_eq⟩ := (Work.MotA.coheight_eq_one_iff K 3 x).mp hcoh
  rw [hp_eq] at hx ⊢
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg ⟨0, by ring⟩
  have hA : Work.MotAS.Nodes.Fw3.asA a b ≠ 0 := by
    show a ^ 2 - a * b - b ^ 2 ≠ 0
    exact ha
  intro hfw
  have hsAS : p ∣ Work.MotAS.sAS2 a b g := Ideal.mem_span_singleton.mp hx
  have hfw3 : p ∣ Work.MotAS.fwVecAS2 a b g 3 := Ideal.mem_span_singleton.mp hfw
  have hpu : ¬ IsUnit p := hpprime.not_isUnit
  rw [Work.MotAS.Nodes.Fw3FwEq K a b g] at hfw3
  have hu : IsUnit ((MvPolynomial.C (4 : K)) *
      (MvPolynomial.C (Work.MotAS.Nodes.Fw3.asA a b)) ^ 2 :
        MvPolynomial (Fin 3) K) := by
    have hC : (MvPolynomial.C (4 : K) *
        (MvPolynomial.C (Work.MotAS.Nodes.Fw3.asA a b)) ^ 2 : MvPolynomial (Fin 3) K)
        = MvPolynomial.C (4 * (Work.MotAS.Nodes.Fw3.asA a b) ^ 2) := by
      rw [map_mul, map_pow]
    rw [hC]
    exact IsUnit.map (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
      (isUnit_iff_ne_zero.mpr (mul_ne_zero (four_ne_zero K) (pow_ne_zero 2 hA)))
  have hasH : p ∣ Work.MotAS.Nodes.Fw3.asH a b g := hu.dvd_mul_left.mp hfw3
  have hirr : Irreducible (Work.MotAS.Nodes.Fw3.asH a b g) :=
    Work.MotAS.Nodes.Fw3.asH_irreducible a b g hA hg0
  have hstop := Work.MotAS.Nodes.Fw3Stop K a b g hA
  have hHne : Work.MotAS.Nodes.Fw3.asH a b g ≠ 0 := Work.MotAS.Nodes.Fw3.asH_ne_zero a b g hA
  have hSne : Work.MotAS.sAS2 a b g ≠ 0 := by
    intro h0
    have h1 : (Work.MotAS.sAS2 a b g).totalDegree = 10 := hstop.2
    rw [h0, MvPolynomial.totalDegree_zero] at h1
    exact absurd h1 (by norm_num)
  have hnotdvd : ¬ (Work.MotAS.Nodes.Fw3.asH a b g ∣ Work.MotAS.sAS2 a b g) := by
    intro hdvd
    have htf := topForm_dvd_topForm hHne hSne hdvd
    rw [Work.MotAS.Nodes.Fw3.topForm_asH a b g hA, Work.MotK.TGen.topForm, hstop.2,
      hstop.1] at htf
    obtain ⟨q, hq⟩ := htf
    have hX2dvd : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣
        MvPolynomial.C ((Work.MotAS.Nodes.Fw3.asA a b) ^ 5)
          * (Work.MotAS.Nodes.Fw3.asQ a b) ^ 5 :=
      ⟨-(Work.MotAS.Nodes.Fw3.asQ a b * q), by
        rw [hq]
        simp only [Work.MotAS.Nodes.Fw3.asH3]
        ring⟩
    have hu2 : IsUnit (MvPolynomial.C ((Work.MotAS.Nodes.Fw3.asA a b) ^ 5) :
        MvPolynomial (Fin 3) K) :=
      IsUnit.map (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
        (isUnit_iff_ne_zero.mpr (pow_ne_zero 5 hA))
    have hX2dvd2 : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣
        (Work.MotAS.Nodes.Fw3.asQ a b) ^ 5 := hu2.dvd_mul_left.mp hX2dvd
    have hpX2 : Prime (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) := MvPolynomial.X_prime
    exact Work.MotAS.Nodes.Fw3.not_dvd_X2_asQ a b hA (hpX2.dvd_of_dvd_pow hX2dvd2)
  obtain ⟨s, hs⟩ := hasH
  rcases hirr.isUnit_or_isUnit hs with hu2 | hu3
  · exact hpu hu2
  · have hpu' : p = Work.MotAS.Nodes.Fw3.asH a b g * ↑(hu3.unit)⁻¹ := by
      have h1 : Work.MotAS.Nodes.Fw3.asH a b g = p * ↑(hu3.unit) := by
        rw [IsUnit.unit_spec hu3]; exact hs
      rw [h1, mul_assoc, Units.mul_inv, mul_one]
    exact hnotdvd (dvd_trans ⟨↑(hu3.unit)⁻¹, hpu'⟩ hsAS)

end Work.MotC5N3
