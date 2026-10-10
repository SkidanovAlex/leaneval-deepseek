import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.AK
import Submission.Work.MotA.coheight_eq_one_iff
import Submission.Work.MotAS.Nodes.Fw3Aux
import Submission.Work.MotAS.Nodes.Fw3FwEq
import Submission.Work.MotAS.Nodes.Fw3Stop
import Submission.Work.MotAS.Nodes.Fw3Irred
import Submission.Work.MotAS.FdivASGen3
import Submission.Work.MotK.TGen.TopFormMul
import Submission.Work.MotK.TGen.TopFormUnit

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.Nodes

/-
VERBATIM the statement of `Work.MotAS.ASRulV2M.fwVecAS2_three_notMem_x`
(`Submission/Work/MotAS/ASRulV2M/fwVecAS2_three_notMem_x.lean`), still `by sorry` there; once
proved here it is rewritten there as a one-line application.  It is one of the two outside
non-vanishing inputs of the K5 node `Work.MotAS.ASRulingMain` (see the header of
`Submission/Work/MotAS/ASRulingMain.lean`): `fwVecAS2 a b g 3 ≠ 0` at the residue field of a
height-one prime `x ∋ sAS2` is exactly `c₃ ≠ 0` for `c = kleinPAS a b g y`, i.e. the hypothesis
`w ≠ 0` of `Work.MotAS.ASRul.kernel_basis` / `Work.MotAS.ASRulV2M.hparam_kernel`.

MATHEMATICAL ROUTE.  `x = (p)` for a prime `p` (`Work.MotA.coheight_eq_one_iff`); `p ∣ sAS2` and,
assuming `fwVecAS2 · 3 ∈ x`, also `p ∣ fwVecAS2 · 3`.  The CAS certificate
`Work.MotAS.Nodes.Fw3FwEq` gives `fwVecAS2 a b g 3 = C 4 · C A² · asH` with `A = a² − ab − b²`
(nonzero by `Work.MotAS.aK_sq_sub_ne` and `ASGood`), so `p ∣ asH` (the factor `C 4 · C A²` is a
unit).  `asH` is irreducible as a polynomial (`Work.MotAS.Nodes.Fw3AsHIrred`: it is linear in `X 0`
with coprime coefficients), so any prime divisor of `asH` is associated to it; hence
`asH ∣ p ∣ sAS2`.  This is impossible: `Work.MotAS.Nodes.Fw3Stop` computes the top forms
`topForm (asH a b g) = -(X 2 · asQ a b)` and `topForm (sAS2 a b g) = C (A^5) · (asQ a b)^5`
(`asQ = A·(X 1² + 2 X 0 X 2) − 2(a²+b²)·X 2²`), and top forms are multiplicative
(`Work.MotK.TGen.TopFormMul`), so `asH ∣ sAS2` would force `X 2 ∣ asQ`, contradicting
`Work.MotAS.Nodes.Fw3.not_dvd_X2_asQ` (`asQ(0,1,0) = A ≠ 0`).
-/

/-- The top form of a divisor divides the top form. -/
theorem topForm_dvd_topForm (K : Type) [Field K] {p q : MvPolynomial (Fin 3) K}
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
theorem four_ne_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (4 : RatFunc 𝕜) ≠ 0 := by
  intro h
  have hd : (5 : ℕ) ∣ 4 := (CharP.cast_eq_zero_iff (RatFunc 𝕜) 5 4).mp h
  norm_num at hd

theorem fwVecAS2ThreeNotMemXProof (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (x : Work.MotA.polySpec (RatFunc 𝕜) 3)
    (hcoh : Order.coheight x = 1)
    (hx : Work.MotAS.sAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal) :
    Work.MotAS.fwVecAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) 3 ∉ x.asIdeal := by
  obtain ⟨p, hpprime, hp_eq⟩ := (Work.MotA.coheight_eq_one_iff (RatFunc 𝕜) 3 x).mp hcoh
  rw [hp_eq] at hx ⊢
  set a : RatFunc 𝕜 := Work.MotAS.aK D with ha
  set b : RatFunc 𝕜 := Work.MotAS.bK D with hb
  set g : RatFunc 𝕜 := Work.MotV.fAS 𝕜 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]
    exact Work.MotAS.fAS_ne_zero
  have hA : Work.MotAS.Nodes.Fw3.asA a b ≠ 0 := by
    show a ^ 2 - a * b - b ^ 2 ≠ 0
    rw [ha, hb]
    exact Work.MotAS.aK_sq_sub_ne D hD
  intro hfw
  have hsAS : p ∣ Work.MotAS.sAS2 a b g := Ideal.mem_span_singleton.mp hx
  have hfw3 : p ∣ Work.MotAS.fwVecAS2 a b g 3 := Ideal.mem_span_singleton.mp hfw
  have hpu : ¬ IsUnit p := hpprime.not_isUnit
  rw [Work.MotAS.Nodes.Fw3FwEq (RatFunc 𝕜) a b g] at hfw3
  have hu : IsUnit ((MvPolynomial.C (4 : RatFunc 𝕜)) *
      (MvPolynomial.C (Work.MotAS.Nodes.Fw3.asA a b)) ^ 2 :
        MvPolynomial (Fin 3) (RatFunc 𝕜)) := by
    have hC : (MvPolynomial.C (4 : RatFunc 𝕜) *
        (MvPolynomial.C (Work.MotAS.Nodes.Fw3.asA a b)) ^ 2 : MvPolynomial (Fin 3) (RatFunc 𝕜))
        = MvPolynomial.C (4 * (Work.MotAS.Nodes.Fw3.asA a b) ^ 2) := by
      rw [map_mul, map_pow]
    rw [hC]
    exact IsUnit.map (MvPolynomial.C : RatFunc 𝕜 →+* MvPolynomial (Fin 3) (RatFunc 𝕜))
      (isUnit_iff_ne_zero.mpr (mul_ne_zero (four_ne_zero 𝕜) (pow_ne_zero 2 hA)))
  have hasH : p ∣ Work.MotAS.Nodes.Fw3.asH a b g := hu.dvd_mul_left.mp hfw3
  have hirr : Irreducible (Work.MotAS.Nodes.Fw3.asH a b g) :=
    Work.MotAS.Nodes.Fw3.asH_irreducible a b g hA hg0
  have hstop := Work.MotAS.Nodes.Fw3Stop (RatFunc 𝕜) a b g hA
  have hHne : Work.MotAS.Nodes.Fw3.asH a b g ≠ 0 := Work.MotAS.Nodes.Fw3.asH_ne_zero a b g hA
  have hSne : Work.MotAS.sAS2 a b g ≠ 0 := by
    intro h0
    have h1 : (Work.MotAS.sAS2 a b g).totalDegree = 10 := hstop.2
    rw [h0, MvPolynomial.totalDegree_zero] at h1
    exact absurd h1 (by norm_num)
  have hnotdvd : ¬ (Work.MotAS.Nodes.Fw3.asH a b g ∣ Work.MotAS.sAS2 a b g) := by
    intro hdvd
    have htf := topForm_dvd_topForm (RatFunc 𝕜) hHne hSne hdvd
    rw [Work.MotAS.Nodes.Fw3.topForm_asH a b g hA, Work.MotK.TGen.topForm, hstop.2,
      hstop.1] at htf
    obtain ⟨q, hq⟩ := htf
    have hX2dvd : (MvPolynomial.X 2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) ∣
        MvPolynomial.C ((Work.MotAS.Nodes.Fw3.asA a b) ^ 5)
          * (Work.MotAS.Nodes.Fw3.asQ a b) ^ 5 :=
      ⟨-(Work.MotAS.Nodes.Fw3.asQ a b * q), by
        rw [hq]
        simp only [Work.MotAS.Nodes.Fw3.asH3]
        ring⟩
    have hu2 : IsUnit (MvPolynomial.C ((Work.MotAS.Nodes.Fw3.asA a b) ^ 5) :
        MvPolynomial (Fin 3) (RatFunc 𝕜)) :=
      IsUnit.map (MvPolynomial.C : RatFunc 𝕜 →+* MvPolynomial (Fin 3) (RatFunc 𝕜))
        (isUnit_iff_ne_zero.mpr (pow_ne_zero 5 hA))
    have hX2dvd2 : (MvPolynomial.X 2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) ∣
        (Work.MotAS.Nodes.Fw3.asQ a b) ^ 5 := hu2.dvd_mul_left.mp hX2dvd
    have hpX2 : Prime (MvPolynomial.X 2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) :=
      MvPolynomial.X_prime
    exact Work.MotAS.Nodes.Fw3.not_dvd_X2_asQ a b hA (hpX2.dvd_of_dvd_pow hX2dvd2)
  obtain ⟨s, hs⟩ := hasH
  rcases hirr.isUnit_or_isUnit hs with hu2 | hu3
  · exact hpu hu2
  · have hpu' : p = Work.MotAS.Nodes.Fw3.asH a b g * ↑(hu3.unit)⁻¹ := by
      have h1 : Work.MotAS.Nodes.Fw3.asH a b g = p * ↑(hu3.unit) := by
        rw [IsUnit.unit_spec hu3]; exact hs
      rw [h1, mul_assoc, Units.mul_inv, mul_one]
    exact hnotdvd (dvd_trans ⟨↑(hu3.unit)⁻¹, hpu'⟩ hsAS)

end Work.MotAS.Nodes
