import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Transcendental

/-- If `u` is transcendental over a field `R` and a nonzero polynomial `s` in `u`
realises `v` as a rational function of `u` (`v * s(u) = r(u)`), then `v` can be
written as `P(u)/Q(u)` with `Q ≠ 0` and `P`, `Q` coprime. -/
theorem exists_coprime_aeval_div_eq {R S : Type*} [Field R] [Field S] [Algebra R S] {u v : S}
    (hu : Transcendental R u)
    (h : ∃ r s : Polynomial R, s ≠ 0 ∧ v * (Polynomial.aeval u) s = (Polynomial.aeval u) r) :
    ∃ P Q : Polynomial R, Q ≠ 0 ∧ IsCoprime P Q ∧ v * (Polynomial.aeval u) Q = (Polynomial.aeval u) P := by
  classical
  obtain ⟨r, s, hs0, hvs⟩ := h
  letI : GCDMonoid (Polynomial R) := EuclideanDomain.gcdMonoid (Polynomial R)
  set g : Polynomial R := GCDMonoid.gcd r s with hg
  have hg0 : g ≠ 0 := gcd_ne_zero_of_right hs0
  have hug : (Polynomial.aeval u) g ≠ 0 := fun h0 => hg0 ((transcendental_iff.mp hu) g h0)
  have hsmul : g * (s / g) = s := EuclideanDomain.mul_div_cancel' hg0 (GCDMonoid.gcd_dvd_right r s)
  have hrmul : g * (r / g) = r := EuclideanDomain.mul_div_cancel' hg0 (GCDMonoid.gcd_dvd_left r s)
  have es : (Polynomial.aeval u) s = (Polynomial.aeval u) g * (Polynomial.aeval u) (s / g) := by
    conv_lhs => rw [← hsmul]
    rw [map_mul]
  have er : (Polynomial.aeval u) r = (Polynomial.aeval u) g * (Polynomial.aeval u) (r / g) := by
    conv_lhs => rw [← hrmul]
    rw [map_mul]
  refine ⟨r / g, s / g, right_div_gcd_ne_zero hs0, isCoprime_div_gcd_div_gcd hs0, ?_⟩
  have key : (Polynomial.aeval u) g * (v * (Polynomial.aeval u) (s / g))
      = (Polynomial.aeval u) g * (Polynomial.aeval u) (r / g) := by
    calc (Polynomial.aeval u) g * (v * (Polynomial.aeval u) (s / g))
        = v * ((Polynomial.aeval u) g * (Polynomial.aeval u) (s / g)) := by ring
      _ = v * (Polynomial.aeval u) s := by rw [← es]
      _ = (Polynomial.aeval u) r := hvs
      _ = (Polynomial.aeval u) g * (Polynomial.aeval u) (r / g) := er
  exact mul_left_cancel₀ hug key

end Commons.FieldTheory.Transcendental