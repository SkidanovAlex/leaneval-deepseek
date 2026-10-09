import Mathlib.NumberTheory.Padics.HeightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

/-- If a height-one prime ideal `v` of the ring of integers of `ℚ` corresponds, under
`Rat.HeightOneSpectrum.primesEquiv`, to the prime `p`, then `p` itself lies in `v.asIdeal`. -/
theorem mem_of_primesEquiv_eq (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (p : ℕ) (hp : p.Prime) (h : Rat.HeightOneSpectrum.primesEquiv v = ⟨p, hp⟩) :
    (p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  -- The natural generator of the ideal is `p`.
  have hgen : Rat.HeightOneSpectrum.natGenerator v = p := congrArg Subtype.val h
  -- The image of `v.asIdeal` under the canonical ring equivalence `𝓞 ℚ ≃+* ℤ` is `span {p}`.
  have hspan : Ideal.span {(p : ℤ)} =
      v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)) := by
    rw [← hgen]
    exact Rat.HeightOneSpectrum.span_natGenerator v
  -- Membership transfers across the ring equivalence.
  rw [← Ideal.apply_mem_of_equiv_iff
    (f := Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))]
  rw [← hspan, Ideal.mem_span_singleton]
  simp

end Commons.NumberTheory.NumberField