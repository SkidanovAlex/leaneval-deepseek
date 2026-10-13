import Mathlib

namespace Work.WilkiesH.Norm

/-- For a finite place `v` of a number field `K` and `a = b * x` with `b ≠ 0`, the identity
`max (v x) 1 = max (v a) (v b) / v b` holds pointwise (both numerator and denominator are
multiplied by the positive number `v b`), and hence the corresponding Finprod identity holds. -/
lemma finprod_finitePlace_max_div {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0)
    {a b : NumberField.RingOfIntegers K} (hb : b ≠ 0)
    (hab : (a : K) = (b : K) * x) :
    ∏ᶠ v : NumberField.FinitePlace K, max (v x) 1
      = (∏ᶠ v : NumberField.FinitePlace K, max (v (a : K)) (v (b : K)))
        / (∏ᶠ v : NumberField.FinitePlace K, v (b : K)) := by
  have hbK : (b : K) ≠ 0 := fun h => hb (Subtype.ext h)
  have haK : (a : K) ≠ 0 := by
    intro h
    have h0 : (b : K) * x = 0 := by rw [← hab, h]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hbK h1
    · exact hx h1
  have hfinA : Function.HasFiniteMulSupport (fun v : NumberField.FinitePlace K => v (a : K)) :=
    NumberField.FinitePlace.hasFiniteMulSupport haK
  have hfinB : Function.HasFiniteMulSupport (fun v : NumberField.FinitePlace K => v (b : K)) :=
    NumberField.FinitePlace.hasFiniteMulSupport hbK
  have hmax : Function.HasFiniteMulSupport
      (fun v : NumberField.FinitePlace K => max (v (a : K)) (v (b : K))) :=
    hfinA.max hfinB
  have hpoint : ∀ v : NumberField.FinitePlace K,
      max (v x) 1 = max (v (a : K)) (v (b : K)) / v (b : K) := by
    intro v
    have hBpos : 0 < v (b : K) := NumberField.FinitePlace.pos_iff.mpr hbK
    have hmap : v (a : K) = v (b : K) * v x := by rw [hab, map_mul]
    have hmaxeq : max (v (b : K) * v x) (v (b : K)) = v (b : K) * max (v x) 1 := by
      rw [mul_max_of_nonneg (v x) 1 hBpos.le, mul_one]
    rw [hmap, hmaxeq, mul_div_cancel_left₀ _ hBpos.ne']
  rw [← finprod_div_distrib hmax hfinB]
  exact finprod_congr hpoint

end Work.WilkiesH.Norm
