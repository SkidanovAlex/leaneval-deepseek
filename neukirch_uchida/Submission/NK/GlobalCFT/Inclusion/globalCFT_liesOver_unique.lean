import Mathlib
import Submission.NK.GlobalCFT.Place

open NumberField IsDedekindDomain

namespace NK.GlobalCFT.Inclusion

/-- The place of `K` below a place of a finite extension `L / K` is unique: if `w` lies over
both `v` and `v'`, then `v = v'`.  The infinite case is the uniqueness of the restriction of an
absolute value, the finite case the uniqueness of the contraction of a prime. -/
theorem globalCFT_liesOver_unique {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {w : Place L} {v v' : Place K}
    (h : Place.LiesOver w v) (h' : Place.LiesOver w v') : v = v' := by
  rcases h with ⟨w1, v1, hw1, hv1, hL1⟩ | ⟨q1, Q1, hw1, hv1, hL1⟩
  · -- `w` and `v` are both archimedean
    rcases h' with ⟨w2, v2, hw2, hv2, hL2⟩ | ⟨q2, Q2, hw2, hv2, hL2⟩
    · -- `v'` is archimedean too: the two infinite places of `L` coincide, and the
      -- restriction of an absolute value is unique
      have hw : w1 = w2 := Place.ofInfinite_inj.mp (hw1.symm.trans hw2)
      subst hw
      rw [hv1, hv2]
      refine Place.ofInfinite_inj.mpr ?_
      have e1 := AbsoluteValue.LiesOver.comp_eq (w := w1.val) (v := v1.val)
      have e2 := AbsoluteValue.LiesOver.comp_eq (w := w1.val) (v := v2.val)
      exact Subtype.ext (e1.symm.trans e2)
    · -- `w` infinite and `v'` finite: the same place of `L` cannot be both
      exact absurd (hw1.symm.trans hw2) Sum.inl_ne_inr
  · -- `w` and `v` are both nonarchimedean
    rcases h' with ⟨w2, v2, hw2, hv2, hL2⟩ | ⟨q2, Q2, hw2, hv2, hL2⟩
    · -- `w` finite and `v'` infinite: impossible
      exact absurd (hw1.symm.trans hw2) Sum.inr_ne_inl
    · -- both finite: the two primes of `𝓞 L` coincide, and the contraction of a prime is unique
      have hq : q1 = q2 := Place.ofFinite_inj.mp (hw1.symm.trans hw2)
      subst hq
      rw [hv1, hv2]
      refine Place.ofFinite_inj.mpr ?_
      apply HeightOneSpectrum.ext
      have o1 : Q1.asIdeal = q1.asIdeal.under (𝓞 K) := hL1.over
      have o2 : Q2.asIdeal = q1.asIdeal.under (𝓞 K) := hL2.over
      rw [o1, o2]

end NK.GlobalCFT.Inclusion
