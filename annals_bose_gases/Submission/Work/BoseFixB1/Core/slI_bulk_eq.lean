import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseFixB1S.MeanSq.Box3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Core

/-!
# The bulk (unclipped) form of the sliding interval

The sliding interval is defined by

  `slI ℓ h u = Icc (max (-ℓ/2) (h·u - h/2)) (min (ℓ/2) (h·u + h/2))`,

i.e. the window `[h·u - h/2, h·u + h/2]` of length `h` centred at `h·u`, intersected with the
large interval `[-ℓ/2, ℓ/2]`.  On the *bulk* range

  `u ∈ Ioc (-((ℓ - h)/(2h))) ((ℓ - h)/(2h))`

the window does not meet either endpoint of the large interval, so both the `max` and the `min`
are attained at the window's own endpoints and the clipping is inactive:

  `slI ℓ h u = Icc (h·u - h/2) (h·u + h/2)`,

a genuine interval of length `h` (this is what makes the volume computation in `bulkEst` work).

The hypothesis `0 < h` is what makes multiplication by `h` monotone, so that the two membership
inequalities transfer to `-(ℓ-h)/2 < h·u ≤ (ℓ-h)/2`; specifically

* `h·u > -(ℓ-h)/2 = (h - ℓ)/2` gives `h·u - h/2 > -ℓ/2`, so `max (-ℓ/2) (h·u - h/2) = h·u - h/2`;
* `h·u ≤ (ℓ-h)/2` gives `h·u + h/2 ≤ ℓ/2`, so `min (ℓ/2) (h·u + h/2) = h·u + h/2`.
-/

theorem slI_bulk_eq {ℓ h u : ℝ} (hh : 0 < h)
    (hu : u ∈ Set.Ioc (-((ℓ - h) / (2 * h))) ((ℓ - h) / (2 * h))) :
    Work.BoseFixB1S.slI ℓ h u = Set.Icc (h * u - h / 2) (h * u + h / 2) := by
  -- Transfer the two membership inequalities through the order isomorphism `y ↦ h * y`.
  have hlow : -(ℓ - h) / 2 < h * u := by
    have hmul := mul_lt_mul_of_pos_left hu.1 hh
    have hkey : h * (-((ℓ - h) / (2 * h))) = -(ℓ - h) / 2 := by field_simp
    rwa [hkey] at hmul
  have hupp : h * u ≤ (ℓ - h) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hu.2 hh.le
    have hkey : h * ((ℓ - h) / (2 * h)) = (ℓ - h) / 2 := by field_simp
    rwa [hkey] at hmul
  -- Both clips are inactive, so `max` and `min` reduce to the window endpoints.
  rw [Work.BoseFixB1S.slI, max_eq_right (by linarith), min_eq_right (by linarith)]

end Work.BoseFixB1.Core
