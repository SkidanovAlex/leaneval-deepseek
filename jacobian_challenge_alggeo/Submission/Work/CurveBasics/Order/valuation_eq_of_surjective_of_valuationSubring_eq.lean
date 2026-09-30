import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

/-- Two surjective `ℤᵐ⁰`-valued valuations on a field which have the same valuation subring
coincide.  (Both are then normalized so that the value of a uniformizer is `exp (-1)`.) -/
theorem valuation_eq_of_surjective_of_valuationSubring_eq {K : Type*} [Field K]
    (v w : Valuation K (WithZero (Multiplicative ℤ)))
    (hv : Function.Surjective v) (hw : Function.Surjective w)
    (h : v.valuationSubring = w.valuationSubring) : v = w := by
  -- Equal valuation subrings mean the two valuations are equivalent.
  have heq : v.IsEquiv w := (Valuation.isEquiv_iff_valuationSubring v w).2 h
  -- A uniformizer `π` for `v`: an element with `v π = exp 1`.
  obtain ⟨π, hπ⟩ := hv (WithZero.exp (1 : ℤ))
  have hvπ_ne : v π ≠ 0 := by rw [hπ]; exact WithZero.exp_ne_zero
  have hwπ_ne : w π ≠ 0 := fun hh => hvπ_ne ((heq.eq_zero).mpr hh)
  -- The key computation: for every nonzero `x` the two logarithms differ by the fixed factor
  -- `log (w π)`.  Indeed `x / π ^ (log (v x))` is a unit for `v`, hence for `w`.
  have key : ∀ x : K, x ≠ 0 → (w x).log = (v x).log * (w π).log := by
    intro x hx
    have hvx_ne : v x ≠ 0 := v.ne_zero_iff.mpr hx
    have hwx_ne : w x ≠ 0 := w.ne_zero_iff.mpr hx
    set n : ℤ := (v x).log with hn
    have hvx : v x = WithZero.exp n := by
      rw [hn]; exact (WithZero.exp_log hvx_ne).symm
    have hvπn : v (π ^ n) = WithZero.exp n := by
      rw [map_zpow₀ v π n, hπ, ← WithZero.exp_zsmul]
      simp
    have hvu : v (x / π ^ n) = 1 := by
      rw [Valuation.map_div, hvx, hvπn, div_self (WithZero.exp_ne_zero)]
    have hwu : w (x / π ^ n) = 1 := (heq.eq_one_iff_eq_one).mp hvu
    have hwπn_ne : w (π ^ n) ≠ 0 := by
      rw [map_zpow₀ w π n]; exact zpow_ne_zero n hwπ_ne
    have hlog : (w (x / π ^ n)).log = (w x).log - n * (w π).log := by
      rw [Valuation.map_div, WithZero.log_div hwx_ne hwπn_ne, map_zpow₀ w π n,
        WithZero.log_zpow]
      simp
    have hlog0 : (w (x / π ^ n)).log = 0 := by rw [hwu, WithZero.log_one]
    have hEq : (w x).log = n * (w π).log := by
      have : (w x).log - n * (w π).log = 0 := by rw [← hlog, hlog0]
      exact sub_eq_zero.mp this
    rw [hEq, hn]
  -- `log (w π)` is positive, since `π` is not in the (common) valuation ring.
  have hlw_pos : 0 < (w π).log := by
    have hvπ_gt : ¬ (v π ≤ 1) := by
      rw [hπ]; exact not_le.mpr ((WithZero.one_lt_exp_iff).mpr (by norm_num))
    have hnot : ¬ (w π ≤ 1) := fun hw1 => hvπ_gt ((heq.le_one_iff_le_one).mpr hw1)
    have hiff : ((w π).log ≤ 0) ↔ (w π ≤ 1) := by
      rw [WithZero.log_le_iff_le_exp hwπ_ne, WithZero.exp_zero]
    exact lt_of_not_ge (hiff.not.mpr hnot)
  -- A uniformizer `a` for `w`.
  obtain ⟨a, ha⟩ := hw (WithZero.exp (1 : ℤ))
  have hane : a ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at ha; exact WithZero.exp_ne_zero ha.symm
  have hmul : (v a).log * (w π).log = 1 := by
    rw [← key a hane, ha, WithZero.log_exp]
  -- Since `log (v a) * log (w π) = 1` and `log (w π) > 0`, we get `log (w π) = 1`.
  have hlw : (w π).log = 1 := by
    have h' : (w π).log * (v a).log = 1 := by rw [mul_comm]; exact hmul
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h' with h1 | h1
    · exact h1
    · rw [h1] at hlw_pos; norm_num at hlw_pos
  -- Now the key computation collapses to `(w x).log = (v x).log`, whence `v = w`.
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Valuation.map_zero, Valuation.map_zero]
  · have hvx_ne : v x ≠ 0 := v.ne_zero_iff.mpr hx
    have hwx_ne : w x ≠ 0 := w.ne_zero_iff.mpr hx
    rw [← WithZero.exp_log hvx_ne, ← WithZero.exp_log hwx_ne]
    congr 1
    rw [key x hx, hlw, mul_one]

end Work.CurveBasics.Order
