import Mathlib

set_option linter.style.haveILetI false

namespace Work.WilE4.CAD

open scoped Topology
open Filter

/-- If `u` tends to a nonzero limit `c`, then eventually `u` has the same `SignType.sign` as `c`. -/
private lemma eventually_sign_eq_of_tendsto {α : Type*} {l : Filter α} {u : α → ℝ} {c : ℝ}
    (h : Tendsto u l (𝓝 c)) (hc : c ≠ 0) :
    ∀ᶠ z in l, SignType.sign (u z) = SignType.sign c := by
  rcases lt_or_gt_of_ne hc.symm with hc | hc
  · filter_upwards [h.eventually (isOpen_Ioi.mem_nhds hc)] with z hz
    rw [sign_pos hz, sign_pos hc]
  · filter_upwards [h.eventually (isOpen_Iio.mem_nhds hc)] with z hz
    rw [sign_neg hz, sign_neg hc]

/-- In `SignType`, `a * (-1) = -a`. -/
private lemma signType_mul_neg_one (a : SignType) : a * (-1) = -a := by
  cases a <;> rfl

/-- At a simple real root of a real polynomial, every nonzero sign value is attained at a point
arbitrarily close to the root. -/
theorem exists_sign_eq_of_simple_root {f : Polynomial ℝ} {y : ℝ} (hroot : f.IsRoot y)
    (hderiv : f.derivative.eval y ≠ 0) (s : SignType) (hs : s ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ z, |z - y| < ε ∧ SignType.sign (f.eval z) = s := by
  have hc : f.derivative.eval y ≠ 0 := hderiv
  have hrefy : f.eval y = 0 := Polynomial.IsRoot.def.mp hroot
  -- The slope of `f` at `y` tends to `f'(y)`, which is the derivative of `f.eval` at `y`.
  have hslope : Tendsto (slope (fun z => f.eval z) y) (𝓝[≠] y) (𝓝 (f.derivative.eval y)) :=
    hasDerivAt_iff_tendsto_slope.mp (f.hasDerivAt y)
  have hu : Tendsto (fun z => f.eval z / (z - y)) (𝓝[≠] y) (𝓝 (f.derivative.eval y)) := by
    apply hslope.congr'
    filter_upwards with z
    simp [slope_def_field, hrefy]
  -- On the right of `y` the sign of `f` is that of `f'(y)`.
  have hright : ∀ᶠ z in 𝓝[>] y,
      SignType.sign (f.eval z) = SignType.sign (f.derivative.eval y) := by
    have hupos : Tendsto (fun z => f.eval z / (z - y)) (𝓝[>] y) (𝓝 (f.derivative.eval y)) :=
      hu.mono_left (nhdsWithin_mono y (fun z hz => ne_of_gt hz))
    filter_upwards [eventually_sign_eq_of_tendsto hupos hc, self_mem_nhdsWithin] with z hz hyz
    have hzn : (z - y) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hyz)
    have hmul : SignType.sign (f.eval z)
        = SignType.sign (f.eval z / (z - y)) * SignType.sign (z - y) := by
      rw [← sign_mul, div_mul_cancel₀ _ hzn]
    rw [hmul, sign_pos (sub_pos.mpr hyz), mul_one, hz]
  -- On the left of `y` the sign of `f` is the opposite of that of `f'(y)`.
  have hleft : ∀ᶠ z in 𝓝[<] y,
      SignType.sign (f.eval z) = - SignType.sign (f.derivative.eval y) := by
    have huneg : Tendsto (fun z => f.eval z / (z - y)) (𝓝[<] y) (𝓝 (f.derivative.eval y)) :=
      hu.mono_left (nhdsWithin_mono y (fun z hz => ne_of_lt hz))
    filter_upwards [eventually_sign_eq_of_tendsto huneg hc, self_mem_nhdsWithin] with z hz hzy
    have hzn : (z - y) ≠ 0 := sub_ne_zero.mpr (ne_of_lt hzy)
    have hmul : SignType.sign (f.eval z)
        = SignType.sign (f.eval z / (z - y)) * SignType.sign (z - y) := by
      rw [← sign_mul, div_mul_cancel₀ _ hzn]
    rw [hmul, sign_neg (sub_neg.mpr hzy), hz, signType_mul_neg_one]
  have hballR : ∀ᶠ z in 𝓝[>] y, dist z y < ε :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds y hε)
  have hballL : ∀ᶠ z in 𝓝[<] y, dist z y < ε :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds y hε)
  haveI hneR : NeBot (𝓝[>] y) := nhdsWithin_Ioi_neBot (le_refl y)
  have hevR : ∀ᶠ z in 𝓝[>] y, y < z ∧ dist z y < ε ∧
      SignType.sign (f.eval z) = SignType.sign (f.derivative.eval y) := by
    filter_upwards [self_mem_nhdsWithin, hballR, hright] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨zR, hyzR, hzRd, hzRs⟩ := hevR.exists
  haveI hneL : NeBot (𝓝[<] y) := nhdsWithin_Iio_neBot (le_refl y)
  have hevL : ∀ᶠ z in 𝓝[<] y, z < y ∧ dist z y < ε ∧
      SignType.sign (f.eval z) = - SignType.sign (f.derivative.eval y) := by
    filter_upwards [self_mem_nhdsWithin, hballL, hleft] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨zL, hzyL, hzLd, hzLs⟩ := hevL.exists
  -- Every nonzero `s` is either `sign f'(y)` or its negative.
  have hsgn : s = SignType.sign (f.derivative.eval y) ∨
      s = - SignType.sign (f.derivative.eval y) := by
    have hc' : SignType.sign (f.derivative.eval y) ≠ 0 := sign_ne_zero.mpr hc
    rcases SignType.trichotomy s with h | h | h
    · rcases SignType.trichotomy (SignType.sign (f.derivative.eval y)) with g | g | g
      · exact Or.inl (by rw [h, g])
      · exact absurd g hc'
      · exact Or.inr (by rw [h, g])
    · exact absurd h hs
    · rcases SignType.trichotomy (SignType.sign (f.derivative.eval y)) with g | g | g
      · exact Or.inr (by rw [h, g]; rfl)
      · exact absurd g hc'
      · exact Or.inl (by rw [h, g])
  rcases hsgn with h | h
  · exact ⟨zR, by rw [← Real.dist_eq]; exact hzRd, by rw [hzRs, h]⟩
  · exact ⟨zL, by rw [← Real.dist_eq]; exact hzLd, by rw [hzLs, h]⟩

end Work.WilE4.CAD
