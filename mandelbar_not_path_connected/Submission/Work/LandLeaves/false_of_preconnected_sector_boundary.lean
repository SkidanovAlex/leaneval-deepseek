import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology
/-- No nonempty preconnected set of unit complex numbers can be contained in the *boundary* of the
sector `(c * d ^ n).re = 0` (a line through the origin meets the circle in two points, so
`c * d ^ n ∈ {i‖c‖, -i‖c‖}`) while being invariant under an `n`-th root of unity `z` with
`z ^ n = -1`.
Hint: `d ↦ c * d ^ n` maps `L` into the two-point set `{i * ‖c‖, -i * ‖c‖}` and is continuous, so
its image is preconnected, hence a single point `a`; then for `d ∈ L` one gets
`c * (z * d) ^ n = c * d ^ n = a`, so `z ^ n = 1`, contradicting `hzn : z ^ n = -1`. -/
theorem false_of_preconnected_sector_boundary {n : ℕ} (hn : 2 ≤ n) {c z : ℂ} (hc : c ≠ 0)
    (hzn : z ^ n = -1) (hz1 : z ≠ 1) {L : Set ℂ} (hLcpt : IsCompact L)
    (hLpre : IsPreconnected L) (hLne : L.Nonempty) (hLsph : L ⊆ Metric.sphere (0 : ℂ) 1)
    (hLsect : ∀ d ∈ L, (c * d ^ n).re = 0) (hLinv : ∀ d ∈ L, z * d ∈ L) : False := by
  -- Every point of `L` lies on the unit circle.
  have hnorm1 : ∀ d ∈ L, ‖d‖ = 1 := by
    intro d hd
    have h : dist d (0 : ℂ) = 1 := Metric.mem_sphere.mp (hLsph hd)
    rwa [dist_zero_right] at h
  -- Hence `c * d ^ n` has modulus `‖c‖` for `d ∈ L`.
  have hnormw : ∀ d ∈ L, ‖c * d ^ n‖ = ‖c‖ := by
    intro d hd
    rw [norm_mul, norm_pow, hnorm1 d hd, one_pow, mul_one]
  -- The real part of `c * d ^ n` vanishes, so its imaginary part is `± ‖c‖`.
  have him : ∀ d ∈ L, (c * d ^ n).im = ‖c‖ ∨ (c * d ^ n).im = -‖c‖ := by
    intro d hd
    have hns : Complex.normSq (c * d ^ n) = (c * d ^ n).im ^ 2 := by
      rw [Complex.normSq_apply, hLsect d hd]; ring
    have hsq : (c * d ^ n).im ^ 2 = ‖c‖ ^ 2 := by
      rw [← hns, Complex.normSq_eq_norm_sq, hnormw d hd]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  -- The imaginary part is constant on `L`, by the intermediate value theorem.
  have hconst : ∀ a ∈ L, ∀ b ∈ L, (c * a ^ n).im = (c * b ^ n).im := by
    intro a ha b hb
    by_contra hne
    have hcont : ContinuousOn (fun d : ℂ => (c * d ^ n).im) L := by fun_prop
    rcases him a ha with ha1 | ha2 <;> rcases him b hb with hb1 | hb2
    · exact hne (ha1.trans hb1.symm)
    · -- `im a = ‖c‖`, `im b = -‖c‖`: IVT on the reversed orientation
      have h0 : (0 : ℝ) ∈ Set.Icc ((c * b ^ n).im) ((c * a ^ n).im) := by
        rw [hb2, ha1, Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
      obtain ⟨t, htL, htval⟩ := (hLpre.intermediate_value hb ha hcont) h0
      dsimp only at htval
      rcases him t htL with h | h <;> rw [h] at htval <;> linarith
    · -- `im a = -‖c‖`, `im b = ‖c‖`
      have h0 : (0 : ℝ) ∈ Set.Icc ((c * a ^ n).im) ((c * b ^ n).im) := by
        rw [ha2, hb1, Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
      obtain ⟨t, htL, htval⟩ := (hLpre.intermediate_value ha hb hcont) h0
      dsimp only at htval
      rcases him t htL with h | h <;> rw [h] at htval <;> linarith
    · exact hne (ha2.trans hb2.symm)
  -- So `c * d ^ n` itself is constant on `L`.
  obtain ⟨d₀, hd₀⟩ := hLne
  have hconstf : ∀ d ∈ L, c * d ^ n = c * d₀ ^ n := by
    intro d hd
    apply Complex.ext
    · rw [hLsect d hd, hLsect d₀ hd₀]
    · rw [hconst d hd d₀ hd₀]
  have key : ∀ d ∈ L, c * (z * d) ^ n = c * d ^ n := by
    intro d hd
    rw [hconstf (z * d) (hLinv d hd), hconstf d hd]
  -- `d₀ ≠ 0` and the invariance give `z ^ n = 1`.
  have hd₀ne : d₀ ≠ 0 := by
    intro h
    have h1 : ‖d₀‖ = 1 := hnorm1 d₀ hd₀
    rw [h, norm_zero] at h1
    norm_num at h1
  have hcd : c * d₀ ^ n ≠ 0 := mul_ne_zero hc (pow_ne_zero n hd₀ne)
  have hkey := key d₀ hd₀
  rw [mul_pow] at hkey
  have h2 : c * d₀ ^ n * z ^ n = c * d₀ ^ n * 1 := by
    rw [mul_one]
    calc c * d₀ ^ n * z ^ n = c * (z ^ n * d₀ ^ n) := by ring
      _ = c * d₀ ^ n := hkey
  have hzn1 : z ^ n = 1 := mul_left_cancel₀ hcd h2
  rw [hzn] at hzn1
  norm_num at hzn1

end Work.LandLeaves
