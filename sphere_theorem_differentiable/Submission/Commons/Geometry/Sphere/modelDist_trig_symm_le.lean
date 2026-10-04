import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Geometry.Sphere

/-- The core monotonicity behind the symmetrised model distance: for `A ≤ 0 ≤ B` with
`A ± B ∈ [-1, 1]`, the map `u ↦ arccos (A + B*u) + arccos (A - B*u)` is monotone on
`[0, 1]`.  Equivalently, the sum of the two arccosines is maximised at the endpoints.

The proof passes to `arcsin` (using `arccos x = π/2 - arcsin x`), where the derivative is
`B·(1/√(1-(A+Bu)²) - 1/√(1-(A-Bu)²))`; since `A ≤ 0 ≤ B`, one has `(A+Bu)² ≤ (A-Bu)²`
for `u ≥ 0`, hence the derivative is `≤ 0`. -/
theorem arccos_shift_le' {A B t : ℝ} (hA : A ≤ 0) (hB : 0 ≤ B)
    (hAlow : -1 ≤ A - B) (hBhigh : A + B ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.arccos (A + B * t) + Real.arccos (A - B * t)
      ≤ Real.arccos (A + B) + Real.arccos (A - B) := by
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · subst hB0; simp
  · have hlt_hi : ∀ u ∈ Set.Ioo (0:ℝ) 1, A + B * u < 1 := by
      intro u hu
      have : A + B * u < A + B := by
        have := mul_lt_mul_of_pos_left hu.2 hBpos
        linarith
      linarith [hBhigh]
    have hlt_lo : ∀ u ∈ Set.Ioo (0:ℝ) 1, -1 < A + B * u := by
      intro u hu
      have : A - B < A + B * u := by
        have := mul_lt_mul_of_pos_left hu.1 hBpos
        linarith
      linarith [hAlow]
    have hlt_lo2 : ∀ u ∈ Set.Ioo (0:ℝ) 1, -1 < A - B * u := by
      intro u hu
      have : A - B < A - B * u := by
        have := mul_lt_mul_of_pos_left hu.2 hBpos
        linarith
      linarith [hAlow]
    have hlt_hi2 : ∀ u ∈ Set.Ioo (0:ℝ) 1, A - B * u < 1 := by
      intro u hu
      have : A - B * u < A := by
        have : 0 < B * u := mul_pos hBpos hu.1
        linarith
      linarith [hA]
    have hD1 : ∀ u ∈ Set.Ioo (0:ℝ) 1,
        HasDerivAt (fun u : ℝ => Real.arcsin (A + B * u))
          ((1 / Real.sqrt (1 - (A + B * u) ^ 2)) * B) u := by
      intro u hu
      have hinner : HasDerivAt (fun u : ℝ => A + B * u) B u := by
        have h : HasDerivAt (fun u : ℝ => B * u) B u := by
          simpa using (hasDerivAt_id u).const_mul B
        simpa using h.const_add A
      have houter : HasDerivAt Real.arcsin ((1 / Real.sqrt (1 - (A + B * u) ^ 2))) (A + B * u) :=
        Real.hasDerivAt_arcsin (ne_of_gt (hlt_lo u hu)) (ne_of_lt (hlt_hi u hu))
      exact houter.comp u hinner
    have hD2 : ∀ u ∈ Set.Ioo (0:ℝ) 1,
        HasDerivAt (fun u : ℝ => Real.arcsin (A - B * u))
          ((1 / Real.sqrt (1 - (A - B * u) ^ 2)) * (-B)) u := by
      intro u hu
      have hinner : HasDerivAt (fun u : ℝ => A - B * u) (-B) u := by
        have h : HasDerivAt (fun u : ℝ => B * u) B u := by
          simpa using (hasDerivAt_id u).const_mul B
        have h2 : HasDerivAt (fun u : ℝ => -(B * u)) (-B) u := h.neg
        have h3 := h2.const_add A
        simpa only [sub_eq_add_neg] using h3
      have houter : HasDerivAt Real.arcsin ((1 / Real.sqrt (1 - (A - B * u) ^ 2))) (A - B * u) :=
        Real.hasDerivAt_arcsin (ne_of_gt (hlt_lo2 u hu)) (ne_of_lt (hlt_hi2 u hu))
      exact houter.comp u hinner
    have hanti : AntitoneOn (fun u : ℝ => Real.arcsin (A + B * u) + Real.arcsin (A - B * u))
        (Set.Icc (0:ℝ) 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) 1)
      · exact (by fun_prop : Continuous (fun u : ℝ => Real.arcsin (A + B * u) + Real.arcsin (A - B * u))).continuousOn
      · rw [interior_Icc]
        intro u hu
        exact ((hD1 u hu).differentiableAt.add (hD2 u hu).differentiableAt).differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have h1 := hD1 u hu
        have h2 := hD2 u hu
        change deriv ((fun u : ℝ => Real.arcsin (A + B * u)) + (fun u : ℝ => Real.arcsin (A - B * u))) u ≤ 0
        rw [(h1.add h2).deriv]
        have hsq : (A + B * u) ^ 2 ≤ (A - B * u) ^ 2 := by
          have h1' : 0 ≤ -A := by linarith
          have h2' : 0 ≤ B * u := mul_nonneg hB (le_of_lt hu.1)
          nlinarith [h1', h2']
        have hp1 : 0 < 1 - (A + B * u) ^ 2 := by
          have := hlt_lo u hu; have := hlt_hi u hu; nlinarith
        have hq1 : 0 < 1 - (A - B * u) ^ 2 := by
          have := hlt_lo2 u hu; have := hlt_hi2 u hu; nlinarith
        have hsqrt : Real.sqrt (1 - (A - B * u) ^ 2) ≤ Real.sqrt (1 - (A + B * u) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
        have hposq : 0 < Real.sqrt (1 - (A - B * u) ^ 2) := Real.sqrt_pos_of_pos hq1
        have hrec : 1 / Real.sqrt (1 - (A + B * u) ^ 2) ≤ 1 / Real.sqrt (1 - (A - B * u) ^ 2) :=
          one_div_le_one_div_of_le hposq hsqrt
        have key : B * (1 / Real.sqrt (1 - (A + B * u) ^ 2) - 1 / Real.sqrt (1 - (A - B * u) ^ 2)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hB (by linarith [hrec])
        linarith [key]
    have ht_mem : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0, ht1⟩
    have h1mem : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
    have hH := hanti ht_mem h1mem ht1
    simp only [mul_one] at hH
    rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin,
        Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
    linarith

/-- The endpoint (collinear) case of the symmetrised model distance: when the two azimuths
coincide (`cos α = ± 1`), the sum of the two arccosines is exactly `2r`. -/
theorem arccos_modelDist_endpoints' {a r : ℝ} (ha : 0 ≤ a) (har : a + r ≤ Real.pi)
    (hr : Real.pi / 2 ≤ r) (hr' : r ≤ Real.pi) :
    Real.arccos (Real.cos a * Real.cos r + Real.sin a * Real.sin r)
      + Real.arccos (Real.cos a * Real.cos r - Real.sin a * Real.sin r) = 2 * r := by
  have har1 : Real.cos a * Real.cos r + Real.sin a * Real.sin r = Real.cos (a - r) := by
    rw [Real.cos_sub]
  have har2 : Real.cos a * Real.cos r - Real.sin a * Real.sin r = Real.cos (a + r) := by
    rw [Real.cos_add]
  rw [har1, har2]
  have hneg : a - r = -(r - a) := by ring
  rw [hneg, Real.cos_neg]
  have hra0 : 0 ≤ r - a := by linarith
  have hraπ : r - a ≤ Real.pi := by linarith
  have hab0 : 0 ≤ a + r := by linarith
  rw [Real.arccos_cos hra0 hraπ, Real.arccos_cos hab0 har]
  ring

/-- **Symmetry of the model distance sum.**  For a spherical triangle with two sides `a`, `r`
(so that `a + r ≤ π` and `r ≥ π/2`), the sum of the two model distances obtained from the
azimuthal angles `α` and `π - α` is at most `2r`.  This is the "folding" estimate used in the
topological sphere theorem. -/
theorem modelDist_trig_symm_le {a r α : ℝ} (ha : 0 ≤ a) (har : a + r ≤ Real.pi)
    (hr : Real.pi / 2 ≤ r) (hr' : r ≤ Real.pi) (hα : 0 ≤ α) (hα' : α ≤ Real.pi) :
    Real.arccos (Real.cos a * Real.cos r + Real.sin a * Real.sin r * Real.cos α)
      + Real.arccos (Real.cos a * Real.cos r + Real.sin a * Real.sin r * Real.cos (Real.pi - α))
      ≤ 2 * r := by
  have ha2 : a ≤ Real.pi / 2 := by linarith
  have hcos_a : 0 ≤ Real.cos a :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ha2⟩
  have hsin_a : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha (by linarith)
  have hsin_r : 0 ≤ Real.sin r := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) hr'
  have hcos_r : Real.cos r ≤ 0 := by
    have h1 : Real.pi / 2 ∈ Set.Icc (0:ℝ) Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
    have h2 : r ∈ Set.Icc (0:ℝ) Real.pi := ⟨by linarith [Real.pi_pos], hr'⟩
    have := Real.cos_le_cos_of_nonneg_of_le_pi h1.1 h2.2 hr
    simpa [Real.cos_pi_div_two] using this
  have hA : Real.cos a * Real.cos r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcos_a hcos_r
  have hB : 0 ≤ Real.sin a * Real.sin r := mul_nonneg hsin_a hsin_r
  have hABm : -1 ≤ Real.cos a * Real.cos r - Real.sin a * Real.sin r := by
    rw [← Real.cos_add]; exact Real.neg_one_le_cos (a + r)
  have hAB : Real.cos a * Real.cos r + Real.sin a * Real.sin r ≤ 1 := by
    rw [← Real.cos_sub]; exact Real.cos_le_one (a - r)
  have key : ∀ t ∈ Set.Icc (0:ℝ) 1,
      Real.arccos (Real.cos a * Real.cos r + Real.sin a * Real.sin r * t)
        + Real.arccos (Real.cos a * Real.cos r - Real.sin a * Real.sin r * t) ≤ 2 * r := by
    intro t ht
    refine le_trans (arccos_shift_le' hA hB hABm hAB ht.1 ht.2) ?_
    exact le_of_eq (arccos_modelDist_endpoints' ha har hr hr')
  rw [Real.cos_pi_sub]
  have hargA : Real.cos a * Real.cos r + Real.sin a * Real.sin r * (-Real.cos α)
      = Real.cos a * Real.cos r - Real.sin a * Real.sin r * Real.cos α := by ring
  rcases le_total 0 (Real.cos α) with hc | hc
  · rw [hargA]
    exact key (Real.cos α) ⟨hc, Real.cos_le_one α⟩
  · have hgoal : Real.arccos (Real.cos a * Real.cos r + Real.sin a * Real.sin r * Real.cos α)
        + Real.arccos (Real.cos a * Real.cos r + Real.sin a * Real.sin r * (-Real.cos α))
        = Real.arccos (Real.cos a * Real.cos r + Real.sin a * Real.sin r * (-Real.cos α))
        + Real.arccos (Real.cos a * Real.cos r - Real.sin a * Real.sin r * (-Real.cos α)) := by
      rw [show Real.cos a * Real.cos r - Real.sin a * Real.sin r * (-Real.cos α)
            = Real.cos a * Real.cos r + Real.sin a * Real.sin r * Real.cos α by ring]
      ring
    rw [hgoal]
    exact key (-Real.cos α) ⟨by linarith, by linarith [Real.neg_one_le_cos α]⟩

end Commons.Geometry.Sphere