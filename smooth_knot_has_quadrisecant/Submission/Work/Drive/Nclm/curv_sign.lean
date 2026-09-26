import Mathlib
import Submission.Work.Drive.H2.chartE_accel_neg
import Submission.Work.Drive.H2.baseHeight_lower
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Generic.nclmE0
import Submission.Work.Drive.AB.windowDataSmall

namespace Work.Drive.Nclm

open LeanEval.KnotTheory.Quadrisecant

/-!
# The sign of the curvature numerator against the needle's chart

This module proves `Work.Drive.Nclm.curv_sign`.  The quantity

`⟪r'(x) ∧ r''(x), v ∧ chartE⟫`

(with `v` the unit direction of the needle's chord and `chartE = ‖chartUp‖⁻¹ • chartUp` the unit
"up" direction of the needle's chart) is the *sign of the curvature* of the band arc, measured in
the frame of the needle's chart.  By Binet–Cauchy it equals

`⟪r'(x), v⟫ * ⟪r''(x), chartE⟫ - ⟪r'(x), chartE⟫ * ⟪r''(x), v⟫`,

and the three inputs are:

* `⟪r''(x), chartE⟫ ≤ -c < 0` — `Work.Drive.H2.chartE_accel_neg` (the acceleration points opposite
  to the chart's "up" direction, because the chart's up direction is the sagitta direction);
* `⟪r'(x), v⟫ ≥ m/4 > 0` — `Work.Drive.Generic.nclm_tang` (the velocity is tangent to a short arc,
  hence nearly parallel to the chord direction);
* `|⟪r'(x), chartE⟫| ≤ (K + m) * δ` — because `chartE ⊥ v` and `r'(x)` is `δ`-close to the
  velocity at the collapsed end, which is parallel to `v` up to the small direction error
  (`Work.Drive.windowDataSmall`).

Choosing `δ` small enough that `(K + m) * K * δ ≤ m * c / 4` (and `δ` is the parameter of
`windowDataSmall`) makes the first term dominate the second, so the total is `≤ 0`.
-/

/-- **Binet–Cauchy for the cross product** on `Space`:
`⟪a ∧ b, c ∧ d⟫ = ⟪a, c⟫ * ⟪b, d⟫ - ⟪a, d⟫ * ⟪b, c⟫`. -/
lemma binet_cauchy_crossv (a b c d : Space) :
    inner ℝ (Work.Drive.crossv a b) (Work.Drive.crossv c d)
      = inner ℝ a c * inner ℝ b d - inner ℝ a d * inner ℝ b c := by
  simp only [Work.Drive.inner_eq_dot, Work.Drive.crossv_ofLp]
  exact cross_dot_cross a.ofLp b.ofLp c.ofLp d.ofLp

/-- Normalising a vector gives a vector of norm at most `1`. -/
lemma norm_inv_smul_le_one (x : Space) : ‖(‖x‖)⁻¹ • x‖ ≤ 1 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  rcases eq_or_ne x 0 with rfl | hne
  · simp
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

/-- A Lipschitz bound for the velocity, from a global bound on the acceleration. -/
lemma deriv_lipschitz_of_accel_bound {r : ℝ → Space} (hr : IsSmoothKnot r) {K : ℝ}
    (hK : ∀ x : ℝ, ‖deriv (deriv r) x‖ ≤ K) :
    ∀ x y : ℝ, ‖deriv r x - deriv r y‖ ≤ K * |x - y| := by
  have hs : ContDiff ℝ Work.Drive.cInfT r := hr.smooth.of_le le_top
  have hd : ContDiff ℝ Work.Drive.cInfT (deriv r) :=
    ((contDiff_infty_iff_deriv (𝕜 := ℝ)).mp hs).2
  intro x y
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := deriv r) (s := Set.univ)
    (C := K) (fun t _ => (hd.differentiable (by simp)) t) (fun t _ => hK t) convex_univ
    (Set.mem_univ x) (Set.mem_univ y)
  simpa [Real.norm_eq_abs, norm_sub_rev, abs_sub_comm] using h

theorem curv_sign {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ 1 / 4 ∧
        ∀ lam δ₁ δ₂ : ℝ, 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ v : LeanEval.KnotTheory.Quadrisecant.Space, ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
        ∀ x : ℝ, Work.Drive.taR D σ ≤ x → x ≤ Work.Drive.tbR D σ →
          inner ℝ (Work.Drive.crossv (LeanEval.KnotTheory.Quadrisecant.velocity r x)
              (deriv (deriv r) x))
            (Work.Drive.crossv v (Work.Drive.chartE r D lam δ₁ δ₂ ε v)) ≤ 0 := by
  -- a global bound for the acceleration
  obtain ⟨K, hK1, hKb⟩ := Work.Drive.H2.H2_accel_bound hr
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  -- the speed at the collapsed end
  set m : ℝ := ‖deriv r (Work.Drive.taR D 0)‖ with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact norm_pos_iff.mpr (hr.regular (Work.Drive.taR D 0))
  -- the definite transverse acceleration of the chart
  obtain ⟨c, hc0, εc, hεc0, hεc12, hchart⟩ := Work.Drive.H2.chartE_accel_neg hr hinfl D
  -- the smallness threshold for the arc-closeness
  set δ : ℝ := m * c / (8 * K * (K + m)) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hnum : (K + m) * K * δ ≤ m * c / 4 := by
    have hKne : K ≠ 0 := ne_of_gt hK0
    have hKm : K + m ≠ 0 := ne_of_gt (by linarith)
    have h1 : (K + m) * K * δ = m * c / 8 := by
      rw [hδdef]
      field_simp
    rw [h1]
    linarith [mul_pos hmpos hc0]
  -- the three thresholds
  obtain ⟨εw, hεw0, hεw1, hwin⟩ := Work.Drive.windowDataSmall hr D δ hδ0
  obtain ⟨εt, hεt0, hεt12, htang⟩ := Work.Drive.Generic.nclm_tang hr D
  refine ⟨min (min εc εw) (min εt (1 / 2)),
    lt_min (lt_min hεc0 hεw0) (lt_min hεt0 (by norm_num)),
    le_trans (min_le_right _ _) (min_le_right _ _), ?_⟩
  intro ε hε0 hεle
  have hεc : ε ≤ εc := le_trans hεle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεw : ε ≤ εw := le_trans hεle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεt : ε ≤ εt := le_trans hεle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεhalf : ε ≤ 1 / 2 := le_trans hεle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Λ, hΛ0, hΛ14, hΛmain⟩ := hchart ε hε0 hεc
  refine ⟨Λ, hΛ0, hΛ14, ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε v hv hcv σ hσlo hσhi x hxlo hxhi
  -- the chord vector and `v` as its unit direction
  set C : Space := Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε with hC
  obtain ⟨harcC, hCne, hdirC⟩ := hwin δ₂ ε hδ₂0 hδ₂ε hε0 hεw
  have hCne' : C ≠ 0 := by rw [hC]; exact sub_ne_zero.mpr hCne
  have hvunit : v = ‖C‖⁻¹ • C := by
    have h2 : ‖C‖ ≠ 0 := norm_ne_zero_iff.mpr hCne'
    have hgen : ∀ y : Space, y = ‖C‖ • v → ‖C‖⁻¹ • y = v := fun y hy => by
      rw [hy, smul_smul, inv_mul_cancel₀ h2, one_smul]
    exact (hgen C (by rw [hC]; exact hcv)).symm
  -- the unit tangent at the collapsed end
  set T : Space := (‖deriv r (Work.Drive.taR D 0)‖)⁻¹ • deriv r (Work.Drive.taR D 0) with hT
  have hdirv : ‖v - T‖ ≤ δ := by
    rw [hvunit, hT, hC]
    exact hdirC
  -- the chart's up direction
  set E : Space := Work.Drive.chartE r D lam δ₁ δ₂ ε v with hEdef
  change inner ℝ (Work.Drive.crossv (deriv r x) (deriv (deriv r) x)) (Work.Drive.crossv v E) ≤ 0
  -- the tangent pairing with the chord direction is positive
  have hav : m / 4 ≤ inner ℝ (deriv r x) v := by
    have h := htang δ₂ ε σ x hδ₂0 hδ₂ε hε0 hεt hσlo hσhi ⟨hxlo, hxhi⟩
    simpa only [hm, hvunit, hC, velocity] using h
  -- `x` as a fraction of the retained arc, and the closeness to the collapsed end
  have hWσpos := Work.Drive.Generic.nclm_window_wpos D hδ₂0 hδ₂ε hε0 hεhalf hσlo hσhi
  have hwtb : Work.Drive.taR D σ + Work.Drive.sweepW' D σ = Work.Drive.tbR D σ := by
    rw [Work.Drive.sweepW']; ring
  set ξ : ℝ := (x - Work.Drive.taR D σ) / Work.Drive.sweepW' D σ with hξ
  have hξ0 : 0 ≤ ξ := by rw [hξ]; exact div_nonneg (by linarith) hWσpos.le
  have hξ1 : ξ ≤ 1 := by rw [hξ, div_le_one hWσpos]; linarith
  have hxeq : x = Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ := by
    rw [hξ]; field_simp; ring
  have hxclose : |x - Work.Drive.taR D 0| ≤ δ := by
    rw [hxeq]
    exact harcC σ hσlo hσhi ξ hξ0 hξ1
  -- the velocity at `x` is close to the velocity at the collapsed end
  have hdv : ‖deriv r x - deriv r (Work.Drive.taR D 0)‖ ≤ K * δ := by
    have h1 := deriv_lipschitz_of_accel_bound hr hKb x (Work.Drive.taR D 0)
    calc ‖deriv r x - deriv r (Work.Drive.taR D 0)‖ ≤ K * |x - Work.Drive.taR D 0| := h1
      _ ≤ K * δ := mul_le_mul_of_nonneg_left hxclose hK0.le
  -- the chart vector is a bounded vector
  have hE : ‖E‖ ≤ 1 := by
    rw [hEdef, Work.Drive.chartE]
    exact norm_inv_smul_le_one _
  have hEv : inner ℝ E v = 0 := by
    rw [hEdef, Work.Drive.chartE, real_inner_smul_left,
      Work.Drive.inner_chartUp_v r D lam δ₁ δ₂ ε hv, mul_zero]
  -- the tangent at the collapsed end, rescaled
  have hv0T : deriv r (Work.Drive.taR D 0) = m • T := by
    have hv0ne : deriv r (Work.Drive.taR D 0) ≠ 0 := hr.regular (Work.Drive.taR D 0)
    rw [hT, hm, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne), one_smul]
  -- the velocity–chart pairing is small
  have hAE : |inner ℝ (deriv r x) E| ≤ (K + m) * δ := by
    have hsplit : inner ℝ (deriv r x - deriv r (Work.Drive.taR D 0)) E + m * inner ℝ T E
        = inner ℝ (deriv r x) E := by
      rw [inner_sub_left, hv0T, real_inner_smul_left]
      ring
    have h2 : |inner ℝ (deriv r x - deriv r (Work.Drive.taR D 0)) E| ≤ K * δ := by
      calc |inner ℝ (deriv r x - deriv r (Work.Drive.taR D 0)) E|
          ≤ ‖deriv r x - deriv r (Work.Drive.taR D 0)‖ * ‖E‖ := abs_real_inner_le_norm _ _
        _ ≤ (K * δ) * 1 := mul_le_mul hdv hE (norm_nonneg _) (mul_nonneg hK0.le hδ0.le)
        _ = K * δ := by ring
    have h3 : |m * inner ℝ T E| ≤ m * δ := by
      have hEv' : inner ℝ v E = 0 := by rw [real_inner_comm]; exact hEv
      have h4 : inner ℝ T E = inner ℝ (T - v) E := by
        rw [inner_sub_left, hEv', sub_zero]
      have h5 : |inner ℝ (T - v) E| ≤ δ := by
        calc |inner ℝ (T - v) E| ≤ ‖T - v‖ * ‖E‖ := abs_real_inner_le_norm _ _
          _ ≤ δ * 1 := mul_le_mul (by rw [norm_sub_rev]; exact hdirv) hE (norm_nonneg _) hδ0.le
          _ = δ := by ring
      rw [h4, abs_mul, abs_of_pos hmpos]
      exact mul_le_mul_of_nonneg_left h5 hmpos.le
    rw [← hsplit]
    calc |inner ℝ (deriv r x - deriv r (Work.Drive.taR D 0)) E + m * inner ℝ T E|
        ≤ |inner ℝ (deriv r x - deriv r (Work.Drive.taR D 0)) E| + |m * inner ℝ T E| :=
          abs_add_le _ _
      _ ≤ K * δ + m * δ := add_le_add h2 h3
      _ = (K + m) * δ := by ring
  -- the acceleration–chord pairing is bounded
  have hBv : |inner ℝ (deriv (deriv r) x) v| ≤ K := by
    calc |inner ℝ (deriv (deriv r) x) v| ≤ ‖deriv (deriv r) x‖ * ‖v‖ :=
          abs_real_inner_le_norm _ _
      _ = ‖deriv (deriv r) x‖ := by rw [hv, mul_one]
      _ ≤ K := hKb x
  -- the acceleration–chart pairing is negative
  have hiter : iteratedDeriv 2 r = deriv (deriv r) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  have hBE : inner ℝ (deriv (deriv r) x) E ≤ -c := by
    have h := hΛmain lam δ₁ δ₂ hlam0 hlamΛ hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε v hv hcv
      σ hσlo hσhi x hxlo hxhi
    rw [hEdef, ← hiter]
    exact h
  -- Binet–Cauchy and the two estimates
  rw [binet_cauchy_crossv]
  have hb0 : inner ℝ (deriv (deriv r) x) E ≤ 0 := by linarith [hBE, hc0]
  have h1 : inner ℝ (deriv r x) v * inner ℝ (deriv (deriv r) x) E ≤ -(m * c / 4) := by
    have hstep : inner ℝ (deriv r x) v * inner ℝ (deriv (deriv r) x) E
        ≤ (m / 4) * inner ℝ (deriv (deriv r) x) E := by
      have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hav) hb0
      nlinarith [hmul]
    have hstep2 : (m / 4) * inner ℝ (deriv (deriv r) x) E ≤ (m / 4) * (-c) :=
      mul_le_mul_of_nonneg_left hBE (by linarith [hmpos])
    linarith
  have h2 : -(inner ℝ (deriv r x) E * inner ℝ (deriv (deriv r) x) v) ≤ (K + m) * K * δ := by
    have habs : |inner ℝ (deriv r x) E * inner ℝ (deriv (deriv r) x) v|
        ≤ (K + m) * δ * K := by
      rw [abs_mul]
      exact mul_le_mul hAE hBv (abs_nonneg _) (by positivity)
    have hle : -(inner ℝ (deriv r x) E * inner ℝ (deriv (deriv r) x) v)
        ≤ (K + m) * δ * K := by
      simpa only [neg_neg] using neg_le_neg (neg_le_of_abs_le habs)
    calc -(inner ℝ (deriv r x) E * inner ℝ (deriv (deriv r) x) v)
        ≤ (K + m) * δ * K := hle
      _ = (K + m) * K * δ := by ring
  have hsum := add_le_add h1 (le_trans h2 hnum)
  have hz : -(m * c / 4) + m * c / 4 = 0 := by ring
  rw [hz] at hsum
  have hfin : inner ℝ (deriv r x) v * inner ℝ (deriv (deriv r) x) E
        - inner ℝ (deriv r x) E * inner ℝ (deriv (deriv r) x) v
      = inner ℝ (deriv r x) v * inner ℝ (deriv (deriv r) x) E
        + -(inner ℝ (deriv r x) E * inner ℝ (deriv (deriv r) x) v) := by ring
  rw [hfin]
  exact hsum

end Work.Drive.Nclm
