import Mathlib
import Submission.Work.WilC4aA.Defs
import Submission.Work.WilC4aA.analytic_factor
import Submission.Work.WilC4aA.analytic_hasAsymAt0
import Submission.Work.WilC4aA.asym_div_rpow
import Submission.Work.WilC4aA.analyticAt_exists_continuousOn

set_option autoImplicit false
noncomputable section
open Classical Topology Filter Set

namespace Work.WilC4aA

/-- **Surjectivity onto a right-neighbourhood of `0` by the intermediate value theorem.**

If `t` is continuous on `[0, ε]` with `t 0 = 0` and `ε > 0`, then `t` realises every value in
`(0, t ε)` at some point `s ∈ (0, ε)`.  (One uses `t 0 = 0 < t'` and `t' < t ε` to see that the
intermediate point can be neither endpoint.) -/
theorem exists_eta_of_continuousOn {t : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (h0 : t 0 = 0)
    (hcont : ContinuousOn t (Set.Icc 0 ε)) :
    ∀ t' ∈ Set.Ioo (0 : ℝ) (t ε), ∃ s ∈ Set.Ioo (0 : ℝ) ε, t s = t' := by
  intro t' ht'
  obtain ⟨ht'pos, ht'lt⟩ := ht'
  have hmem : t' ∈ Set.Icc (t 0) (t ε) :=
    ⟨by rw [h0]; exact le_of_lt ht'pos, le_of_lt ht'lt⟩
  obtain ⟨s, hsIcc, hseq⟩ := intermediate_value_Icc hε.le hcont hmem
  have hsne : s ≠ 0 := by
    intro h
    rw [h, h0] at hseq
    exact (ne_of_gt ht'pos) hseq.symm
  have hsne' : s ≠ ε := by
    intro h
    rw [h] at hseq
    exact (ne_of_lt ht'lt) hseq.symm
  exact ⟨s, ⟨lt_of_le_of_ne hsIcc.1 (Ne.symm hsne), lt_of_le_of_ne hsIcc.2 hsne'⟩, hseq⟩

/-- **A positive lower bound on a compact interval.**  A continuous function which is strictly
positive on `Icc δ ε` (with `δ ≤ ε`) is bounded below by a positive constant there. -/
theorem exists_pos_lower_bound {t : ℝ → ℝ} {δ ε : ℝ} (_hδ : 0 < δ) (hδε : δ ≤ ε)
    (hcont : ContinuousOn t (Set.Icc δ ε)) (hpos : ∀ s ∈ Set.Icc δ ε, 0 < t s) :
    ∃ m > (0 : ℝ), ∀ s ∈ Set.Icc δ ε, m ≤ t s := by
  obtain ⟨x, hx, hxmin⟩ :=
    (isCompact_Icc (a := δ) (b := ε)).exists_isMinOn ⟨δ, le_rfl, hδε⟩ hcont
  exact ⟨t x, hpos x hx, fun s hs => hxmin hs⟩

/-- **Rational-exponent asymptotics along an analytic arc.**

Let `t, y : ℝ → ℝ` be analytic at `0` with `t 0 = 0` and `t > 0` on a right-neighbourhood of
`0`.  Then there are `ε, η > 0` such that `t` maps `(0, ε)` onto `(0, η)`, and on that arc either
`y` vanishes identically, or there are `q : ℚ` and `a ≠ 0` with `y(s) / t'^q → a` as
`t' = t(s) → 0⁺` (uniformly over the arc).

The proof factors `t s = s^N u(s)` (`analytic_factor`) with `N ≥ 1`, `u 0 > 0`, so that
`y(s) / t(s)^q` is `(y(s)/s^m) · u(s)^{-q}` (`asym_div_rpow`), whose limit at `0⁺` is nonzero;
`ε` is chosen so small that a single `δ` from this limit covers the whole arc. -/
theorem asymT_of_arc {t y : ℝ → ℝ} (ht : AnalyticAt ℝ t 0) (ht0 : t 0 = 0)
    (hpos : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t s) (hy : AnalyticAt ℝ y 0) :
    ∃ ε > (0 : ℝ), ∃ η > (0 : ℝ),
      (∀ t' ∈ Set.Ioo (0 : ℝ) η, ∃ s ∈ Set.Ioo (0 : ℝ) ε, t s = t') ∧
      ((∃ η' > (0 : ℝ), ∀ t' ∈ Set.Ioo (0 : ℝ) η', ∀ s ∈ Set.Ioo (0 : ℝ) ε, t s = t' →
          y s = 0) ∨
        ∃ (q : ℚ) (a : ℝ), a ≠ 0 ∧ ∀ ε' > (0 : ℝ), ∃ η' > (0 : ℝ),
          ∀ t' ∈ Set.Ioo (0 : ℝ) η', ∀ s ∈ Set.Ioo (0 : ℝ) ε, t s = t' →
            |y s / t' ^ ((q : ℝ)) - a| < ε') := by
  -- Factor `t s = s^N * u s` and get the one-sided asymptotics of `y` in terms of `s`.
  obtain ⟨N, u, hN, hu, hu0, _hupos, htu⟩ := analytic_factor ht ht0 hpos
  obtain ⟨htpos, hcases⟩ := asym_div_rpow hN hu hu0 htu (analytic_hasAsymAt0 hy)
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := eventually_nhdsGT_iff.mp htpos
  obtain ⟨rt, hrtpos, hcontt⟩ := analyticAt_exists_continuousOn ht
  rcases hcases with hy0 | ⟨q, b, hb, hlim⟩
  · -- **Case 1.** `y` vanishes for small positive arguments.
    obtain ⟨εz, hεzpos, hεz⟩ := eventually_nhdsGT_iff.mp hy0
    set ε : ℝ := min (min ε₁ rt) εz / 2 with hεdef
    have hminpos : (0 : ℝ) < min (min ε₁ rt) εz := lt_min (lt_min hε₁pos hrtpos) hεzpos
    have hεpos : 0 < ε := by rw [hεdef]; exact half_pos hminpos
    have hε_lt₁ : ε < ε₁ := by
      rw [hεdef]
      linarith [min_le_left (min ε₁ rt) εz, min_le_left ε₁ rt]
    have hε_lt_t : ε < rt := by
      rw [hεdef]
      linarith [min_le_left (min ε₁ rt) εz, min_le_right ε₁ rt]
    have hε_lt_z : ε < εz := by
      rw [hεdef]
      linarith [min_le_right (min ε₁ rt) εz]
    have htεpos : 0 < t ε := hε₁ ε ⟨hεpos, hε_lt₁⟩
    have hcontε : ContinuousOn t (Set.Icc 0 ε) :=
      hcontt.mono (fun s hs => ⟨by linarith [hs.1], lt_of_le_of_lt hs.2 hε_lt_t⟩)
    refine ⟨ε, hεpos, t ε, htεpos, exists_eta_of_continuousOn hεpos ht0 hcontε, Or.inl ?_⟩
    refine ⟨1, one_pos, ?_⟩
    intro t' _ s hs _
    exact hεz s ⟨hs.1, lt_of_lt_of_le hs.2 (le_of_lt hε_lt_z)⟩
  · -- **Case 2.** `y s / t s ^ q → b ≠ 0` along `0⁺`.
    set ε : ℝ := min ε₁ rt / 2 with hεdef
    have hminpos : (0 : ℝ) < min ε₁ rt := lt_min hε₁pos hrtpos
    have hεpos : 0 < ε := by rw [hεdef]; exact half_pos hminpos
    have hε_lt₁ : ε < ε₁ := by rw [hεdef]; linarith [min_le_left ε₁ rt]
    have hε_lt_t : ε < rt := by rw [hεdef]; linarith [min_le_right ε₁ rt]
    have htεpos : 0 < t ε := hε₁ ε ⟨hεpos, hε_lt₁⟩
    have hcontε : ContinuousOn t (Set.Icc 0 ε) :=
      hcontt.mono (fun s hs => ⟨by linarith [hs.1], lt_of_le_of_lt hs.2 hε_lt_t⟩)
    refine ⟨ε, hεpos, t ε, htεpos, exists_eta_of_continuousOn hεpos ht0 hcontε,
      Or.inr ⟨q, b, hb, ?_⟩⟩
    intro ε' hε'pos
    obtain ⟨δ, hδpos, hδ⟩ := eventually_nhdsGT_iff.mp ((Metric.tendsto_nhds.mp hlim) ε' hε'pos)
    by_cases hδε : ε ≤ δ
    · -- The whole arc already lies inside the convergence interval.
      refine ⟨t ε, htεpos, ?_⟩
      intro t' _ s hs hseq
      have hthis := hδ s ⟨hs.1, lt_of_lt_of_le hs.2 hδε⟩
      rw [Real.dist_eq] at hthis
      rw [← hseq]
      exact hthis
    · -- `δ < ε`: only points `s ≥ δ` are excluded, and for small `t'` none of these occur.
      have hδε' : δ < ε := lt_of_not_ge hδε
      have hcontδε : ContinuousOn t (Set.Icc δ ε) :=
        hcontt.mono (fun s hs => ⟨by linarith [hs.1, hδpos], lt_of_le_of_lt hs.2 hε_lt_t⟩)
      have hposδε : ∀ s ∈ Set.Icc δ ε, 0 < t s := fun s hs =>
        hε₁ s ⟨lt_of_lt_of_le hδpos hs.1, lt_of_le_of_lt hs.2 hε_lt₁⟩
      obtain ⟨m, hmpos, hmle⟩ := exists_pos_lower_bound hδpos (le_of_lt hδε') hcontδε hposδε
      refine ⟨m, hmpos, ?_⟩
      intro t' ht' s hs hseq
      have hsd : s < δ := by
        by_contra hcon
        rw [not_lt] at hcon
        have hsIcc : s ∈ Set.Icc δ ε := ⟨hcon, le_of_lt hs.2⟩
        have hle : m ≤ t s := hmle s hsIcc
        rw [hseq] at hle
        exact absurd (lt_of_lt_of_le ht'.2 hle) (lt_irrefl t')
      have hthis := hδ s ⟨hs.1, hsd⟩
      rw [Real.dist_eq] at hthis
      rw [← hseq]
      exact hthis

end Work.WilC4aA
