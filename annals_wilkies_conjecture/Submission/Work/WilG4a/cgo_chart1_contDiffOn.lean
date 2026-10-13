import Mathlib
import Submission.Work.WilG4a.LipChartsDefs

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical
open Filter

namespace Work.WilG4a

/-! ## Continuity and differentiability of the chart `chart1 f κ l` on `I`

The chart `chart1 f κ l` is the branch of the inverse of `x ↦ f l x` over the image of the
fibre, linearly reparametrised by `t`.  The two hypotheses that drive everything are

* `hmono` : `f l` is strictly monotone on the fibre `fibre κ l = (a,b)`, and
* `hchar` : for `t ∈ I` the point `chart1 f κ l t` lies in the fibre and
  `f l (chart1 f κ l t) = Aend + (Bend - Aend) * t`.

Since `f l` is injective on the fibre, `chart1 f κ l` is *the* point of the fibre at which
`f l` takes the prescribed value, so it is a right inverse of the strictly monotone function
`f l` composed with the affine reparametrisation `t ↦ Aend + (Bend - Aend) * t`.  Continuity of
such a right inverse is purely order-theoretic (no continuity of `f l` is needed), and once
continuity is known the derivative is the "easy half of the inverse function theorem"
(`HasDerivAt.of_comp_left`). -/

/-- **Continuity of a local right inverse of a strictly monotone function.**

If `g` is strictly monotone (in either sense) on the open interval `(a,b)` and `ψ` is, near
`t₀`, a right inverse of `g` up to the affine reparametrisation `u ↦ A + (B - A) * u` taking
values in `(a,b)`, then `ψ` is continuous at `t₀`.

Only the order structure is used: no continuity of `g` and no non-degeneracy of the
reparametrisation (`B ≠ A`) is required. -/
theorem continuousAt_of_affine_localInverse {g ψ : ℝ → ℝ} {a b A B t₀ : ℝ}
    (hmono : StrictMonoOn g (Set.Ioo a b) ∨ StrictAntiOn g (Set.Ioo a b))
    (hψ : ∀ᶠ u in nhds t₀, ψ u ∈ Set.Ioo a b ∧ g (ψ u) = A + (B - A) * u) :
    ContinuousAt ψ t₀ := by
  set y₀ : ℝ := ψ t₀ with hy₀def
  have hy₀mem : y₀ ∈ Set.Ioo a b := by rw [hy₀def]; exact hψ.self_of_nhds.1
  have hy₀eq : g y₀ = A + (B - A) * t₀ := by rw [hy₀def]; exact hψ.self_of_nhds.2
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- Two points of `(a,b)` squeezing `y₀` inside the ball of radius `ε`.
  set y₁ : ℝ := max ((a + y₀) / 2) (y₀ - ε) with hy₁def
  set y₂ : ℝ := min ((y₀ + b) / 2) (y₀ + ε) with hy₂def
  have hy₁lt : y₁ < y₀ := by
    rw [hy₁def, max_lt_iff]
    exact ⟨by linarith [hy₀mem.1], by linarith⟩
  have hy₁gt : a < y₁ := by
    rw [hy₁def]
    exact lt_of_lt_of_le (by linarith [hy₀mem.1]) (le_max_left _ _)
  have hy₂gt : y₀ < y₂ := by
    rw [hy₂def]
    exact lt_min (by linarith [hy₀mem.2]) (by linarith)
  have hy₂lt : y₂ < b := by
    rw [hy₂def]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith [hy₀mem.2])
  have hy₁mem : y₁ ∈ Set.Ioo a b := ⟨hy₁gt, lt_trans hy₁lt hy₀mem.2⟩
  have hy₂mem : y₂ ∈ Set.Ioo a b := ⟨lt_trans hy₀mem.1 hy₂gt, hy₂lt⟩
  -- Monotonicity localises: `g y` close to `g y₀` forces `y ∈ (y₁,y₂)`.
  have hstep : ∃ δ > 0, ∀ y ∈ Set.Ioo a b, |g y - g y₀| < δ → y ∈ Set.Ioo y₁ y₂ := by
    rcases hmono with hm | ha
    · have hlt₁ : g y₁ < g y₀ := (hm.lt_iff_lt hy₁mem hy₀mem).mpr hy₁lt
      have hlt₂ : g y₀ < g y₂ := (hm.lt_iff_lt hy₀mem hy₂mem).mpr hy₂gt
      refine ⟨min (g y₀ - g y₁) (g y₂ - g y₀),
        lt_min (sub_pos.mpr hlt₁) (sub_pos.mpr hlt₂), ?_⟩
      intro y hy hδ
      refine ⟨?_, ?_⟩
      · by_contra hcon
        simp only [not_lt] at hcon
        have h1 : g y ≤ g y₁ := hm.monotoneOn hy hy₁mem hcon
        have h1' : g y ≤ g y₀ := le_trans h1 (le_of_lt hlt₁)
        have h2 : |g y - g y₀| = g y₀ - g y := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1')]
        have h3 : min (g y₀ - g y₁) (g y₂ - g y₀) ≤ g y₀ - g y :=
          le_trans (min_le_left _ _) (sub_le_sub_left h1 (g y₀))
        rw [h2] at hδ
        exact absurd h3 (not_le.mpr hδ)
      · by_contra hcon
        simp only [not_lt] at hcon
        have h1 : g y₂ ≤ g y := hm.monotoneOn hy₂mem hy hcon
        have h1' : g y₀ ≤ g y := le_trans (le_of_lt hlt₂) h1
        have h2 : |g y - g y₀| = g y - g y₀ := abs_of_nonneg (sub_nonneg.mpr h1')
        have h3 : min (g y₀ - g y₁) (g y₂ - g y₀) ≤ g y - g y₀ :=
          le_trans (min_le_right _ _) (sub_le_sub_right h1 (g y₀))
        rw [h2] at hδ
        exact absurd h3 (not_le.mpr hδ)
    · have hlt₁ : g y₀ < g y₁ := by
        have h := (ha.neg).lt_iff_lt hy₁mem hy₀mem |>.mpr hy₁lt
        exact neg_lt_neg_iff.mp h
      have hlt₂ : g y₂ < g y₀ := by
        have h := (ha.neg).lt_iff_lt hy₀mem hy₂mem |>.mpr hy₂gt
        exact neg_lt_neg_iff.mp h
      refine ⟨min (g y₁ - g y₀) (g y₀ - g y₂),
        lt_min (sub_pos.mpr hlt₁) (sub_pos.mpr hlt₂), ?_⟩
      intro y hy hδ
      refine ⟨?_, ?_⟩
      · by_contra hcon
        simp only [not_lt] at hcon
        have h1 : g y₁ ≤ g y := by
          have h := (ha.neg).monotoneOn hy hy₁mem hcon
          exact neg_le_neg_iff.mp h
        have h1' : g y₀ ≤ g y := le_trans (le_of_lt hlt₁) h1
        have h2 : |g y - g y₀| = g y - g y₀ := abs_of_nonneg (sub_nonneg.mpr h1')
        have h3 : min (g y₁ - g y₀) (g y₀ - g y₂) ≤ g y - g y₀ :=
          le_trans (min_le_left _ _) (sub_le_sub_right h1 (g y₀))
        rw [h2] at hδ
        exact absurd h3 (not_le.mpr hδ)
      · by_contra hcon
        simp only [not_lt] at hcon
        have h1 : g y ≤ g y₂ := by
          have h := (ha.neg).monotoneOn hy₂mem hy hcon
          exact neg_le_neg_iff.mp h
        have h1' : g y ≤ g y₀ := le_trans h1 (le_of_lt hlt₂)
        have h2 : |g y - g y₀| = g y₀ - g y := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1')]
        have h3 : min (g y₁ - g y₀) (g y₀ - g y₂) ≤ g y₀ - g y :=
          le_trans (min_le_right _ _) (sub_le_sub_left h1 (g y₀))
        rw [h2] at hδ
        exact absurd h3 (not_le.mpr hδ)
  obtain ⟨δ, hδpos, hδ⟩ := hstep
  -- The affine reparametrisation is continuous, so `g (ψ u) → g y₀` as `u → t₀`.
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.mem_nhds_iff.mp hψ
  have hcontv : ContinuousAt (fun u : ℝ => A + (B - A) * u) t₀ := by fun_prop
  obtain ⟨δv, hδvpos, hδvsub⟩ := (Metric.continuousAt_iff.mp hcontv) δ hδpos
  refine ⟨min δ₀ δv, lt_min hδ₀pos hδvpos, ?_⟩
  intro u hu
  have hu₀ : ψ u ∈ Set.Ioo a b ∧ g (ψ u) = A + (B - A) * u :=
    hδ₀sub (by rw [Metric.mem_ball]; exact lt_of_lt_of_le hu (min_le_left _ _))
  have hv : dist (A + (B - A) * u) (A + (B - A) * t₀) < δ :=
    hδvsub (lt_of_lt_of_le hu (min_le_right _ _))
  have hgy : |g (ψ u) - g y₀| < δ := by
    rw [← hu₀.2, ← hy₀eq, Real.dist_eq] at hv
    exact hv
  have hmem := hδ (ψ u) hu₀.1 hgy
  rw [Real.dist_eq, show ψ t₀ = y₀ from hy₀def.symm, abs_lt]
  exact ⟨by have h := le_max_right ((a + y₀) / 2) (y₀ - ε); linarith [hmem.1],
    by have h := min_le_right ((y₀ + b) / 2) (y₀ + ε); linarith [hmem.2]⟩

/-- **The chart `chart1 f κ l` is `C¹` on `I`.**

If the fibre of `κ` over `l` is the open interval `(a,b)`, `f l` is strictly monotone on it,
the chart is the corresponding branch of the inverse of `f l` linearly reparametrised by `t`
(`hchar`), `f l` is differentiable on the fibre with non-vanishing derivative there, then
`chart1 f κ l` is continuous on `I` and has derivative
`(Bend κ f l - Aend κ f l) / deriv (f l) (chart1 f κ l t)` at every `t ∈ I`. -/
theorem cgo_chart1_contDiffOn {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p+1) → ℝ)) (l : Fin p → ℝ) {a b : ℝ}
    (hfib : Work.WilG4a.fibre κ l = Set.Ioo a b) (hne : (Work.WilG4a.fibre κ l).Nonempty)
    (hmono : StrictMonoOn (f l) (Work.WilG4a.fibre κ l) ∨
      StrictAntiOn (f l) (Work.WilG4a.fibre κ l))
    (hchar : ∀ t ∈ Work.WilG4a.I, Work.WilG4a.chart1 f κ l t ∈ Work.WilG4a.fibre κ l ∧
      f l (Work.WilG4a.chart1 f κ l t) =
        Work.WilG4a.Aend κ f l + (Work.WilG4a.Bend κ f l - Work.WilG4a.Aend κ f l) * t)
    (hdiff : ∀ y ∈ Work.WilG4a.fibre κ l, HasDerivAt (f l) (deriv (f l) y) y)
    (hne' : ∀ y ∈ Work.WilG4a.fibre κ l, deriv (f l) y ≠ 0) :
    ContinuousOn (Work.WilG4a.chart1 f κ l) Work.WilG4a.I ∧
    ∀ t ∈ Work.WilG4a.I, HasDerivAt (Work.WilG4a.chart1 f κ l)
      ((Work.WilG4a.Bend κ f l - Work.WilG4a.Aend κ f l) /
        deriv (f l) (Work.WilG4a.chart1 f κ l t)) t := by
  have hmono' : StrictMonoOn (f l) (Set.Ioo a b) ∨ StrictAntiOn (f l) (Set.Ioo a b) := by
    rwa [hfib] at hmono
  have hchar' : ∀ t ∈ I, chart1 f κ l t ∈ Set.Ioo a b ∧
      f l (chart1 f κ l t) = Aend κ f l + (Bend κ f l - Aend κ f l) * t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hchar t ht
    exact ⟨by rw [← hfib]; exact h1, h2⟩
  -- The chart is a right inverse of `f l`, up to the affine reparametrisation, on `I`.
  have hev : ∀ t₀ ∈ I, ∀ᶠ u in nhds t₀,
      chart1 f κ l u ∈ Set.Ioo a b ∧
        f l (chart1 f κ l u) = Aend κ f l + (Bend κ f l - Aend κ f l) * u :=
    fun t₀ ht₀ => Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht₀) (fun u hu => hchar' u hu)
  have hcont : ∀ t₀ ∈ I, ContinuousAt (chart1 f κ l) t₀ :=
    fun t₀ ht₀ => continuousAt_of_affine_localInverse hmono' (hev t₀ ht₀)
  refine ⟨?_, ?_⟩
  · exact (isOpen_Ioo.continuousOn_iff (f := chart1 f κ l)).mpr (fun t ht => hcont t ht)
  · intro t₀ ht₀
    have hst : ContinuousAt (chart1 f κ l) t₀ := hcont t₀ ht₀
    have hmem : chart1 f κ l t₀ ∈ fibre κ l := (hchar t₀ ht₀).1
    have hf : HasDerivAt (f l) (deriv (f l) (chart1 f κ l t₀)) (chart1 f κ l t₀) := hdiff _ hmem
    have hf' : deriv (f l) (chart1 f κ l t₀) ≠ 0 := hne' _ hmem
    have hh : HasDerivAt (fun t : ℝ => Aend κ f l + (Bend κ f l - Aend κ f l) * t)
        (Bend κ f l - Aend κ f l) t₀ := by
      have h1 : HasDerivAt (fun t : ℝ => (Bend κ f l - Aend κ f l) * t)
          ((Bend κ f l - Aend κ f l) * 1) t₀ := (hasDerivAt_id t₀).const_mul _
      simpa using h1.add_const (Aend κ f l)
    have hcomp : (f l) ∘ (chart1 f κ l) =ᶠ[nhds t₀]
        (fun t : ℝ => Aend κ f l + (Bend κ f l - Aend κ f l) * t) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht₀] with u hu
      exact (hchar u hu).2
    exact HasDerivAt.of_comp_left hst hf hh hf' hcomp

end Work.WilG4a
