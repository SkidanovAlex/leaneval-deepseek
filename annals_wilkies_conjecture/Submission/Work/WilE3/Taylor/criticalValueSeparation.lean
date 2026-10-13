import Mathlib
import Submission.Work.WilE3.Taylor.HasLoj.Reductions
import Submission.Work.WilE3.Loj.curve_selection

set_option autoImplicit false

namespace Work.WilE3.Taylor

open scoped Topology

/-!
# Separation of the critical values of a nonnegative analytic germ from `0`

Let `Φ` be real analytic on all of `ℝ^k`, with `Φ y = 0` and `Φ ≥ 0` near `y`
(so `y` is a local minimum of `Φ`).  The theorem `criticalValueSeparation` below says that there is
a ball around `y` on which every critical point of `Φ` is a zero of `Φ`: the critical *values* of
`Φ` do not accumulate at `0`.

This is the `κ → 1` shadow of the Łojasiewicz gradient inequality
`c |Φ x|^κ ≤ ‖∇Φ x‖` (`κ < 1`, `c > 0`) near `y`, which is the standard input for such
statements.  The proof below avoids the gradient inequality altogether and uses only two
ingredients available in this workspace:

* **analytic curve selection** (`Work.WilE3.Loj.curveSel_full`, i.e.
  `WilkiesDesign.CG.C4a.CurveSel`): if `y` is a cluster point of a basic semianalytic set
  `{F = 0} ∩ {g > 0}` (with analytic data), an analytic arc through `y` runs inside the set;
* the **chain rule**, i.e. the one-variable fact that an analytic function whose derivative
  vanishes on an interval is constant there.

Suppose the conclusion failed.  Then there are critical points `zₙ → y` with `Φ zₙ ≠ 0`, i.e.
`y` is a cluster point of the semianalytic set `{∇Φ = 0} ∩ {Φ > 0}` (here `Φ ≥ 0` near `y`, so
`Φ ≠ 0` becomes `Φ > 0`).  Curve selection produces an analytic arc `γ` through `y` along which
`∇Φ (γ s) = 0` and `Φ (γ s) > 0` for all small `s > 0`.  But then the one-variable function
`s ↦ Φ (γ s)` is analytic at `0`, vanishes at `0`, and by the chain rule has derivative `0`
identically on `(0, ε)`, hence is constantly `0` there — contradicting `Φ (γ s) > 0`.

The critical set is encoded by the analytic function `critSqFun Φ = ∑ᵢ (∂ᵢΦ)²`, whose zero set
is exactly `{fderiv ℝ Φ = 0}`: each `(∂ᵢΦ)²` is nonnegative.
-/

/-- The sum of the squares of the coordinate partial derivatives of `Φ`.  It is analytic wherever
`Φ` is (`AnalyticAt.fderiv`), nonnegative, and its zero set is exactly the critical set of `Φ`. -/
noncomputable def critSqFun {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) : (Fin k → ℝ) → ℝ :=
  fun x => ∑ i : Fin k, (fderiv ℝ Φ x (Pi.single i 1)) ^ 2

/-- The coordinate partial derivative `x ↦ ∂ᵢΦ(x)` of an analytic function is analytic. -/
lemma analyticAt_fderiv_apply {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} (i : Fin k)
    (h : AnalyticAt ℝ Φ y) :
    AnalyticAt ℝ (fun x => fderiv ℝ Φ x (Pi.single i 1)) y := by
  have h1 : AnalyticAt ℝ (fderiv ℝ Φ) y := h.fderiv
  have h2 : AnalyticAt ℝ (fun L : (Fin k → ℝ) →L[ℝ] ℝ => L (Pi.single i 1))
      (fderiv ℝ Φ y) :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1:ℝ))).analyticAt (fderiv ℝ Φ y)
  exact h2.comp h1

/-- If `Φ` is analytic everywhere then so is `critSqFun Φ`. -/
lemma analyticAt_critSqFun {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} (hΦ : ∀ x, AnalyticAt ℝ Φ x)
    (y : Fin k → ℝ) : AnalyticAt ℝ (critSqFun Φ) y := by
  have h := Finset.analyticAt_sum (Finset.univ : Finset (Fin k))
    (fun i _ => (analyticAt_fderiv_apply i (hΦ y)).pow 2)
  have hfun : (∑ i : Fin k, (fun x => fderiv ℝ Φ x (Pi.single i 1)) ^ 2 :
        (Fin k → ℝ) → ℝ) = fun x => ∑ i : Fin k, (fderiv ℝ Φ x (Pi.single i 1)) ^ 2 := by
    funext x; simp [Finset.sum_apply, Pi.pow_apply]
  rw [hfun] at h
  exact h

/-- `critSqFun Φ` vanishes exactly at the critical points of `Φ`. -/
lemma critSqFun_eq_zero_iff {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {z : Fin k → ℝ} :
    critSqFun Φ z = 0 ↔ fderiv ℝ Φ z = 0 := by
  constructor
  · intro h
    -- all partial derivatives vanish, since they occur as nonnegative squares
    have hterm : ∀ i : Fin k, fderiv ℝ Φ z (Pi.single i 1) = 0 := by
      intro i
      have hsum : ∑ i : Fin k, (fderiv ℝ Φ z (Pi.single i 1)) ^ 2 = 0 := h
      have h' := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun i : Fin k => (fderiv ℝ Φ z (Pi.single i 1)) ^ 2)
        (fun i _ => sq_nonneg _)).mp hsum
      exact sq_eq_zero_iff.mp (h' i (Finset.mem_univ i))
    -- the standard basis vectors span, so the whole derivative vanishes
    have hdecomp : ∀ v : Fin k → ℝ, (∑ i : Fin k, v i • Pi.single i (1:ℝ)) = v := by
      intro v; funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Pi.single_eq_of_ne (Ne.symm hij), mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    ext v
    rw [← hdecomp v, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [map_smul, hterm i, smul_zero]
  · intro h
    simp [critSqFun, h]

/-- **Separation of the critical values of a nonnegative analytic germ from `0`.**

If `Φ` is analytic on `ℝ^k` with `Φ y = 0` and `Φ ≥ 0` near `y`, then near `y` every critical
point of `Φ` is a zero of `Φ`. -/
theorem criticalValueSeparation {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ}
    (hΦ : ∀ x, AnalyticAt ℝ Φ x) (hy : Φ y = 0)
    (hnn : Filter.Eventually (fun x => 0 ≤ Φ x) (nhds y)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Fin k → ℝ, dist z y < ρ → fderiv ℝ Φ z = 0 → Φ z = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- counterexample points: critical for `Φ`, with `Φ ≠ 0`, accumulating at `y`
  have hbad : ∀ n : ℕ, ∃ z : Fin k → ℝ,
      dist z y < 1 / (n + 1) ∧ fderiv ℝ Φ z = 0 ∧ Φ z ≠ 0 :=
    fun n => hcon (1 / (n + 1)) (by positivity)
  choose z hzd hzf hzΦ using hbad
  have hz_tendsto : Filter.Tendsto z Filter.atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hzd n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- `y` is a cluster point of the semianalytic set `{∇Φ = 0, Φ > 0}`
  have hycl : y ∈ closure (WilkiesDesign.CG.C4a.BasicSA (critSqFun Φ) (fun _ : Fin 1 => Φ)) := by
    refine mem_closure_of_tendsto hz_tendsto ?_
    filter_upwards [hz_tendsto.eventually hnn] with n hn
    exact ⟨critSqFun_eq_zero_iff.mpr (hzf n),
      fun _ => lt_of_le_of_ne hn (Ne.symm (hzΦ n))⟩
  -- analytic curve selection
  obtain ⟨γ, hγan, hγ0, ε, hεpos, hγε⟩ :=
    Work.WilE3.Loj.curveSel_full k 1 (critSqFun Φ) (fun _ : Fin 1 => Φ) y
      (analyticAt_critSqFun hΦ y) (fun _ => hΦ y) hycl
  have hcrit : ∀ s ∈ Set.Ioo (0:ℝ) ε, critSqFun Φ (γ s) = 0 := fun s hs => (hγε s hs).1
  have hpos : ∀ s ∈ Set.Ioo (0:ℝ) ε, 0 < Φ (γ s) := fun s hs => (hγε s hs).2 0
  -- `γ` is differentiable near `0`
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ → DifferentiableAt ℝ γ s := by
    have hev : ∀ᶠ s in 𝓝 (0:ℝ), DifferentiableAt ℝ γ s :=
      hγan.eventually_analyticAt.mono fun s hs => hs.differentiableAt
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
    exact ⟨δ, hδpos, fun s hs => hδ (by simpa [Real.dist_eq] using hs)⟩
  set s₁ : ℝ := min ε δ / 2 with hs₁def
  have hs₁pos : 0 < s₁ := by rw [hs₁def]; have := lt_min hεpos hδpos; linarith
  have hs₁ε : s₁ < ε := by rw [hs₁def]; linarith [min_le_left ε δ]
  have hs₁δ : s₁ < δ := by rw [hs₁def]; linarith [min_le_right ε δ]
  -- the one-variable function `s ↦ Φ (γ s)`
  set hh : ℝ → ℝ := fun s => Φ (γ s) with hhdef
  have hgan : AnalyticAt ℝ hh 0 := by
    have h1 : AnalyticAt ℝ Φ (γ 0) := by rw [hγ0]; exact hΦ y
    have h2 : AnalyticAt ℝ (Φ ∘ γ) 0 := h1.comp hγan
    rw [hhdef]
    exact h2
  have hdiffAt : ∀ c ∈ Set.Icc (0:ℝ) s₁, DifferentiableAt ℝ hh c := by
    intro c hc
    rcases eq_or_lt_of_le hc.1 with hc0 | hc0
    · rw [← hc0]; exact hgan.differentiableAt
    · have hcδ : |c| < δ := by
        rw [abs_of_pos hc0]; exact lt_of_le_of_lt hc.2 hs₁δ
      have hγc : DifferentiableAt ℝ γ c := hδ c hcδ
      have hΦc : DifferentiableAt ℝ Φ (γ c) := (hΦ (γ c)).differentiableAt
      have h3 : DifferentiableAt ℝ (Φ ∘ γ) c := hΦc.comp c hγc
      rw [hhdef]
      exact h3
  have hdiffOnIcc : DifferentiableOn ℝ hh (Set.Icc 0 s₁) := fun c hc =>
    (hdiffAt c hc).differentiableWithinAt
  have hcont : ContinuousOn hh (Set.Icc 0 s₁) := hdiffOnIcc.continuousOn
  have hdiffOn : DifferentiableOn ℝ hh (Set.Ioo (0:ℝ) s₁) := fun c hc =>
    (hdiffAt c ⟨hc.1.le, hc.2.le⟩).differentiableWithinAt
  -- the chain rule: `deriv hh` vanishes on `(0, s₁)`, because `γ` runs in the critical set
  have hderiv0 : ∀ c ∈ Set.Ioo (0:ℝ) s₁, deriv hh c = 0 := by
    intro c hc
    have hcε : c ∈ Set.Ioo (0:ℝ) ε := ⟨hc.1, lt_trans hc.2 hs₁ε⟩
    have hcδ : |c| < δ := by
      rw [abs_of_pos hc.1]; exact lt_of_lt_of_le hc.2 (le_of_lt hs₁δ)
    have hγc : DifferentiableAt ℝ γ c := hδ c hcδ
    have hΦc : DifferentiableAt ℝ Φ (γ c) := (hΦ (γ c)).differentiableAt
    have hfc : fderiv ℝ Φ (γ c) = 0 := critSqFun_eq_zero_iff.mp (hcrit c hcε)
    have h1 : HasFDerivAt Φ (fderiv ℝ Φ (γ c)) (γ c) := hΦc.hasFDerivAt
    have h2 : HasDerivAt γ (deriv γ c) c := hγc.hasDerivAt
    have h3 : HasDerivAt (Φ ∘ γ) ((fderiv ℝ Φ (γ c)) (deriv γ c)) c :=
      h1.comp_hasDerivAt c h2
    have h4 : HasDerivAt hh ((fderiv ℝ Φ (γ c)) (deriv γ c)) c := by
      rw [hhdef]; exact h3
    rw [hfc] at h4
    simpa using h4.deriv
  -- mean value theorem on `[0, s₁]`: `hh s₁ = hh 0`
  obtain ⟨c, hcmem, hceq⟩ := exists_deriv_eq_slope hh hs₁pos hcont hdiffOn
  have hzero : (hh s₁ - hh 0) / (s₁ - 0) = 0 := by rw [← hceq, hderiv0 c hcmem]
  have hval : hh s₁ = hh 0 := by
    rw [div_eq_zero_iff] at hzero
    rcases hzero with h | h
    · linarith
    · exact absurd h (by linarith)
  have hh0 : hh 0 = 0 := by simp [hhdef, hγ0, hy]
  have hpos₁ : 0 < hh s₁ := by
    have := hpos s₁ ⟨hs₁pos, hs₁ε⟩
    simpa [hhdef] using this
  -- contradiction: `hh s₁ = 0` but `hh s₁ > 0`
  rw [hval, hh0] at hpos₁
  exact lt_irrefl 0 hpos₁

end Work.WilE3.Taylor
