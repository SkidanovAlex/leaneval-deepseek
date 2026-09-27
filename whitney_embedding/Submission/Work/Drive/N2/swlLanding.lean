import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.levelBoundsOfJourney
import Submission.Work.Drive.N2.levelRateOnChart
import Submission.Work.Drive.N2.sepClosedModelBall
import Submission.Work.Drive.N2.norm_le_of_mem_closure_modelBall
import Submission.Work.Drive.N2.hmono_of_chartODE

/-!
# The landing of the box condition (independent proof)

`Work.Drive.N2.swlLandingOfBox`: a point `x` of the value window
`(f p - lam0 ^ 2 * eta, f p + lam0 ^ 2 * eta)` whose invariant `|Im ((Zs x) ^ 2)|` is bounded below
by the entry bound (`x` off the ball of radius `rho j`, or `|Im| >= c₀ lam0 ^ 2`) reaches the anchor
level `f p - lam0 ^ 2 * eta` under the flow.

This is a self-contained proof of the landing row of `Work.Drive.N2.saddleWindow_legality`, obtained
by the standard legality argument for the model-adapted flow:

* the trace of `x` never enters the model ball of another chart: the value separation `2 eta d` holds
  on the *closures* of those balls (`Work.Drive.N2.sepClosedModelBall`), while the level of the
  journey stays in the window (`Work.Drive.N2.levelBoundsOfJourney`);
* the trace never enters the marked ball.  Let `t₀` be the infimum of the times from which the trace
  is clean up to `0`.  The infimum is itself clean; if it were larger than the initial time, the trace
  at `t₀` would be a limit of bad points, the level law on `[t₀, 0]` would pin `f` there and the marked
  chart would put the trace on the *sphere* of its ball (norm exactly `lam0`).  Then the invariant
  `Im ((Zs ·) ^ 2)` (constant on the chart-confined part of the trace) and the identity
  `||phi' y|| ^ 4 = Re ((Zs y) ^ 2) ^ 2 + Im ((Zs y) ^ 2) ^ 2` contradict the box condition: either the
  trace cannot leave the chart region at all (then `Im` is transported from `x`), or it leaves it at a
  point of the boundary of the chart region, where the chart norm is at least `rho j = 8 lam0`, forcing
  `|Re| >= 63 lam0 ^ 2` against the window bound `|Re| < lam0 ^ 2 eta`.
* Hence the trace avoids every model ball on `[f p - lam0 ^ 2 * eta - f x, 0]` and the level law
  `WindowDatum.hlevel` gives the landing.

The one point where the endpoint of the window matters: `|f (Phi (u, x)) - f p| <= lam0 ^ 2 * eta`
(not `<`) is what `levelBoundsOfJourney` gives, and it is all that is needed; strictness at the times
strictly inside the window is recorded separately (`swlLanding_band_lt`).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

set_option maxHeartbeats 1000000

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The square of the norm of the complex chart coordinate is the sum of the squares of the two real
chart coordinates. -/
theorem swlL_Zs_sq (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I) (y : M) :
    ‖Zs y‖ ^ 2 = (φ' y 0) ^ 2 + (φ' y 1) ^ 2 := by
  rw [hZs y, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

/-- The norm of the complex chart coordinate is the chart norm. -/
theorem swlL_Zs_norm (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I) (y : M) :
    ‖Zs y‖ = ‖φ' y‖ := by
  have h2 : ‖Zs y‖ ^ 2 = ‖φ' y‖ ^ 2 := by
    rw [swlL_Zs_sq φ' Zs hZs y, norm_uVec]
  rw [← Real.sqrt_sq (norm_nonneg (Zs y)), ← Real.sqrt_sq (norm_nonneg (φ' y)), h2]

/-- **The fourth power identity**: `||phi' y|| ^ 4 = Re ((Zs y) ^ 2) ^ 2 + Im ((Zs y) ^ 2) ^ 2`. -/
theorem swlL_Zs_fourth (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I) (y : M) :
    ‖φ' y‖ ^ 4 = ((Zs y) ^ 2).re ^ 2 + ((Zs y) ^ 2).im ^ 2 := by
  have hsq : ‖Zs y‖ ^ 2 = ‖φ' y‖ ^ 2 := by
    rw [swlL_Zs_sq φ' Zs hZs y, norm_uVec]
  have hc : ((Zs y) ^ 2).re ^ 2 + ((Zs y) ^ 2).im ^ 2 = ‖(Zs y) ^ 2‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hc, norm_pow, hsq]
  ring

/-- **The invariance of `Im ((Zs ·) ^ 2)` on an arbitrary chart-confined segment**, obtained from
the `[min 0 t, max 0 t]` form `him` by restarting the flow (`WindowDatum.hΦcomp`). -/
theorem swlL_im_eq {f : M → ℝ} {p : M} (D : WindowDatum f p) (Zs : M → ℂ)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    {y : M} {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hconf : ∀ u ∈ Set.Icc t₁ t₂, D.Φ (u, y) ∈ D.C D.j) :
    ((Zs (D.Φ (t₂, y))) ^ 2).im = ((Zs (D.Φ (t₁, y))) ^ 2).im := by
  have hmin : min 0 (t₂ - t₁) = 0 := min_eq_left (by linarith)
  have hmax : max 0 (t₂ - t₁) = t₂ - t₁ := max_eq_right (by linarith)
  have h := him (D.Φ (t₁, y)) (t₂ - t₁) (by
    intro u hu
    rw [hmin, hmax] at hu
    rw [D.hΦcomp u t₁ y]
    exact hconf (u + t₁) ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  rw [D.hΦcomp (t₂ - t₁) t₁ y, show t₂ - t₁ + t₁ = t₂ by ring] at h
  exact h

/-- Two charts with the same source and the same model balls have the same chart norm on the
source. -/
theorem swlL_norm_eq_of_modelBall_eq
    (φ φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hsrc : φ'.source = φ.source) (hball : ∀ r : ℝ, modelBall φ' r = modelBall φ r)
    {z : M} (hz : z ∈ φ.source) : ‖φ z‖ = ‖φ' z‖ := by
  have hz' : z ∈ φ'.source := by rw [hsrc]; exact hz
  have key : ∀ r : ℝ, (‖φ z‖ < r ↔ ‖φ' z‖ < r) := by
    intro r
    have h1 : z ∈ modelBall φ r ↔ z ∈ modelBall φ' r := by rw [← hball r]
    constructor
    · intro h; exact (h1.mp ⟨hz, h⟩).2
    · intro h; exact (h1.mpr ⟨hz', h⟩).2
  have hIoi : Set.Ioi (‖φ z‖) = Set.Ioi (‖φ' z‖) := by
    ext r
    simp only [Set.mem_Ioi]
    exact key r
  exact Set.Ioi_inj.mp hIoi

/-- **The chart ball of radius `ρ j` is inside the interior of `C j`**: it is open
(`Work.Drive.N2.isOpen_modelBall`) and contained in `C j` (`WindowDatum.hCop`). -/
theorem swlL_mem_interior_C {f : M → ℝ} {p : M} (D : WindowDatum f p)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hball : ∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r)
    {z : M} (hz : z ∈ φ'.source) (hzn : ‖φ' z‖ < D.ρ D.j) : z ∈ interior (D.C D.j) := by
  have hsub : modelBall φ' (D.ρ D.j) ⊆ D.C D.j := by
    rw [hball (D.ρ D.j)]
    exact D.hCop D.j
  exact interior_maximal hsub (isOpen_modelBall φ' (D.ρ D.j)) ⟨hz, hzn⟩

/-- **A point of `C j` which is a limit of points outside `C j` has chart norm at least `ρ j`.** -/
theorem swlL_norm_ge_rho_of_closure_compl {f : M → ℝ} {p : M} (D : WindowDatum f p)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r)
    {z : M} (hzC : z ∈ D.C D.j) (hzcl : z ∈ closure ((D.C D.j)ᶜ)) :
    D.ρ D.j ≤ ‖φ' z‖ := by
  by_contra hc
  push_neg at hc
  have hzsrc : z ∈ φ'.source := by rw [hsrc]; exact D.hCsub D.j hzC
  have hint : z ∈ interior (D.C D.j) := swlL_mem_interior_C D φ' hball hzsrc hc
  obtain ⟨y, hyint, hycomp⟩ := (mem_closure_iff_nhds.mp hzcl) (interior (D.C D.j))
    (isOpen_interior.mem_nhds hint)
  exact hycomp (interior_subset hyint)

/-- **The window bound on the trace of `x`, in the non-strict form** (the strict form fails at the
initial time, where the level is exactly the lower end of the window). -/
theorem swlLanding_band_le {f : M → ℝ} {p : M} (D : WindowDatum f p) {x : M} {lam0 η : ℝ}
    (hband_hi : f x < f p + lam0 ^ 2 * η) :
    ∀ u ∈ Set.Icc (f p - lam0 ^ 2 * η - f x) 0,
      |f (D.Φ (u, x)) - f p| ≤ lam0 ^ 2 * η := by
  intro u hu
  obtain ⟨hu1, hu2⟩ := hu
  have hb := levelBoundsOfJourney D (x := x) (τ := u) hu2
  have ha : f (D.Φ (u, x)) - f p ≤ lam0 ^ 2 * η := by linarith [hb.2, hband_hi]
  have hb' : -(lam0 ^ 2 * η) ≤ f (D.Φ (u, x)) - f p := by linarith [hb.1, hu1]
  exact abs_le.mpr ⟨hb', ha⟩

/-- **The window bound, strict at the times strictly inside the window.** -/
theorem swlLanding_band_lt {f : M → ℝ} {p : M} (D : WindowDatum f p) {x : M} {lam0 η : ℝ}
    (hband_hi : f x < f p + lam0 ^ 2 * η) :
    ∀ u ∈ Set.Icc (f p - lam0 ^ 2 * η - f x) 0, f p - lam0 ^ 2 * η - f x < u →
      |f (D.Φ (u, x)) - f p| < lam0 ^ 2 * η := by
  intro u hu hlt
  obtain ⟨-, hu2⟩ := hu
  have hb := levelBoundsOfJourney D (x := x) (τ := u) hu2
  have ha : f (D.Φ (u, x)) - f p < lam0 ^ 2 * η := by linarith [hb.2, hband_hi]
  have hb' : -(lam0 ^ 2 * η) < f (D.Φ (u, x)) - f p := by linarith [hb.1, hlt]
  exact abs_lt.mpr ⟨hb', ha⟩

/-- **The landing of the box condition.** -/
theorem swlLandingOfBox {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ) (lam0 : ℝ)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    (_hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ' (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ' (D.Φ (t, y)) 1)) t)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    {η c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hc₀ : 1 < c₀)
    (hsep : (D.ρ D.j / 8) ^ 2 * η < 2 * D.ηd)
    {x : M}
    (hbox : x ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
      c₀ * lam0 ^ 2 ≤ |((Zs x) ^ 2).im|)
    (hband : f x ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η)) :
    f (D.Φ (f p - lam0 ^ 2 * η - f x, x)) = f p - lam0 ^ 2 * η := by
  classical
  -- ## 0. notation and numerical facts
  set τ : ℝ := f p - lam0 ^ 2 * η - f x with hτdef
  set B8 : Set M := modelBall (D.φ D.j) (D.ρ D.j / 8) with hB8def
  have hρpos : 0 < D.ρ D.j := D.hρ D.j
  have hlam0pos : 0 < lam0 := by rw [hlam0]; positivity
  have hlam0sqpos : 0 < lam0 ^ 2 := pow_pos hlam0pos 2
  have hsepη : lam0 ^ 2 * η < 2 * D.ηd := by rw [hlam0]; exact hsep
  have hband_lo : f p - lam0 ^ 2 * η < f x := hband.1
  have hband_hi : f x < f p + lam0 ^ 2 * η := hband.2
  have hτneg : τ < 0 := by rw [hτdef]; linarith
  have hρ8 : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
  have hballJ : modelBall φ' lam0 = B8 := by
    rw [hB8def, hlam0]; exact hball (D.ρ D.j / 8)
  have hsubBalls : B8 ⊆ modelBall (D.φ D.j) (D.ρ D.j) :=
    fun y hy => ⟨hy.1, by linarith [hy.2, hρpos]⟩
  have hγ : Continuous fun s : ℝ => D.Φ (s, x) :=
    D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
  -- ## 1. `x` is outside the marked ball
  have hx_not_B8 : x ∉ B8 := by
    intro hxB
    rcases hbox with hA | hB
    · exact hA (hsubBalls hxB)
    · have hlt : ‖φ' x‖ < lam0 := by
        rw [← hballJ] at hxB
        exact hxB.2
      have hnorm : ‖(Zs x) ^ 2‖ = ‖φ' x‖ ^ 2 := by
        rw [norm_pow, swlL_Zs_norm φ' Zs hZs x]
      have him_le : |((Zs x) ^ 2).im| ≤ ‖(Zs x) ^ 2‖ := Complex.abs_im_le_norm _
      have hlt2 : |((Zs x) ^ 2).im| < lam0 ^ 2 := by
        have h1 : ‖φ' x‖ ^ 2 < lam0 ^ 2 :=
          pow_lt_pow_left₀ hlt (norm_nonneg (φ' x)) (by norm_num : (2 : ℕ) ≠ 0)
        rw [hnorm] at him_le
        linarith
      have h2 : lam0 ^ 2 < c₀ * lam0 ^ 2 := by nlinarith [hc₀, hlam0sqpos]
      linarith
  -- ## 2. the level of the whole journey stays in the window
  have hband_le : ∀ u ∈ Set.Icc τ 0, |f (D.Φ (u, x)) - f p| ≤ lam0 ^ 2 * η := by
    intro u hu
    rw [hτdef] at hu
    exact swlLanding_band_le D hband_hi u hu
  have hband_lt : ∀ u ∈ Set.Icc τ 0, τ < u → |f (D.Φ (u, x)) - f p| < lam0 ^ 2 * η := by
    intro u hu hlt
    rw [hτdef] at hu hlt
    exact swlLanding_band_lt D hband_hi u hu hlt
  -- ## 3. the balls of the other charts are avoided
  have hnot_other : ∀ u ∈ Set.Icc τ 0, ∀ i : Fin D.N, i ≠ D.j →
      D.Φ (u, x) ∉ modelBall (D.φ i) (D.ρ i / 8) := by
    intro u hu i hi hmem
    have h1 := sepClosedModelBall D hi (D.Φ (u, x)) (subset_closure hmem)
    have h2 := hband_le u hu
    linarith [h1, h2, hsepη]
  -- ## 4. the marked ball is avoided
  have hav_j : ∀ u ∈ Set.Icc τ 0, D.Φ (u, x) ∉ B8 := by
    set G : Set ℝ := {t : ℝ | t ∈ Set.Icc τ 0 ∧
      ∀ v ∈ Set.Icc t 0, D.Φ (v, x) ∉ B8} with hGdef
    have hG0 : (0 : ℝ) ∈ G := by
      refine ⟨⟨le_of_lt hτneg, le_rfl⟩, ?_⟩
      intro v hv
      rw [Set.mem_Icc] at hv
      have hv0 : v = 0 := le_antisymm hv.2 hv.1
      rw [hv0, D.hΦ0 x]
      exact hx_not_B8
    have hGne : G.Nonempty := ⟨0, hG0⟩
    have hGbdd : BddBelow G := ⟨τ, fun t ht => ht.1.1⟩
    set t₀ : ℝ := sInf G with ht₀def
    have ht₀_le : t₀ ≤ 0 := csInf_le hGbdd hG0
    have ht₀_ge : τ ≤ t₀ := le_csInf hGne (fun t ht => ht.1.1)
    -- the times strictly above the infimum are clean
    have hclean_gt : ∀ u ∈ Set.Icc t₀ 0, t₀ < u → D.Φ (u, x) ∉ B8 := by
      intro u hu hlt
      have hex : ∃ t ∈ G, t < u := by
        by_contra hcon
        simp only [not_exists, not_and] at hcon
        exact absurd (le_csInf hGne (fun t ht => not_lt.mp (hcon t ht))) (not_le.mpr hlt)
      obtain ⟨t, htG, htu⟩ := hex
      exact htG.2 u ⟨le_of_lt htu, hu.2⟩
    -- the infimum itself is clean
    have ht₀_clean : ∀ u ∈ Set.Icc t₀ 0, D.Φ (u, x) ∉ B8 := by
      intro u hu
      by_cases hlt : t₀ < u
      · exact hclean_gt u hu hlt
      · have heq : u = t₀ := le_antisymm (not_lt.mp hlt) hu.1
        subst heq
        by_contra hbad
        have hopen : IsOpen B8 := isOpen_modelBall (D.φ D.j) _
        have hnhds : (fun s : ℝ => D.Φ (s, x)) ⁻¹' B8 ∈ 𝓝 t₀ :=
          hγ.continuousAt.preimage_mem_nhds (hopen.mem_nhds hbad)
        obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hnhds
        by_cases ht₀neg : t₀ < 0
        · set u' : ℝ := t₀ + min ε (-t₀) / 2 with hu'def
          have hminpos : 0 < min ε (-t₀) := lt_min hεpos (by linarith)
          have hu'_gt : t₀ < u' := by rw [hu'def]; linarith
          have hu'_le : u' ≤ 0 := by
            rw [hu'def]
            have h1 : min ε (-t₀) ≤ -t₀ := min_le_right _ _
            linarith
          have hu'ball : u' ∈ Metric.ball t₀ ε := by
            rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
            have h1 : min ε (-t₀) ≤ ε := min_le_left _ _
            rw [hu'def]; linarith
          exact absurd (hε hu'ball) (hclean_gt u' ⟨le_of_lt hu'_gt, hu'_le⟩ hu'_gt)
        · have h0 : t₀ = 0 := le_antisymm ht₀_le (not_lt.mp ht₀neg)
          rw [h0, D.hΦ0 x] at hbad
          exact hx_not_B8 hbad
    by_cases ht₀τ : t₀ = τ
    · intro u hu
      rw [← ht₀τ] at hu
      exact ht₀_clean u hu
    · exfalso
      have ht₀_gt : τ < t₀ := lt_of_le_of_ne ht₀_ge (Ne.symm ht₀τ)
      -- the level at `t₀`
      have hlev₀ : f (D.Φ (t₀, x)) = f x + t₀ := by
        refine D.hlevel x t₀ ?_
        intro u hu i
        have hu' : u ∈ Set.Icc t₀ 0 := by
          rw [Set.mem_Icc] at hu ⊢
          rwa [min_eq_right ht₀_le, max_eq_left ht₀_le] at hu
        by_cases hi : i = D.j
        · rw [hi]; exact ht₀_clean u hu'
        · exact hnot_other u ⟨le_trans (le_of_lt ht₀_gt) hu'.1, hu'.2⟩ i hi
      -- `Phi (t₀, x)` is a limit of bad points
      have hcl : D.Φ (t₀, x) ∈ closure B8 := by
        rw [mem_closure_iff_nhds]
        intro t ht
        have hpre : (fun s : ℝ => D.Φ (s, x)) ⁻¹' t ∈ 𝓝 t₀ :=
          hγ.continuousAt.preimage_mem_nhds ht
        obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hpre
        set u : ℝ := t₀ - min δ (t₀ - τ) / 2 with hudef
        have hminpos : 0 < min δ (t₀ - τ) := lt_min hδpos (by linarith)
        have hu_lt : u < t₀ := by rw [hudef]; linarith
        have hu_ge : τ ≤ u := by
          rw [hudef]
          have h1 : min δ (t₀ - τ) ≤ t₀ - τ := min_le_right _ _
          linarith
        have huG : u ∉ G := fun hmem => absurd (csInf_le hGbdd hmem) (not_le.mpr hu_lt)
        have hbadv : ∃ v ∈ Set.Icc u 0, D.Φ (v, x) ∈ B8 := by
          by_contra hcon
          simp only [not_exists, not_and] at hcon
          exact huG ⟨⟨hu_ge, by linarith⟩, hcon⟩
        obtain ⟨v, hv, hvm⟩ := hbadv
        have hv_lt : v < t₀ := by
          by_contra hvc
          rw [not_lt] at hvc
          exact ht₀_clean v ⟨hvc, hv.2⟩ hvm
        have hvball : v ∈ Metric.ball t₀ δ := by
          rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
          have h1 : min δ (t₀ - τ) ≤ δ := min_le_left _ _
          rw [hudef] at hv
          linarith [hv.1]
        exact ⟨D.Φ (v, x), ⟨hδ hvball, hvm⟩⟩
      have hnotmem₀ : D.Φ (t₀, x) ∉ B8 := ht₀_clean t₀ ⟨le_rfl, ht₀_le⟩
      have hsrc₀ : D.Φ (t₀, x) ∈ (D.φ D.j).source :=
        (D.hCcl D.j).2 (closure_mono (D.hCball D.j) hcl)
      have hsub : closure (modelBall φ' lam0) ⊆ φ'.source := by
        rw [hballJ, hsrc]
        exact (closure_mono (D.hCball D.j)).trans (D.hCcl D.j).2
      have hnorm₀ : ‖φ' (D.Φ (t₀, x))‖ = lam0 := by
        have hle := norm_le_of_mem_closure_modelBall φ' lam0 hsub (D.Φ (t₀, x))
          (by rw [hballJ]; exact hcl)
        have hge : lam0 ≤ ‖φ' (D.Φ (t₀, x))‖ := by
          by_contra hcon
          rw [not_le] at hcon
          exact hnotmem₀ (by rw [← hballJ]; exact ⟨by rw [hsrc]; exact hsrc₀, hcon⟩)
        exact le_antisymm hle hge
      -- a neighbourhood of `t₀` is confined to the chart region
      have hinner : ∃ ε > 0, ∀ s : ℝ, |s - t₀| < ε → D.Φ (s, x) ∈ D.C D.j := by
        have hopen : IsOpen (modelBall φ' (D.ρ D.j)) := isOpen_modelBall φ' _
        have hmem : D.Φ (t₀, x) ∈ modelBall φ' (D.ρ D.j) := by
          refine ⟨by rw [hsrc]; exact hsrc₀, ?_⟩
          rw [hρ8]; linarith
        have hsub' : modelBall φ' (D.ρ D.j) ⊆ D.C D.j := by
          rw [hball (D.ρ D.j)]
          exact D.hCop D.j
        obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp
          (hγ.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem))
        refine ⟨δ / 2, by linarith, fun s hs => hsub' (hδ ?_)⟩
        rw [Metric.mem_ball, Real.dist_eq]
        linarith
      -- the maximal prefix above `t₀` on which the trace is confined to the chart region
      set S : Set ℝ := {u : ℝ | u ∈ Set.Icc t₀ 0 ∧
        ∀ v ∈ Set.Icc t₀ u, D.Φ (v, x) ∈ D.C D.j} with hSdef
      have hconf₀ : D.Φ (t₀, x) ∈ D.C D.j := by
        obtain ⟨ε, hεpos, hεconf⟩ := hinner
        exact hεconf t₀ (by rw [sub_self, abs_zero]; linarith)
      have ht₀S : t₀ ∈ S := by
        refine ⟨⟨le_rfl, ht₀_le⟩, ?_⟩
        intro v hv
        rw [Set.mem_Icc] at hv
        have hv' : v = t₀ := le_antisymm hv.2 hv.1
        rw [hv']
        exact hconf₀
      have hSne : S.Nonempty := ⟨t₀, ht₀S⟩
      have hSbdd : BddAbove S := ⟨0, fun u hu => hu.1.2⟩
      set β : ℝ := sSup S with hβdef
      have hβ_ge : t₀ ≤ β := le_csSup hSbdd ht₀S
      have hβ_le : β ≤ 0 := csSup_le hSne (fun u hu => hu.1.2)
      have hβ_mem : β ∈ S := by
        refine ⟨⟨hβ_ge, hβ_le⟩, ?_⟩
        intro v hv
        by_cases hlt : v < β
        · obtain ⟨u, huS, hvu⟩ := exists_lt_of_lt_csSup hSne hlt
          exact huS.2 v ⟨hv.1, le_of_lt hvu⟩
        · have hvβ : v = β := le_antisymm hv.2 (not_lt.mp hlt)
          subst hvβ
          have hclC : D.Φ (β, x) ∈ closure (D.C D.j) := by
            rw [mem_closure_iff_nhds]
            intro t ht
            have hpre : (fun s : ℝ => D.Φ (s, x)) ⁻¹' t ∈ 𝓝 β :=
              hγ.continuousAt.preimage_mem_nhds ht
            obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hpre
            obtain ⟨u, huS, hu_gt⟩ := exists_lt_of_lt_csSup hSne
              (show β - min δ 1 / 2 < β by
                have h2 : 0 < min δ 1 / 2 := by positivity
                linarith)
            have hu_le : u ≤ β := le_csSup hSbdd huS
            have huball : u ∈ Metric.ball β δ := by
              rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
              have h1 : min δ 1 / 2 ≤ δ := by
                have h2 : min δ 1 ≤ δ := min_le_left _ _
                linarith
              linarith
            exact ⟨D.Φ (u, x), ⟨hδ huball, huS.2 u ⟨huS.1.1, le_refl u⟩⟩⟩
          rwa [(D.hCclosed D.j).closure_eq] at hclC
      -- the norm identity at `t₀`
      have hnorm4 : lam0 ^ 4 = ((Zs (D.Φ (t₀, x))) ^ 2).re ^ 2 +
          ((Zs (D.Φ (t₀, x))) ^ 2).im ^ 2 := by
        rw [← swlL_Zs_fourth φ' Zs hZs (D.Φ (t₀, x)), hnorm₀]
      by_cases hβ0 : β = 0
      · -- the trace is confined to the chart region on `[t₀, 0]`
        have hconf : ∀ v ∈ Set.Icc t₀ 0, D.Φ (v, x) ∈ D.C D.j := by
          intro v hv
          exact hβ_mem.2 v ⟨hv.1, by rw [hβ0]; exact hv.2⟩
        have him₀ : ((Zs (D.Φ (t₀, x))) ^ 2).im = ((Zs x) ^ 2).im := by
          refine him x t₀ ?_
          intro u hu
          have hu' : u ∈ Set.Icc t₀ 0 := by
            rw [Set.mem_Icc] at hu ⊢
            rwa [min_eq_right ht₀_le, max_eq_left ht₀_le] at hu
          exact hconf u hu'
        have himle : ((Zs x) ^ 2).im ^ 2 ≤ lam0 ^ 4 := by
          rw [← him₀]
          nlinarith [hnorm4, sq_nonneg (((Zs (D.Φ (t₀, x))) ^ 2).re)]
        rcases hbox with hA | hB
        · -- `x` is off the ball of radius `rho j`
          have hxsrcD : x ∈ (D.φ D.j).source := by
            have h0 := hconf 0 ⟨ht₀_le, le_rfl⟩
            rw [D.hΦ0 x] at h0
            exact D.hCsub D.j h0
          have hxsrc : x ∈ φ'.source := by rw [hsrc]; exact hxsrcD
          have hxnorm : ‖D.φ D.j x‖ = ‖φ' x‖ :=
            swlL_norm_eq_of_modelBall_eq (D.φ D.j) φ' hsrc hball hxsrcD
          have hbig : (8 : ℝ) * lam0 ≤ ‖φ' x‖ := by
            have h1 : D.ρ D.j ≤ ‖D.φ D.j x‖ := by
              by_contra hc
              rw [not_le] at hc
              exact hA ⟨hxsrcD, hc⟩
            rw [hρ8] at h1
            rwa [hxnorm] at h1
          have h8 : ((8 : ℝ) * lam0) ^ 4 ≤ ‖φ' x‖ ^ 4 :=
            pow_le_pow_left₀ (by positivity) hbig 4
          have hdecomp : ‖φ' x‖ ^ 4 = ((Zs x) ^ 2).re ^ 2 + ((Zs x) ^ 2).im ^ 2 :=
            swlL_Zs_fourth φ' Zs hZs x
          rw [hdecomp] at h8
          have h8v : ((8 : ℝ) * lam0) ^ 4 = 4096 * lam0 ^ 4 := by ring
          rw [h8v] at h8
          have hrex : ((Zs x) ^ 2).re = f x - f p := by
            have h0 := hlev x hxsrcD
            linarith
          rw [hrex] at h8
          have habs : |f x - f p| < lam0 ^ 2 * η :=
            abs_lt.mpr ⟨by linarith [hband_lo], by linarith [hband_hi]⟩
          have hsq : (f x - f p) ^ 2 < (lam0 ^ 2 * η) ^ 2 := by
            rw [sq_lt_sq, abs_of_pos (by positivity : (0 : ℝ) < lam0 ^ 2 * η)]
            exact habs
          have hη2 : η ^ 2 < 1 := by nlinarith [hη, hη']
          have hηstep : (lam0 ^ 2 * η) ^ 2 < lam0 ^ 4 := by
            have h1 : (lam0 ^ 2 * η) ^ 2 = lam0 ^ 4 * η ^ 2 := by ring
            have h2 : lam0 ^ 4 * η ^ 2 < lam0 ^ 4 * 1 :=
              mul_lt_mul_of_pos_left hη2 (by positivity : (0 : ℝ) < lam0 ^ 4)
            linarith
          have hlt : lam0 ^ 4 < ((Zs x) ^ 2).im ^ 2 :=
            by nlinarith [h8, hsq, hηstep, hlam0sqpos]
          exact absurd hlt (not_lt.mpr himle)
        · -- the invariant bound of the box condition
          have h2 : lam0 ^ 2 < |((Zs x) ^ 2).im| := by nlinarith [hB, hc₀, hlam0sqpos]
          have h3 : (lam0 ^ 2) ^ 2 < |((Zs x) ^ 2).im| ^ 2 :=
            pow_lt_pow_left₀ h2 (by positivity : (0 : ℝ) ≤ lam0 ^ 2) (by norm_num : (2 : ℕ) ≠ 0)
          have hlt : lam0 ^ 4 < ((Zs x) ^ 2).im ^ 2 := by
            rwa [sq_abs, show (lam0 ^ 2) ^ 2 = lam0 ^ 4 by ring] at h3
          exact absurd hlt (not_lt.mpr himle)
      · -- the trace leaves the chart region at `β`
        have hβ_lt : β < 0 := lt_of_le_of_ne hβ_le hβ0
        have hβC : D.Φ (β, x) ∈ D.C D.j := hβ_mem.2 β ⟨hβ_ge, le_refl β⟩
        have hβcl : D.Φ (β, x) ∈ closure ((D.C D.j)ᶜ) := by
          rw [mem_closure_iff_nhds]
          intro t ht
          have hpre : (fun s : ℝ => D.Φ (s, x)) ⁻¹' t ∈ 𝓝 β :=
            hγ.continuousAt.preimage_mem_nhds ht
          obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hpre
          set u : ℝ := β + min δ (-β) / 2 with hudef
          have hminpos : 0 < min δ (-β) := lt_min hδpos (by linarith)
          have hu_gt : β < u := by rw [hudef]; linarith
          have hu_le : u ≤ 0 := by
            rw [hudef]
            have h1 : min δ (-β) ≤ -β := min_le_right _ _
            linarith
          have huS : u ∉ S := fun hmem => absurd (le_csSup hSbdd hmem) (not_le.mpr hu_gt)
          have hbadv : ∃ v ∈ Set.Icc t₀ u, D.Φ (v, x) ∉ D.C D.j := by
            by_contra hcon
            simp only [not_exists, not_and, not_not] at hcon
            exact huS ⟨⟨le_trans hβ_ge (le_of_lt hu_gt), hu_le⟩, hcon⟩
          obtain ⟨v, hv, hvm⟩ := hbadv
          have hv_gt : β < v := by
            by_contra hvc
            rw [not_lt] at hvc
            exact hvm (hβ_mem.2 v ⟨hv.1, hvc⟩)
          have hvball : v ∈ Metric.ball β δ := by
            rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
            have h1 : min δ (-β) ≤ δ := min_le_left _ _
            rw [hudef] at hv
            linarith [hv.2]
          exact ⟨D.Φ (v, x), ⟨hδ hvball, hvm⟩⟩
        have hβnorm : (8 : ℝ) * lam0 ≤ ‖φ' (D.Φ (β, x))‖ := by
          have h := swlL_norm_ge_rho_of_closure_compl D φ' hsrc hball hβC hβcl
          rwa [hρ8] at h
        have himβ : ((Zs (D.Φ (β, x))) ^ 2).im = ((Zs (D.Φ (t₀, x))) ^ 2).im :=
          swlL_im_eq D Zs him hβ_ge hβ_mem.2
        have hbig : (4096 : ℝ) * lam0 ^ 4 ≤ ((Zs (D.Φ (β, x))) ^ 2).re ^ 2 +
            ((Zs (D.Φ (β, x))) ^ 2).im ^ 2 := by
          rw [← swlL_Zs_fourth φ' Zs hZs (D.Φ (β, x))]
          have h8 : ((8 : ℝ) * lam0) ^ 4 ≤ ‖φ' (D.Φ (β, x))‖ ^ 4 :=
            pow_le_pow_left₀ (by positivity) hβnorm 4
          have h8v : ((8 : ℝ) * lam0) ^ 4 = 4096 * lam0 ^ 4 := by ring
          linarith [h8, h8v]
        have hβband : |f (D.Φ (β, x)) - f p| ≤ lam0 ^ 2 * η :=
          hband_le β ⟨le_trans ht₀_ge hβ_ge, hβ_le⟩
        have hreβ : ((Zs (D.Φ (β, x))) ^ 2).re = f (D.Φ (β, x)) - f p := by
          have hs : D.Φ (β, x) ∈ (D.φ D.j).source := D.hCsub D.j hβC
          have h0 := hlev (D.Φ (β, x)) hs
          linarith
        have hsmall : ((Zs (D.Φ (β, x))) ^ 2).re ^ 2 ≤ lam0 ^ 4 := by
          rw [hreβ]
          have hsq : (f (D.Φ (β, x)) - f p) ^ 2 ≤ (lam0 ^ 2 * η) ^ 2 := by
            calc (f (D.Φ (β, x)) - f p) ^ 2 = |f (D.Φ (β, x)) - f p| ^ 2 := by rw [sq_abs]
              _ ≤ (lam0 ^ 2 * η) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hβband 2
          have hη2 : η ^ 2 < 1 := by nlinarith [hη, hη']
          have hηstep : (lam0 ^ 2 * η) ^ 2 < lam0 ^ 4 := by
            have h1 : (lam0 ^ 2 * η) ^ 2 = lam0 ^ 4 * η ^ 2 := by ring
            have h2 : lam0 ^ 4 * η ^ 2 < lam0 ^ 4 * 1 :=
              mul_lt_mul_of_pos_left hη2 (by positivity : (0 : ℝ) < lam0 ^ 4)
            linarith
          linarith
        have him2le : ((Zs (D.Φ (β, x))) ^ 2).im ^ 2 ≤ lam0 ^ 4 := by
          rw [himβ]
          nlinarith [hnorm4, sq_nonneg (((Zs (D.Φ (t₀, x))) ^ 2).re)]
        nlinarith [hbig, hsmall, him2le, hlam0sqpos]
  -- ## 5. the level law gives the landing
  have hclean : ∀ u ∈ Set.Icc τ 0, ∀ i : Fin D.N,
      D.Φ (u, x) ∉ modelBall (D.φ i) (D.ρ i / 8) := by
    intro u hu i
    by_cases hi : i = D.j
    · rw [hi]; exact hav_j u hu
    · exact hnot_other u hu i hi
  have hclean' : ∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), ∀ i : Fin D.N,
      D.Φ (u, x) ∉ modelBall (D.φ i) (D.ρ i / 8) := by
    intro u hu
    rw [min_eq_right (le_of_lt hτneg), max_eq_left (le_of_lt hτneg)] at hu
    exact hclean u hu
  have h := D.hlevel x τ hclean'
  rw [h, hτdef]
  ring

end Work.Drive.N2
