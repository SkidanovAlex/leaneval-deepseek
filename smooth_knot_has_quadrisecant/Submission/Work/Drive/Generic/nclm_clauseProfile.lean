import Mathlib
import Submission.Work.Drive.Generic.nclmPkg
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Generic.nclmDefs
import Submission.Work.Drive.Generic.nclmChart
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.H2.basePoint_v_coord
import Submission.Work.Drive.H2.baseHeight_lower
import Submission.Work.Drive.Nclm.base_close_arcMid_rate

/-!
# The profile package of the needle's chart data

This module proves `Work.Drive.Generic.nclmPkgProfile`: the five "profile" clauses of the chart of
the needle's retained arc, at a fixed box `(lam, δ₁, δ₂, ε)` and uniformly over the sweep window
`σ ∈ [ε - δ₂, ε + δ₂]`.

The chart (see `Submission/Work/Drive/AB/pinSetup.lean`) has origin `chartC`, abscissa the unit
chord direction `v` and ordinate `chartE` (the unit direction of `chartUp`, perpendicular to `v`).
The two coordinates of the point at fraction `ξ` of the raw retained arc are

* `nclmAX r D … σ v ξ = ⟪sweepArc' r D σ ξ - chartC, v⟫`,
* `nclmAH r D … σ v ξ = ⟪sweepArc' r D σ ξ - chartC, chartE⟫`.

The five clauses are:

1. the *tangent pairing* `cm/4 ≤ ⟪r'(x), v⟫` on every retained arc of the window
   (`Work.Drive.Generic.nclm_tang`, with `cm = ‖r'(taR D 0)‖`);
2. the strict monotonicity of the abscissa `X̃` on `[0,1]`;
3. the positivity of `X̃'` on `(0,1)`;
4. the *lower rate* `cm * sweepW' D σ / 8 ≤ X̃'` on `(lam, 1-lam)`;
5. the existence, on `(lam,1-lam)`, of the crossing point `ξ₀` (`X̃ ξ₀ = 0`) with a definite
   ordinate `ch * (sweepW' D ε)^2 ≤ H̃ ξ₀`.

Clauses 2–4 are immediate from clause 1 and the derivative formula
`Work.Drive.Generic.nclm_deriv_nclmAX` (`X̃' = sweepW' D σ * ⟪r'(x), v⟫`) together with the
window comparison `sweepW' D ε / 2 ≤ sweepW' D σ` of `Work.Drive.Generic.nclm_window_eps`.

Clause 5 is the geometric heart.  There are three inputs:

* `Work.Drive.Nclm.base_close_arcMid_rate` — the needle's base point `N 0` is within `cN * W²` of
  the *midpoint* `sweepArc' r D σ (1/2)` of the retained arc, `W = sweepW' D ε`;
* `Work.Drive.H2.baseHeight_lower` — the base point's offset `chartUp` from the chord's *line* is at
  least `c * W²`;
* the identity `⟪N 0 - chordEndA, chartE⟫ = ‖chartUp‖` (the normalisation of `chartUp`).

Since `chartC = chordEndA + (ncoord of N 0) • v + (‖chartUp‖/2) • chartE`, the abscissa at `ξ = 1/2`
is exactly `⟪sweepArc' σ (1/2) - N 0, v⟫`, so `|X̃ (1/2)| ≤ cN * W²`, while the ordinate is
`⟪sweepArc' σ (1/2) - N 0, chartE⟫ + ‖chartUp‖/2 ≥ ‖chartUp‖/2 - cN * W² ≥ (c/2 - cN) * W²`.
Choosing `cN` a tiny multiple of `c * cm / M` (`M` a global Lipschitz constant of `r`, so that
`cN ≤ c/1024` *and* the transfer error below is of order `c * W² / 32`), the zero `ξ₀` of `X̃` — which
by clause 4 lies within `ρ = 16 cN W / cm ≤ 1/8` of `1/2` — satisfies
`H̃ ξ₀ ≥ ‖chartUp‖/2 - cN W² - M * 2W * ρ ≥ c W² / 4`.  The `M * 2W * ρ` term is the Lipschitz
transfer of the ordinate between `ξ = 1/2` and `ξ = ξ₀`.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

variable {r : ℝ → Space} {d : BandArcData} {D : Work.Drive.SweepData d}

/-! ## Elementary facts about the retained arc -/

/-- The point at fraction `ξ ∈ [0,1]` of a non-degenerate retained arc lies on the arc. -/
lemma nclm_mem_arc {σ ξ : ℝ} (hw : 0 < Work.Drive.sweepW' D σ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ ∈
      Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ) := by
  have htb : Work.Drive.tbR D σ = Work.Drive.taR D σ + Work.Drive.sweepW' D σ := by
    rw [Work.Drive.sweepW']; ring
  constructor
  · nlinarith [hξ.1, hw.le]
  · rw [htb]; nlinarith [hξ.2, hw.le]

lemma nclm_continuous_sweepArc' (hr : IsSmoothKnot r) (σ : ℝ) :
    Continuous (Work.Drive.sweepArc' r D σ) := by
  rw [nclm_sweepArc'_eq r D σ]
  exact hr.smooth.continuous.comp (continuous_const.add (continuous_id.mul continuous_const))

lemma nclm_continuous_nclmAX (hr : IsSmoothKnot r) (lam δ₁ δ₂ ε σ : ℝ) (v : Space) :
    Continuous (nclmAX r D lam δ₁ δ₂ ε σ v) := by
  change Continuous (fun ξ : ℝ => inner ℝ (Work.Drive.sweepArc' r D σ ξ
    - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v)
  exact ((nclm_continuous_sweepArc' hr σ).sub continuous_const).inner continuous_const

lemma nclm_continuous_nclmAH (hr : IsSmoothKnot r) (lam δ₁ δ₂ ε σ : ℝ) (v : Space) :
    Continuous (nclmAH r D lam δ₁ δ₂ ε σ v) := by
  change Continuous (fun ξ : ℝ => inner ℝ (Work.Drive.sweepArc' r D σ ξ
    - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v))
  exact ((nclm_continuous_sweepArc' hr σ).sub continuous_const).inner continuous_const

lemma nclm_differentiable_nclmAX (hr : IsSmoothKnot r) (lam δ₁ δ₂ ε σ : ℝ) (v : Space) :
    Differentiable ℝ (nclmAX r D lam δ₁ δ₂ ε σ v) := by
  unfold nclmAX
  simp only [Work.Drive.sweepArc']
  refine Differentiable.inner ℝ ?_ (differentiable_const v)
  exact ((hr.smooth.differentiable (by simp)).comp
    ((differentiable_id.mul_const (Work.Drive.sweepW' D σ)).const_add
      (Work.Drive.taR D σ))).sub (differentiable_const _)

/-! ## The chart frame -/

lemma nclm_chartE_norm {lam δ₁ δ₂ ε : ℝ} {v : Space}
    (hpos : 0 < ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖) :
    ‖Work.Drive.chartE r D lam δ₁ δ₂ ε v‖ = 1 := by
  rw [Work.Drive.chartE, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
    inv_mul_cancel₀ (ne_of_gt hpos)]

lemma nclm_inner_v_chartE {lam δ₁ δ₂ ε : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ v (Work.Drive.chartE r D lam δ₁ δ₂ ε v) = 0 := by
  rw [Work.Drive.chartE, real_inner_smul_right, real_inner_comm,
    Work.Drive.inner_chartUp_v r D lam δ₁ δ₂ ε hv, mul_zero]

lemma nclm_inner_shiftedNeedle_chartE {lam δ₁ δ₂ ε : ℝ} {v : Space} (hv : ‖v‖ = 1)
    (hpos : 0 < ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖) :
    inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0 - Work.Drive.chordEndA r D δ₂ ε)
      (Work.Drive.chartE r D lam δ₁ δ₂ ε v) = ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
  rw [Work.Drive.chartE, real_inner_smul_right,
    Work.Drive.inner_shiftedNeedle_chartUp r D lam δ₁ δ₂ ε hv]
  field_simp

/-! ## The two chart coordinates at the middle of the arc -/

/-- The abscissa at `ξ = 1/2` is the chord coordinate of the *difference* between the arc's middle
and the needle's base point: the contributions of `chordEndA` and of the `chartE`-term of `chartC`
cancel. -/
lemma nclmAX_half {lam δ₁ δ₂ ε σ : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    nclmAX r D lam δ₁ δ₂ ε σ v (1/2)
      = inner ℝ (Work.Drive.sweepArc' r D σ (1/2) - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0)
          v := by
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hE : inner ℝ (Work.Drive.chartE r D lam δ₁ δ₂ ε v) v = 0 := by
    rw [Work.Drive.chartE, real_inner_smul_left,
      Work.Drive.inner_chartUp_v r D lam δ₁ δ₂ ε hv, mul_zero]
  have hC : inner ℝ (Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
      = inner ℝ (Work.Drive.chordEndA r D δ₂ ε) v
        + Work.Drive.nCoord r D lam δ₁ δ₂ ε v 0 := by
    rw [Work.Drive.chartC, inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, hvv, hE]
    ring
  have hL : nclmAX r D lam δ₁ δ₂ ε σ v (1/2)
      = inner ℝ (Work.Drive.sweepArc' r D σ (1/2)
        - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v := rfl
  rw [hL, inner_sub_left, hC, Work.Drive.nCoord, inner_sub_left, inner_sub_left]
  ring

/-- The ordinate at `ξ = 1/2` is `‖chartUp‖/2` plus the `chartE`-deviation of the arc's middle from
the needle's base point. -/
lemma nclmAH_half {lam δ₁ δ₂ ε σ : ℝ} {v : Space} (hv : ‖v‖ = 1)
    (hpos : 0 < ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖) :
    nclmAH r D lam δ₁ δ₂ ε σ v (1/2)
      = inner ℝ (Work.Drive.sweepArc' r D σ (1/2)
          - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0)
          (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
        + ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
  have hEE : inner ℝ (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
      (Work.Drive.chartE r D lam δ₁ δ₂ ε v) = 1 := by
    rw [real_inner_self_eq_norm_sq, nclm_chartE_norm (r := r) (D := D)
      (lam := lam) (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) (v := v) hpos]
    norm_num
  have hC : inner ℝ (Work.Drive.chartC r D lam δ₁ δ₂ ε v)
      (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
      = inner ℝ (Work.Drive.chordEndA r D δ₂ ε) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
        + ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
    rw [Work.Drive.chartC, inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, hEE, nclm_inner_v_chartE (r := r) (D := D) hv]
    ring
  have hsplit : inner ℝ (Work.Drive.sweepArc' r D σ (1/2)
        - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
      + inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0 - Work.Drive.chordEndA r D δ₂ ε)
          (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
      = inner ℝ (Work.Drive.sweepArc' r D σ (1/2) - Work.Drive.chordEndA r D δ₂ ε)
          (Work.Drive.chartE r D lam δ₁ δ₂ ε v) := by
    rw [← inner_add_left]; congr 1; abel
  have hL : nclmAH r D lam δ₁ δ₂ ε σ v (1/2)
      = inner ℝ (Work.Drive.sweepArc' r D σ (1/2)
        - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v) := rfl
  rw [hL, inner_sub_left, hC]
  have h1 : inner ℝ (Work.Drive.sweepArc' r D σ (1/2)) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
        - (inner ℝ (Work.Drive.chordEndA r D δ₂ ε) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
          + ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2)
      = inner ℝ (Work.Drive.sweepArc' r D σ (1/2) - Work.Drive.chordEndA r D δ₂ ε)
          (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
        - ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
    rw [inner_sub_left]; ring
  rw [h1, ← hsplit, nclm_inner_shiftedNeedle_chartE (r := r) (D := D) hv hpos]
  ring

/-- The ordinate difference between two fractions of the retained arc. -/
lemma nclmAH_sub (lam δ₁ δ₂ ε σ : ℝ) (v : Space) (ξ η : ℝ) :
    nclmAH r D lam δ₁ δ₂ ε σ v ξ - nclmAH r D lam δ₁ δ₂ ε σ v η
      = inner ℝ (r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)
          - r (Work.Drive.taR D σ + η * Work.Drive.sweepW' D σ))
          (Work.Drive.chartE r D lam δ₁ δ₂ ε v) := by
  simp only [nclmAH, Work.Drive.sweepArc']
  rw [← inner_sub_left]
  congr 1
  abel

/-! ## The target -/

theorem nclm_clauseProfile {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    Work.Drive.Generic.nclmPkgProfile r D := by
  -- ## A global velocity bound and a global Lipschitz constant for `r`
  obtain ⟨B, -, hB⟩ := Work.Drive.exists_bound_iteratedDeriv_knot hr 1
  set M : ℝ := max B 1 with hMdef
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMne : M ≠ 0 := ne_of_gt hM0
  have hvel_le : ∀ x : ℝ, ‖velocity r x‖ ≤ M := by
    intro x
    have h1 : velocity r x = iteratedDeriv 1 r x := by rw [iteratedDeriv_one]; rfl
    rw [h1]
    exact le_trans (hB x) (le_max_left _ _)
  have hlip : ∀ x y : ℝ, ‖r x - r y‖ ≤ M * |x - y| := by
    intro x y
    rcases lt_or_ge x y with hxy | hyx
    · have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := r) (s := Set.Icc x y)
        (fun z _ => (hr.smooth.differentiable (by simp)).differentiableAt)
        (fun z _ => hvel_le z) (convex_Icc x y) ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩
      simpa only [Real.norm_eq_abs, norm_sub_rev] using h
    · have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := r) (s := Set.Icc y x)
        (fun z _ => (hr.smooth.differentiable (by simp)).differentiableAt)
        (fun z _ => hvel_le z) (convex_Icc y x) ⟨le_rfl, hyx⟩ ⟨hyx, le_rfl⟩
      simpa only [Real.norm_eq_abs] using h
  -- ## The constants of the package
  obtain ⟨c, hc0, ε₀H, hε₀H0, hε₀H1, hHspec⟩ := Work.Drive.H2.baseHeight_lower hr hinfl D
  set cm : ℝ := ‖velocity r (Work.Drive.taR D 0)‖ with hcmdef
  have hcm0 : 0 < cm := by rw [hcmdef]; exact norm_pos_iff.mpr (hr.regular _)
  have hcmne : cm ≠ 0 := ne_of_gt hcm0
  have hcmM : cm ≤ M := by rw [hcmdef]; exact hvel_le _
  set cN : ℝ := min (c * cm / (1024 * M)) (c / 2048) with hcNdef
  have hcN0 : 0 < cN := by rw [hcNdef]; exact lt_min (by positivity) (by positivity)
  have hcNc : cN ≤ c / 1024 := by
    rw [hcNdef]
    exact (min_le_right _ _).trans (by linarith [hc0])
  have hcNcm : cN ≤ c * cm / (1024 * M) := by rw [hcNdef]; exact min_le_left _ _
  -- ## The thresholds
  obtain ⟨ε₀N, hε₀N0, -, hNrate⟩ := Work.Drive.Nclm.base_close_arcMid_rate hr D cN hcN0
  obtain ⟨ε₀T, hε₀T0, -, hT⟩ := nclm_tang hr D
  obtain ⟨ε₀W, hε₀W0, -, hwds⟩ := Work.Drive.windowDataSmall hr D 1 (by norm_num)
  obtain ⟨η, hη0, hη⟩ := Work.Drive.exists_window_small D (by positivity : (0 : ℝ) < 4 * M / c)
  set ε₀ : ℝ := min ε₀H (min ε₀N (min ε₀T (min ε₀W (min η (1/4))))) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min hε₀H0 (lt_min hε₀N0 (lt_min hε₀T0 (lt_min hε₀W0 (lt_min hη0 (by norm_num)))))
  have hε₀H : ε₀ ≤ ε₀H := by rw [hε₀def]; exact min_le_left _ _
  have hε₀N : ε₀ ≤ ε₀N := by rw [hε₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hε₀T : ε₀ ≤ ε₀T := by
    rw [hε₀def]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₀W : ε₀ ≤ ε₀W := by
    rw [hε₀def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε₀η : ε₀ ≤ η := by
    rw [hε₀def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hε₀q : ε₀ ≤ 1/4 := by
    rw [hε₀def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro ε hε0 hεε₀
  have hεH : ε ≤ ε₀H := le_trans hεε₀ hε₀H
  have hεN : ε ≤ ε₀N := le_trans hεε₀ hε₀N
  have hεT : ε ≤ ε₀T := le_trans hεε₀ hε₀T
  have hεW : ε ≤ ε₀W := le_trans hεε₀ hε₀W
  have hεη : ε ≤ η := le_trans hεε₀ hε₀η
  have hεq : ε ≤ 1/4 := le_trans hεε₀ hε₀q
  have hε1 : ε < 1 := by linarith
  have hε12 : ε ≤ 1/2 := by linarith
  have hWpos : 0 < Work.Drive.sweepW' D ε := Work.Drive.wds_sweepW'_pos D hε0 hε1
  obtain ⟨Λw, hΛw0, hΛwspec⟩ := nclm_window_eps D hε0 hε1
  obtain ⟨ΛN, hΛN0, hΛN14, hNrate'⟩ := hNrate ε hε0 hεN
  obtain ⟨ΛH, hΛH0, hΛH12, hHspec'⟩ := hHspec ε hε0 hεH
  set Λ : ℝ := min (min ΛH ΛN) Λw with hΛdef
  have hΛ0 : 0 < Λ := by rw [hΛdef]; exact lt_min (lt_min hΛH0 hΛN0) hΛw0
  have hΛleH : Λ ≤ ΛH := by rw [hΛdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hΛleN : Λ ≤ ΛN := by rw [hΛdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hΛlew : Λ ≤ Λw := by rw [hΛdef]; exact min_le_right _ _
  refine ⟨cm, c/4, Λ, hcm0, by positivity, hΛ0, ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε
  intro v hv hCv
  -- the chord and its unit direction
  set C : Space := Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε with hCdef
  have hCv' : C = ‖C‖ • v := by rw [hCdef]; exact hCv
  have hCne : C ≠ 0 := by
    rw [hCdef]
    exact sub_ne_zero.mpr (hwds δ₂ ε hδ₂0 hδ₂ε hε0 hεW).2.1
  have hv_eq : ‖C‖⁻¹ • C = v := by
    rw [hCv', smul_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg _), hv, mul_one,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hCne), one_smul]
  have hδ₂Λw : δ₂ ≤ Λw := le_trans hδ₂Λ hΛlew
  have hδ₂ΛN : δ₂ ≤ ΛN := le_trans hδ₂Λ hΛleN
  have hδ₁ΛN : δ₁ ≤ ΛN := le_trans hδ₁Λ hΛleN
  have hlamΛN : lam ≤ ΛN := le_trans hlamΛ hΛleN
  have hδ₂ΛH : δ₂ ≤ ΛH := le_trans hδ₂Λ hΛleH
  have hδ₁ΛH : δ₁ ≤ ΛH := le_trans hδ₁Λ hΛleH
  have hlamΛH : lam ≤ ΛH := le_trans hlamΛ hΛleH
  have hlam4 : lam ≤ 1/4 := le_trans hlamΛN hΛN14
  have hWσpos : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → 0 < Work.Drive.sweepW' D σ :=
    fun σ h1 h2 => nclm_window_wpos D hδ₂0 hδ₂ε hε0 hε12 h1 h2
  have hcontAX : ∀ σ : ℝ, Continuous (nclmAX r D lam δ₁ δ₂ ε σ v) :=
    fun σ => nclm_continuous_nclmAX hr lam δ₁ δ₂ ε σ v
  have hdiffAX : ∀ σ : ℝ, Differentiable ℝ (nclmAX r D lam δ₁ δ₂ ε σ v) :=
    fun σ => nclm_differentiable_nclmAX hr lam δ₁ δ₂ ε σ v
  -- ### clause (i): the tangent pairing
  have harc : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        cm / 4 ≤ inner ℝ (velocity r x) v := by
    intro σ hσlo hσhi x hx
    have h := hT δ₂ ε σ x hδ₂0 hδ₂ε hε0 hεT hσlo hσhi hx
    rw [← hcmdef] at h
    rwa [hv_eq] at h
  -- ### clauses (iii) and (iv): the derivative of the abscissa
  have hderiv_lower : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Ioo lam (1 - lam),
      cm * Work.Drive.sweepW' D σ / 8 ≤ deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ := by
    intro σ hσlo hσhi ξ hξ
    rw [nclm_deriv_nclmAX hr D lam δ₁ δ₂ ε σ v ξ]
    have hW := hWσpos σ hσlo hσhi
    have hx : Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ ∈
        Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ) :=
      nclm_mem_arc (D := D) hW ⟨le_of_lt (lt_trans hlam0 hξ.1), by linarith [hξ.2, hlam0]⟩
    have hA := harc σ hσlo hσhi _ hx
    nlinarith [hA, hW, hcm0]
  have hpos_deriv : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Ioo (0 : ℝ) 1,
      0 < deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ := by
    intro σ hσlo hσhi ξ hξ
    rw [nclm_deriv_nclmAX hr D lam δ₁ δ₂ ε σ v ξ]
    have hW := hWσpos σ hσlo hσhi
    have hx : Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ ∈
        Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ) :=
      nclm_mem_arc (D := D) hW ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
    have hA := harc σ hσlo hσhi _ hx
    nlinarith [hA, hW, hcm0]
  -- ### clause (v): the crossing point and its height
  have hclause5 : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∃ ξ₀ ∈ Set.Ioo lam (1 - lam),
        nclmAX r D lam δ₁ δ₂ ε σ v ξ₀ = 0
          ∧ c / 4 * (Work.Drive.sweepW' D ε) ^ 2 ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ₀ := by
    intro σ hσlo hσhi
    have hW := hWσpos σ hσlo hσhi
    have hWle : Work.Drive.sweepW' D σ ≤ 2 * Work.Drive.sweepW' D ε :=
      (hΛwspec δ₂ σ hδ₂0 hδ₂Λw hδ₂ε hσlo hσhi).2.1
    have hWge : Work.Drive.sweepW' D ε ≤ 2 * Work.Drive.sweepW' D σ := by
      linarith [(hΛwspec δ₂ σ hδ₂0 hδ₂Λw hδ₂ε hσlo hσhi).1]
    have hchart : c * (Work.Drive.sweepW' D ε) ^ 2 ≤
        ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ :=
      hHspec' lam δ₁ δ₂ hlam0 hlamΛH hδ₁0 hδ₁ΛH hδ₂0 hδ₂ΛH hδ₂ε v hv hCv
    have hchartpos : 0 < ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ :=
      lt_of_lt_of_le (by positivity) hchart
    -- the closeness of the arc's middle to the needle's base point
    have hmid : ‖Work.Drive.sweepArc' r D σ (1/2) - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0‖
        ≤ cN * (Work.Drive.sweepW' D ε) ^ 2 := by
      simpa only [norm_sub_rev] using
        hNrate' lam δ₁ δ₂ hlam0 hlamΛN hlam12 hδ₁0 hδ₁ΛN hδ₂0 hδ₂ΛN hδ₂ε σ hσlo hσhi
    -- the abscissa at `ξ = 1/2`
    have hXhalf : |nclmAX r D lam δ₁ δ₂ ε σ v (1/2)|
        ≤ cN * (Work.Drive.sweepW' D ε) ^ 2 := by
      rw [nclmAX_half (r := r) (D := D) hv]
      calc |inner ℝ (Work.Drive.sweepArc' r D σ (1/2)
              - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0) v|
          ≤ ‖Work.Drive.sweepArc' r D σ (1/2)
              - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0‖ * ‖v‖ :=
            abs_real_inner_le_norm _ _
        _ = ‖Work.Drive.sweepArc' r D σ (1/2)
              - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0‖ := by rw [hv, mul_one]
        _ ≤ cN * (Work.Drive.sweepW' D ε) ^ 2 := hmid
    set W := Work.Drive.sweepW' D ε with hWdef
    set ρ : ℝ := 32 * cN * W / cm with hρdef
    have hρ0 : 0 < ρ := by rw [hρdef]; positivity
    have hWm : W * c ≤ 4 * M := by
      have hWle' : W ≤ 4 * M / c := (hη ε hε0.le hεη).2
      rw [le_div_iff₀ hc0] at hWle'
      linarith [hWle']
    have hρle : ρ ≤ 1/8 := by
      have h1 : ρ ≤ 32 * (c * cm / (1024 * M)) * W / cm := by
        rw [hρdef]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcNcm (by norm_num : (0 : ℝ) ≤ 32)) hWpos.le) hcm0.le
      have h2 : 32 * (c * cm / (1024 * M)) * W / cm = c * W / (32 * M) := by
        field_simp
        ring
      have h3 : c * W / (32 * M) ≤ 1/8 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 32 * M)]
        nlinarith [hWm, hc0, hM0]
      linarith [h1, h2.le, h2.ge, h3]
    -- the interval where the zero lies
    have haa : lam < 1/2 - ρ := by linarith
    have hbb : 1/2 + ρ < 1 - lam := by linarith
    have hleft : (cm * W / 16) * ρ ≤ nclmAX r D lam δ₁ δ₂ ε σ v (1/2)
        - nclmAX r D lam δ₁ δ₂ ε σ v (1/2 - ρ) := by
      obtain ⟨c', hc'mem, hc'eq⟩ := exists_deriv_eq_slope (nclmAX r D lam δ₁ δ₂ ε σ v)
        (by linarith : 1/2 - ρ < 1/2)
        (hcontAX σ).continuousOn
        (hdiffAX σ).differentiableOn
      have hc'mem' : c' ∈ Set.Ioo lam (1 - lam) :=
        ⟨by linarith [hc'mem.1, haa], by linarith [hc'mem.2]⟩
      have hlow := hderiv_lower σ hσlo hσhi c' hc'mem'
      have hrr : 1/2 - (1/2 - ρ) = ρ := by ring
      rw [hc'eq, le_div_iff₀ (by linarith : (0 : ℝ) < 1/2 - (1/2 - ρ)), hrr] at hlow
      have hstep : cm * W / 16 ≤ cm * Work.Drive.sweepW' D σ / 8 := by
        rw [hWdef]
        have h1 : cm * Work.Drive.sweepW' D ε ≤
            cm * (2 * Work.Drive.sweepW' D σ) := mul_le_mul_of_nonneg_left hWge hcm0.le
        linarith [h1]
      have h2 := mul_le_mul_of_nonneg_right hstep hρ0.le
      linarith [hlow, h2]
    have hright : (cm * W / 16) * ρ ≤ nclmAX r D lam δ₁ δ₂ ε σ v (1/2 + ρ)
        - nclmAX r D lam δ₁ δ₂ ε σ v (1/2) := by
      obtain ⟨c', hc'mem, hc'eq⟩ := exists_deriv_eq_slope (nclmAX r D lam δ₁ δ₂ ε σ v)
        (by linarith : 1/2 < 1/2 + ρ)
        (hcontAX σ).continuousOn
        (hdiffAX σ).differentiableOn
      have hc'mem' : c' ∈ Set.Ioo lam (1 - lam) :=
        ⟨by linarith [hc'mem.1, haa], by linarith [hc'mem.2, hbb]⟩
      have hlow := hderiv_lower σ hσlo hσhi c' hc'mem'
      have hrr : 1/2 + ρ - 1/2 = ρ := by ring
      rw [hc'eq, le_div_iff₀ (by linarith : (0 : ℝ) < 1/2 + ρ - 1/2), hrr] at hlow
      have hstep : cm * W / 16 ≤ cm * Work.Drive.sweepW' D σ / 8 := by
        rw [hWdef]
        have h1 : cm * Work.Drive.sweepW' D ε ≤
            cm * (2 * Work.Drive.sweepW' D σ) := mul_le_mul_of_nonneg_left hWge hcm0.le
        linarith [h1]
      have h2 := mul_le_mul_of_nonneg_right hstep hρ0.le
      linarith [hlow, h2]
    have hprod : (cm * W / 16) * ρ = 2 * (cN * W ^ 2) := by
      rw [hρdef]
      field_simp
      ring
    have hXa : nclmAX r D lam δ₁ δ₂ ε σ v (1/2 - ρ) ≤ 0 := by
      have h1 : nclmAX r D lam δ₁ δ₂ ε σ v (1/2) ≤ cN * W ^ 2 := le_trans (le_abs_self _) hXhalf
      have h2 : 0 ≤ cN * W ^ 2 := by positivity
      linarith [hleft, hprod, h1, h2]
    have hXb : 0 ≤ nclmAX r D lam δ₁ δ₂ ε σ v (1/2 + ρ) := by
      have h1 := abs_le.mp hXhalf |>.1
      have h2 : 0 ≤ cN * W ^ 2 := by positivity
      linarith [hright, hprod, h1, h2]
    obtain ⟨ξ₀, hξ₀mem, hξ₀zero⟩ := intermediate_value_Icc
      (by linarith : 1/2 - ρ ≤ 1/2 + ρ)
      (hcontAX σ).continuousOn ⟨hXa, hXb⟩
    have hξ₀dist : |ξ₀ - 1/2| ≤ ρ :=
      abs_le.mpr ⟨by linarith [hξ₀mem.1], by linarith [hξ₀mem.2]⟩
    refine ⟨ξ₀, ⟨by linarith [hξ₀mem.1, haa], by linarith [hξ₀mem.2, hbb]⟩, hξ₀zero, ?_⟩
    -- the height at the crossing
    have hhalf : ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 - cN * W ^ 2
        ≤ nclmAH r D lam δ₁ δ₂ ε σ v (1/2) := by
      rw [nclmAH_half (r := r) (D := D) hv hchartpos]
      have h1 : |inner ℝ (Work.Drive.sweepArc' r D σ (1/2)
            - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0)
            (Work.Drive.chartE r D lam δ₁ δ₂ ε v)| ≤ cN * W ^ 2 := by
        calc |inner ℝ (Work.Drive.sweepArc' r D σ (1/2)
                - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0)
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
            ≤ ‖Work.Drive.sweepArc' r D σ (1/2)
                - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0‖ *
              ‖Work.Drive.chartE r D lam δ₁ δ₂ ε v‖ := abs_real_inner_le_norm _ _
          _ = ‖Work.Drive.sweepArc' r D σ (1/2)
                - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0‖ := by
              rw [nclm_chartE_norm (r := r) (D := D) hchartpos, mul_one]
          _ ≤ cN * W ^ 2 := hmid
      linarith [abs_le.mp h1 |>.1]
    have hdiff : |nclmAH r D lam δ₁ δ₂ ε σ v ξ₀ - nclmAH r D lam δ₁ δ₂ ε σ v (1/2)|
        ≤ c * W ^ 2 / 16 := by
      rw [nclmAH_sub (r := r) (D := D) lam δ₁ δ₂ ε σ v ξ₀ (1/2)]
      calc |inner ℝ (r (Work.Drive.taR D σ + ξ₀ * Work.Drive.sweepW' D σ)
              - r (Work.Drive.taR D σ + (1/2) * Work.Drive.sweepW' D σ))
              (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
          ≤ ‖r (Work.Drive.taR D σ + ξ₀ * Work.Drive.sweepW' D σ)
              - r (Work.Drive.taR D σ + (1/2) * Work.Drive.sweepW' D σ)‖ *
            ‖Work.Drive.chartE r D lam δ₁ δ₂ ε v‖ := abs_real_inner_le_norm _ _
        _ = ‖r (Work.Drive.taR D σ + ξ₀ * Work.Drive.sweepW' D σ)
              - r (Work.Drive.taR D σ + (1/2) * Work.Drive.sweepW' D σ)‖ := by
            rw [nclm_chartE_norm (r := r) (D := D) hchartpos, mul_one]
        _ ≤ M * |(Work.Drive.taR D σ + ξ₀ * Work.Drive.sweepW' D σ)
              - (Work.Drive.taR D σ + (1/2) * Work.Drive.sweepW' D σ)| := hlip _ _
        _ = M * (Work.Drive.sweepW' D σ * |ξ₀ - 1/2|) := by
            rw [show (Work.Drive.taR D σ + ξ₀ * Work.Drive.sweepW' D σ)
                  - (Work.Drive.taR D σ + (1/2) * Work.Drive.sweepW' D σ)
                = Work.Drive.sweepW' D σ * (ξ₀ - 1/2) by ring, abs_mul, abs_of_pos hW]
        _ ≤ M * (2 * W * ρ) := by
            have h1 : Work.Drive.sweepW' D σ * |ξ₀ - 1/2| ≤ 2 * W * ρ := by
              calc Work.Drive.sweepW' D σ * |ξ₀ - 1/2| ≤ Work.Drive.sweepW' D σ * ρ :=
                    mul_le_mul_of_nonneg_left hξ₀dist hW.le
                _ ≤ 2 * W * ρ := by
                    rw [hWdef]
                    exact mul_le_mul_of_nonneg_right hWle hρ0.le
            exact mul_le_mul_of_nonneg_left h1 hM0.le
        _ ≤ c * W ^ 2 / 16 := by
            have h1 : M * (2 * W * ρ) = 64 * M * cN * W ^ 2 / cm := by
              rw [hρdef]; ring
            rw [h1]
            have h2 : 64 * M * cN * W ^ 2 / cm
                ≤ 64 * M * (c * cm / (1024 * M)) * W ^ 2 / cm :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hcNcm (by positivity : (0 : ℝ) ≤ 64 * M))
                  (sq_nonneg W)) hcm0.le
            have h3 : 64 * M * (c * cm / (1024 * M)) * W ^ 2 / cm = c * W ^ 2 / 16 := by
              field_simp
              ring
            linarith [h2, h3.le, h3.ge]
    have hcNbound : cN * W ^ 2 ≤ c * W ^ 2 / 1024 := by
      have := mul_le_mul_of_nonneg_right hcNc (sq_nonneg W)
      linarith [this]
    have hfin : c / 4 * W ^ 2 ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ₀ := by
      rw [show c / 4 * W ^ 2 = (c * W ^ 2) / 4 by ring]
      have h4 : -((c * W ^ 2) / 16) ≤
          nclmAH r D lam δ₁ δ₂ ε σ v ξ₀ - nclmAH r D lam δ₁ δ₂ ε σ v (1/2) :=
        abs_le.mp hdiff |>.1
      have h5 : (c * W ^ 2) / 2 ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
        linarith [hchart]
      have h6 : (c * W ^ 2) / 2 - cN * W ^ 2 ≤ nclmAH r D lam δ₁ δ₂ ε σ v (1/2) := by
        linarith [hhalf, h5]
      have h7 : cN * W ^ 2 ≤ (c * W ^ 2) / 1024 := hcNbound
      have h8 : (c * W ^ 2) / 4 ≤
          (c * W ^ 2) / 2 - (c * W ^ 2) / 1024 - (c * W ^ 2) / 16 := by
        have hW2 : 0 ≤ c * W ^ 2 := mul_nonneg hc0.le (sq_nonneg W)
        linarith
      linarith [h4, h6, h7, h8]
    rw [hWdef] at hfin
    exact hfin
  -- ## The package
  have hmono : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      StrictMonoOn (nclmAX r D lam δ₁ δ₂ ε σ v) (Set.Icc (0 : ℝ) 1) := by
    intro σ hσlo hσhi
    refine strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) (hcontAX σ).continuousOn ?_
    intro ξ hξ
    rw [interior_Icc] at hξ
    exact hpos_deriv σ hσlo hσhi ξ hξ
  exact ⟨harc, hmono, (fun σ h1 h2 ξ hξ => hpos_deriv σ h1 h2 ξ hξ),
    (fun σ h1 h2 ξ hξ => hderiv_lower σ h1 h2 ξ hξ), hclause5⟩

end Work.Drive.Generic
