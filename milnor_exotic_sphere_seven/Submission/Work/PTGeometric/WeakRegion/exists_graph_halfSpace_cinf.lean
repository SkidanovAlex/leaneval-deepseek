import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Basic
import Submission.Work.PTGeometric.WeakRegion.HalfSpaceCoords
import Submission.Work.PTGeometric.WeakRegion.HalfSpaceGraphData
import Submission.Work.PTGeometric.WeakRegion.derivBoundIcc
import Submission.Work.PTGeometric.WeakRegion.rootParamContinuous
import Submission.Work.PTGeometric.WeakRegion.exists_box
import Submission.Work.PTGeometric.WeakRegion.rootLipschitz
import Submission.Work.PTGeometric.WeakRegion.exists_root
import Submission.Work.PTGeometric.WeakRegion.expandTangential
import Submission.Work.PTGeometric.WeakRegion.expandNormal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# PTGeometric/WeakRegion: the half-space graph result at `C^∞`

This file proves `Work.PTGeometric.WeakRegion.exists_graph_halfSpace_cinf`.  The proof works in the
coordinates `(u,s) ∈ T × ℝ` (`T = hsTang n` the tangential hyperplane, `hsConn (u,s) = u + s • e 0`)
set up in `HalfSpaceCoords`/`HalfSpaceGraphData`; `HalfSpaceGraphData` also contains the box
`HalfSpaceGraphSetup.Box` on which all local estimates hold uniformly and the root function
`HalfSpaceGraphSetup.Root` of the `s`-slice `s ↦ F (u,s) = Ψ (u + s • e 0)`.

The two analytic steps performed here are

* `root_hasFDerivAt_aux`: the root function is differentiable with derivative
  `-(∂_s F)⁻¹ ∂_u F`, by subtracting the two root identities, expanding both differences to first
  order (using the uniform expansions `expandTangential`/`expandNormal` of the child modules) and
  dividing by the nonvanishing normal derivative;
* `root_contDiff_aux`: bootstrapping `C^0 → C^1 → …`: if `h` is differentiable with the displayed
  derivative and `Ψ` is `C^{m+1}` on the *fixed* relative set `U ∩ {0 ≤ z 0}`, then the displayed
  derivative is `C^m` near every point of the ball (composition of the `C^m` graph map
  `u ↦ (u, h u)` into the fixed set with `L`, then division by the nonvanishing `Ds`), so `h` is
  `C^{m+1}`; this uses the set-level hypothesis in an essential way.
-/

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric.WeakRegion

noncomputable section

variable {n : ℕ} [NeZero n]


/-- The differentiability of the root function. -/
theorem root_hasFDerivAt_aux (S : HalfSpaceGraphSetup n) {ρ δ M : ℝ} (B : S.Box ρ δ M)
    {h : hsTang n → ℝ} (H : S.Root B h)
    (hlip : ∀ u ∈ Metric.ball (hsMk S.p) ρ, ∀ u' ∈ Metric.ball (hsMk S.p) ρ,
      |h u' - h u| ≤ 2 * M / |S.c| * ‖u' - u‖)
    (hexpU : ∀ (x₀ : hsTang n × ℝ), x₀ ∈ S.dom → x₀.1 ∈ Metric.ball (hsMk S.p) ρ →
      ∀ ε > 0, ∃ η > 0, ∀ u : hsTang n, ‖u - x₀.1‖ < η → ∀ b ∈ Set.Icc 0 δ, |b - x₀.2| < η →
        ‖S.F (u, b) - S.F (x₀.1, b) - S.Du x₀ (u - x₀.1)‖ ≤ ε * ‖u - x₀.1‖)
    (hexpN : ∀ (u : hsTang n), u ∈ Metric.ball (hsMk S.p) ρ → ∀ (s₀ : ℝ), s₀ ∈ Set.Icc 0 δ →
      ∀ ε > 0, ∃ η > 0, ∀ b ∈ Set.Icc 0 δ, |b - s₀| < η →
        ‖S.F (u, b) - S.F (u, s₀) - S.Ds (u, s₀) * (b - s₀)‖ ≤ ε * |b - s₀|)
    (u₀ : hsTang n) (hu₀ : u₀ ∈ Metric.ball (hsMk S.p) ρ) :
    HasFDerivAt h (S.A (u₀, h u₀)) u₀ := by
  have hcpos : 0 < |S.c| := abs_pos.mpr (ne_of_lt S.hc)
  have hrootu₀ : S.F (u₀, h u₀) = 0 := (H.hmem u₀ hu₀).2
  have hx₀dom : (u₀, h u₀) ∈ S.dom := B.hmem u₀ hu₀ (h u₀) (H.hmem u₀ hu₀).1
  have hDs_le : S.Ds (u₀, h u₀) ≤ S.c / 2 := (B.hL u₀ hu₀ (h u₀) (H.hmem u₀ hu₀).1).2
  have hDs_neg : S.Ds (u₀, h u₀) < 0 := by linarith [S.hc]
  have hDs_abs : |S.Ds (u₀, h u₀)| ≥ |S.c| / 2 := by
    rw [abs_of_neg hDs_neg, abs_of_neg S.hc]
    linarith [hDs_le]
  have hρpos : 0 < ρ - ‖u₀ - hsMk S.p‖ := by
    have h := Metric.mem_ball.mp hu₀
    rw [dist_eq_norm] at h
    linarith
  -- the main ε-δ estimate
  have key : ∀ ε > 0, ∃ η > 0, ∀ u : hsTang n, ‖u - u₀‖ < η →
      ‖h u - h u₀ - S.A (u₀, h u₀) (u - u₀)‖ ≤ ε * ‖u - u₀‖ := by
    intro ε hε
    set μ : ℝ := |S.c| / 2 with hμdef
    have hμpos : 0 < μ := by rw [hμdef]; linarith
    set K : ℝ := 2 * M / |S.c| with hKdef
    have hKpos : 0 < K := by
      rw [hKdef]
      exact div_pos (by linarith [B.hM]) (abs_pos.mpr (ne_of_lt S.hc))
    have hεμ : 0 < ε * μ / 4 := div_pos (mul_pos hε hμpos) (by norm_num)
    have hεμK : 0 < ε * μ / (4 * K) := div_pos (mul_pos hε hμpos) (by linarith [hKpos])
    obtain ⟨η₁, hη₁pos, hU1⟩ := hexpU (u₀, h u₀) hx₀dom hu₀ (ε * μ / 4) hεμ
    obtain ⟨η₂, hη₂pos, hN1⟩ := hexpN u₀ hu₀ (h u₀) (H.hmem u₀ hu₀).1 (ε * μ / (4 * K)) hεμK
    refine ⟨min η₁ (min (η₁ / K) (min η₂ (min (η₂ / K) (ρ - ‖u₀ - hsMk S.p‖)))), ?_, ?_⟩
    · positivity
    intro u hu
    simp only [lt_min_iff] at hu
    obtain ⟨hu1, hu2, hu3, hu4, hu5⟩ := hu
    have hu_ball : u ∈ Metric.ball (hsMk S.p) ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖u - hsMk S.p‖ = ‖(u - u₀) + (u₀ - hsMk S.p)‖ := by
            congr 1
            abel
        _ ≤ ‖u - u₀‖ + ‖u₀ - hsMk S.p‖ := norm_add_le _ _
        _ < (ρ - ‖u₀ - hsMk S.p‖) + ‖u₀ - hsMk S.p‖ := by linarith
        _ = ρ := by ring
    have huI : h u ∈ Set.Icc 0 δ := (H.hmem u hu_ball).1
    have hroutu : S.F (u, h u) = 0 := (H.hmem u hu_ball).2
    have hΔ : |h u - h u₀| ≤ K * ‖u - u₀‖ := by
      have h1 : |h u₀ - h u| ≤ K * ‖u₀ - u‖ := hlip u hu_ball u₀ hu₀
      calc |h u - h u₀| = |h u₀ - h u| := abs_sub_comm _ _
        _ ≤ K * ‖u₀ - u‖ := h1
        _ = K * ‖u - u₀‖ := by rw [norm_sub_rev]
    have hΔ1 : |h u - h u₀| < η₁ := by
      have h2 : K * ‖u - u₀‖ < η₁ := by
        have := (lt_div_iff₀ hKpos).mp hu2
        linarith [this]
      linarith
    have hΔ2 : |h u - h u₀| < η₂ := by
      have h2 : K * ‖u - u₀‖ < η₂ := by
        have := (lt_div_iff₀ hKpos).mp hu4
        linarith [this]
      linarith
    have e1 := hU1 u hu1 (h u) huI hΔ1
    have e2 := hN1 (h u) huI hΔ2
    -- algebra
    have hr2' : ‖S.F (u₀, h u) - S.F (u₀, h u₀) - S.Ds (u₀, h u₀) * (h u - h u₀)‖
        ≤ ε * μ / 4 * ‖u - u₀‖ := by
      refine le_trans e2 ?_
      have h3 : 0 < ε * μ / (4 * K) := by positivity
      calc ε * μ / (4 * K) * |h u - h u₀| ≤ ε * μ / (4 * K) * (K * ‖u - u₀‖) :=
            mul_le_mul_of_nonneg_left hΔ h3.le
        _ = ε * μ / 4 * ‖u - u₀‖ := by
            have hKK : ε * μ / (4 * K) * K = ε * μ / 4 := by
              field_simp
            rw [← mul_assoc, hKK]
    have e1' : ‖S.F (u, h u) - S.F (u₀, h u) - S.Du (u₀, h u₀) (u - u₀)‖
        ≤ ε * μ / 4 * ‖u - u₀‖ := by simpa using e1
    have hid : S.Du (u₀, h u₀) (u - u₀) + S.Ds (u₀, h u₀) * (h u - h u₀)
        = - ((S.F (u, h u) - S.F (u₀, h u) - S.Du (u₀, h u₀) (u - u₀))
            + (S.F (u₀, h u) - S.F (u₀, h u₀) - S.Ds (u₀, h u₀) * (h u - h u₀))) := by
      rw [hroutu, hrootu₀]
      ring
    have hbound : ‖S.Du (u₀, h u₀) (u - u₀) + S.Ds (u₀, h u₀) * (h u - h u₀)‖
        ≤ ε * μ / 2 * ‖u - u₀‖ := by
      rw [hid, norm_neg]
      calc ‖(S.F (u, h u) - S.F (u₀, h u) - S.Du (u₀, h u₀) (u - u₀))
              + (S.F (u₀, h u) - S.F (u₀, h u₀) - S.Ds (u₀, h u₀) * (h u - h u₀))‖
          ≤ ‖S.F (u, h u) - S.F (u₀, h u) - S.Du (u₀, h u₀) (u - u₀)‖
            + ‖S.F (u₀, h u) - S.F (u₀, h u₀) - S.Ds (u₀, h u₀) * (h u - h u₀)‖ :=
            norm_add_le _ _
        _ ≤ ε * μ / 4 * ‖u - u₀‖ + ε * μ / 4 * ‖u - u₀‖ := add_le_add e1' hr2'
        _ = ε * μ / 2 * ‖u - u₀‖ := by ring
    have hmain : h u - h u₀ - S.A (u₀, h u₀) (u - u₀)
        = (S.Du (u₀, h u₀) (u - u₀) + S.Ds (u₀, h u₀) * (h u - h u₀))
          / S.Ds (u₀, h u₀) := by
      have hDne : S.Ds (u₀, h u₀) ≠ 0 := ne_of_lt hDs_neg
      rw [S.A_apply, S.Du_apply, div_eq_mul_inv]
      field_simp
      ring
    calc ‖h u - h u₀ - S.A (u₀, h u₀) (u - u₀)‖
        = ‖S.Du (u₀, h u₀) (u - u₀) + S.Ds (u₀, h u₀) * (h u - h u₀)‖
            / |S.Ds (u₀, h u₀)| := by
          rw [hmain]
          simp only [norm_div, Real.norm_eq_abs]
      _ ≤ (ε * μ / 2 * ‖u - u₀‖) / μ := by
          refine le_trans ?_ (div_le_div_of_nonneg_right hbound hμpos.le)
          exact div_le_div_of_nonneg_left (norm_nonneg _) hμpos hDs_abs
      _ = ε / 2 * ‖u - u₀‖ := by
          rw [hμdef]
          field_simp
      _ ≤ ε * ‖u - u₀‖ := by
          have h1 : 0 ≤ ‖u - u₀‖ := norm_nonneg _
          nlinarith [hε, h1]
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨η, hη, hkey⟩ := key ε hε
  refine Metric.mem_nhds_iff.mpr ⟨η, hη, fun k hk => ?_⟩
  have hk' : ‖k‖ < η := by
    have := Metric.mem_ball.mp hk
    simpa using this
  have := hkey (u₀ + k) (by simpa using hk')
  simpa using this

/-- The bootstrap: if the root function is differentiable with the displayed derivative, then it is
`C^k` on the ball for every `k`. -/
theorem root_contDiff_aux (S : HalfSpaceGraphSetup n) {ρ δ M : ℝ} (B : S.Box ρ δ M)
    {h : hsTang n → ℝ} (H : S.Root B h)
    (hderiv : ∀ u ∈ Metric.ball (hsMk S.p) ρ, HasFDerivAt h (S.A (u, h u)) u) :
    ∀ k : ℕ, ContDiffOn ℝ (k : WithTop ℕ∞) h (Metric.ball (hsMk S.p) ρ) := by
  intro k
  induction k with
  | zero => exact contDiffOn_zero.mpr H.hcont
  | succ k ih =>
    have hdiff : DifferentiableOn ℝ h (Metric.ball (hsMk S.p) ρ) :=
      fun u hu => (hderiv u hu).differentiableAt.differentiableWithinAt
    have hA_ball : ContDiffOn ℝ (k : WithTop ℕ∞) (fun u : hsTang n => S.A (u, h u))
        (Metric.ball (hsMk S.p) ρ) := by
      refine contDiffOn_clm_apply.mpr (fun v => ?_)
      have hgraph : ContDiffOn ℝ (k : WithTop ℕ∞) (fun u : hsTang n => (u, h u))
          (Metric.ball (hsMk S.p) ρ) := contDiffOn_id.prodMk ih
      have hmap : MapsTo (fun u : hsTang n => (u, h u)) (Metric.ball (hsMk S.p) ρ) S.dom :=
        fun u hu => B.hmem u hu (h u) (H.hmem u hu).1
      have hLc : ContDiffOn ℝ (k : WithTop ℕ∞) (fun u : hsTang n => S.L (u, h u))
          (Metric.ball (hsMk S.p) ρ) := (S.contDiffOn_L k).comp hgraph hmap
      have hSc : ContDiffOn ℝ (k : WithTop ℕ∞) (fun u : hsTang n => S.Ds (u, h u))
          (Metric.ball (hsMk S.p) ρ) := (S.contDiffOn_Ds k).comp hgraph hmap
      have hnum : ContDiffOn ℝ (k : WithTop ℕ∞)
          (fun u : hsTang n => S.L (u, h u) ((v : hsTang n) : EuclideanSpace ℝ (Fin n)))
          (Metric.ball (hsMk S.p) ρ) := hLc.clm_apply contDiffOn_const
      have hne : ∀ u ∈ Metric.ball (hsMk S.p) ρ, S.Ds (u, h u) ≠ 0 := by
        intro u hu
        have h1 := (B.hL u hu (h u) (H.hmem u hu).1).2
        exact ne_of_lt (lt_of_le_of_lt h1 (by linarith [S.hc]))
      refine (hnum.div hSc hne).neg.congr (fun u hu => ?_)
      rw [S.A_apply, div_eq_mul_inv]
      simp only [Pi.mul_apply, Pi.inv_apply]
      ring
    have hfderiv : ContDiffOn ℝ (k : WithTop ℕ∞) (fderivWithin ℝ h (Metric.ball (hsMk S.p) ρ))
        (Metric.ball (hsMk S.p) ρ) :=
      hA_ball.congr (fun u hu => (hderiv u hu).hasFDerivWithinAt.fderivWithin
        (Metric.isOpen_ball.uniqueDiffWithinAt hu))
    exact contDiffOn_succ_of_fderivWithin hdiff (by simp) hfderiv

/-- **The half-space graph result, at `C^∞` (smooth, not analytic), with the set-level smoothness hypothesis.**

`Ψ` is `C^∞` on `U ∩ {0 ≤ z 0}` for a FIXED open neighbourhood `U` of `p`; `Ψ p = 0`; the
within-derivative of `Ψ` at `p` is the *negative* multiple `c` of the normal-coordinate functional;
`Ψ ≥ 0` on the boundary hyperplane near `p`. Conclusion: near `p` inside the half-space, `{Ψ ≤ 0}` is
the epigraph `{s ≥ h u}` of a `C^∞` `h ≥ 0` with `h (tail p) = 0`, depending on the tangential
variables only. (`consVec s u = u + s • e 0`, `tailVec z = z - (z 0) • e 0`.)

Why the hypothesis is the *set*-level one and not `ContDiffWithinAt ℝ ∞ Ψ (range I) p` (which is what
a pointwise order-`∞` smoothness gives, and is NOT enough): for `n = 2` and
`Ψ z = -(z 0) + φ (z 0) + (z 1)^2` with `φ` of class `C^m` on `(-1/m, 1/m)` for every `m` but not
`C^∞` near `0`, every hypothesis except this one holds (`c = -1`), yet the root
`y ↦ (· - φ)⁻¹ (y^2)` is not `C^∞` on any neighbourhood of `0`. In the intended application the
hypothesis is available: `Φ` is `ContMDiff 𝓡∂ 𝓘(ℝ,ℝ) ∞` (at every point), so in a fixed chart of the
maximal atlas its chart expression is `C^∞` on the fixed relative set
`(chart.extend) '' (chart.source ∩ V)` by `OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff` plus
`contMDiffOn_iff_contDiffOn`.

Suggested route, using only Mathlib's within-calculus (no extension of `Ψ` across the boundary is
available or needed).
* `F u s := Ψ (consVec s u)` is `C^k` on a fixed relative neighbourhood of `(tail p,0)` in the
  half-space, for every `k`; `R u := F u 0 = Ψ u ≥ 0` two-sidedly in `u` near `tail p`
  (the boundary sign hypothesis) and `R (tail p) = 0`.
* Continuity of the within-derivative `∂_s F` at `(tail p, 0)` (value `c < 0`) gives `∂_s F < 0` on a
  fixed box `{|u - tail p| ≤ ρ} × [0, δ]`, so `s ↦ F u s` is strictly decreasing there and has a
  unique root `h u ∈ [0, δ]` for every `u` in that ball (existence: `R u ≥ 0`, `F u δ < 0` by the
  intermediate-value property; if `R u = 0` the root is `0`). Then `h ≥ 0`, `h` continuous,
  `h (tail p) = 0`, and `F u s ≤ 0 ↔ h u ≤ s` for `s ∈ [0, δ]`.
* Differentiability of `h` at each point `u` of a fixed ball `W ∋ tail p`, with
  `∂h u = -(∂_u F) (u, h u) / (∂_s F) (u, h u)`: subtract the identities `F (u', h u') = 0` and
  `F (u, h u) = 0`, apply the one-variable mean-value property to `s ↦ F u' s` on `[h u, h u']`
  (both endpoints `≥ 0`, so the interval lies in the half-space) and use that `u' ↦ F u' (h u)` is
  differentiable at `u` (the point `(u, h u)` is in the half-space) together with `h u' → h u`.
* Bootstrapping: if `h` is `C^m` near `u` and differentiable there with the displayed derivative,
  then the right-hand side is `C^m` near `u` provided `Ψ` is `C^{m+1}` near `(u, h u)` — the
  composition rule for within-calculus, using `h ≥ 0` so that `(u, h u)` lies in the half-space. So
  `h` is `C^{m+1}` near `u`, and `C^0 → C^1 → …` gives `ContDiffOn ℝ ∞ h W`. (`ContDiffOn ℝ ∞ h W`
  requires `h` to be `C^m` near EVERY point of `W`, but the neighbourhood of each point may depend on
  `m`; so `W` can be fixed once and for all and the induction performed at each point of `W`, which
  works because the hypothesis above is set-level.) -/

theorem exists_graph_halfSpace_cinf {n : ℕ} [NeZero n]
    (Ψ : EuclideanSpace ℝ (Fin n) → ℝ) (p : EuclideanSpace ℝ (Fin n))
    (hp0 : p.ofLp 0 = 0)
    (hC : ∃ U ∈ nhds p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ
      (U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)))
    (h0 : Ψ p = 0) (c : ℝ) (hc : c < 0)
    (hd : fderivWithin ℝ Ψ (Set.range (modelWithCornersEuclideanHalfSpace n)) p
      = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0))
    (hsign : Filter.Eventually (fun z : EuclideanSpace ℝ (Fin n) =>
        z.ofLp 0 = 0 → 0 ≤ Ψ z)
        (nhdsWithin p (Set.range (modelWithCornersEuclideanHalfSpace n)))) :
    ∃ (h : EuclideanSpace ℝ (Fin n) → ℝ) (W : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen W ∧ Work.PTGeometric.tailVec p ∈ W ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h W ∧ (∀ u ∈ W, 0 ≤ h u) ∧
      h (Work.PTGeometric.tailVec p) = 0 ∧
      Filter.Eventually (fun z : EuclideanSpace ℝ (Fin n) =>
        (Ψ z ≤ 0 ↔ h (Work.PTGeometric.tailVec z) ≤ z.ofLp 0))
        (nhdsWithin p (Set.range (modelWithCornersEuclideanHalfSpace n))) := by
  obtain ⟨U₀, hU₀mem, hCU₀⟩ := hC
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp hU₀mem
  have hCU : ContDiffOn ℝ ∞ Ψ (U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)) :=
    hCU₀.mono (fun z hz => ⟨hUsub hz.1, hz.2⟩)
  let S : HalfSpaceGraphSetup n :=
    { Ψ := Ψ, p := p, hp0 := hp0, U := U, hUopen := hUopen, hpU := hpU, hCU := hCU,
      h0 := h0, c := c, hc := hc, hd := hd, hsign := hsign }
  obtain ⟨ρ, δ, M, B⟩ := exists_box S
  obtain ⟨h₀, H⟩ := exists_root S B
  have hderiv : ∀ u ∈ Metric.ball (hsMk S.p) ρ, HasFDerivAt h₀ (S.A (u, h₀ u)) u :=
    fun u hu => root_hasFDerivAt_aux S B H (rootLipschitz S H)
      (fun x₀ hx₀ hx₀ρ => expandTangential S B x₀ hx₀ hx₀ρ)
      (fun u hu s₀ hs₀ => expandNormal S B hu hs₀) u hu
  have hcd : ∀ k : ℕ, ContDiffOn ℝ (k : WithTop ℕ∞) h₀ (Metric.ball (hsMk S.p) ρ) :=
    root_contDiff_aux S B H hderiv
  have hcdInf : ContDiffOn ℝ ∞ h₀ (Metric.ball (hsMk S.p) ρ) := contDiffOn_infty.mpr hcd
  refine ⟨fun z => h₀ (hsMk z), hsMk ⁻¹' Metric.ball (hsMk S.p) ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Metric.isOpen_ball.preimage hsMk.continuous
  · rw [Set.mem_preimage, hsMk_tailVec]
    exact Metric.mem_ball_self B.hρ
  · exact hcdInf.comp_continuousLinearMap hsMk
  · intro u hu
    exact (H.hmem (hsMk u) hu).1.1
  · show h₀ (hsMk (tailVec p)) = 0
    rw [hsMk_tailVec]
    exact H.hzero
  · refine eventually_nhdsWithin_iff.mpr ?_
    have hball : ∀ᶠ z in 𝓝 p, hsMk z ∈ Metric.ball (hsMk S.p) ρ :=
      (hsMk.continuous.continuousAt (x := p)).preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self B.hρ))
    have hlt : ∀ᶠ z : EuclideanSpace ℝ (Fin n) in 𝓝 p, z.ofLp 0 < δ := by
      have hcont : ContinuousAt (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp 0) p := by
        simpa only [PiLp.proj_apply] using
          (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) 0).continuousAt
      exact hcont.eventually (Iio_mem_nhds (by simpa [hp0] using B.hδ))
    filter_upwards [hball, hlt] with z hz hzlt hzH
    have hz0 : 0 ≤ z.ofLp 0 := by
      rw [range_modelWithCornersEuclideanHalfSpace, Set.mem_ofPred_eq] at hzH
      exact hzH
    have hzIcc : z.ofLp 0 ∈ Set.Icc 0 δ := ⟨hz0, le_of_lt hzlt⟩
    have hzeq : Ψ z = S.F (hsMk z, z.ofLp 0) := by
      rw [S.F_apply, hsConn_mk]
    rw [hzeq, H.hchar (hsMk z) hz (z.ofLp 0) hzIcc]
    simp only [hsMk_tailVec]


end

end Work.PTGeometric.WeakRegion
