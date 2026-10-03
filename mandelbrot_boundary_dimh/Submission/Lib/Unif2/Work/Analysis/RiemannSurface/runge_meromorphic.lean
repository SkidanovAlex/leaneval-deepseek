import Mathlib
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.runge_interface
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.DivisorBasics
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall
import Submission.Lib.Unif2.HolomorphicLog

/-!
# The divisor theorem from the meromorphic Behnke--Stein (Runge) approximation input

`Work.Analysis.RiemannSurface.single_simple_zero_at` asks for a holomorphic function on a
non-compact connected Riemann surface whose zero set is exactly one prescribed point, the zero being
simple.  In the Mittag--Leffler formulation (`DivisorBasics.lean`) it is the datum

`h` holomorphic and nowhere zero on `X ∖ {x₀}`, with `h ∘ c.symm =ᶠ (w - w₀)⁻¹ + (analytic)`
at `x₀` (`c = chartAt ℂ x₀`, `w₀ = c x₀`),

and `singleSimpleZero_of_poleData` turns that datum into the target.

This file isolates **the one approximation input** the divisor chapter needs, in the form in which
the classical theory (Behnke--Stein 1948; Forster, *Lectures on Riemann Surfaces*, ch. 26--30)
delivers it, and proves that the target follows from it by a *single* application, with no
induction, no limit and no convergence argument:

* the input is `MeromorphicRunge x₀` below: a function `u` that is holomorphic and **zero-free** on
  an open set `W` and has a simple pole of the model shape at `x₀ ∈ W` is uniformly approximable on
  a compact `D ⊆ W` (with the Runge hole condition of `runge_interface.lean`) by a function `U` that
  is holomorphic and **zero-free** on a larger open set `E`, again with the same simple pole;
* the target is then `MeromorphicRunge x₀` applied with `E := Set.univ` and `u` the *chart model*
  `y ↦ (c y - w₀)⁻¹` (holomorphic and zero-free on a chart ball, with principal part exactly
  `(w - w₀)⁻¹`), and `D` a smaller closed chart ball.  The hole condition for that pair is
  `notRelCompactComponents_univ_chartClosedBall`: `X ∖ D` is preconnected (a closed chart disc does
  not disconnect a surface, `Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall`), so a
  compact `K` containing it would give `X = D ∪ K` compact, contradicting `¬ CompactSpace X`.

## Why *this* form of the input (and not the holomorphic `RungePairApproximation`)

Three obstructions, each of which cost an earlier session, are dodged by this formulation; they are
recorded in `NOTES_divisor_chapter_plan.md` §22 and §24.

1. **The approximant must be allowed to keep the pole.**  The datum `u` has a pole at `x₀`, so it is
   *not* holomorphic on any neighbourhood of a compact set containing `x₀`; a purely holomorphic
   approximation theorem can therefore only be applied to compacta avoiding `x₀`.  Since the datum
   is only defined *locally* (`p = (c · - w₀)⁻¹` is not a global function), the "correction"
   `h_n - p` that a Mittag--Leffler induction would feed to the holomorphic interface is not even a
   function on a neighbourhood of `x₀`.  Carrying the pole in the approximating class removes this
   difficulty completely.
2. **Zero-freeness must be preserved.**  The target's datum needs `h ≠ 0` off `x₀`; approximating by
   *arbitrary* holomorphic or meromorphic functions does not preserve that, and the "Rouché /
   maximum principle" repair fails on an exhaustion because each step only controls the error on a
   *smaller* piece than the one where zero-freeness is known (one step of deficit, which never
   closes).  Requiring the approximant to be zero-free by hypothesis removes the whole issue.
3. **The `X ∖ {x₀}` splitting is impossible.**  Applying the holomorphic interface to a datum that is
   `p` near `x₀` and `c` far away fails deterministically: the functional
   `(dz on a middle circle) - (dz on an inner circle)` annihilates `O(X ∖ {x₀})` and pairs with the
   piecewise datum to `2πi (a₋₁(c) - 1)` (plane model, `NOTES_…` §22.5).  The input below never
   splits `D`, so the obstruction does not arise.
-/

open Set Metric
open scoped Topology Manifold

set_option linter.unusedSectionVars false

noncomputable section

open Filter Classical

namespace Work.Analysis.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The meromorphic (zero-free preserving) Behnke--Stein approximation input.**

`D` is compact with `D ⊆ W ⊆ E`, `x₀ ∈ D` (so the pole is inside the compact set), and `u` is
holomorphic and zero-free on `W ∖ {x₀}` with a simple pole of the model shape at `x₀` (in the
preferred chart at `x₀`).  The conclusion is `U`, holomorphic and zero-free on `E ∖ {x₀}`, with the
*same* principal part at `x₀`, and uniformly within `ε` of `u` on `D` (away from `x₀`; the
difference is holomorphic at `x₀` because the principal parts agree, so the estimate is meaningful
there as well).

The side condition is the Runge hole condition on the pair `(D, E)`, `NotRelCompactComponents E D`.

This is the statement whose classical proof is the Behnke--Stein approximation theory for
meromorphic functions on a non-compact Riemann surface; it is *stronger* than the target (which is
the special case `E = univ` without the approximation requirement). -/
def MeromorphicRunge (x₀ : X) : Prop :=
  ∀ (D E W : Set X) (u : X → ℂ),
    IsCompact D → IsOpen E → IsOpen W → x₀ ∈ D → D ⊆ W → W ⊆ E →
    NotRelCompactComponents E D →
    (∀ x ∈ W, x ≠ x₀ → Submission.HolomorphicOnXAt u x) →
    (∀ x ∈ W, x ≠ x₀ → u x ≠ 0) →
    (∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧
      (u ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀)⁻¹ + H w)) →
    ∀ ε : ℝ, 0 < ε →
      ∃ U : X → ℂ,
        (∀ x ∈ E, x ≠ x₀ → Submission.HolomorphicOnXAt U x) ∧
        (∀ x ∈ E, x ≠ x₀ → U x ≠ 0) ∧
        (∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧
          (U ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
            (fun w : ℂ => (w - (chartAt ℂ x₀) x₀)⁻¹ + H w)) ∧
        (∀ x ∈ D, x ≠ x₀ → ‖U x - u x‖ < ε)

/-! ## The chart model `y ↦ (c y - w₀)⁻¹` -/

section Model

variable {x₀ : X}

/-- **The chart model is holomorphic away from the pole.** -/
theorem holomorphicOnXAt_chartModel {x : X} (hx : x ∈ (chartAt ℂ x₀).source) (hne : x ≠ x₀) :
    Submission.HolomorphicOnXAt
      (fun y : X => ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀)⁻¹) x := by
  rw [Submission.HolomorphicOnXAt_iff_chart (f := fun y : X =>
      ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀)⁻¹) (x := x) (y := x₀) hx]
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc
  set w₀ : ℂ := c x₀ with hw
  have hxsrc : x ∈ c.source := hx
  have hfac : ((fun y : X => (c y - w₀)⁻¹) ∘ c.symm) =ᶠ[𝓝 (c x)]
      (fun w : ℂ => (w - w₀)⁻¹) := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hxsrc)] with w hwt
    simp only [Function.comp_apply]
    rw [c.right_inv hwt]
  have hne' : c x - w₀ ≠ 0 := by
    rw [sub_ne_zero]
    intro hcon
    exact hne (c.injOn hxsrc (mem_chart_source ℂ x₀) hcon)
  have hana : AnalyticAt ℂ (fun w : ℂ => (w - w₀)⁻¹) (c x) :=
    (analyticAt_id.sub analyticAt_const).inv (by simpa using hne')
  exact hana.congr hfac.symm

/-- **The chart model is zero-free away from the pole.** -/
theorem chartModel_ne_zero {x : X} (hx : x ∈ (chartAt ℂ x₀).source) (hne : x ≠ x₀) :
    ((chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀)⁻¹ ≠ 0 :=
  inv_ne_zero fun h0 =>
    hne ((chartAt ℂ x₀).injOn hx (mem_chart_source ℂ x₀) (sub_eq_zero.mp h0))

/-- **The chart model has principal part exactly `(w - w₀)⁻¹` at `x₀`.** -/
theorem chartModel_poleData (x₀ : X) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧
      ((fun y : X => ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀)⁻¹) ∘ (chartAt ℂ x₀).symm)
        =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀)⁻¹ + H w) := by
  refine ⟨0, analyticAt_const, ?_⟩
  filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds
    ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))] with w hwt
  simp only [Function.comp_apply, Pi.zero_apply, (chartAt ℂ x₀).right_inv hwt, add_zero]

end Model

/-- **The Runge hole condition for a closed chart disc.**  If `D` is a closed chart disc of a
connected Riemann surface that is not compact, then no component of `X ∖ D` is contained in a
compact subset of `X`: `X ∖ D` is preconnected (a closed disc does not disconnect a surface), and a
compact set containing it would make `X = D ∪ K` compact. -/
theorem notRelCompactComponents_univ_chartClosedBall (hX : ¬ CompactSpace X)
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {s : ℝ}
    (hsub : Metric.closedBall a s ⊆ c.target) :
    NotRelCompactComponents (univ : Set X) (Submission.chartClosedBall c a s) := by
  intro x hx
  rintro ⟨K, hKc, _hKE, hKsub⟩
  have hpre : IsPreconnected (univ \ Submission.chartClosedBall c a s) :=
    Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall (Ω := univ) isOpen_univ
      isPreconnected_univ hsub (subset_univ _)
  have hcomp : connectedComponentIn (univ \ Submission.chartClosedBall c a s) x
      = univ \ Submission.chartClosedBall c a s :=
    hpre.connectedComponentIn hx
  have hXsub : (univ : Set X) ⊆ Submission.chartClosedBall c a s ∪ K := by
    intro y _
    by_cases hy : y ∈ Submission.chartClosedBall c a s
    · exact Or.inl hy
    · refine Or.inr (hKsub ?_)
      rw [hcomp]
      exact ⟨mem_univ y, hy⟩
  have hcompK : IsCompact (Submission.chartClosedBall c a s ∪ K) :=
    (Submission.isCompact_chartClosedBall hsub).union hKc
  exact hX (isCompact_univ_iff.mp (hcompK.of_isClosed_subset isClosed_univ hXsub))

/-! ## The target from the input -/

/-- **The divisor theorem from the meromorphic Runge input.**  For a non-compact connected Riemann
surface, `MeromorphicRunge x₀` (the Behnke--Stein approximation theorem for meromorphic functions
with a simple pole at `x₀`, preserving zero-freeness) implies the existence of a holomorphic function
on `X` whose zero set is exactly `{x₀}`, simply — the statement
`Work.Analysis.RiemannSurface.single_simple_zero_at`.

The proof is a *single* application of the input with `E := univ`: the datum is the chart model
`y ↦ (c y - w₀)⁻¹`, holomorphic and zero-free on a chart ball and with principal part exactly
`(w - w₀)⁻¹`, and `D` is a smaller closed chart ball, over which the Runge hole condition holds
because `X ∖ D` is preconnected and `X` is not compact. -/
theorem exists_singleZero_of_meromorphicRunge (x₀ : X) (hX : ¬ CompactSpace X)
    (h : MeromorphicRunge (X := X) x₀) :
    ∃ g : X → ℂ, Submission.HolomorphicOnX g Set.univ ∧ (∀ z : X, z ≠ x₀ → g z ≠ 0) ∧
      Submission.HasLogPoleAt x₀ g := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc
  set w₀ : ℂ := c x₀ with hw
  have hwmem : w₀ ∈ c.target := by
    rw [hw]; exact c.map_source (mem_chart_source ℂ x₀)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hwmem)
  have hsub' : Metric.closedBall w₀ (ρ/2) ⊆ c.target :=
    (Metric.closedBall_subset_ball (by linarith : ρ/2 < ρ)).trans hρsub
  have hWopen : IsOpen (Submission.chartBall c w₀ ρ) :=
    ContinuousOn.isOpen_inter_preimage c.continuousOn c.open_source Metric.isOpen_ball
  have hx₀D : x₀ ∈ Submission.chartClosedBall c w₀ (ρ/2) := by
    rw [Submission.mem_chartClosedBall]
    exact ⟨mem_chart_source ℂ x₀, by
      rw [hw]; exact Metric.mem_closedBall_self (by linarith)⟩
  have hDW : Submission.chartClosedBall c w₀ (ρ/2) ⊆ Submission.chartBall c w₀ ρ := by
    intro y hy
    rw [Submission.mem_chartClosedBall] at hy
    rw [Submission.mem_chartBall]
    exact ⟨hy.1, Metric.closedBall_subset_ball (by linarith) hy.2⟩
  have hhole : NotRelCompactComponents (univ : Set X) (Submission.chartClosedBall c w₀ (ρ/2)) :=
    notRelCompactComponents_univ_chartClosedBall hX hsub'
  have hhol : ∀ x ∈ Submission.chartBall c w₀ ρ, x ≠ x₀ →
      Submission.HolomorphicOnXAt (fun y : X => (c y - w₀)⁻¹) x := by
    intro x hxW hne
    rw [Submission.mem_chartBall] at hxW
    have hsrc : x ∈ (chartAt ℂ x₀).source := by rw [← hc]; exact hxW.1
    simpa only [hc, hw] using holomorphicOnXAt_chartModel (x₀ := x₀) (x := x) hsrc hne
  have hne_u : ∀ x ∈ Submission.chartBall c w₀ ρ, x ≠ x₀ →
      (fun y : X => (c y - w₀)⁻¹) x ≠ 0 := by
    intro x hxW hne
    rw [Submission.mem_chartBall] at hxW
    have hsrc : x ∈ (chartAt ℂ x₀).source := by rw [← hc]; exact hxW.1
    simpa only [hc, hw] using chartModel_ne_zero (x₀ := x₀) (x := x) hsrc hne
  have hpole : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧
      ((fun y : X => (c y - w₀)⁻¹) ∘ (chartAt ℂ x₀).symm)
        =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀)⁻¹ + H w) := by
    simpa only [hc, hw] using chartModel_poleData x₀
  obtain ⟨U, hres⟩ :=
    h (Submission.chartClosedBall c w₀ (ρ/2)) univ (Submission.chartBall c w₀ ρ)
      (fun y : X => (c y - w₀)⁻¹)
      (Submission.isCompact_chartClosedBall hsub') isOpen_univ hWopen hx₀D hDW (subset_univ _)
      hhole hhol hne_u hpole 1 (by norm_num)
  have hUhol : Submission.HolomorphicOnX U (univ \ {x₀}) :=
    fun x hx => hres.1 x hx.1 hx.2
  have hUne : ∀ z : X, z ≠ x₀ → U z ≠ 0 := fun z hz => hres.2.1 z (mem_univ z) hz
  obtain ⟨H, hHana, hHeq⟩ := hres.2.2.1
  exact singleSimpleZero_of_poleData hUhol hUne hHana hHeq

/-! ## The multiplicative step: units from logarithms -/

/-- **Multiplicative approximation from a logarithm.**  If `g` is holomorphic on `W ⊇ D` and
`exp ∘ g` is bounded by `C` on the compact `D`, then `exp ∘ g` is uniformly approximable on `D` by
**zero-free** holomorphic functions on `E`: take the Runge approximant `F` of `g` (`hR`) and
exponentiate it.  Zero-freeness is preserved because an exponential never vanishes, and the error is
controlled by `‖exp a - exp b‖ = ‖exp b‖·‖exp (a - b) - 1‖ ≤ ‖exp b‖·2‖a - b‖` for
`‖a - b‖ ≤ 1`.

This is the elementary half of the multiplicative Behnke--Stein input `MeromorphicRunge`: it shows
that on the pieces where the datum has a *single-valued logarithm* (`g`), the zero-free
approximation is a formal consequence of the holomorphic Runge interface
`RungePairApproximation`. -/
theorem unit_approx_of_log (hR : RungePairApproximation (X := X))
    {D E W : Set X} (hD : IsCompact D) (hE : IsOpen E) (hW : IsOpen W) (hDW : D ⊆ W)
    (hWE : W ⊆ E) (hhole : NotRelCompactComponents E D)
    {g : X → ℂ} (hg : ∀ x ∈ W, Submission.HolomorphicOnXAt g x)
    (hbdd : ∃ C : ℝ, ∀ x ∈ D, ‖Complex.exp (g x)‖ ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : X → ℂ, (∀ x ∈ E, Submission.HolomorphicOnXAt U x) ∧ (∀ x ∈ E, U x ≠ 0) ∧
      (∀ x ∈ D, ‖U x - Complex.exp (g x)‖ < ε) := by
  classical
  obtain ⟨C, hC⟩ := hbdd
  have hCpos : (0 : ℝ) < |C| + 1 := by positivity
  set δ : ℝ := min 1 (ε / (4 * (|C| + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / (4 * (|C| + 1)) := min_le_right _ _
  obtain ⟨F, hFhol, hFapp⟩ :=
    hR D E W hD hE hW hDW hWE hhole g hg δ hδpos
  refine ⟨fun x => Complex.exp (F x), ?_, ?_, ?_⟩
  · intro x hx
    exact (hFhol x hx).cexp
  · intro x hx
    exact Complex.exp_ne_zero (F x)
  · intro x hx
    have h1 : ‖F x - g x‖ < δ := hFapp x hx
    have hEq : Complex.exp (F x) - Complex.exp (g x)
        = Complex.exp (g x) * (Complex.exp (F x - g x) - 1) := by
      have hsum : Complex.exp (F x)
          = Complex.exp (g x) * Complex.exp (F x - g x) := by
        rw [← Complex.exp_add, show g x + (F x - g x) = F x by ring]
      rw [hsum]; ring
    rw [hEq, norm_mul]
    have h3 : ‖Complex.exp (F x - g x) - 1‖ ≤ 2 * ‖F x - g x‖ :=
      Complex.norm_exp_sub_one_le (by linarith : ‖F x - g x‖ ≤ 1)
    have h4 : ‖Complex.exp (g x)‖ ≤ |C| + 1 := by
      have := hC x hx
      linarith [le_abs_self C]
    have h5 : ‖Complex.exp (g x)‖ * ‖Complex.exp (F x - g x) - 1‖ ≤ (|C| + 1) * (2 * δ) := by
      have h3' : ‖Complex.exp (F x - g x) - 1‖ ≤ 2 * δ := by linarith [h3, h1, hδ1]
      exact mul_le_mul h4 h3' (norm_nonneg _) (by positivity)
    have h6 : (|C| + 1) * (2 * δ) ≤ ε / 2 := by
      have h2 : (|C| + 1) * (2 * δ) ≤ (|C| + 1) * (2 * (ε / (4 * (|C| + 1)))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h3' : (|C| + 1) * (2 * (ε / (4 * (|C| + 1)))) = ε / 2 := by
        field_simp; ring
      linarith [h2, h3'.le, h3'.ge]
    linarith [h5, h6]

/-! ## The weighted (first-order) approximation at the pole -/

/-- **Weighted approximation with an exact zero at `x₀`.**  If `g` is holomorphic on `W ∋ x₀`,
`g x₀ = 0`, and the whole configuration lies in the chart at `x₀`, then `g` can be approximated on
the compact `D` by a holomorphic function `G` on `E` which vanishes *exactly* at `x₀`, with the error
weighted by the chart distance to `x₀`.

The construction: the quotient `g / (c · - w₀)` extends holomorphically to `W` (removable
singularity at `x₀`, the only place where the vanishing of `g` is used), the Runge interface `hR`
approximates that quotient on `D` by a function `F` holomorphic on `E`, and `G := (c · - w₀) · F`.
The weight is exactly `‖c · - w₀‖`, so the estimate is immediate and no maximum-principle argument is
needed.  This is the tool that makes the *principal part match exactly* in pole-carrying
constructions. -/
theorem weighted_approx_of_chart_model (hR : RungePairApproximation (X := X)) (x₀ : X)
    {D E W : Set X} (hD : IsCompact D) (hE : IsOpen E) (hW : IsOpen W)
    (hx₀D : x₀ ∈ D) (hDW : D ⊆ W) (hWE : W ⊆ E)
    (hDsrc : D ⊆ (chartAt ℂ x₀).source) (hWsrc : W ⊆ (chartAt ℂ x₀).source)
    (hEsrc : E ⊆ (chartAt ℂ x₀).source)
    (hhole : NotRelCompactComponents E D)
    {g : X → ℂ} (hg : ∀ x ∈ W, Submission.HolomorphicOnXAt g x) (hg0 : g x₀ = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ G : X → ℂ, (∀ x ∈ E, Submission.HolomorphicOnXAt G x) ∧ G x₀ = 0 ∧
      ∀ x ∈ D, x ≠ x₀ →
        ‖G x - g x‖ < ε * ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc
  set w₀ : ℂ := c x₀ with hw
  have hx₀src : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hx₀W : x₀ ∈ W := hDW hx₀D
  -- (1) the coordinate `c · - w₀` is holomorphic on the chart source
  have hcoord : ∀ x ∈ c.source, Submission.HolomorphicOnXAt (fun y : X => c y - w₀) x := by
    intro x hx
    rw [Submission.HolomorphicOnXAt_iff_chart (f := fun y : X => c y - w₀) (x := x) (y := x₀) hx]
    have hev : ((fun y : X => c y - w₀) ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) x)]
        (fun v : ℂ => v - w₀) := by
      filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with v hv
      simp only [Function.comp_apply]
      rw [c.right_inv hv]
    exact ((analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := w₀)
      (x := (chartAt ℂ x₀) x))).congr (by filter_upwards with v; rfl)).congr hev.symm
  have hne : ∀ x ∈ c.source, x ≠ x₀ → c x - w₀ ≠ 0 := by
    intro x hx hxne hcon
    exact hxne (c.injOn hx hx₀src (sub_eq_zero.mp hcon))
  -- (2) the removable-singularity factorization of `g` at the pole
  have hgz : AnalyticAt ℂ (g ∘ c.symm) w₀ := by
    have h1 : Submission.HolomorphicOnXAt g x₀ := hg x₀ hx₀W
    rw [Submission.HolomorphicOnXAt] at h1
    simpa only [hc, hw] using h1
  have hgz0 : (g ∘ c.symm) w₀ = 0 := by
    simp only [Function.comp_apply]
    rw [c.left_inv hx₀src, hg0]
  obtain ⟨F₀, hF₀ana, hF₀eq⟩ : ∃ F₀ : ℂ → ℂ, AnalyticAt ℂ F₀ w₀ ∧
      (g ∘ c.symm) =ᶠ[𝓝 w₀] (fun w : ℂ => (w - w₀) * F₀ w) := by
    have hgzshift : AnalyticAt ℂ (fun v : ℂ => (g ∘ c.symm) (w₀ + v)) 0 := by
      have hgz' : AnalyticAt ℂ (g ∘ c.symm) (w₀ + 0) := by simpa using hgz
      have hinner : AnalyticAt ℂ (fun v : ℂ => w₀ + v) 0 :=
        ((analyticAt_const (𝕜 := ℂ) (v := w₀) (x := (0 : ℂ))).add
          (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ)))).congr (by filter_upwards with v; rfl)
      exact (hgz'.comp (f := fun v : ℂ => w₀ + v) hinner).congr (by
        filter_upwards with v
        simp only [Function.comp_apply])
    obtain ⟨F, hFana, hFeq⟩ := hgzshift.exists_eventuallyEq_sum_add_pow_mul 1
    refine ⟨fun w : ℂ => F (w - w₀), ?_, ?_⟩
    · have hFana' : AnalyticAt ℂ F (w₀ - w₀) := by simpa using hFana
      have hinner : AnalyticAt ℂ (fun w : ℂ => w - w₀) w₀ :=
        (analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := w₀) (x := w₀))).congr
          (by filter_upwards with w; rfl)
      exact (hFana'.comp (f := fun w : ℂ => w - w₀) hinner).congr (by
        filter_upwards with w
        simp only [Function.comp_apply])
    · have htend : Filter.Tendsto (fun w : ℂ => w - w₀) (𝓝 w₀) (𝓝 (0 : ℂ)) := by
        have hh : Filter.Tendsto (fun w : ℂ => w - w₀) (𝓝 w₀) (𝓝 (w₀ - w₀)) :=
          tendsto_id.sub_const w₀
        simpa using hh
      filter_upwards [htend.eventually hFeq] with w hw'
      have hsum0 : (∑ i ∈ Finset.range 1, ((w - w₀) ^ i / ((i.factorial : ℕ) : ℂ)) •
          iteratedDeriv i (fun v : ℂ => (g ∘ c.symm) (w₀ + v)) 0) = 0 := by
        rw [Finset.sum_range_one, iteratedDeriv_zero]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul,
          add_zero, Function.comp_apply]
        exact hgz0
      rw [hsum0, zero_add] at hw'
      have hpow : (w - w₀) ^ 1 • F (w - w₀) = (w - w₀) * F (w - w₀) := by simp
      rw [hpow] at hw'
      rwa [show w₀ + (w - w₀) = w from by ring] at hw'
  -- (3) the quotient, with the removable singularity filled in
  set q : X → ℂ := fun y : X => if y = x₀ then F₀ w₀ else g y * (c y - w₀)⁻¹ with hq
  have hq_hol : ∀ x ∈ W, Submission.HolomorphicOnXAt q x := by
    intro x hxW
    rcases eq_or_ne x x₀ with hxx | hxx
    · -- at the pole: `q ∘ c.symm =ᶠ F₀` near `w₀`
      have hq_at : Submission.HolomorphicOnXAt q x₀ := by
        rw [Submission.HolomorphicOnXAt_iff_chart (f := q) (x := x₀) (y := x₀) hx₀src]
        have hev : (q ∘ c.symm) =ᶠ[𝓝 w₀] F₀ := by
          filter_upwards [c.open_target.mem_nhds (c.map_source hx₀src), hF₀eq] with w hwt hwF
          rw [Function.comp_apply]
          by_cases hwne : w = w₀
          · subst hwne
            have hsymm : c.symm w₀ = x₀ := by rw [hw]; exact c.left_inv hx₀src
            simp only [hq, if_pos hsymm]
          · have hsymm : c.symm w ≠ x₀ := by
              intro hcon
              have hw' : w = c x₀ := by rw [← c.right_inv hwt, hcon]
              exact hwne (hw'.trans hw.symm)
            have hcv : c (c.symm w) = w := c.right_inv hwt
            have hgval : g (c.symm w) = (w - w₀) * F₀ w := by
              simpa only [Function.comp_apply] using hwF
            simp only [hq, hcv, hgval, if_neg hsymm]
            rw [mul_comm ((w - w₀) * F₀ w) ((w - w₀)⁻¹), ← mul_assoc,
              inv_mul_cancel₀ (by rw [sub_ne_zero]; exact hwne), one_mul]
        exact (hF₀ana.congr hev.symm)
      rw [hxx]
      exact hq_at
    · -- off the pole: the product of `g` and the model reciprocal
      have hxc : x ∈ (chartAt ℂ x₀).source := hWsrc hxW
      rw [Submission.HolomorphicOnXAt_iff_chart (f := q) (x := x) (y := x₀) hxc]
      have hg' : AnalyticAt ℂ (g ∘ c.symm) (c x) := by
        have h1 : Submission.HolomorphicOnXAt g x := hg x hxW
        rwa [Submission.HolomorphicOnXAt_iff_chart (f := g) (x := x) (y := x₀) hxc] at h1
      have hinv : AnalyticAt ℂ (fun v : ℂ => (v - w₀)⁻¹) (c x) := by
        refine (analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := w₀) (x := c x))).inv ?_
        have hh := hne x hxc hxx
        simpa only [Pi.sub_apply, id_eq] using hh
      have hev : (q ∘ c.symm) =ᶠ[𝓝 (c x)]
          ((g ∘ c.symm) * fun v : ℂ => (v - w₀)⁻¹) := by
        have hnhds : ∀ᶠ v in 𝓝 (c x), c.symm v ≠ x₀ := by
          have hcont : Filter.Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
            have hh := (c.continuousAt_symm (c.map_source hxc)).tendsto
            rwa [c.left_inv hxc] at hh
          filter_upwards [hcont.eventually (eventually_ne_nhds hxx)] with v hv
          exact hv
        filter_upwards [c.open_target.mem_nhds (c.map_source hxc), hnhds] with v hvt hvx
        have hcv : c (c.symm v) = v := c.right_inv hvt
        simp only [Function.comp_apply, hq, if_neg hvx, hcv, Pi.mul_apply]
      exact (hg'.mul hinv).congr hev.symm
  obtain ⟨F, hFhol, hFapp⟩ := hR D E W hD hE hW hDW hWE hhole q hq_hol ε hε
  refine ⟨fun y : X => (c y - w₀) * F y, ?_, ?_, ?_⟩
  · intro x hx
    exact (hcoord x (hEsrc hx)).mul (hFhol x hx)
  · have h0 : c x₀ - w₀ = 0 := by rw [hw]; ring
    simp [h0]
  · intro x hx hxne
    have hxc : x ∈ c.source := hDsrc hx
    have hqval : q x = g x * (c x - w₀)⁻¹ := by
      simp only [hq]
      rw [if_neg hxne]
    have hval : (c x - w₀) * q x = g x := by
      rw [hqval, mul_comm (c x - w₀) (g x * (c x - w₀)⁻¹), mul_assoc,
        inv_mul_cancel₀ (hne x hxc hxne), mul_one]
    have happ := hFapp x hx
    calc ‖(c x - w₀) * F x - g x‖
        = ‖(c x - w₀) * (F x - q x)‖ := by rw [← hval]; ring_nf
      _ = ‖c x - w₀‖ * ‖F x - q x‖ := norm_mul _ _
      _ < ‖c x - w₀‖ * ε := by
          refine mul_lt_mul_of_pos_left happ ?_
          rw [norm_pos_iff]
          exact hne x hxc hxne
      _ = ε * ‖c x - w₀‖ := by ring

/-! ## The chart-local case of the input, for data with a single-valued logarithm -/

/-- **First-order Taylor expansion of an analytic function** (`ℂ`-version, at an arbitrary point). -/
theorem exists_taylor_one {G : ℂ → ℂ} {w₀ : ℂ} (hG : AnalyticAt ℂ G w₀) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F w₀ ∧
      G =ᶠ[𝓝 w₀] (fun w : ℂ => G w₀ + (w - w₀) * F w) := by
  have hshift : AnalyticAt ℂ (fun v : ℂ => G (w₀ + v)) 0 := by
    have hG' : AnalyticAt ℂ G (w₀ + 0) := by simpa using hG
    have hinner : AnalyticAt ℂ (fun v : ℂ => w₀ + v) 0 :=
      ((analyticAt_const (𝕜 := ℂ) (v := w₀) (x := (0 : ℂ))).add
        (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ)))).congr (by filter_upwards with v; rfl)
    exact (hG'.comp (f := fun v : ℂ => w₀ + v) hinner).congr (by
      filter_upwards with v; simp only [Function.comp_apply])
  obtain ⟨F, hFana, hFeq⟩ := hshift.exists_eventuallyEq_sum_add_pow_mul 1
  refine ⟨fun w : ℂ => F (w - w₀), ?_, ?_⟩
  · have hFana' : AnalyticAt ℂ F (w₀ - w₀) := by simpa using hFana
    have hinner : AnalyticAt ℂ (fun w : ℂ => w - w₀) w₀ :=
      (analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := w₀) (x := w₀))).congr
        (by filter_upwards with w; rfl)
    exact (hFana'.comp (f := fun w : ℂ => w - w₀) hinner).congr (by
      filter_upwards with w; simp only [Function.comp_apply])
  · have htend : Filter.Tendsto (fun w : ℂ => w - w₀) (𝓝 w₀) (𝓝 (0 : ℂ)) := by
      have hh : Filter.Tendsto (fun w : ℂ => w - w₀) (𝓝 w₀) (𝓝 (w₀ - w₀)) :=
        tendsto_id.sub_const w₀
      simpa using hh
    filter_upwards [htend.eventually hFeq] with w hw'
    have hsum0 : (∑ i ∈ Finset.range 1, ((w - w₀) ^ i / ((i.factorial : ℕ) : ℂ)) •
        iteratedDeriv i (fun v : ℂ => G (w₀ + v)) 0) = G w₀ := by
      rw [Finset.sum_range_one, iteratedDeriv_zero]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul,
        add_zero, Function.comp_apply]
    rw [hsum0] at hw'
    have hpow : (w - w₀) ^ 1 • F (w - w₀) = (w - w₀) * F (w - w₀) := by simp
    rw [hpow] at hw'
    rwa [show w₀ + (w - w₀) = w from by ring] at hw'

/-- **The chart-local case of the multiplicative Behnke--Stein input, for a datum presented by a
single-valued logarithm.**  If `θ` is holomorphic on `W ∋ x₀` with `θ x₀ = 0`, the chart distance is
bounded on `D` by `M`, and the whole configuration lies in the chart at `x₀`, then the zero-free
datum `u = (c · - c x₀)⁻¹ · exp ∘ θ` is uniformly approximable on `D` by a zero-free function `U` on
`E` with the *same model principal part* `(c · - c x₀)⁻¹`.

Proof: `weighted_approx_of_chart_model` gives `Θ ∈ O(E)` with `Θ x₀ = 0` exactly and
`‖Θ x - θ x‖ < δ‖c x - c x₀‖`; choose `δ` also below `1/M`, so that `‖Θ x - θ x‖ ≤ 1` on `D` and the
elementary bound `‖e^a - e^b‖ ≤ 2‖e^b‖‖a - b‖` applies.  Then set
`U := (c · - c x₀)⁻¹ · exp ∘ Θ`: the estimate on `D∖{x₀}` is
`‖(c·-c x₀)⁻¹‖ · 2C‖Θ - θ‖ ≤ 2Cδ` (the weight cancels), and the principal part matches because
`exp ∘ Θ = 1 + (c·-c x₀)·(analytic)` at `x₀` (`exists_taylor_one`). -/
theorem meromorphicRunge_chart_of_log (hR : RungePairApproximation (X := X)) (x₀ : X)
    {D E W : Set X} (hD : IsCompact D) (hE : IsOpen E) (hW : IsOpen W) (hx₀D : x₀ ∈ D)
    (hDW : D ⊆ W) (hWE : W ⊆ E)
    (hDsrc : D ⊆ (chartAt ℂ x₀).source) (hWsrc : W ⊆ (chartAt ℂ x₀).source)
    (hEsrc : E ⊆ (chartAt ℂ x₀).source)
    (hhole : NotRelCompactComponents E D)
    {θ : X → ℂ} (hθ : ∀ x ∈ W, Submission.HolomorphicOnXAt θ x) (hθ0 : θ x₀ = 0)
    (hbdd : ∃ C : ℝ, ∀ x ∈ D, ‖Complex.exp (θ x)‖ ≤ C)
    (hMd : ∃ M : ℝ, ∀ x ∈ D, ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : X → ℂ,
      (∀ x ∈ E, x ≠ x₀ → Submission.HolomorphicOnXAt U x) ∧
      (∀ x ∈ E, x ≠ x₀ → U x ≠ 0) ∧
      (∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧
        (U ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
          (fun w : ℂ => (w - (chartAt ℂ x₀) x₀)⁻¹ + H w)) ∧
      (∀ x ∈ D, x ≠ x₀ →
        ‖U x - ((chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀)⁻¹ * Complex.exp (θ x)‖ < ε) := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc
  set w₀ : ℂ := c x₀ with hw
  have hx₀src : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hx₀W : x₀ ∈ W := hDW hx₀D
  have hx₀E : x₀ ∈ E := hWE hx₀W
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨M, hM⟩ := hMd
  have hCpos : (0 : ℝ) < |C| + 1 := by positivity
  have hMpos : (0 : ℝ) < |M| + 2 := by positivity
  set δ : ℝ := min (1 / (|M| + 2)) (ε / (4 * (|C| + 1))) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδM : δ ≤ 1 / (|M| + 2) := min_le_left _ _
  have hδε : δ ≤ ε / (4 * (|C| + 1)) := min_le_right _ _
  obtain ⟨Θ, hΘhol, hΘ0, hΘw⟩ :=
    weighted_approx_of_chart_model hR x₀ hD hE hW hx₀D hDW hWE hDsrc hWsrc hEsrc hhole hθ hθ0
      δ hδpos
  -- (2) the first-order Taylor expansion of `exp ∘ (Θ ∘ c.symm)` at `w₀`
  have hGan : AnalyticAt ℂ (Θ ∘ c.symm) w₀ := by
    have h1 : Submission.HolomorphicOnXAt Θ x₀ := hΘhol x₀ hx₀E
    rw [Submission.HolomorphicOnXAt] at h1
    simpa only [hc, hw] using h1
  have hG0 : Θ (c.symm w₀) = 0 := by
    rw [c.left_inv hx₀src, hΘ0]
  obtain ⟨H₀, hH₀ana, hH₀eq⟩ := exists_taylor_one (hGan.cexp)
  have hbar : (fun w : ℂ => Complex.exp (Θ (c.symm w)))
      =ᶠ[𝓝 w₀] (fun w : ℂ => 1 + (w - w₀) * H₀ w) := by
    filter_upwards [hH₀eq] with w hw'
    simp only [Function.comp_apply] at hw'
    rw [hw', hG0, Complex.exp_zero]
  -- (3) the candidate
  set U : X → ℂ := fun y : X => if y = x₀ then H₀ w₀
    else (c y - w₀)⁻¹ * Complex.exp (Θ y) with hU
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro x hx hxne
    have hxsrc : x ∈ (chartAt ℂ x₀).source := hEsrc hx
    have hmodel : Submission.HolomorphicOnXAt (fun y : X => (c y - w₀)⁻¹) x := by
      simpa only [hc, hw] using holomorphicOnXAt_chartModel (x₀ := x₀) (x := x) hxsrc hxne
    have hexp : Submission.HolomorphicOnXAt (fun y : X => Complex.exp (Θ y)) x :=
      (hΘhol x hx).cexp
    have hprod := hmodel.mul hexp
    rw [Submission.HolomorphicOnXAt] at hprod ⊢
    refine hprod.congr ?_
    have hcont : Filter.Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x)) (𝓝 x) := by
      simpa using ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source
        (mem_chart_source ℂ x))).tendsto
    filter_upwards [hcont.eventually (eventually_ne_nhds hxne)] with v hv
    simp only [Function.comp_apply, Pi.mul_apply, hU, if_neg hv]
  · intro x hx hxne
    have hxsrc : x ∈ (chartAt ℂ x₀).source := hEsrc hx
    have hne : c x - w₀ ≠ 0 := by
      intro hcon
      refine hxne ?_
      have : c x = c x₀ := by rw [← hw]; exact sub_eq_zero.mp hcon
      exact c.injOn hxsrc hx₀src this
    simp only [hU, if_neg hxne]
    exact mul_ne_zero (inv_ne_zero hne) (Complex.exp_ne_zero (Θ x))
  · refine ⟨H₀, hH₀ana, ?_⟩
    filter_upwards [c.open_target.mem_nhds (c.map_source hx₀src), hbar] with w hwt hwbar
    have hcv : c (c.symm w) = w := c.right_inv hwt
    by_cases hweq : w = w₀
    · subst hweq
      have hsymm : c.symm w₀ = x₀ := by rw [hw]; exact c.left_inv hx₀src
      have hzero : (w₀ - w₀)⁻¹ + H₀ w₀ = H₀ w₀ := by rw [sub_self, inv_zero, zero_add]
      simp only [Function.comp_apply, hU, if_pos hsymm, hzero]
    · have hsymm : c.symm w ≠ x₀ := by
        intro hcon
        have hw' : w = c x₀ := by rw [← c.right_inv hwt, hcon]
        exact hweq (hw'.trans hw.symm)
      simp only [Function.comp_apply, hU, if_neg hsymm, hcv, hwbar]
      rw [mul_add, mul_one, ← mul_assoc, inv_mul_cancel₀ (by rw [sub_ne_zero]; exact hweq),
        one_mul]
  · intro x hx hxne
    have hxc : x ∈ c.source := hDsrc hx
    have hne : c x - w₀ ≠ 0 := by
      intro hcon
      exact hxne (c.injOn hxc hx₀src (sub_eq_zero.mp hcon))
    have hUval : U x = (c x - w₀)⁻¹ * Complex.exp (Θ x) := by
      simp only [hU, if_neg hxne]
    have h1 : ‖Θ x - θ x‖ < δ * ‖c x - w₀‖ := hΘw x hx hxne
    have hMx : ‖c x - w₀‖ ≤ |M| + 1 := by
      have := hM x hx
      linarith [le_abs_self M]
    have hsmall : ‖Θ x - θ x‖ ≤ 1 := by
      have h2 : δ * ‖c x - w₀‖ ≤ (1 / (|M| + 2)) * (|M| + 1) := by
        refine mul_le_mul hδM hMx (norm_nonneg _) (by positivity)
      have h3 : (1 / (|M| + 2)) * (|M| + 1) ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one (by positivity)]
        linarith [abs_nonneg M]
      linarith [h1, h2, h3]
    have h3 : ‖Complex.exp (Θ x) - Complex.exp (θ x)‖ ≤ 2 * (|C| + 1) * ‖Θ x - θ x‖ := by
      have hfac : Complex.exp (Θ x) - Complex.exp (θ x)
          = Complex.exp (θ x) * (Complex.exp (Θ x - θ x) - 1) := by
        have : Complex.exp (Θ x) = Complex.exp (θ x) * Complex.exp (Θ x - θ x) := by
          rw [← Complex.exp_add, show θ x + (Θ x - θ x) = Θ x by ring]
        rw [this]; ring
      rw [hfac, norm_mul]
      have hexpθ : ‖Complex.exp (θ x)‖ ≤ |C| + 1 := by
        have := hC x hx
        linarith [le_abs_self C]
      calc ‖Complex.exp (θ x)‖ * ‖Complex.exp (Θ x - θ x) - 1‖
          ≤ (|C| + 1) * (2 * ‖Θ x - θ x‖) :=
            mul_le_mul hexpθ (Complex.norm_exp_sub_one_le hsmall) (norm_nonneg _)
              (by positivity)
        _ = 2 * (|C| + 1) * ‖Θ x - θ x‖ := by ring
    calc ‖U x - (c x - w₀)⁻¹ * Complex.exp (θ x)‖
        = ‖(c x - w₀)⁻¹ * (Complex.exp (Θ x) - Complex.exp (θ x))‖ := by
          rw [hUval]; ring_nf
      _ = ‖(c x - w₀)⁻¹‖ * ‖Complex.exp (Θ x) - Complex.exp (θ x)‖ := norm_mul _ _
      _ ≤ ‖(c x - w₀)⁻¹‖ * (2 * (|C| + 1) * ‖Θ x - θ x‖) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ ≤ ‖(c x - w₀)⁻¹‖ * (2 * (|C| + 1) * (δ * ‖c x - w₀‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left h1.le (by positivity)
      _ = 2 * (|C| + 1) * δ * (‖(c x - w₀)⁻¹‖ * ‖c x - w₀‖) := by ring
      _ = 2 * (|C| + 1) * δ := by
          rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne), mul_one]
      _ ≤ 2 * (|C| + 1) * (ε / (4 * (|C| + 1))) := by
          refine mul_le_mul_of_nonneg_left hδε (by positivity)
      _ = ε / 2 := by
          field_simp
          ring
      _ < ε := by linarith

/-- **The chart distance is bounded on a compact set inside the chart source.** -/
theorem exists_bound_chart_sub (x₀ : X) {D : Set X} (hD : IsCompact D)
    (hDsrc : D ⊆ (chartAt ℂ x₀).source) :
    ∃ M : ℝ, ∀ x ∈ D, ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ ≤ M := by
  have hcont : ContinuousOn (fun x : X => (chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀) D :=
    ((chartAt ℂ x₀).continuousOn.mono hDsrc).sub continuousOn_const
  exact hD.exists_bound_of_continuousOn hcont

/-- **`exp ∘ θ` is bounded on a compact set on which `θ` is holomorphic.** -/
theorem exists_bound_exp_of_holomorphic {θ : X → ℂ} {D W : Set X} (hD : IsCompact D)
    (hDW : D ⊆ W) (hθ : ∀ x ∈ W, Submission.HolomorphicOnXAt θ x) :
    ∃ C : ℝ, ∀ x ∈ D, ‖Complex.exp (θ x)‖ ≤ C := by
  have hcontθ : ContinuousOn θ D :=
    fun x hx => ((hθ x (hDW hx)).continuousAt).continuousWithinAt
  exact hD.exists_bound_of_continuousOn (Complex.continuous_exp.comp_continuousOn hcontθ)

/-- **The chart-local case of the multiplicative input, with the bounds discharged.**  Same
conclusion as `meromorphicRunge_chart_of_log`, with the two numerical bounds obtained from
compactness of `D` and continuity (`exists_bound_exp_of_holomorphic`,
`exists_bound_chart_sub`). -/
theorem meromorphicRunge_chart_of_log' (hR : RungePairApproximation (X := X)) (x₀ : X)
    {D E W : Set X} (hD : IsCompact D) (hE : IsOpen E) (hW : IsOpen W) (hx₀D : x₀ ∈ D)
    (hDW : D ⊆ W) (hWE : W ⊆ E)
    (hDsrc : D ⊆ (chartAt ℂ x₀).source) (hWsrc : W ⊆ (chartAt ℂ x₀).source)
    (hEsrc : E ⊆ (chartAt ℂ x₀).source)
    (hhole : NotRelCompactComponents E D)
    {θ : X → ℂ} (hθ : ∀ x ∈ W, Submission.HolomorphicOnXAt θ x) (hθ0 : θ x₀ = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : X → ℂ,
      (∀ x ∈ E, x ≠ x₀ → Submission.HolomorphicOnXAt U x) ∧
      (∀ x ∈ E, x ≠ x₀ → U x ≠ 0) ∧
      (∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧
        (U ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
          (fun w : ℂ => (w - (chartAt ℂ x₀) x₀)⁻¹ + H w)) ∧
      (∀ x ∈ D, x ≠ x₀ →
        ‖U x - ((chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀)⁻¹ * Complex.exp (θ x)‖ < ε) :=
  meromorphicRunge_chart_of_log hR x₀ hD hE hW hx₀D hDW hWE hDsrc hWsrc hEsrc hhole hθ hθ0
    (exists_bound_exp_of_holomorphic hD hDW hθ) (exists_bound_chart_sub x₀ hD hDsrc) ε hε

end Work.Analysis.RiemannSurface
