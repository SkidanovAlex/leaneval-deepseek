import Submission.SecondVar2
import Submission.JacobiGen
import Submission.JetGap
import Submission.ChartPieces
import Submission.Minimising
import Submission.BonnetMyers2
import Submission.CurveCov
import Submission.Commons.Topology.Order.exists_partition_subordinate_Icc
import Submission.Commons.Topology.Compact.exists_pos_forall_mem_of_isCompact
import Submission.Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Global Bonnet–Myers

If `γ` is a minimising unit-speed geodesic on `[0,L]` of a Riemannian manifold whose sectional
curvature is `≥ 1` (`QuarterPinched cov`), then `L ≤ π`.

The construction follows the plan of `Submission/Roadmap.lean` §17 (see also `Submission.ChartPieces`
and `Submission/JetGap`):

* cover `[0,L]` by chart pieces (`ChartPieces.exists_chart_pieces`), reparametrised to `[0, ℓ k]`;
* on each piece use the *quadratic* family `u t + s η t + (s²/2) ζ t` with `η` the coordinates of the
  test field `sin (π t / L) • Y` (`Y` the parallel unit field orthogonal to `γ'`, glued across the
  pieces by parallel transport) and `ζ = -Γ(η,η)`, so that the intrinsic acceleration of the family
  vanishes and the boundary terms in the second-variation formula drop;
* the junction gaps are `O(s³)` (`JetGap.riemannianEDist_le_cube_of_jet`);
* minimality forces the second derivative of the total energy at `s = 0` to be `≥ 0`, while the
  index-form bound makes it `< 0` as soon as `L > π`.

Main result: `le_pi_of_minimising_geodesic`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.GeodesicSpeed
open Submission.Length
open Submission.Jacobi
open Submission.ChartCurv
open Submission.ChartConnection
open Submission.SecondVariation
open Submission.IndexForm
open Submission.IndexForm2
open Submission.BonnetMyers
open Submission.BonnetMyers2
open Submission.SecondVar2
open Submission.Gauss
open Submission.ChartBounds
open Submission.CurvatureVec
open Submission.Pinch
open Submission.GlobalExp
open Submission.HopfRinow

namespace Submission.GlobalBM

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## Shifting the parameter -/

/-- Derivative of a composition with a translation. -/
lemma hasDerivAt_comp_const_add {f f' : ℝ → E} {c t : ℝ}
    (h : HasDerivAt f (f' (c + t)) (c + t)) :
    HasDerivAt (fun s : ℝ => f (c + s)) (f' (c + t)) t := by
  have hg : HasDerivAt (fun s : ℝ => c + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add c
  have h3 := h.hasFDerivAt.comp t hg.hasFDerivAt
  have h5 := h3.hasDerivAt
  rw [ContinuousLinearMap.comp_apply] at h5
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h5
  simpa only [Function.comp_def] using h5

/-- Derivative of a composition with a translation, `ℝ`-valued. -/
lemma hasDerivAt_comp_const_add' {f f' : ℝ → ℝ} {c t : ℝ}
    (h : HasDerivAt f (f' (c + t)) (c + t)) :
    HasDerivAt (fun s : ℝ => f (c + s)) (f' (c + t)) t :=
  hasDerivAt_comp_const_add (E := ℝ) h

/-! ## The energy integrand of the quadratic family -/

/-- The integrand of the energy of the quadratic family, `⟪∂_tΨ, ∂_tΨ⟫`. -/
def fam2G (x₀ : M) (u η ζ w e ζ' : ℝ → E) (s t : ℝ) : ℝ :=
  chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t) (fam2T w e ζ' s t) (fam2T w e ζ' s t)

lemma fam2Energy_eq_fam2G (x₀ : M) (u η ζ w e ζ' : ℝ → E) (L s : ℝ) :
    fam2Energy (I := I) x₀ u η ζ w e ζ' L s
      = ∫ t in (0 : ℝ)..L, fam2G (I := I) x₀ u η ζ w e ζ' s t := rfl

/-- The `t`-derivative of the quadratic family. -/
lemma hasDerivAt_fam2_t {u η ζ w e ζ' : ℝ → E} {s t : ℝ}
    (hu : HasDerivAt u (w t) t) (hη : HasDerivAt η (e t) t) (hζ : HasDerivAt ζ (ζ' t) t) :
    HasDerivAt (fun r : ℝ => fam2 u η ζ s r) (fam2T w e ζ' s t) t := by
  have h1 : HasDerivAt (fun r : ℝ => s • η r) (s • e t) t := hη.const_smul s
  have h2 : HasDerivAt (fun r : ℝ => (s ^ 2 / 2) • ζ r) ((s ^ 2 / 2) • ζ' t) t :=
    hζ.const_smul (s ^ 2 / 2)
  have h3 : HasDerivAt (fun r : ℝ => u r + s • η r + (s ^ 2 / 2) • ζ r)
      (w t + s • e t + (s ^ 2 / 2) • ζ' t) t := (hu.add h1).add h2
  simpa only [fam2, fam2T] using h3

/-- **The speed of the curve of the quadratic family** is the square root of the energy integrand. -/
lemma curveSpeed_fam2Curve {x₀ : M} {u η ζ w e ζ' : ℝ → E} {s t : ℝ}
    (hu : HasDerivAt u (w t) t) (hη : HasDerivAt η (e t) t) (hζ : HasDerivAt ζ (ζ' t) t)
    (htgt : fam2 u η ζ s t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ r in 𝓝 t, fam2 u η ζ s r ∈ (extChartAt I x₀).target) :
    curveSpeed (I := I) (fam2Curve (I := I) x₀ u η ζ s) t
      = Real.sqrt (fam2G (I := I) x₀ u η ζ w e ζ' s t) :=
  curveSpeed_chartCurve (I := I) (x₀ := x₀) (u := fam2 u η ζ s) (t := t) (v := fam2T w e ζ' s t)
    (hasDerivAt_fam2_t hu hη hζ) htgt hstay

/-- The quadratic family is independent of the chosen `e`, `ζ'` at `s = 0`. -/
lemma fam2T_zero (w e ζ' : ℝ → E) (t : ℝ) : fam2T w e ζ' 0 t = w t := by
  simp only [fam2T, pow_two, zero_mul, zero_div, zero_smul, add_zero]

/-! ## The chart pieces of a minimising geodesic -/

/-! ## Two conversion lemmas -/

/-- **The chart metric only depends on the intrinsic inner product**: the chart coordinates of a
tangent vector are `continuousLinearMapAt`, and the chart metric of those coordinates is the
intrinsic inner product. -/
lemma chartGram_continuousLinearMapAt (x p : M) (hp : p ∈ (chartAt H x).source)
    (X Y : TangentSpace I p) :
    chartGram (I := I) x p
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ p X)
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ p Y) = inner ℝ X Y := by
  have hbase : p ∈ (trivializationAt E (TangentSpace I) x).baseSet := by simpa using hp
  simp only [chartGram_apply, frameVector]
  rw [Trivialization.symmL_continuousLinearMapAt (trivializationAt E (TangentSpace I) x)
      (R := ℝ) hbase X,
    Trivialization.symmL_continuousLinearMapAt (trivializationAt E (TangentSpace I) x)
      (R := ℝ) hbase Y]

lemma mem_extChartAt_source_iff {x p : M} : p ∈ (extChartAt I x).source ↔
    p ∈ (chartAt H x).source := by
  rw [extChartAt_source]

/-- The coordinates of `frameVector x p v` are `v`. -/
lemma continuousLinearMapAt_frameVector (x p : M) (hp : p ∈ (chartAt H x).source) (v : E) :
    (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ p
      (frameVector (I := I) x p v) = v := by
  show (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ p
    ((trivializationAt E (TangentSpace I) x).symmL ℝ p v) = v
  exact Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) (by simpa using hp) v

/-- `frameVector x p` inverts `continuousLinearMapAt`. -/
lemma frameVector_continuousLinearMapAt (x p : M) (hp : p ∈ (chartAt H x).source)
    (X : TangentSpace I p) :
    frameVector (I := I) x p
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ p X) = X := by
  show (trivializationAt E (TangentSpace I) x).symmL ℝ p
    ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ p X) = X
  exact Trivialization.symmL_continuousLinearMapAt _ (R := ℝ) (by simpa using hp) X

/-- The chart coordinate velocity of a curve is the coordinate vector of its velocity. -/
lemma deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (x : M) {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) (hx : γ t ∈ (chartAt H x).source) :
    deriv (fun s => (extChartAt I x) (γ s)) t
      = (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ (γ t)
          (curveVelocity (I := I) γ t) :=
  Submission.CurveField.deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity
    (I := I) hγ hx


/-- The chart coordinate curve of the piece `k`, in the global parameter. -/
def coeffCurve (x : ℕ → M) (γ : ℝ → M) (k : ℕ) : ℝ → E := fun r => (extChartAt I (x k)) (γ r)

/-- The chart coordinate velocity of the piece `k`. -/
def coeffVel (x : ℕ → M) (γ : ℝ → M) (k : ℕ) : ℝ → E := deriv (coeffCurve (I := I) x γ k)

/-! ## The glued parallel field

Parallel transport of a unit vector orthogonal to the velocity, along the geodesic, pieced together
over the chart cover.  The chart pieces are index by `k < N`, the piece `k` being parametrised by
`s ∈ [0, c (k+1) - c k]`.  The field on the piece `k+1` is initialised with the *coordinates*, in the
chart at `x (k+1)`, of the value of the field of the piece `k` at the junction. -/

theorem exists_parallel_system [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hdim : 2 ≤ Module.finrank ℝ E)
    {N : ℕ} (hN : 0 < N) {c : ℕ → ℝ} (hmono : ∀ k < N, c k < c (k + 1))
    {x : ℕ → M} {A B : ℕ → ℝ} {up wp wp' : ℕ → ℝ → E} {q : ℕ → M}
    (hAB : ∀ k < N, A k < c k ∧ c (k + 1) < B k)
    (hIcc : ∀ k < N, Icc (0 : ℝ) (c (k + 1) - c k) ⊆ Ioo (A k - c k) (B k - c k))
    (hup : ∀ k < N, ∀ s ∈ Ioo (A k - c k) (B k - c k), HasDerivAt (up k) (wp k s) s)
    (hwp : ∀ k < N, ∀ s ∈ Ioo (A k - c k) (B k - c k), HasDerivAt (wp k) (wp' k s) s)
    (hwp_chart : ∀ k < N, ∀ s ∈ Ioo (A k - c k) (B k - c k),
      wp' k s = chartGeodesicVectorField cov (x k) (up k s, wp k s))
    (hstage : ∀ k < N, ∀ s ∈ Ioo (A k - c k) (B k - c k),
      up k s ∈ (extChartAt I (x k)).target)
    (hstageIcc : ∀ k < N, ∀ s ∈ Icc (0 : ℝ) (c (k + 1) - c k),
      up k s ∈ (extChartAt I (x k)).target)
    (hunit : ∀ k < N, ∀ s ∈ Icc (0 : ℝ) (c (k + 1) - c k),
      chartGram (I := I) (x k) ((extChartAt I (x k)).symm (up k s)) (wp k s) (wp k s) = 1)
    (hpt0 : ∀ k < N, (extChartAt I (x k)).symm (up k 0) = q k)
    (hpt1 : ∀ k, k + 1 < N →
      (extChartAt I (x k)).symm (up k (c (k + 1) - c k)) = q (k + 1))
    (hmatchvel : ∀ k, k + 1 < N →
      frameVector (I := I) (x k) (q (k + 1)) (wp k (c (k + 1) - c k))
        = frameVector (I := I) (x (k + 1)) (q (k + 1)) (wp (k + 1) 0)) :
    ∃ Y : ℕ → ℝ → E,
      (∀ k < N, ∀ s ∈ Icc (0 : ℝ) (c (k + 1) - c k),
        HasDerivAt (Y k) (-(christoffelLM cov (x k) ((extChartAt I (x k)).symm (up k s))
          (frameVector (I := I) (x k) ((extChartAt I (x k)).symm (up k s)) (wp k s))) (Y k s)) s) ∧
      (∀ k < N, ∀ s ∈ Icc (0 : ℝ) (c (k + 1) - c k),
        chartGram (I := I) (x k) ((extChartAt I (x k)).symm (up k s)) (Y k s) (Y k s) = 1) ∧
      (∀ k < N, ∀ s ∈ Icc (0 : ℝ) (c (k + 1) - c k),
        chartGram (I := I) (x k) ((extChartAt I (x k)).symm (up k s)) (Y k s) (wp k s) = 0) ∧
      (∀ k, k + 1 < N →
        frameVector (I := I) (x k) (q (k + 1)) (Y k (c (k + 1) - c k))
          = frameVector (I := I) (x (k + 1)) (q (k + 1)) (Y (k + 1) 0)) := by
  classical
  let Par : ℕ → (ℝ → E) → Prop := fun k Y => k < N →
    (∀ s ∈ Icc (0 : ℝ) (c (k + 1) - c k),
      HasDerivAt Y (-(christoffelLM cov (x k) ((extChartAt I (x k)).symm (up k s))
        (frameVector (I := I) (x k) ((extChartAt I (x k)).symm (up k s)) (wp k s))) (Y s)) s) ∧
    (∀ s ∈ Icc (0 : ℝ) (c (k + 1) - c k),
      chartGram (I := I) (x k) ((extChartAt I (x k)).symm (up k s)) (Y s) (Y s) = 1) ∧
    (∀ s ∈ Icc (0 : ℝ) (c (k + 1) - c k),
      chartGram (I := I) (x k) ((extChartAt I (x k)).symm (up k s)) (Y s) (wp k s) = 0)
  let Mtch : ℕ → (ℝ → E) → (ℝ → E) → Prop := fun k Y Z =>
    frameVector (I := I) (x k) (q (k + 1)) (Y (c (k + 1) - c k))
      = frameVector (I := I) (x (k + 1)) (q (k + 1)) (Z 0)
  let MtchN : ℕ → (ℝ → E) → (ℝ → E) → Prop := fun k Y Z => k + 1 < N → Mtch k Y Z
  have hllpos : ∀ k < N, 0 < c (k + 1) - c k := fun k hk => by
    have := hmono k hk; linarith
  have hwp' : ∀ k < N, ∀ s ∈ Ioo (A k - c k) (B k - c k),
      HasDerivAt (wp k) (chartGeodesicVectorField cov (x k) (up k s, wp k s)) s := by
    intro k hk s hs
    rw [← hwp_chart k hk s hs]
    exact hwp k hk s hs
  -- the first piece
  have hseed : ∃ Z : ℝ → E, Par 0 Z := by
    have h0 : (0 : ℝ) < c (0 + 1) - c 0 := hllpos 0 hN
    have hwu : chartGram (I := I) (x 0) ((extChartAt I (x 0)).symm (up 0 0)) (wp 0 0) (wp 0 0)
        = 1 := hunit 0 hN 0 ⟨le_refl _, h0.le⟩
    obtain ⟨Z, hZode, hZunit, hZorth⟩ :=
      Submission.JacobiGen.exists_parallel_unit_orthogonal_Ioo (cov := cov) hmet htor hdim
        (x₀ := x 0) (u := up 0) (w := wp 0)
        (A := A 0 - c 0) (B := B 0 - c 0) (a := 0) (b := c (0 + 1) - c 0) (t₀ := 0)
        (hstage 0 hN) (hup 0 hN) (hwp' 0 hN) h0 (hIcc 0 hN) ⟨le_refl _, h0.le⟩ hwu
    exact ⟨Z, fun _ => ⟨hZode, hZunit, hZorth⟩⟩
  -- the transport step
  have hstep : ∀ k, k + 1 < N → ∀ Y : ℝ → E, Par k Y →
      ∃ Z : ℝ → E, Par (k + 1) Z ∧ MtchN k Y Z := by
    intro k hkN Y hY
    have hk : k < N := by omega
    have hpart := hY hk
    have h0 : (0 : ℝ) < c (k + 1 + 1) - c (k + 1) := hllpos (k + 1) hkN
    have hpk : q (k + 1) ∈ (chartAt H (x k)).source := by
      rw [← hpt1 k hkN]; exact mem_source_chartCurve (I := I)
        (hstageIcc k hk (c (k + 1) - c k) ⟨(hllpos k hk).le, le_refl _⟩)
    have hpk' : q (k + 1) ∈ (chartAt H (x (k + 1))).source := by
      rw [← hpt0 (k + 1) hkN]; exact mem_source_chartCurve (I := I)
        (hstageIcc (k + 1) hkN 0 ⟨le_refl _, (hllpos (k + 1) hkN).le⟩)
    have hbase : q (k + 1) ∈ (trivializationAt E (TangentSpace I) (x (k + 1))).baseSet := by
      simpa using hpk'
    have hbase' : q (k + 1) ∈ (trivializationAt E (TangentSpace I) (x k)).baseSet := by
      simpa using hpk
    set X : TangentSpace I (q (k + 1)) :=
      frameVector (I := I) (x k) (q (k + 1)) (Y (c (k + 1) - c k)) with hXdef
    set y0 : E :=
      (trivializationAt E (TangentSpace I) (x (k + 1))).continuousLinearMapAt ℝ (q (k + 1)) X
      with hy0def
    have hclm' : (trivializationAt E (TangentSpace I) (x k)).continuousLinearMapAt ℝ (q (k + 1)) X
        = Y (c (k + 1) - c k) := by
      rw [hXdef]
      exact Trivialization.continuousLinearMapAt_symmL
        (trivializationAt E (TangentSpace I) (x k)) (R := ℝ) hbase' (Y (c (k + 1) - c k))
    have hunitk : chartGram (I := I) (x k) (q (k + 1)) (Y (c (k + 1) - c k))
        (Y (c (k + 1) - c k)) = 1 := by
      rw [← hpt1 k hkN]
      exact hpart.2.1 (c (k + 1) - c k) ⟨(hllpos k hk).le, le_refl _⟩
    have horthk : chartGram (I := I) (x k) (q (k + 1)) (Y (c (k + 1) - c k))
        (wp k (c (k + 1) - c k)) = 0 := by
      rw [← hpt1 k hkN]
      exact hpart.2.2 (c (k + 1) - c k) ⟨(hllpos k hk).le, le_refl _⟩
    have hvelc : (trivializationAt E (TangentSpace I) (x k)).continuousLinearMapAt ℝ (q (k + 1))
        (frameVector (I := I) (x k) (q (k + 1)) (wp k (c (k + 1) - c k)))
        = wp k (c (k + 1) - c k) :=
      continuousLinearMapAt_frameVector (I := I) (x k) (q (k + 1)) hpk (wp k (c (k + 1) - c k))
    have hy0unit : chartGram (I := I) (x (k + 1)) (q (k + 1)) y0 y0 = 1 := by
      have h1 : chartGram (I := I) (x (k + 1)) (q (k + 1)) y0 y0 = inner ℝ X X := by
        rw [hy0def]
        exact chartGram_continuousLinearMapAt (I := I) (x (k + 1)) (q (k + 1)) hpk' X X
      have h2 : inner ℝ X X = chartGram (I := I) (x k) (q (k + 1))
          (Y (c (k + 1) - c k)) (Y (c (k + 1) - c k)) := by
        rw [← chartGram_continuousLinearMapAt (I := I) (x k) (q (k + 1)) hpk X X, hclm']
      rw [h1, h2, hunitk]
    have hy0orth : chartGram (I := I) (x (k + 1)) (q (k + 1)) y0 (wp (k + 1) 0) = 0 := by
      have hwpc : (trivializationAt E (TangentSpace I) (x (k + 1))).continuousLinearMapAt ℝ
          (q (k + 1)) (frameVector (I := I) (x (k + 1)) (q (k + 1)) (wp (k + 1) 0))
          = wp (k + 1) 0 :=
        continuousLinearMapAt_frameVector (I := I) (x (k + 1)) (q (k + 1)) hpk' (wp (k + 1) 0)
      have h1 : chartGram (I := I) (x (k + 1)) (q (k + 1)) y0 (wp (k + 1) 0)
          = inner ℝ X (frameVector (I := I) (x (k + 1)) (q (k + 1)) (wp (k + 1) 0)) := by
        rw [hy0def]
        conv_lhs => rw [← hwpc]
        exact chartGram_continuousLinearMapAt (I := I) (x (k + 1)) (q (k + 1)) hpk' X
          (frameVector (I := I) (x (k + 1)) (q (k + 1)) (wp (k + 1) 0))
      have h2 : inner ℝ X (frameVector (I := I) (x (k + 1)) (q (k + 1)) (wp (k + 1) 0))
          = chartGram (I := I) (x k) (q (k + 1)) (Y (c (k + 1) - c k))
              (wp k (c (k + 1) - c k)) := by
        rw [← hmatchvel k hkN,
          ← chartGram_continuousLinearMapAt (I := I) (x k) (q (k + 1)) hpk X
            (frameVector (I := I) (x k) (q (k + 1)) (wp k (c (k + 1) - c k))), hclm', hvelc]
      rw [h1, h2, horthk]
    obtain ⟨Z, hZ0, hZode, hZcov⟩ :=
      Submission.JacobiGen.exists_parallel_field_Ioo (cov := cov) htor
        (x₀ := x (k + 1)) (u := up (k + 1)) (w := wp (k + 1))
        (A := A (k + 1) - c (k + 1)) (B := B (k + 1) - c (k + 1))
        (a := 0) (b := c (k + 1 + 1) - c (k + 1)) (t₀ := 0)
        h0 (hIcc (k + 1) hkN) (hstage (k + 1) hkN) (hup (k + 1) hkN) (hwp' (k + 1) hkN)
        ⟨le_refl _, h0.le⟩ y0
    have hsub : Icc (0 : ℝ) (c (k + 1 + 1) - c (k + 1))
        ⊆ Ioo (A (k + 1) - c (k + 1)) (B (k + 1) - c (k + 1)) := hIcc (k + 1) hkN
    have hvel : ∀ t ∈ Icc (0 : ℝ) (c (k + 1 + 1) - c (k + 1)),
        HasDerivAt (wp (k + 1)) (-(christoffelLM cov (x (k + 1))
          ((extChartAt I (x (k + 1))).symm (up (k + 1) t))
          (frameVector (I := I) (x (k + 1)) ((extChartAt I (x (k + 1))).symm (up (k + 1) t))
            (wp (k + 1) t))) (wp (k + 1) t)) t :=
      fun t ht => Submission.JacobiGen.hasDerivAt_velocity_Ioo (hup (k + 1) hkN)
        (hwp' (k + 1) hkN) (hstage (k + 1) hkN) t (hsub ht)
    refine ⟨Z, fun _ => ⟨?_, ?_, ?_⟩, fun _ => ?_⟩
    · intro s hs
      exact hZode s hs
    · intro s hs
      rw [Submission.JacobiGen.chartGram_parallel_self_const_Ioo (cov := cov) hmet
        (A := A (k + 1) - c (k + 1)) (B := B (k + 1) - c (k + 1))
        (a := 0) (b := c (k + 1 + 1) - c (k + 1)) (t₀ := 0)
        (hstage (k + 1) hkN) (hup (k + 1) hkN) (hwp' (k + 1) hkN)
        h0.le hsub ⟨le_refl _, h0.le⟩ hZode s hs]
      rw [hpt0 (k + 1) hkN, hZ0]
      exact hy0unit
    · intro s hs
      rw [Submission.JacobiGen.chartGram_parallel_const_Ioo (cov := cov) hmet
        (A := A (k + 1) - c (k + 1)) (B := B (k + 1) - c (k + 1))
        (a := 0) (b := c (k + 1 + 1) - c (k + 1)) (t₀ := 0)
        (hstage (k + 1) hkN) (hup (k + 1) hkN) (hwp' (k + 1) hkN)
        h0.le hsub ⟨le_refl _, h0.le⟩ hZode hvel s hs]
      rw [hpt0 (k + 1) hkN, hZ0]
      exact hy0orth
    · show frameVector (I := I) (x k) (q (k + 1)) (Y (c (k + 1) - c k))
        = frameVector (I := I) (x (k + 1)) (q (k + 1)) (Z 0)
      rw [hZ0]
      show X = frameVector (I := I) (x (k + 1)) (q (k + 1)) y0
      exact (Trivialization.symmL_continuousLinearMapAt
        (trivializationAt E (TangentSpace I) (x (k + 1))) (R := ℝ) hbase X).symm
  -- assemble
  have hbuild : ∀ K, K ≤ N → ∃ Y : ℕ → ℝ → E,
      (∀ k < K, Par k (Y k)) ∧ (∀ k, k + 1 < K → MtchN k (Y k) (Y (k + 1))) := by
    intro K
    induction K with
    | zero =>
      intro _
      exact ⟨fun _ _ => 0, fun k hk => absurd hk (Nat.not_lt_zero k),
        fun k hk => absurd hk (by omega)⟩
    | succ K ih =>
      intro hKN
      obtain ⟨Y, hYpar, hYmat⟩ := ih (by omega)
      have hKN' : K < N := hKN
      obtain ⟨Z, hZpar, hZmat⟩ : ∃ Z : ℝ → E,
          Par K Z ∧ (K = 0 ∨ MtchN (K - 1) (Y (K - 1)) Z) := by
        rcases K.eq_zero_or_pos with h | h
        · subst h
          exact ⟨hseed.choose, hseed.choose_spec, Or.inl rfl⟩
        · obtain ⟨Z, hZ1, hZ2⟩ := hstep (K - 1) (by omega) (Y (K - 1))
            (hYpar (K - 1) (by omega))
          have hZ1' : Par K Z := by
            have hK1 : K - 1 + 1 = K := by omega
            rwa [hK1] at hZ1
          exact ⟨Z, hZ1', Or.inr hZ2⟩
      refine ⟨Function.update Y K Z, ?_, ?_⟩
      · intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
        · rw [Function.update_of_ne (by omega : k ≠ K)]
          exact hYpar k h
        · rw [h, Function.update_self]
          exact hZpar
      · intro k hk
        have hkK : k + 1 ≤ K := by omega
        rcases lt_or_eq_of_le hkK with h | h
        · have hne1 : k ≠ K := by omega
          have hne2 : k + 1 ≠ K := by omega
          rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
          exact hYmat k h
        · have hk' : k = K - 1 := by omega
          have hK1 : K - 1 + 1 = K := by omega
          rw [hk', hK1, Function.update_of_ne (by omega : K - 1 ≠ K), Function.update_self]
          rcases hZmat with h0 | h0
          · omega
          · exact h0
  obtain ⟨Y, hYpar, hYmat⟩ := hbuild N le_rfl
  exact ⟨Y, (fun k hk => (hYpar k hk hk).1), (fun k hk => (hYpar k hk hk).2.1),
    (fun k hk => (hYpar k hk hk).2.2), (fun k hk => hYmat k hk hk)⟩

/-! ## Margins for the quadratic family -/

/-- If `u` takes its values in the (open) chart target on `(A,B)` and `u, η, ζ` are continuous on
`[A₀,B₀] ⊆ (A,B)`, then for small `s` the quadratic family `u t + s • η t + (s²/2) • ζ t` still takes
its values in the target, uniformly for `t ∈ [A₀,B₀]`. -/
lemma exists_margins_fam2 {x₀ : M} {u η ζ : ℝ → E} {A B A₀ B₀ : ℝ}
    (hAA₀ : A < A₀) (hB₀B : B₀ < B)
    (huC : ContinuousOn u (Icc A₀ B₀)) (hηC : ContinuousOn η (Icc A₀ B₀))
    (hζC : ContinuousOn ζ (Icc A₀ B₀))
    (hu : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target) :
    ∃ a₁ a₂ : ℝ, a₁ < 0 ∧ 0 < a₂ ∧
      ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc A₀ B₀,
        u t + s • η t + (s ^ 2 / 2) • ζ t ∈ (extChartAt I x₀).target := by
  have hsub : Icc A₀ B₀ ⊆ Ioo A B := by
    intro t ht; exact ⟨by linarith [ht.1, hAA₀], by linarith [ht.2, hB₀B]⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      u p.2 + p.1 • η p.2 + (p.1 ^ 2 / 2) • ζ p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) := by
    have hsnd : ContinuousOn (fun p : ℝ × ℝ => p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      continuousOn_snd
    have hfst : ContinuousOn (fun p : ℝ × ℝ => p.1) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      continuousOn_fst
    have h1 : ContinuousOn (fun p : ℝ × ℝ => u p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      huC.comp hsnd (fun p hp => hp.2)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => η p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      hηC.comp hsnd (fun p hp => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => ζ p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      hζC.comp hsnd (fun p hp => hp.2)
    have h4 : ContinuousOn (fun p : ℝ × ℝ => p.1 • η p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      hfst.smul h2
    have h5 : ContinuousOn (fun p : ℝ × ℝ => (p.1 ^ 2 / 2) • ζ p.2)
        (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      ((hfst.pow 2).div_const 2).smul h3
    exact (h1.add h4).add h5
  obtain ⟨ε, hε, hmem⟩ := Commons.Topology.Compact.exists_pos_forall_mem_of_isCompact
    (X := E) (W := (extChartAt I x₀).target) (isOpen_extChartAt_target x₀) isCompact_Icc
    (f := fun s t => u t + s • η t + (s ^ 2 / 2) • ζ t)
    (by simpa only [] using hcont)
    (fun t ht => by simpa using hu t (hsub ht))
  exact ⟨-ε, ε, by linarith, hε, fun s hs t ht => hmem s hs t ht⟩

/-! ## The shifted test field

The classical test field along the piece `k` is `sin (π t / L) • Y` in the *global* parameter; in the
piece-local parameter `s = t - c k` it becomes `sin (π (c k + s) / L) • Y`.  The two lemmas below are
the shifted forms of `BonnetMyers.covDsP_testField` and `BonnetMyers.indexIntegrand_testField_pointwise`. -/

/-- The shifted test field. -/
def testFieldS (L a : ℝ) (Y : ℝ → E) : ℝ → E := fun t => Real.sin (Real.pi * (a + t) / L) • Y t

/-- The derivative of the shifted test field. -/
def testFieldSDeriv (L a : ℝ) (Y : ℝ → E) : ℝ → E := fun t =>
  (Real.pi / L * Real.cos (Real.pi * (a + t) / L)) • Y t
    + Real.sin (Real.pi * (a + t) / L) • deriv Y t

lemma hasDerivAt_sin_pi_shift (L a t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (Real.pi * (a + t) / L))
      (Real.pi / L * Real.cos (Real.pi * (a + t) / L)) t :=
  hasDerivAt_comp_const_add' (f := fun u : ℝ => Real.sin (Real.pi * u / L))
    (f' := fun u : ℝ => Real.pi / L * Real.cos (Real.pi * u / L)) (c := a)
    (BonnetMyers.hasDerivAt_sin_pi L (a + t))

lemma hasDerivAt_testFieldS {L a : ℝ} {Y : ℝ → E} {t : ℝ} (hY : HasDerivAt Y (deriv Y t) t) :
    HasDerivAt (testFieldS (E := E) L a Y) (testFieldSDeriv (E := E) L a Y t) t := by
  have h := (hasDerivAt_sin_pi_shift L a t).smul hY
  refine h.congr_deriv ?_
  simp only [testFieldSDeriv]
  rw [add_comm]

lemma covDsP_testFieldS (htor : cov.torsion = 0)
    {x₀ : M} {u w Y : ℝ → E} {L a t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source)
    (hpar : deriv Y t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0) :
    covDsP cov x₀ u (testFieldS (E := E) L a Y) w (testFieldSDeriv (E := E) L a Y) 0 t
      = (Real.pi / L * Real.cos (Real.pi * (a + t) / L)) • Y t := by
  have hTF : testFieldS (E := E) L a Y t = Real.sin (Real.pi * (a + t) / L) • Y t := rfl
  have hTFD : testFieldSDeriv (E := E) L a Y t
      = (Real.pi / L * Real.cos (Real.pi * (a + t) / L)) • Y t
        + Real.sin (Real.pi * (a + t) / L) • deriv Y t := rfl
  rw [covDsP]
  simp only [fam, famP, zero_smul, add_zero, zero_add, smul_zero]
  rw [hTF, hTFD]
  rw [chrB_smul_snd, chrB_comm (cov := cov) htor hsrc]
  rw [add_assoc, ← smul_add, hpar, smul_zero, add_zero]

/-- **The pointwise index-form bound for the shifted test field.** -/
lemma indexIntegrand_testFieldS_pointwise (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {x₀ : M} {u w Y : ℝ → E} {L a t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source)
    (hunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (Y t) = 1)
    (horth : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0)
    (hwunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hpar : deriv Y t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0) :
    Real.sin (Real.pi * (a + t) / L) ^ 2
        - (Real.pi / L * Real.cos (Real.pi * (a + t) / L)) ^ 2
      ≤ indexIntegrand cov x₀ u (testFieldS (E := E) L a Y) w (testFieldSDeriv (E := E) L a Y) t := by
  have hp : (1 : ℝ) ≤ inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t))
      (curvVec cov ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) := by
    refine Submission.Pinch.one_le_inner_curvVec hcov hmet hpinch ?_ ?_ ?_
    · simpa only [chartGram_apply] using hunit
    · simpa only [chartGram_apply] using hwunit
    · simpa only [chartGram_apply] using horth
  have hGt : Gt cov x₀ u (testFieldS (E := E) L a Y) w (testFieldSDeriv (E := E) L a Y) t
      = (Real.pi / L * Real.cos (Real.pi * (a + t) / L)) ^ 2 := by
    rw [Gt, DtQ, covDsP_testFieldS (cov := cov) htor hsrc hpar]
    simp only [chartGram_smul_smul, hunit, mul_one]
  have hRt : Real.sin (Real.pi * (a + t) / L) ^ 2
      ≤ Rt cov x₀ u (testFieldS (E := E) L a Y) w t := by
    have hTF' : testFieldS (E := E) L a Y t = Real.sin (Real.pi * (a + t) / L) • Y t := rfl
    change Real.sin (Real.pi * (a + t) / L) ^ 2 ≤
      inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (testFieldS (E := E) L a Y t))
        (curvVec cov ((extChartAt I x₀).symm (u t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (testFieldS (E := E) L a Y t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)))
    rw [hTF', frameVector_smul, curvVec_smul_left cov hcov]
    rw [real_inner_smul_left, real_inner_smul_right]
    nlinarith [hp, sq_nonneg (Real.sin (Real.pi * (a + t) / L))]
  rw [indexIntegrand]
  linarith




/-- **The strict form of the pointwise bound** for the test field `sin (π (a + t) / L) • Y`:
if the sine factor is nonzero, the pinching bound `sec > 1` makes the inequality of
`indexIntegrand_testFieldS_pointwise` strict. -/
lemma indexIntegrand_testFieldS_pointwise_strict (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {x₀ : M} {u w Y : ℝ → E} {L a t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source)
    (hunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (Y t) = 1)
    (horth : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0)
    (hwunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hpar : deriv Y t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0)
    (hsin : Real.sin (Real.pi * (a + t) / L) ≠ 0) :
    Real.sin (Real.pi * (a + t) / L) ^ 2
        - (Real.pi / L * Real.cos (Real.pi * (a + t) / L)) ^ 2
      < indexIntegrand cov x₀ u (testFieldS (E := E) L a Y) w (testFieldSDeriv (E := E) L a Y) t := by
  have hp : (1 : ℝ) < inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t))
      (curvVec cov ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) := by
    refine Submission.Pinch.one_lt_inner_curvVec hcov hmet hpinch ?_ ?_ ?_
    · simpa only [chartGram_apply] using hunit
    · simpa only [chartGram_apply] using hwunit
    · simpa only [chartGram_apply] using horth
  have hGt : Gt cov x₀ u (testFieldS (E := E) L a Y) w (testFieldSDeriv (E := E) L a Y) t
      = (Real.pi / L * Real.cos (Real.pi * (a + t) / L)) ^ 2 := by
    rw [Gt, DtQ, covDsP_testFieldS (cov := cov) htor hsrc hpar]
    simp only [chartGram_smul_smul, hunit, mul_one]
  have hRt : Real.sin (Real.pi * (a + t) / L) ^ 2
      < Rt cov x₀ u (testFieldS (E := E) L a Y) w t := by
    have hTF' : testFieldS (E := E) L a Y t = Real.sin (Real.pi * (a + t) / L) • Y t := rfl
    change Real.sin (Real.pi * (a + t) / L) ^ 2 <
      inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (testFieldS (E := E) L a Y t))
        (curvVec cov ((extChartAt I x₀).symm (u t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (testFieldS (E := E) L a Y t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)))
    rw [hTF', frameVector_smul, curvVec_smul_left cov hcov]
    rw [real_inner_smul_left, real_inner_smul_right]
    nlinarith [hp, sq_pos_of_ne_zero hsin]
  rw [indexIntegrand]
  linarith

/-! ## A chain of triangle inequalities -/

/-- The Riemannian distance between the endpoints of a chain of points is at most the sum of the
distances between consecutive points. -/
lemma edist_le_sum_pairs {n : ℕ} {a b : ℕ → M} :
    Manifold.riemannianEDist I (a 0) (a n) ≤
      ∑ k ∈ Finset.range n, (Manifold.riemannianEDist I (a k) (b k)
        + Manifold.riemannianEDist I (b k) (a (k + 1))) := by
  induction n with
  | zero => simp [Manifold.riemannianEDist_self]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc Manifold.riemannianEDist I (a 0) (a (n + 1))
        ≤ Manifold.riemannianEDist I (a 0) (a n)
          + Manifold.riemannianEDist I (a n) (a (n + 1)) := Manifold.riemannianEDist_triangle
      _ ≤ (∑ k ∈ Finset.range n, (Manifold.riemannianEDist I (a k) (b k)
            + Manifold.riemannianEDist I (b k) (a (k + 1))))
          + (Manifold.riemannianEDist I (a n) (b n)
            + Manifold.riemannianEDist I (b n) (a (n + 1))) :=
          add_le_add ih Manifold.riemannianEDist_triangle
      _ = (∑ k ∈ Finset.range n, (Manifold.riemannianEDist I (a k) (b k)
            + Manifold.riemannianEDist I (b k) (a (k + 1))))
          + (Manifold.riemannianEDist I (a n) (b n)
            + Manifold.riemannianEDist I (b n) (a (n + 1))) := rfl


/-- **The distance between the two endpoints of the variation of a piece is at most `√(L₀ · E(s))`.**
The curve `t ↦ fam2Curve u η ζ s t` runs from `fam2Curve … s 0` to `fam2Curve … s L₀`, so its
Riemannian distance is at most its length, which by Cauchy–Schwarz is at most `√(L₀ · E(s))`. -/
lemma edist_piece_le [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    {x₀ : M} {u η ζ w e ζ' w' : ℝ → E} {L₀ s : ℝ} (hL₀ : 0 < L₀)
    (hu : ∀ t ∈ Icc 0 L₀, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L₀, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L₀, HasDerivAt η (e t) t) (hζ : ∀ t ∈ Icc 0 L₀, HasDerivAt ζ (ζ' t) t)
    (heC : ContinuousOn e (Icc 0 L₀)) (hζ'C : ContinuousOn ζ' (Icc 0 L₀))
    (hstay : ∀ t ∈ Icc 0 L₀, fam2 u η ζ s t ∈ (extChartAt I x₀).target) :
    Manifold.riemannianEDist I (fam2Curve (I := I) x₀ u η ζ s 0)
        (fam2Curve (I := I) x₀ u η ζ s L₀)
      ≤ ENNReal.ofReal (Real.sqrt (L₀ * fam2Energy (I := I) x₀ u η ζ w e ζ' L₀ s)) := by
  have hstayn : ∀ t ∈ Icc (0:ℝ) L₀, ∀ᶠ r in 𝓝 t, fam2 u η ζ s r ∈ (extChartAt I x₀).target :=
    fun t ht => (hasDerivAt_fam2_t (hu t ht) (hη t ht) (hζ t ht)).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (hstay t ht))
  have hTc : ContinuousOn (fun t => fam2T w e ζ' s t) (Icc (0:ℝ) L₀) := by
    have h1 : ContinuousOn (fun t => w t + s • e t) (Icc (0:ℝ) L₀) :=
      (HasDerivAt.continuousOn hw).add (heC.const_smul s)
    refine ContinuousOn.congr (g := fun t => fam2T w e ζ' s t) (h1.add (hζ'C.const_smul (s ^ 2 / 2))) ?_
    intro t ht
    simp only [fam2T, Pi.add_apply, Pi.smul_apply]
  -- the curve is `C¹`
  have hγ : CMDiff[Icc (0:ℝ) L₀] 1 (fam2Curve (I := I) x₀ u η ζ s) := by
    have hs : UniqueDiffOn ℝ (Icc (0:ℝ) L₀) := uniqueDiffOn_Icc hL₀
    have hdiff : DifferentiableOn ℝ (fun t => fam2 u η ζ s t) (Icc (0:ℝ) L₀) :=
      fun t ht => (hasDerivAt_fam2_t (hu t ht) (hη t ht) (hζ t ht)).differentiableAt.differentiableWithinAt
    have hderiv : EqOn (derivWithin (fun t => fam2 u η ζ s t) (Icc (0:ℝ) L₀))
        (fun t => fam2T w e ζ' s t) (Icc (0:ℝ) L₀) :=
      fun t ht => (hasDerivAt_fam2_t (hu t ht) (hη t ht) (hζ t ht)).hasDerivWithinAt.derivWithin (hs t ht)
    have hcont : ContinuousOn (derivWithin (fun t => fam2 u η ζ s t) (Icc (0:ℝ) L₀))
        (Icc (0:ℝ) L₀) := ContinuousOn.congr hTc hderiv
    have hu' : ContDiffOn ℝ (1 : ℕ∞ω) (fun t => fam2 u η ζ s t) (Icc (0:ℝ) L₀) :=
      (contDiffOn_one_iff_derivWithin hs).mpr ⟨hdiff, hcont⟩
    have hu'' : CMDiff[Icc (0:ℝ) L₀] 1 (fun t => fam2 u η ζ s t) :=
      contMDiffOn_iff_contDiffOn.mpr hu'
    exact (contMDiffOn_extChartAt_symm (I := I) x₀).comp hu'' hstay
  have hfamc : ContinuousOn (fun t => fam2Curve (I := I) x₀ u η ζ s t) (Icc (0:ℝ) L₀) :=
    hγ.continuousOn
  have hGc : ContinuousOn (fun t => fam2G (I := I) x₀ u η ζ w e ζ' s t) (Icc (0:ℝ) L₀) :=
    continuousOn_chartGram_curve (I := I) hfamc hTc hTc
      (fun t ht => mem_source_chartCurve (I := I) (hstay t ht))
  have hsp : ∀ t ∈ Icc (0:ℝ) L₀, curveSpeed (I := I) (fam2Curve (I := I) x₀ u η ζ s) t
      = Real.sqrt (fam2G (I := I) x₀ u η ζ w e ζ' s t) :=
    fun t ht => curveSpeed_fam2Curve (I := I) (hu t ht) (hη t ht) (hζ t ht) (hstay t ht)
      (hstayn t ht)
  have hspc : ContinuousOn (fun t : ℝ => curveSpeed (I := I) (fam2Curve (I := I) x₀ u η ζ s) t)
      (Icc (0:ℝ) L₀) :=
    ContinuousOn.congr (g := fun t : ℝ => curveSpeed (I := I) (fam2Curve (I := I) x₀ u η ζ s) t)
      hGc.sqrt (fun t ht => hsp t ht)
  have hnn : ∀ t ∈ Icc (0:ℝ) L₀, 0 ≤ curveSpeed (I := I) (fam2Curve (I := I) x₀ u η ζ s) t :=
    fun t _ => curveSpeed_nonneg (I := I) _ t
  have hlen : Manifold.pathELength I (fam2Curve (I := I) x₀ u η ζ s) 0 L₀
      = ENNReal.ofReal (∫ t in (0:ℝ)..L₀, curveSpeed (I := I) (fam2Curve (I := I) x₀ u η ζ s) t) := by
    refine Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg
      (I := I) hL₀.le (hspc.integrableOn_Icc) hnn ?_
    intro t ht
    show ‖curveVelocity (I := I) (fam2Curve (I := I) x₀ u η ζ s) t‖ₑ
      = ENNReal.ofReal (curveSpeed (I := I) (fam2Curve (I := I) x₀ u η ζ s) t)
    rw [Submission.Minimal.enorm_eq_ofReal_norm,
      Submission.GeodesicSpeed.curveSpeed_eq_norm (I := I) (fam2Curve (I := I) x₀ u η ζ s) t]
  have h1 : Manifold.riemannianEDist I (fam2Curve (I := I) x₀ u η ζ s 0)
      (fam2Curve (I := I) x₀ u η ζ s L₀)
      ≤ Manifold.pathELength I (fam2Curve (I := I) x₀ u η ζ s) 0 L₀ :=
    Manifold.riemannianEDist_le_pathELength hγ rfl rfl hL₀.le
  rw [hlen] at h1
  refine h1.trans ?_
  rw [ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)]
  have hcs := Commons.Analysis.Calculus.sq_intervalIntegral_le_length_mul_intervalIntegral_sq
    (f := fun t : ℝ => curveSpeed (I := I) (fam2Curve (I := I) x₀ u η ζ s) t) hL₀.le
    (by rwa [uIcc_of_le hL₀.le]) (by rw [uIcc_of_le hL₀.le]; exact hnn)
  have hsq : ∫ t in (0:ℝ)..L₀, (curveSpeed (I := I) (fam2Curve (I := I) x₀ u η ζ s) t) ^ 2
      = fam2Energy (I := I) x₀ u η ζ w e ζ' L₀ s := by
    rw [fam2Energy_eq_fam2G]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hL₀.le] at ht
    rw [hsp t ht]
    exact Real.sq_sqrt (Submission.Minimal.chartGram_self_nonneg (I := I) x₀ _ _)
  rw [hsq] at hcs
  exact Real.le_sqrt_of_sq_le (by rw [sub_zero] at hcs; exact hcs)

section Main

variable [ContMDiffCovariantDerivative cov ∞]

/-- **Global Bonnet–Myers.**  A unit-speed geodesic which realises the distance between its
endpoints has length at most `π`, under the strict pinching hypothesis `QuarterPinched cov`. -/
theorem le_pi_of_minimising_geodesic
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {L : ℝ} (hL : 0 < L)
    (hVab : Icc 0 L ⊆ V) (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeo0 : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hunit : ∀ t ∈ V, ‖curveVelocity (I := I) γ t‖ = 1)
    (hmin : Manifold.riemannianEDist I (γ 0) (γ L) = ENNReal.ofReal L) :
    L < Real.pi := by
  classical
  by_contra hcon
  push Not at hcon
  -- non-vanishing velocity
  have hne : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0 := by
    intro t ht h0
    have := hunit t ht
    rw [h0, norm_zero] at this
    exact one_ne_zero this.symm
  -- the chart pieces
  obtain ⟨N, c, hc0, hcN, hmono, x, A, B, hAB, hsrcB, hODE⟩ :=
    Submission.ChartPieces.exists_chart_pieces (cov := cov) hV (a := (0:ℝ)) (b := L) (hL.le) hVab hγ hgeo0 hne
  set ul : ℕ → ℝ → E := fun k r => (extChartAt I (x k)) (γ r) with huldef
  set wl : ℕ → ℝ → E := fun k => deriv (ul k) with hwldef
  set ll : ℕ → ℝ := fun k => c (k + 1) - c k with hlldef
  set up : ℕ → ℝ → E := fun k s => ul k (c k + s) with hupdef
  set wp : ℕ → ℝ → E := fun k s => wl k (c k + s) with hwpdef
  set wp' : ℕ → ℝ → E :=
    fun k s => chartGeodesicVectorField cov (x k) (ul k (c k + s), wl k (c k + s)) with hwp'def
  have hllpos : ∀ k < N, 0 < ll k := by
    intro k hk
    have := hmono k hk
    simp only [hlldef]
    linarith
  have hul : ∀ k < N, ∀ t ∈ Ioo (A k) (B k), HasDerivAt (ul k) (wl k t) t := by
    intro k hk t ht
    have := (hODE k hk t ht).1
    simpa only [ul, wl] using this
  have hwl : ∀ k < N, ∀ t ∈ Ioo (A k) (B k),
      HasDerivAt (wl k) (chartGeodesicVectorField cov (x k) (ul k t, wl k t)) t := by
    intro k hk t ht
    have := (hODE k hk t ht).2
    simpa only [ul, wl] using this
  have hshift : ∀ k < N, ∀ s ∈ Ioo (A k - c k) (B k - c k), c k + s ∈ Ioo (A k) (B k) := by
    intro k hk s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hup : ∀ k < N, ∀ s ∈ Ioo (A k - c k) (B k - c k), HasDerivAt (up k) (wp k s) s := by
    intro k hk s hs
    have := hasDerivAt_comp_const_add (hul k hk (c k + s) (hshift k hk s hs))
    simpa only [up, wp] using this
  have hwp : ∀ k < N, ∀ s ∈ Ioo (A k - c k) (B k - c k), HasDerivAt (wp k) (wp' k s) s := by
    intro k hk s hs
    have h := hasDerivAt_comp_const_add
      (f := wl k) (f' := fun t => chartGeodesicVectorField cov (x k) (ul k t, wl k t))
      (c := c k) (t := s) (hwl k hk (c k + s) (hshift k hk s hs))
    simpa only [up, wp, wp'] using h
  have hwpchart : ∀ k < N, ∀ s ∈ Ioo (A k - c k) (B k - c k),
      HasDerivAt (wp k) (chartGeodesicVectorField cov (x k) (up k s, wp k s)) s :=
    fun k hk s hs => hwp k hk s hs
  have hstagIoo : ∀ k < N, ∀ s ∈ Ioo (A k - c k) (B k - c k),
      up k s ∈ (extChartAt I (x k)).target := by
    intro k hk s hs
    have hsrc : γ (c k + s) ∈ (extChartAt I (x k)).source := by
      rw [extChartAt_source]
      exact hsrcB k hk (c k + s) (hshift k hk s hs)
    have := (extChartAt I (x k)).map_source hsrc
    simpa only [up, ul] using this
  have hstage : ∀ k < N, ∀ s ∈ Icc 0 (ll k), up k s ∈ (extChartAt I (x k)).target := by
    intro k hk s hs
    refine hstagIoo k hk s ⟨?_, ?_⟩
    · have := (hAB k hk).1; linarith [hs.1]
    · have h1 := (hAB k hk).2
      have h2 := hs.2
      dsimp only [ll] at h2
      linarith
  have hgeoeq : ∀ k < N, ∀ s ∈ Icc 0 (ll k),
      wp' k s + chrB cov (x k) ((extChartAt I (x k)).symm (up k s)) (wp k s) (wp k s) = 0 := by
    intro k hk s hs
    simp only [wp', up, wp]
    rw [chartGeodesicVectorField, chrB_apply]
    abel
  have hcmono : ∀ i j, i ≤ j → j ≤ N → c i ≤ c j := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_refl _
    | succ j hij ih =>
      have hlt : j < N := Nat.lt_of_succ_le hj
      exact le_trans (ih (Nat.le_of_succ_le hj)) (le_of_lt (hmono j hlt))
  have hcstrict : ∀ j ≤ N, ∀ i < j, c i < c j := by
    intro j hj
    induction j with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ j ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact lt_trans (ih (by omega) i h) (hmono j (by omega))
      · rw [h]; exact hmono j (by omega)
  have hcle : ∀ k ≤ N, 0 ≤ c k ∧ c k ≤ L := by
    intro k hk
    exact ⟨by rw [← hc0]; exact hcmono 0 k (Nat.zero_le k) hk,
      by rw [← hcN]; exact hcmono k N hk le_rfl⟩
  have hcll : ∀ k < N, c k + ll k = c (k + 1) := by
    intro k hk; simp only [ll]; ring
  have hsc : ∀ k < N, ∀ s ∈ Icc 0 (ll k), c k + s ∈ Icc (0:ℝ) L := by
    intro k hk s hs
    refine ⟨by linarith [(hcle k hk.le).1, hs.1], ?_⟩
    have h2 : c k + s ≤ c k + ll k := by linarith [hs.2]
    rw [hcll k hk] at h2
    exact le_trans h2 (hcle (k + 1) (by omega)).2
  have hmemV : ∀ k < N, ∀ s ∈ Icc 0 (ll k), c k + s ∈ V := by
    intro k hk s hs
    exact hVab (hsc k hk s hs)
  have hsymm : ∀ k < N, ∀ s ∈ Icc 0 (ll k),
      (extChartAt I (x k)).symm (up k s) = γ (c k + s) := by
    intro k hk s hs
    have hsrc : γ (c k + s) ∈ (extChartAt I (x k)).source :=
      mem_extChartAt_source_iff.mpr (hsrcB k hk (c k + s) (hshift k hk s
        ⟨by linarith [(hAB k hk).1, hs.1], by linarith [(hAB k hk).2, hs.2]⟩))
    have h1 : (extChartAt I (x k)) (γ (c k + s)) = up k s := rfl
    rw [← h1]
    exact (extChartAt I (x k)).left_inv hsrc
  have hsrc_s : ∀ k < N, ∀ s ∈ Icc 0 (ll k), γ (c k + s) ∈ (chartAt H (x k)).source := by
    intro k hk s hs
    exact hsrcB k hk (c k + s) (hshift k hk s
      ⟨by linarith [(hAB k hk).1, hs.1], by linarith [(hAB k hk).2, hs.2]⟩)
  have hγmd_s : ∀ k < N, ∀ s ∈ Icc 0 (ll k), MDifferentiableAt 𝓘(ℝ) I γ (c k + s) := by
    intro k hk s hs
    exact (hγ.contMDiffAt (hV.mem_nhds (hmemV k hk s hs))).mdifferentiableAt (by simp)
  have hwvel : ∀ k < N, ∀ s ∈ Icc 0 (ll k), wp k s
      = (trivializationAt E (TangentSpace I) (x k)).continuousLinearMapAt ℝ
          (γ (c k + s)) (curveVelocity (I := I) γ (c k + s)) := by
    intro k hk s hs
    have h := deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (I := I) (x k)
      (hγmd_s k hk s hs) (hsrc_s k hk s hs)
    simpa only [up, ul, wp, wl] using h
  have hwunit : ∀ k < N, ∀ s ∈ Icc 0 (ll k),
      chartGram (I := I) (x k) ((extChartAt I (x k)).symm (up k s)) (wp k s) (wp k s) = 1 := by
    intro k hk s hs
    rw [hsymm k hk s hs, hwvel k hk s hs,
      chartGram_continuousLinearMapAt (I := I) (x k) (γ (c k + s)) (hsrc_s k hk s hs),
      real_inner_self_eq_norm_sq, hunit (c k + s) (hmemV k hk s hs), one_pow]
  -- the interval inclusion, transcribed
  have hIcccll : ∀ k < N, Icc (0 : ℝ) (c (k + 1) - c k) ⊆ Ioo (A k - c k) (B k - c k) := by
    intro k hk s hs
    exact ⟨by linarith [(hAB k hk).1, hs.1], by linarith [(hAB k hk).2, hs.2]⟩
  -- the junction points are the corresponding points of `γ`
  have hpt0 : ∀ k < N, (extChartAt I (x k)).symm (up k 0) = γ (c k) := by
    intro k hk
    rw [hsymm k hk 0 ⟨le_refl _, (hllpos k hk).le⟩, add_zero]
  have hpt1' : ∀ k < N, (extChartAt I (x k)).symm (up k (c (k + 1) - c k)) = γ (c (k + 1)) := by
    intro k hk
    have h := hsymm k hk (c (k + 1) - c k) ⟨(hllpos k hk).le, le_refl _⟩
    rw [h]
    exact congrArg γ (hcll k hk)
  have hpt1 : ∀ k, k + 1 < N →
      (extChartAt I (x k)).symm (up k (c (k + 1) - c k)) = γ (c (k + 1)) :=
    fun k hk => hpt1' k (by omega)
  -- the two velocity coordinate vectors at the junction agree
  have hmatchvel : ∀ k, k + 1 < N →
      frameVector (I := I) (x k) (γ (c (k + 1))) (wp k (c (k + 1) - c k))
        = frameVector (I := I) (x (k + 1)) (γ (c (k + 1))) (wp (k + 1) 0) := by
    intro k hk
    have hk' : k < N := by omega
    have hsrcj : γ (c (k + 1)) ∈ (chartAt H (x k)).source := by
      have h := hsrc_s k hk' (c (k + 1) - c k) ⟨(hllpos k hk').le, le_refl _⟩
      rwa [hcll k hk'] at h
    have hsrcj' : γ (c (k + 1)) ∈ (chartAt H (x (k + 1))).source := by
      have h := hsrc_s (k + 1) hk 0 ⟨le_refl _, (hllpos (k + 1) hk).le⟩
      rwa [add_zero] at h
    have h1 : wp k (c (k + 1) - c k)
        = (trivializationAt E (TangentSpace I) (x k)).continuousLinearMapAt ℝ
            (γ (c (k + 1))) (curveVelocity (I := I) γ (c (k + 1))) := by
      have h := hwvel k hk' (c (k + 1) - c k) ⟨(hllpos k hk').le, le_refl _⟩
      rwa [hcll k hk'] at h
    have h2 : wp (k + 1) 0
        = (trivializationAt E (TangentSpace I) (x (k + 1))).continuousLinearMapAt ℝ
            (γ (c (k + 1))) (curveVelocity (I := I) γ (c (k + 1))) := by
      have h := hwvel (k + 1) hk 0 ⟨le_refl _, (hllpos (k + 1) hk).le⟩
      rwa [add_zero] at h
    rw [h1, h2, frameVector_continuousLinearMapAt (I := I) (x k) (γ (c (k + 1))) hsrcj,
      frameVector_continuousLinearMapAt (I := I) (x (k + 1)) (γ (c (k + 1))) hsrcj']
  -- the glued parallel field
  have hNpos : 0 < N := by
    by_contra h
    have h0 : N = 0 := by omega
    rw [h0, hc0] at hcN
    linarith
  obtain ⟨Y, hYode, hYunit, hYorth, hYmatch⟩ :=
    exists_parallel_system (cov := cov) hmet htor hdim hNpos hmono hAB hIcccll hup hwp
      (fun k hk s hs => rfl) hstagIoo hstage hwunit hpt0 hpt1 hmatchvel
  -- the test field of the piece `k` (in the piece-local parameter)
  set ηk : ℕ → ℝ → E := fun k => testFieldS (E := E) L (c k) (Y k) with hηkdef
  set ek : ℕ → ℝ → E := fun k => testFieldSDeriv (E := E) L (c k) (Y k) with hekdef
  set pt : ℕ → ℝ → M := fun k s => (extChartAt I (x k)).symm (up k s) with hptdef
  set ζk : ℕ → ℝ → E := fun k s => - chrB cov (x k) (pt k s) (ηk k s) (ηk k s) with hζkdef
  set ζk' : ℕ → ℝ → E := fun k s =>
    -(dB cov (x k) (pt k s) (wp k s) (ηk k s) (ηk k s)
      + chrB cov (x k) (pt k s) (ek k s) (ηk k s)
      + chrB cov (x k) (pt k s) (ηk k s) (ek k s)) with hζk'def
  have hηk : ∀ k < N, ∀ s ∈ Icc 0 (ll k), HasDerivAt (ηk k) (ek k s) s := by
    intro k hk s hs
    have hYd : HasDerivAt (Y k) (deriv (Y k) s) s := (hYode k hk s hs).differentiableAt.hasDerivAt
    simpa only [ηk, ek] using hasDerivAt_testFieldS (L := L) (a := c k) (Y := Y k) hYd
  have hζk : ∀ k < N, ∀ s ∈ Icc 0 (ll k), HasDerivAt (ζk k) (ζk' k s) s := by
    intro k hk s hs
    have hupd : HasDerivAt (up k) (wp k s) s := hup k hk s (hIcccll k hk hs)
    have hηd : HasDerivAt (ηk k) (ek k s) s := hηk k hk s hs
    have htgt : up k s ∈ (extChartAt I (x k)).target := hstage k hk s hs
    have hstayn : ∀ᶠ r in 𝓝 s, up k r ∈ (extChartAt I (x k)).target :=
      hupd.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_target (x k)).mem_nhds htgt)
    have h := hasDerivAt_chrB_curve (cov := cov) (x₀ := x k) (u := up k) (a := ηk k) (b := ηk k)
      (v := wp k s) (a' := ek k s) (b' := ek k s) hupd hηd hηd htgt hstayn
    show HasDerivAt (fun s : ℝ => -chrB cov (x k) (pt k s) (ηk k s) (ηk k s))
      (-(dB cov (x k) (pt k s) (wp k s) (ηk k s) (ηk k s)
        + chrB cov (x k) (pt k s) (ek k s) (ηk k s)
        + chrB cov (x k) (pt k s) (ηk k s) (ek k s))) s
    exact h.neg
  have hupC : ∀ k < N, ContinuousOn (up k) (Icc 0 (ll k)) := fun k hk =>
    (HasDerivAt.continuousOn (hup k hk)).mono (hIcccll k hk)
  have hwpC : ∀ k < N, ContinuousOn (wp k) (Icc 0 (ll k)) := fun k hk =>
    (HasDerivAt.continuousOn (hwp k hk)).mono (hIcccll k hk)
  have hptC : ∀ k < N, ContinuousOn (pt k) (Icc 0 (ll k)) := by
    intro k hk
    simpa only [pt] using continuousOn_chartCurve (I := I) (x₀ := x k)
      (hupC k hk) (hstage k hk)
  have hYc : ∀ k < N, ContinuousOn (Y k) (Icc 0 (ll k)) := fun k hk =>
    HasDerivAt.continuousOn (hYode k hk)
  have hηkC : ∀ k < N, ContinuousOn (ηk k) (Icc 0 (ll k)) := by
    intro k hk
    have hcoef : ContinuousOn (fun s : ℝ => Real.sin (Real.pi * (c k + s) / L)) (Icc 0 (ll k)) :=
      Real.continuous_sin.comp_continuousOn
        ((continuousOn_const.mul (continuousOn_const.add continuousOn_id)).div_const L)
    exact ContinuousOn.congr (g := ηk k) (hcoef.smul (hYc k hk)) (fun s hs => rfl)
  have hekC : ∀ k < N, ContinuousOn (ek k) (Icc 0 (ll k)) := by
    intro k hk
    have hcoef : ContinuousOn (fun s : ℝ => Real.pi / L * Real.cos (Real.pi * (c k + s) / L))
        (Icc 0 (ll k)) :=
      continuousOn_const.mul (Real.continuous_cos.comp_continuousOn
        ((continuousOn_const.mul (continuousOn_const.add continuousOn_id)).div_const L))
    have hcoef2 : ContinuousOn (fun s : ℝ => Real.sin (Real.pi * (c k + s) / L)) (Icc 0 (ll k)) :=
      Real.continuous_sin.comp_continuousOn
        ((continuousOn_const.mul (continuousOn_const.add continuousOn_id)).div_const L)
    have hclm : ContinuousOn (fun s : ℝ => (christoffelLM cov (x k) (pt k s)
        (frameVector (I := I) (x k) (pt k s) (wp k s))) (Y k s)) (Icc 0 (ll k)) :=
      ((Submission.JacobiGen.continuousOn_christoffelLM_along_Ioo (cov := cov) htor
        (hstagIoo k hk) (hup k hk) (hwpchart k hk)).mono (hIcccll k hk)).clm_apply (hYc k hk)
    have hder : ContinuousOn (fun s : ℝ => deriv (Y k) s) (Icc 0 (ll k)) :=
      ContinuousOn.congr (g := fun s : ℝ => deriv (Y k) s) hclm.neg
        (fun s hs => ((hYode k hk s hs).deriv).trans rfl)
    exact ContinuousOn.congr (g := ek k) ((hcoef.smul (hYc k hk)).add (hcoef2.smul hder))
      (fun s hs => rfl)
  have hζk'C : ∀ k < N, ContinuousOn (ζk' k) (Icc 0 (ll k)) := by
    intro k hk
    have hmem : ∀ s ∈ Icc 0 (ll k), pt k s ∈ (chartAt H (x k)).source :=
      fun s hs => mem_source_chartCurve (I := I) (hstage k hk s hs)
    have h1 : ContinuousOn (fun s : ℝ => dB cov (x k) (pt k s) (wp k s) (ηk k s) (ηk k s))
        (Icc 0 (ll k)) :=
      continuousOn_dB_curve (cov := cov) (hptC k hk) ((HasDerivAt.continuousOn (hwp k hk)).mono (hIcccll k hk))
        (hηkC k hk) (hηkC k hk) hmem
    have h2 : ContinuousOn (fun s : ℝ => chrB cov (x k) (pt k s) (ek k s) (ηk k s))
        (Icc 0 (ll k)) :=
      continuousOn_chrB_curve (cov := cov) (hptC k hk) (hekC k hk) (hηkC k hk) hmem
    have h3 : ContinuousOn (fun s : ℝ => chrB cov (x k) (pt k s) (ηk k s) (ek k s))
        (Icc 0 (ll k)) :=
      continuousOn_chrB_curve (cov := cov) (hptC k hk) (hηkC k hk) (hekC k hk) hmem
    exact ContinuousOn.congr (g := ζk' k) ((h1.add h2).add h3).neg (fun s hs => rfl)
  -- `fam2A` vanishes identically, by construction of `ζ`
  have hA0 : ∀ k < N, ∀ t : ℝ, fam2A (cov := cov) (x k) (up k) (ηk k) (ζk k) t = 0 := by
    intro k hk t
    simp only [fam2A, ζk]
    rw [neg_add_cancel]
  -- the parallel ODE, in the `chrB` form
  have hYpar : ∀ k < N, ∀ s ∈ Icc 0 (ll k),
      deriv (Y k) s + chrB cov (x k) (pt k s) (Y k s) (wp k s) = 0 := by
    intro k hk s hs
    rw [(hYode k hk s hs).deriv,
      christoffelLM_apply (cov := cov) (p := pt k s)
        (w := frameVector (I := I) (x k) (pt k s) (wp k s))
        (mem_source_chartCurve (I := I) (hstage k hk s hs)) (Y k s),
      chrB_apply]
    abel
  -- the pointwise index-form bound
  have hpoint : ∀ k < N, ∀ s ∈ Icc 0 (ll k),
      Real.sin (Real.pi * (c k + s) / L) ^ 2
          - (Real.pi / L * Real.cos (Real.pi * (c k + s) / L)) ^ 2
        ≤ indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) s := by
    intro k hk s hs
    have h := indexIntegrand_testFieldS_pointwise (cov := cov)
      (hcov := ‹ContMDiffCovariantDerivative cov ∞›)
      hmet htor hpinch (x₀ := x k) (u := up k) (w := wp k) (Y := Y k) (L := L) (a := c k)
      (t := s) (mem_source_chartCurve (I := I) (hstage k hk s hs))
      (hYunit k hk s hs) (hYorth k hk s hs) (hwunit k hk s hs) (hYpar k hk s hs)
    simpa only [ηk, ek] using h
  have hζkC : ∀ k < N, ContinuousOn (ζk k) (Icc 0 (ll k)) := by
    intro k hk
    have hmem : ∀ s ∈ Icc 0 (ll k), pt k s ∈ (chartAt H (x k)).source :=
      fun s hs => mem_source_chartCurve (I := I) (hstage k hk s hs)
    exact ContinuousOn.congr (g := ζk k)
      (continuousOn_chrB_curve (cov := cov) (hptC k hk) (hηkC k hk) (hηkC k hk) hmem).neg
      (fun s hs => by simp only [ζk, Pi.neg_apply])
  -- margins for the quadratic family of each piece
  have hmarg : ∀ k < N, ∃ a₁ a₂ : ℝ, a₁ < 0 ∧ 0 < a₂ ∧
      ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (0 : ℝ) (ll k),
        fam2 (up k) (ηk k) (ζk k) s t ∈ (extChartAt I (x k)).target := by
    intro k hk
    have hAk : A k - c k < 0 := by linarith [(hAB k hk).1]
    have hBk : ll k < B k - c k := by
      have := (hAB k hk).2; simp only [ll]; linarith
    exact exists_margins_fam2 (I := I) (x₀ := x k) (u := up k) (η := ηk k) (ζ := ζk k)
      (A := A k - c k) (B := B k - c k) (A₀ := 0) (B₀ := ll k)
      hAk hBk (hupC k hk) (hηkC k hk) (hζkC k hk) (hstagIoo k hk)
  -- the energy at `s = 0` is the length of the piece
  have hE0 : ∀ k < N, fam2Energy (I := I) (x k) (up k) (ηk k) (ζk k) (wp k) (ek k) (ζk' k) (ll k) 0
      = ll k := by
    intro k hk
    rw [fam2Energy_eq_fam2G]
    have h1 : ∀ t ∈ Icc (0 : ℝ) (ll k),
        fam2G (I := I) (x k) (up k) (ηk k) (ζk k) (wp k) (ek k) (ζk' k) 0 t = 1 := by
      intro t ht
      simp only [fam2G, fam2Curve, fam2, fam2T, pow_two, zero_mul, zero_div, zero_smul, add_zero]
      exact hwunit k hk t ht
    rw [intervalIntegral.integral_congr (fun t ht => h1 t (by rwa [uIcc_of_le (hllpos k hk).le] at ht)),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  -- the first derivative vanishes at `s = 0`
  have hE1 : ∀ k < N, HasDerivAt (fun s => fam2Energy (I := I) (x k) (up k) (ηk k) (ζk k)
      (wp k) (ek k) (ζk' k) (ll k) s) 0 0 := by
    intro k hk
    obtain ⟨a₁, a₂, ha₁, ha₂, hstay⟩ := hmarg k hk
    have h := fam2Energy_hasDerivAt (cov := cov) hmet (x₀ := x k) (L := ll k)
      (hL := (hllpos k hk).le)
      (u := up k) (η := ηk k) (ζ := ζk k) (w := wp k) (e := ek k) (ζ' := ζk' k) (w' := wp' k)
      (a₁ := a₁) (a₂ := a₂) (δ₁ := a₁ / 2) (δ₂ := a₂ / 2) (s₀ := 0)
      (by linarith) (by linarith) (by linarith) (by linarith)
      (fun t ht => hup k hk t (hIcccll k hk ht)) (fun t ht => hwp k hk t (hIcccll k hk ht))
      (hηk k hk) (hζk k hk) (hekC k hk) (hζk'C k hk)
      (A₀ := 0) (B₀ := ll k) (by exact le_refl 0) (by exact le_refl (ll k)) hstay
    refine h.congr_deriv ?_
    have hzero : (∫ t in (0 : ℝ)..(ll k), chartGram (I := I) (x k)
        (fam2Curve (I := I) (x k) (up k) (ηk k) (ζk k) 0 t)
        (fam2DsT (cov := cov) (x k) (up k) (ηk k) (ζk k) (wp k) (ek k) (ζk' k) 0 t)
        (fam2T (wp k) (ek k) (ζk' k) 0 t)) = 0 := by
      have hpt : ∀ t ∈ Icc (0 : ℝ) (ll k), chartGram (I := I) (x k)
          ((extChartAt I (x k)).symm (up k t))
          (fam2DsT (cov := cov) (x k) (up k) (ηk k) (ζk k) (wp k) (ek k) (ζk' k) 0 t)
          (wp k t) = 0 := by
        intro t ht
        have h1 : fam2DsT (cov := cov) (x k) (up k) (ηk k) (ζk k) (wp k) (ek k) (ζk' k) 0 t
            = (Real.pi / L * Real.cos (Real.pi * (c k + t) / L)) • Y k t := by
          have h2 := covDsP_testFieldS (cov := cov) (htor := htor) (x₀ := x k) (u := up k)
            (w := wp k) (Y := Y k) (L := L) (a := c k) (t := t)
            (mem_source_chartCurve (I := I) (hstage k hk t ht)) (hYpar k hk t ht)
          have h3 : fam2DsT (cov := cov) (x k) (up k) (ηk k) (ζk k) (wp k) (ek k) (ζk' k) 0 t
              = covDsP cov (x k) (up k) (ηk k) (wp k) (ek k) 0 t := by
            simp only [fam2DsT, covDsP, fam2ST, fam2T, fam2S, fam2, famP, fam2Curve, fam,
              zero_smul, zero_div, pow_two, zero_mul, add_zero]
          rw [h3]
          exact h2
        rw [h1, chartGram_smul_fst, hYorth k hk t ht, mul_zero]
      have h2 : ∀ t ∈ Icc (0 : ℝ) (ll k), chartGram (I := I) (x k)
          (fam2Curve (I := I) (x k) (up k) (ηk k) (ζk k) 0 t)
          (fam2DsT (cov := cov) (x k) (up k) (ηk k) (ζk k) (wp k) (ek k) (ζk' k) 0 t)
          (fam2T (wp k) (ek k) (ζk' k) 0 t) = 0 := by
        intro t ht
        have hfam := hpt t ht
        simpa only [fam2Curve, fam2T, fam2, pow_two, zero_mul, zero_div, zero_smul, add_zero]
          using hfam
      rw [intervalIntegral.integral_congr
        (fun t ht => h2 t (by rwa [uIcc_of_le (hllpos k hk).le] at ht)),
        intervalIntegral.integral_zero]
    rw [hzero, mul_zero]
  -- the second derivative is the index form
  have hE2 : ∀ k < N, HasDerivAt (deriv (fun s => fam2Energy (I := I) (x k) (up k) (ηk k) (ζk k)
      (wp k) (ek k) (ζk' k) (ll k) s))
      (-2 * ∫ t in (0 : ℝ)..(ll k), indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) t) 0 := by
    intro k hk
    obtain ⟨a₁, a₂, ha₁, ha₂, hstay⟩ := hmarg k hk
    have h := fam2Energy_second_deriv (cov := cov) hmet htor (x₀ := x k) (L := ll k)
      (hL := hllpos k hk)
      (u := up k) (η := ηk k) (ζ := ζk k) (w := wp k) (e := ek k) (ζ' := ζk' k) (w' := wp' k)
      (a₁ := a₁) (a₂ := a₂) ha₁ ha₂
      (fun t ht => hup k hk t (hIcccll k hk ht)) (fun t ht => hwp k hk t (hIcccll k hk ht))
      (hηk k hk) (hζk k hk) (hekC k hk) (hζk'C k hk) (hgeoeq k hk)
      (A₀ := 0) (B₀ := ll k) (by exact le_refl 0) (by exact le_refl (ll k)) hstay
      (fun t ht => hstage k hk t ht)
    refine h.congr_deriv ?_
    rw [hA0 k hk (ll k), hA0 k hk 0, chartGram_zero_fst, chartGram_zero_fst, sub_self, mul_zero,
      zero_sub]
    ring
  -- the two junction curves of the piece `k`
  set σm : ℕ → ℝ → M := fun k s => fam2Curve (I := I) (x k) (up k) (ηk k) (ζk k) s 0 with hσmdef
  set σp : ℕ → ℝ → M := fun k s => fam2Curve (I := I) (x k) (up k) (ηk k) (ζk k) s (ll k) with hσpdef
  have hσm0 : ∀ k < N, σm k 0 = γ (c k) := by
    intro k hk
    have h1 : fam2 (up k) (ηk k) (ζk k) 0 0 = up k 0 := by
      simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]
    show (extChartAt I (x k)).symm (fam2 (up k) (ηk k) (ζk k) 0 0) = γ (c k)
    rw [h1]
    exact hpt0 k hk
  have hσp0 : ∀ k < N, σp k 0 = γ (c (k + 1)) := by
    intro k hk
    have h1 : fam2 (up k) (ηk k) (ζk k) 0 (ll k) = up k (ll k) := by
      simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]
    show (extChartAt I (x k)).symm (fam2 (up k) (ηk k) (ζk k) 0 (ll k)) = γ (c (k + 1))
    rw [h1]
    exact hpt1' k hk
  -- the smoothness of the junction curves
  have hσsmooth : ∀ k < N, ContMDiffAt 𝓘(ℝ) I ∞ (σp k) 0 ∧ ContMDiffAt 𝓘(ℝ) I ∞ (σm k) 0 := by
    intro k hk
    have hmem : up k (ll k) ∈ (extChartAt I (x k)).target :=
      hstage k hk (ll k) ⟨(hllpos k hk).le, le_refl _⟩
    have hmem0 : up k 0 ∈ (extChartAt I (x k)).target :=
      hstage k hk 0 ⟨le_refl _, (hllpos k hk).le⟩
    have hsym₁ : ContMDiffAt 𝓘(ℝ, E) I ∞ ((extChartAt I (x k)).symm)
        (up k (ll k) + (0 : ℝ) • ηk k (ll k) + ((0 : ℝ) ^ 2 / 2) • ζk k (ll k)) := by
      simpa only [zero_smul, zero_div, zero_mul, pow_two, add_zero] using
        (contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) (x := x k)).contMDiffAt
          ((isOpen_extChartAt_target (x k)).mem_nhds hmem)
    have hsym₀ : ContMDiffAt 𝓘(ℝ, E) I ∞ ((extChartAt I (x k)).symm)
        (up k 0 + (0 : ℝ) • ηk k 0 + ((0 : ℝ) ^ 2 / 2) • ζk k 0) := by
      simpa only [zero_smul, zero_div, zero_mul, pow_two, add_zero] using
        (contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) (x := x k)).contMDiffAt
          ((isOpen_extChartAt_target (x k)).mem_nhds hmem0)
    have hcd₁ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => up k (ll k) + s • ηk k (ll k)
        + (s ^ 2 / 2) • ζk k (ll k)) 0 :=
      contMDiffAt_iff_contDiffAt.mpr (by fun_prop)
    have hcd₀ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => up k 0 + s • ηk k 0
        + (s ^ 2 / 2) • ζk k 0) 0 :=
      contMDiffAt_iff_contDiffAt.mpr (by fun_prop)
    constructor
    · show ContMDiffAt 𝓘(ℝ) I ∞ (fun s : ℝ => (extChartAt I (x k)).symm
        (up k (ll k) + s • ηk k (ll k) + (s ^ 2 / 2) • ζk k (ll k))) 0
      exact ContMDiffAt.comp 0 hsym₁ hcd₁
    · show ContMDiffAt 𝓘(ℝ) I ∞ (fun s : ℝ => (extChartAt I (x k)).symm
        (up k 0 + s • ηk k 0 + (s ^ 2 / 2) • ζk k 0)) 0
      exact ContMDiffAt.comp 0 hsym₀ hcd₀
  -- the velocity of the two junction curves
  have hσvelL : ∀ k, k + 1 < N → curveVelocity (I := I) (σp k) 0
      = frameVector (I := I) (x k) (σp k 0) (ηk k (ll k)) := by
    intro k hk
    have hk' : k < N := by omega
    have hmem₁ : (fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) 0
        ∈ (extChartAt I (x k)).target := by
      rw [show (fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) 0 = up k (ll k) from by
        simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
      exact hstage k hk' (ll k) ⟨(hllpos k hk').le, le_refl _⟩
    have hu := hasDerivAt_fam2_s (up k) (ηk k) (ζk k) 0 (ll k)
    have h := curveVelocity_extChartAt_symm (I := I) (x₀ := x k)
      (u := fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) (t := 0)
      (v := fam2S (ηk k) (ζk k) 0 (ll k)) hu hmem₁
      (hu.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_target (x k)).mem_nhds hmem₁))
    have hv : fam2S (ηk k) (ζk k) 0 (ll k) = ηk k (ll k) := by
      simp only [fam2S, zero_smul, add_zero]
    rw [hv] at h
    exact h
  have hσvelR : ∀ k, k + 1 < N → curveVelocity (I := I) (σm (k + 1)) 0
      = frameVector (I := I) (x (k + 1)) (σm (k + 1) 0) (ηk (k + 1) 0) := by
    intro k hk
    have hmem₂ : (fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) 0
        ∈ (extChartAt I (x (k + 1))).target := by
      rw [show (fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) 0 = up (k + 1) 0
          from by simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
      exact hstage (k + 1) hk 0 ⟨le_refl _, (hllpos (k + 1) hk).le⟩
    have hu := hasDerivAt_fam2_s (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) 0 0
    have h := curveVelocity_extChartAt_symm (I := I) (x₀ := x (k + 1))
      (u := fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) (t := 0)
      (v := fam2S (ηk (k + 1)) (ζk (k + 1)) 0 0) hu hmem₂
      (hu.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target (x (k + 1))).mem_nhds hmem₂))
    have hv : fam2S (ηk (k + 1)) (ζk (k + 1)) 0 0 = ηk (k + 1) 0 := by
      simp only [fam2S, zero_smul, add_zero]
    rw [hv] at h
    exact h
  have hσvel : ∀ k, k + 1 < N →
      curveVelocity (I := I) (σp k) 0 = curveVelocity (I := I) (σm (k + 1)) 0 := by
    intro k hk
    have hk' : k < N := by omega
    rw [hσvelL k hk, hσvelR k hk, hσp0 k hk', hσm0 (k + 1) hk]
    have h1 : ηk k (ll k) = Real.sin (Real.pi * c (k + 1) / L) • Y k (ll k) := by
      simp only [ηk, testFieldS]
      rw [hcll k hk']
    have h2 : ηk (k + 1) 0 = Real.sin (Real.pi * c (k + 1) / L) • Y (k + 1) 0 := by
      simp only [ηk, testFieldS, add_zero]
    rw [h1, h2, frameVector_smul, frameVector_smul, hYmatch k hk]
  have hsinpos : ∀ k, k + 1 < N → 0 < Real.sin (Real.pi * c (k + 1) / L) := by
    intro k hk
    have hpos : 0 < c (k + 1) := by
      rw [← hc0]
      exact hcstrict (k + 1) (by omega) 0 (by omega)
    have hlt : c (k + 1) < L := by
      rw [← hcN]
      exact hcstrict N le_rfl (k + 1) hk
    refine Real.sin_pos_of_pos_of_lt_pi (div_pos (mul_pos Real.pi_pos hpos) hL) ?_
    rw [div_lt_iff₀ hL]
    exact mul_lt_mul_of_pos_left hlt Real.pi_pos
  -- the covariant acceleration of each junction curve vanishes
  have haccL : ∀ k, k + 1 < N → ∀ (Z : Π x : M, TangentSpace I x), CMDiff ∞ (T% Z) →
      (∀ᶠ r in 𝓝 (0:ℝ), Z (σp k r) = curveVelocity (I := I) (σp k) r) →
      cov Z (σp k 0) (curveVelocity (I := I) (σp k) 0) = 0 := by
    intro k hk Z hZ hev
    have hk' : k < N := by omega
    haveI : Nontrivial E := (Module.finrank_pos_iff (R := ℝ) (M := E)).mp
      (by omega : 0 < Module.finrank ℝ E)
    have hmem₁ : (fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) 0
        ∈ (extChartAt I (x k)).target := by
      rw [show (fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) 0 = up k (ll k) from by
        simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
      exact hstage k hk' (ll k) ⟨(hllpos k hk').le, le_refl _⟩
    have hptL : (extChartAt I (x k)).symm (fam2 (up k) (ηk k) (ζk k) 0 (ll k)) = γ (c (k + 1)) := by
      rw [show fam2 (up k) (ηk k) (ζk k) 0 (ll k) = up k (ll k) from by
        simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
      exact hpt1' k hk'
    -- the section
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
      ((hasDerivAt_fam2_s (up k) (ηk k) (ζk k) 0 (ll k)).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target (x k)).mem_nhds hmem₁))
    have hmemδ : ∀ r ∈ Ioo (-δ) δ, (fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) r
        ∈ (extChartAt I (x k)).target := fun r hr => hδsub (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨hr.1, hr.2⟩)
    have hcd : ContDiff ℝ ∞ (fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) := by
      simp only [fam2]
      fun_prop
    have hγon : ContMDiffOn 𝓘(ℝ) I ∞ (σp k) (Ioo (-δ) δ) :=
      (contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) (x := x k)).comp
        (contMDiffOn_iff_contDiffOn.mpr hcd.contDiffOn) hmemδ
    have hsrcon : ∀ r ∈ Ioo (-δ) δ, σp k r ∈ (chartAt H (x k)).source :=
      fun r hr => mem_source_chartCurve (I := I) (hmemδ r hr)
    have hy : ContDiffOn ℝ ∞ (fun σ : ℝ => fam2S (ηk k) (ζk k) σ (ll k))
        ((Ioo (-δ) δ) ∩ σp k ⁻¹' (chartAt H (x k)).source) := by
      have h : ContDiff ℝ ∞ (fun σ : ℝ => fam2S (ηk k) (ζk k) σ (ll k)) := by
        simp only [fam2S]
        fun_prop
      exact h.contDiffOn
    have hev' : ∀ᶠ r in 𝓝 (0 : ℝ), Z (σp k r)
        = frameVector (I := I) (x k) (σp k r) (fam2S (ηk k) (ζk k) r (ll k)) := by
      filter_upwards [hev, isOpen_Ioo.mem_nhds (show (0:ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)]
        with r hr hrr
      rw [hr]
      exact curveVelocity_extChartAt_symm (I := I) (x₀ := x k)
        (u := fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) (t := r)
        (v := fam2S (ηk k) (ζk k) r (ll k)) (hasDerivAt_fam2_s (up k) (ηk k) (ζk k) r (ll k))
        (hmemδ r hrr)
        ((hasDerivAt_fam2_s (up k) (ηk k) (ζk k) r (ll k)).continuousAt.preimage_mem_nhds
          ((isOpen_extChartAt_target (x k)).mem_nhds (hmemδ r hrr)))
    have hZeq := Submission.CurveCov.cov_eq_frameVector_chartCoord (cov := cov)
      (x₀ := x k) (γ := σp k) (t₀ := 0) (hγmd := mdifferentiableAt_chartCurve (I := I)
        (hasDerivAt_fam2_s (up k) (ηk k) (ζk k) 0 (ll k)) hmem₁
        ((hasDerivAt_fam2_s (up k) (ηk k) (ζk k) 0 (ll k)).continuousAt.preimage_mem_nhds
          ((isOpen_extChartAt_target (x k)).mem_nhds hmem₁)))
      (hsrc := mem_source_chartCurve (I := I) hmem₁) (y := fun σ : ℝ => fam2S (ηk k) (ζk k) σ (ll k))
      hZ hev'
    rw [hZeq]
    have hclm : (trivializationAt E (TangentSpace I) (x k)).continuousLinearMapAt ℝ (σp k 0)
        (curveVelocity (I := I) (σp k) 0) = ηk k (ll k) := by
      rw [hσvelL k hk]
      exact continuousLinearMapAt_frameVector (I := I) (x k) (σp k 0)
        (mem_source_chartCurve (I := I) hmem₁) (ηk k (ll k))
    have hdv : deriv (fun σ : ℝ => fam2S (ηk k) (ζk k) σ (ll k)) 0 = ζk k (ll k) := by
      simpa only [zero_smul, add_zero] using (hasDerivAt_fam2S_s (ηk k) (ζk k) 0 (ll k)).deriv
    have hy0 : fam2S (ηk k) (ζk k) 0 (ll k) = ηk k (ll k) := by
      simp only [fam2S, zero_smul, add_zero]
    have hzeta : ζk k (ll k) = -chrB cov (x k) (σp k 0) (ηk k (ll k)) (ηk k (ll k)) := by
      have h1 : fam2 (up k) (ηk k) (ζk k) 0 (ll k) = up k (ll k) := by
        simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]
      simp only [ζk, pt, σp, fam2Curve, h1]
    rw [hclm, hdv, hy0, hzeta, neg_add_cancel]
    exact frameVector_zero _ _
  have haccR : ∀ k, k + 1 < N → ∀ (Z : Π x : M, TangentSpace I x), CMDiff ∞ (T% Z) →
      (∀ᶠ r in 𝓝 (0:ℝ), Z (σm (k + 1) r) = curveVelocity (I := I) (σm (k + 1)) r) →
      cov Z (σm (k + 1) 0) (curveVelocity (I := I) (σm (k + 1)) 0) = 0 := by
    intro k hk Z hZ hev
    have hmem₂ : (fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) 0
        ∈ (extChartAt I (x (k + 1))).target := by
      rw [show (fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) 0 = up (k + 1) 0
          from by simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
      exact hstage (k + 1) hk 0 ⟨le_refl _, (hllpos (k + 1) hk).le⟩
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
      ((hasDerivAt_fam2_s (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) 0 0).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target (x (k + 1))).mem_nhds hmem₂))
    have hmemδ : ∀ r ∈ Ioo (-δ) δ,
        (fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) r
          ∈ (extChartAt I (x (k + 1))).target := fun r hr => hδsub (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨hr.1, hr.2⟩)
    have hcd : ContDiff ℝ ∞ (fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) := by
      simp only [fam2]
      fun_prop
    have hγon : ContMDiffOn 𝓘(ℝ) I ∞ (σm (k + 1)) (Ioo (-δ) δ) :=
      (contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) (x := x (k + 1))).comp
        (contMDiffOn_iff_contDiffOn.mpr hcd.contDiffOn) hmemδ
    have hsrcon : ∀ r ∈ Ioo (-δ) δ, σm (k + 1) r ∈ (chartAt H (x (k + 1))).source :=
      fun r hr => mem_source_chartCurve (I := I) (hmemδ r hr)
    have hy : ContDiffOn ℝ ∞ (fun σ : ℝ => fam2S (ηk (k + 1)) (ζk (k + 1)) σ 0)
        ((Ioo (-δ) δ) ∩ σm (k + 1) ⁻¹' (chartAt H (x (k + 1))).source) := by
      have h : ContDiff ℝ ∞ (fun σ : ℝ => fam2S (ηk (k + 1)) (ζk (k + 1)) σ 0) := by
        simp only [fam2S]
        fun_prop
      exact h.contDiffOn
    have hev' : ∀ᶠ r in 𝓝 (0 : ℝ), Z (σm (k + 1) r)
        = frameVector (I := I) (x (k + 1)) (σm (k + 1) r)
            (fam2S (ηk (k + 1)) (ζk (k + 1)) r 0) := by
      filter_upwards [hev, isOpen_Ioo.mem_nhds (show (0:ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)]
        with r hr hrr
      rw [hr]
      exact curveVelocity_extChartAt_symm (I := I) (x₀ := x (k + 1))
        (u := fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) (t := r)
        (v := fam2S (ηk (k + 1)) (ζk (k + 1)) r 0)
        (hasDerivAt_fam2_s (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) r 0) (hmemδ r hrr)
        ((hasDerivAt_fam2_s (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) r 0).continuousAt.preimage_mem_nhds
          ((isOpen_extChartAt_target (x (k + 1))).mem_nhds (hmemδ r hrr)))
    have hZeq := Submission.CurveCov.cov_eq_frameVector_chartCoord (cov := cov)
      (x₀ := x (k + 1)) (γ := σm (k + 1)) (t₀ := 0) (hγmd := mdifferentiableAt_chartCurve (I := I)
        (hasDerivAt_fam2_s (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) 0 0) hmem₂
        ((hasDerivAt_fam2_s (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) 0 0).continuousAt.preimage_mem_nhds
          ((isOpen_extChartAt_target (x (k + 1))).mem_nhds hmem₂)))
      (hsrc := mem_source_chartCurve (I := I) hmem₂)
      (y := fun σ : ℝ => fam2S (ηk (k + 1)) (ζk (k + 1)) σ 0) hZ hev'
    rw [hZeq]
    have hclm : (trivializationAt E (TangentSpace I) (x (k + 1))).continuousLinearMapAt ℝ
        (σm (k + 1) 0) (curveVelocity (I := I) (σm (k + 1)) 0) = ηk (k + 1) 0 := by
      rw [hσvelR k hk]
      exact continuousLinearMapAt_frameVector (I := I) (x (k + 1)) (σm (k + 1) 0)
        (mem_source_chartCurve (I := I) hmem₂) (ηk (k + 1) 0)
    have hdv : deriv (fun σ : ℝ => fam2S (ηk (k + 1)) (ζk (k + 1)) σ 0) 0 = ζk (k + 1) 0 := by
      simpa only [zero_smul, add_zero] using (hasDerivAt_fam2S_s (ηk (k + 1)) (ζk (k + 1)) 0 0).deriv
    have hy0 : fam2S (ηk (k + 1)) (ζk (k + 1)) 0 0 = ηk (k + 1) 0 := by
      simp only [fam2S, zero_smul, add_zero]
    have hzeta : ζk (k + 1) 0 = -chrB cov (x (k + 1)) (σm (k + 1) 0)
        (ηk (k + 1) 0) (ηk (k + 1) 0) := by
      have h1 : fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) 0 0 = up (k + 1) 0 := by
        simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]
      simp only [ζk, pt, σm, fam2Curve, h1]
    rw [hclm, hdv, hy0, hzeta, neg_add_cancel]
    exact frameVector_zero _ _
  -- the section of each junction curve
  have hsecL : ∀ k, k + 1 < N → ∃ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) ∧
      (∀ᶠ r in 𝓝 (0:ℝ), Z (σp k r) = curveVelocity (I := I) (σp k) r) := by
    intro k hk
    have hk' : k < N := by omega
    have hmem₁ : (fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) 0
        ∈ (extChartAt I (x k)).target := by
      rw [show (fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) 0 = up k (ll k) from by
        simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
      exact hstage k hk' (ll k) ⟨(hllpos k hk').le, le_refl _⟩
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
      ((hasDerivAt_fam2_s (up k) (ηk k) (ζk k) 0 (ll k)).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target (x k)).mem_nhds hmem₁))
    have hmemδ : ∀ r ∈ Ioo (-δ) δ, (fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) r
        ∈ (extChartAt I (x k)).target := fun r hr => hδsub (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨hr.1, hr.2⟩)
    have hcd : ContDiff ℝ ∞ (fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) := by
      simp only [fam2]
      fun_prop
    have hγon : ContMDiffOn 𝓘(ℝ) I ∞ (σp k) (Ioo (-δ) δ) :=
      (contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) (x := x k)).comp
        (contMDiffOn_iff_contDiffOn.mpr hcd.contDiffOn) hmemδ
    have hsrcon : ∀ r ∈ Ioo (-δ) δ, σp k r ∈ (chartAt H (x k)).source :=
      fun r hr => mem_source_chartCurve (I := I) (hmemδ r hr)
    have hy : ContDiffOn ℝ ∞ (fun σ : ℝ => fam2S (ηk k) (ζk k) σ (ll k))
        ((Ioo (-δ) δ) ∩ σp k ⁻¹' (chartAt H (x k)).source) := by
      have h : ContDiff ℝ ∞ (fun σ : ℝ => fam2S (ηk k) (ζk k) σ (ll k)) := by
        simp only [fam2S]
        fun_prop
      exact h.contDiffOn
    have hne : curveVelocity (I := I) (σp k) 0 ≠ 0 := by
      intro h0
      have hcs : curveSpeed (I := I) (σp k) 0 = 0 := by
        rw [curveSpeed_eq_norm, h0, norm_zero]
      have hsp : curveSpeed (I := I) (σp k) 0
          = Real.sqrt (chartGram (I := I) (x k) (σp k 0) (ηk k (ll k)) (ηk k (ll k))) := by
        have h := curveSpeed_chartCurve (I := I) (x₀ := x k)
          (u := fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) (t := 0)
          (v := fam2S (ηk k) (ζk k) 0 (ll k)) (hasDerivAt_fam2_s (up k) (ηk k) (ζk k) 0 (ll k))
          hmem₁ ((hasDerivAt_fam2_s (up k) (ηk k) (ζk k) 0 (ll k)).continuousAt.preimage_mem_nhds
            ((isOpen_extChartAt_target (x k)).mem_nhds hmem₁))
        rw [show fam2S (ηk k) (ζk k) 0 (ll k) = ηk k (ll k) from by
          simp only [fam2S, zero_smul, add_zero]] at h
        exact h
      have hval : chartGram (I := I) (x k) (σp k 0) (ηk k (ll k)) (ηk k (ll k))
          = (Real.sin (Real.pi * c (k + 1) / L)) ^ 2 := by
        have h2 : ηk k (ll k) = Real.sin (Real.pi * c (k + 1) / L) • Y k (ll k) := by
          simp only [ηk, testFieldS]
          rw [hcll k hk']
        rw [h2, chartGram_smul_smul]
        have hYu : chartGram (I := I) (x k) (σp k 0) (Y k (ll k)) (Y k (ll k)) = 1 := by
          have h2c : σp k 0 = (extChartAt I (x k)).symm (up k (ll k)) := by
            rw [show σp k 0 = (extChartAt I (x k)).symm (fam2 (up k) (ηk k) (ζk k) 0 (ll k))
              from rfl]
            rw [show fam2 (up k) (ηk k) (ζk k) 0 (ll k) = up k (ll k) from by
              simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
          rw [h2c]
          exact hYunit k hk' (ll k) ⟨(hllpos k hk').le, le_refl _⟩
        rw [hYu, mul_one]
      rw [hsp, hval, Real.sqrt_sq_eq_abs] at hcs
      exact absurd hcs (ne_of_gt (abs_pos.mpr (ne_of_gt (hsinpos k hk))))
    obtain ⟨Z, hZ, hev, -⟩ := Submission.CurveCov.exists_section_and_cov_eq (cov := cov)
      (x₀ := x k) (γ := σp k) (V := Ioo (-δ) δ) isOpen_Ioo (t₀ := 0)
      (show (0:ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩) hγon hsrcon hne hy
    refine ⟨Z, hZ, ?_⟩
    filter_upwards [hev, isOpen_Ioo.mem_nhds (show (0:ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)]
      with r hr hrr
    rw [hr]
    exact (curveVelocity_extChartAt_symm (I := I) (x₀ := x k)
      (u := fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) (t := r)
      (v := fam2S (ηk k) (ζk k) r (ll k)) (hasDerivAt_fam2_s (up k) (ηk k) (ζk k) r (ll k))
      (hmemδ r hrr)
      ((hasDerivAt_fam2_s (up k) (ηk k) (ζk k) r (ll k)).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target (x k)).mem_nhds (hmemδ r hrr)))).symm
  have hsecR : ∀ k, k + 1 < N → ∃ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) ∧
      (∀ᶠ r in 𝓝 (0:ℝ), Z (σm (k + 1) r) = curveVelocity (I := I) (σm (k + 1)) r) := by
    intro k hk
    have hmem₂ : (fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) 0
        ∈ (extChartAt I (x (k + 1))).target := by
      rw [show (fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) 0 = up (k + 1) 0
          from by simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
      exact hstage (k + 1) hk 0 ⟨le_refl _, (hllpos (k + 1) hk).le⟩
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
      ((hasDerivAt_fam2_s (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) 0 0).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target (x (k + 1))).mem_nhds hmem₂))
    have hmemδ : ∀ r ∈ Ioo (-δ) δ,
        (fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) r
          ∈ (extChartAt I (x (k + 1))).target := fun r hr => hδsub (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨hr.1, hr.2⟩)
    have hcd : ContDiff ℝ ∞ (fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) := by
      simp only [fam2]
      fun_prop
    have hγon : ContMDiffOn 𝓘(ℝ) I ∞ (σm (k + 1)) (Ioo (-δ) δ) :=
      (contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) (x := x (k + 1))).comp
        (contMDiffOn_iff_contDiffOn.mpr hcd.contDiffOn) hmemδ
    have hsrcon : ∀ r ∈ Ioo (-δ) δ, σm (k + 1) r ∈ (chartAt H (x (k + 1))).source :=
      fun r hr => mem_source_chartCurve (I := I) (hmemδ r hr)
    have hy : ContDiffOn ℝ ∞ (fun σ : ℝ => fam2S (ηk (k + 1)) (ζk (k + 1)) σ 0)
        ((Ioo (-δ) δ) ∩ σm (k + 1) ⁻¹' (chartAt H (x (k + 1))).source) := by
      have h : ContDiff ℝ ∞ (fun σ : ℝ => fam2S (ηk (k + 1)) (ζk (k + 1)) σ 0) := by
        simp only [fam2S]
        fun_prop
      exact h.contDiffOn
    have hne : curveVelocity (I := I) (σm (k + 1)) 0 ≠ 0 := by
      rw [← hσvel k hk]
      intro h0
      have hcs : curveSpeed (I := I) (σp k) 0 = 0 := by
        rw [curveSpeed_eq_norm, h0]
        exact norm_zero
      have hsp : curveSpeed (I := I) (σp k) 0
          = Real.sqrt (chartGram (I := I) (x k) (σp k 0) (ηk k (ll k)) (ηk k (ll k))) := by
        have h := curveSpeed_chartCurve (I := I) (x₀ := x k)
          (u := fun σ : ℝ => fam2 (up k) (ηk k) (ζk k) σ (ll k)) (t := 0)
          (v := fam2S (ηk k) (ζk k) 0 (ll k)) (hasDerivAt_fam2_s (up k) (ηk k) (ζk k) 0 (ll k))
          (by
            rw [show fam2 (up k) (ηk k) (ζk k) 0 (ll k) = up k (ll k) from by
              simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
            exact hstage k (by omega) (ll k) ⟨(hllpos k (by omega)).le, le_refl _⟩)
          ((hasDerivAt_fam2_s (up k) (ηk k) (ζk k) 0 (ll k)).continuousAt.preimage_mem_nhds
            ((isOpen_extChartAt_target (x k)).mem_nhds (by
              rw [show fam2 (up k) (ηk k) (ζk k) 0 (ll k) = up k (ll k) from by
                simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
              exact hstage k (by omega) (ll k) ⟨(hllpos k (by omega)).le, le_refl _⟩)))
        rw [show fam2S (ηk k) (ζk k) 0 (ll k) = ηk k (ll k) from by
          simp only [fam2S, zero_smul, add_zero]] at h
        exact h
      have hval : chartGram (I := I) (x k) (σp k 0) (ηk k (ll k)) (ηk k (ll k))
          = (Real.sin (Real.pi * c (k + 1) / L)) ^ 2 := by
        have h2 : ηk k (ll k) = Real.sin (Real.pi * c (k + 1) / L) • Y k (ll k) := by
          simp only [ηk, testFieldS]
          rw [hcll k (by omega)]
        rw [h2, chartGram_smul_smul]
        have hYu : chartGram (I := I) (x k) (σp k 0) (Y k (ll k)) (Y k (ll k)) = 1 := by
          have h2c : σp k 0 = (extChartAt I (x k)).symm (up k (ll k)) := by
            rw [show σp k 0 = (extChartAt I (x k)).symm (fam2 (up k) (ηk k) (ζk k) 0 (ll k))
              from rfl]
            rw [show fam2 (up k) (ηk k) (ζk k) 0 (ll k) = up k (ll k) from by
              simp only [fam2, zero_smul, zero_div, zero_mul, pow_two, add_zero]]
          rw [h2c]
          exact hYunit k (by omega) (ll k) ⟨(hllpos k (by omega)).le, le_refl _⟩
        rw [hYu, mul_one]
      rw [hsp, hval, Real.sqrt_sq_eq_abs] at hcs
      exact absurd hcs (ne_of_gt (abs_pos.mpr (ne_of_gt (hsinpos k hk))))
    obtain ⟨Z, hZ, hev, -⟩ := Submission.CurveCov.exists_section_and_cov_eq (cov := cov)
      (x₀ := x (k + 1)) (γ := σm (k + 1)) (V := Ioo (-δ) δ) isOpen_Ioo (t₀ := 0)
      (show (0:ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩) hγon hsrcon hne hy
    refine ⟨Z, hZ, ?_⟩
    filter_upwards [hev, isOpen_Ioo.mem_nhds (show (0:ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)]
      with r hr hrr
    rw [hr]
    exact (curveVelocity_extChartAt_symm (I := I) (x₀ := x (k + 1))
      (u := fun σ : ℝ => fam2 (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) σ 0) (t := r)
      (v := fam2S (ηk (k + 1)) (ζk (k + 1)) r 0)
      (hasDerivAt_fam2_s (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) r 0) (hmemδ r hrr)
      ((hasDerivAt_fam2_s (up (k + 1)) (ηk (k + 1)) (ζk (k + 1)) r 0).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target (x (k + 1))).mem_nhds (hmemδ r hrr)))).symm
  -- the junction gap
  have hgap : ∀ k, k + 1 < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in 𝓝 (0 : ℝ),
      Manifold.riemannianEDist I (σp k s) (σm (k + 1) s) ≤ ENNReal.ofReal (C * |s| ^ 3) := by
    intro k hk
    haveI : Nontrivial E := (Module.finrank_pos_iff (R := ℝ) (M := E)).mp
      (by omega : 0 < Module.finrank ℝ E)
    obtain ⟨Z₁, hZ₁, hev₁⟩ := hsecL k hk
    obtain ⟨Z₂, hZ₂, hev₂⟩ := hsecR k hk
    refine Submission.JetGap.riemannianEDist_le_cube_of_jet (cov := cov)
      (σ₁ := σp k) (σ₂ := σm (k + 1)) (hσsmooth k (by omega)).1 (hσsmooth (k + 1) hk).2
      ?_ (hσvel k hk) hZ₁ hZ₂ hev₁ hev₂ ?_
    · rw [hσp0 k (by omega), hσm0 (k + 1) hk]
    · rw [haccL k hk Z₁ hZ₁ hev₁, haccR k hk Z₂ hZ₂ hev₂]
      try rfl
  -- the total energy
  set Efun : ℕ → ℝ → ℝ := fun k s =>
    fam2Energy (I := I) (x k) (up k) (ηk k) (ζk k) (wp k) (ek k) (ζk' k) (ll k) s with hEfundef
  set Ftot : ℝ → ℝ := fun s => ∑ k ∈ Finset.range N, Efun k s with hFtotdef
  set ff : ℝ → ℝ := fun t => Real.sin (Real.pi * t / L) ^ 2
    - (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2 with hffdef
  have hllsum : (∑ k ∈ Finset.range N, ll k) = L := by
    have h2 := Finset.sum_range_sub c N
    rw [show (∑ k ∈ Finset.range N, ll k) = ∑ k ∈ Finset.range N, (c (k + 1) - c k) from
      Finset.sum_congr rfl (fun k _ => rfl), h2, hcN, hc0, sub_zero]
  -- the energy at `0` is `L`
  have hF0 : Ftot 0 = L := by
    have h1 : ∀ k ∈ Finset.range N, Efun k 0 = ll k := fun k hk => hE0 k (Finset.mem_range.mp hk)
    show (∑ k ∈ Finset.range N, Efun k 0) = L
    rw [Finset.sum_congr rfl h1]
    rw [hllsum]
  -- the first derivative at `0` vanishes
  have hF1 : HasDerivAt Ftot 0 0 := by
    have h := HasDerivAt.sum (u := Finset.range N) (A := Efun) (A' := fun _ => (0:ℝ))
      (fun k hk => hE1 k (Finset.mem_range.mp hk))
    have hfun : (∑ k ∈ Finset.range N, Efun k)
        = fun s : ℝ => ∑ k ∈ Finset.range N, Efun k s := by
      funext s; rw [Finset.sum_apply]
    have h' : HasDerivAt Ftot (∑ _k ∈ Finset.range N, (0:ℝ)) 0 := by
      rw [hFtotdef, ← hfun]
      exact h
    simpa using h'
  -- the second derivative at `0`
  have hF2 : HasDerivAt (deriv Ftot)
      (∑ k ∈ Finset.range N, (-2 * ∫ t in (0:ℝ)..(ll k),
        indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) t)) 0 := by
    have hmem : ∀ᶠ s in 𝓝 (0:ℝ), ∀ k ∈ Finset.range N, DifferentiableAt ℝ (Efun k) s := by
      rw [Finset.eventually_all]
      intro k hk
      obtain ⟨a₁, a₂, ha₁, ha₂, hstayk⟩ := hmarg k (Finset.mem_range.mp hk)
      have ha₁2 : a₁ / 2 < 0 := by linarith
      have ha₂2 : 0 < a₂ / 2 := by linarith
      filter_upwards [Ioo_mem_nhds ha₁2 ha₂2] with s hs
      exact (fam2Energy_hasDerivAt (cov := cov) hmet (x₀ := x k) (L := ll k)
        (hL := (hllpos k (Finset.mem_range.mp hk)).le)
        (u := up k) (η := ηk k) (ζ := ζk k) (w := wp k) (e := ek k) (ζ' := ζk' k) (w' := wp' k)
        (a₁ := a₁) (a₂ := a₂) (δ₁ := a₁ / 2) (δ₂ := a₂ / 2) (s₀ := s)
        (by linarith [ha₁]) (by linarith [ha₂]) (by linarith [hs.1]) (by linarith [hs.2])
        (fun t ht => hup k (Finset.mem_range.mp hk) t (hIcccll k (Finset.mem_range.mp hk) ht))
        (fun t ht => hwp k (Finset.mem_range.mp hk) t (hIcccll k (Finset.mem_range.mp hk) ht))
        (hηk k (Finset.mem_range.mp hk)) (hζk k (Finset.mem_range.mp hk))
        (hekC k (Finset.mem_range.mp hk)) (hζk'C k (Finset.mem_range.mp hk))
        (A₀ := 0) (B₀ := ll k) (by exact le_refl 0) (by exact le_refl (ll k)) hstayk).differentiableAt
    have hev : deriv Ftot =ᶠ[𝓝 (0:ℝ)]
        (fun s => ∑ k ∈ Finset.range N, deriv (Efun k) s) := by
      filter_upwards [hmem] with s hs
      have hfun : (fun s : ℝ => ∑ k ∈ Finset.range N, Efun k s)
          = (∑ k ∈ Finset.range N, Efun k) := by
        funext s
        rw [Finset.sum_apply]
      rw [hFtotdef, hfun]
      exact deriv_sum (fun k hk => hs k hk)
    refine hev.hasDerivAt_iff.mpr ?_
    have h := HasDerivAt.sum (u := Finset.range N) (A := fun k => deriv (Efun k))
      (A' := fun k => -2 * ∫ t in (0:ℝ)..(ll k),
        indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) t)
      (fun k hk => hE2 k (Finset.mem_range.mp hk))
    have hfun : (∑ k ∈ Finset.range N, deriv (Efun k))
        = fun s : ℝ => ∑ k ∈ Finset.range N, deriv (Efun k) s := by
      funext s
      rw [Finset.sum_apply]
    rw [← hfun]
    exact h
  -- the sum of the index-form integrals is at least `(L^2 - π^2)/(2L)`
  have hint : ∑ k ∈ Finset.range N, (-2 * ∫ t in (0:ℝ)..(ll k),
        indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) t)
      < -2 * ((L ^ 2 - Real.pi ^ 2) / (2 * L)) := by
    have hsubst : ∀ k < N, (∫ t in (0:ℝ)..(ll k), ff (c k + t)) = ∫ t in (c k)..(c (k + 1)), ff t := by
      intro k hk
      have h := intervalIntegral.integral_comp_add_right (f := ff) (a := (0:ℝ)) (b := ll k) (d := c k)
      rw [show (∫ t in (0:ℝ)..(ll k), ff (c k + t)) = ∫ t in (0:ℝ)..(ll k), ff (t + c k) from by
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        rw [add_comm]]
      rw [h, zero_add, add_comm (ll k) (c k), hcll k hk]
    have hffint : ∫ t in (0:ℝ)..L, ff t = (L ^ 2 - Real.pi ^ 2) / (2 * L) := by
      have hcont1 : ContinuousOn (fun t : ℝ => Real.sin (Real.pi * t / L) ^ 2) (Icc 0 L) := by fun_prop
      have hint1 : IntervalIntegrable (fun t : ℝ => Real.sin (Real.pi * t / L) ^ 2) volume 0 L :=
        hcont1.intervalIntegrable_of_Icc hL.le
      have hcont3 : ContinuousOn (fun t : ℝ => (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2)
          (Icc 0 L) := by fun_prop
      have hint3 : IntervalIntegrable (fun t : ℝ => (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2)
          volume 0 L := hcont3.intervalIntegrable_of_Icc hL.le
      have hsin : ∫ t in (0:ℝ)..L, Real.sin (Real.pi * t / L) ^ 2 = L / 2 :=
        Commons.Analysis.Calculus.intervalIntegral_sin_sq_pi_mul_div L hL
      have hcos : ∫ t in (0:ℝ)..L, (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2
          = (Real.pi / L) ^ 2 * (L / 2) := by
        have hfun : (fun t : ℝ => (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2)
            = fun t : ℝ => (Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2 := by
          funext t; ring
        rw [hfun, intervalIntegral.integral_const_mul,
          Commons.Analysis.Calculus.intervalIntegral_cos_sq_pi_mul_div L hL]
      rw [hffdef, intervalIntegral.integral_sub hint1 hint3, hsin, hcos]
      field_simp
    have hsum : ∑ k ∈ Finset.range N, (∫ t in (0:ℝ)..(ll k), ff (c k + t))
        = ∫ t in (0:ℝ)..L, ff t := by
      rw [Finset.sum_congr rfl (fun k hk => hsubst k (Finset.mem_range.mp hk))]
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (a := c) (n := N) (f := ff) (fun k hk => (by
          have hc : ContinuousOn ff (Icc (c k) (c (k+1))) := by
            rw [hffdef]; fun_prop
          exact hc.intervalIntegrable_of_Icc (hcmono k (k+1) (Nat.le_succ k) (by omega))))]
      rw [hc0, hcN]
    have hmono : ∀ k ∈ Finset.range N, (∫ t in (0:ℝ)..(ll k), ff (c k + t))
        < ∫ t in (0:ℝ)..(ll k), indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) t := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hcontR : ContinuousOn (fun t : ℝ => Rt cov (x k) (up k) (ηk k) (wp k) t)
          (Icc 0 (ll k)) :=
        continuousOn_Rt (cov := cov) htor (x₀ := x k) (hupC k hk') (hηkC k hk') (hwpC k hk')
          (fun t ht => hstage k hk' t ht)
      have hptc : ContinuousOn (fun t : ℝ => (extChartAt I (x k)).symm (up k t)) (Icc 0 (ll k)) :=
        continuousOn_chartCurve (I := I) (x₀ := x k) (hupC k hk') (hstage k hk')
      have hcontG : ContinuousOn (fun t : ℝ => Gt cov (x k) (up k) (ηk k) (wp k) (ek k) t)
          (Icc 0 (ll k)) :=
        continuousOn_chartGram_curve (I := I) hptc
          (continuousOn_covDsP_along (I := I) (x₀ := x k) (hupC k hk') (hηkC k hk')
            (hwpC k hk') (hekC k hk') (fun t ht => hstage k hk' t ht))
          (continuousOn_covDsP_along (I := I) (x₀ := x k) (hupC k hk') (hηkC k hk')
            (hwpC k hk') (hekC k hk') (fun t ht => hstage k hk' t ht))
          (fun t ht => mem_source_chartCurve (I := I) (hstage k hk' t ht))
      have hcontI : ContinuousOn (fun t : ℝ => indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) t)
          (Icc 0 (ll k)) :=
        hcontR.sub hcontG
      have hcontff : ContinuousOn (fun t : ℝ => ff (c k + t)) (Icc 0 (ll k)) := by
        rw [hffdef]
        fun_prop
      refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (hllpos k hk') hcontff hcontI (fun t ht => ?_) ?_
      · exact hpoint k hk' t ⟨ht.1.le, ht.2⟩
      · -- a point of the piece where the sine factor is nonzero, hence strictness holds
        have hlk : 0 < ll k := hllpos k hk'
        have hkN : k ≤ N := by omega
        refine ⟨ll k / 2, ⟨by linarith, by linarith⟩, ?_⟩
        have hck0 : 0 ≤ c k := by
          rw [← hc0]; exact hcmono 0 k (Nat.zero_le k) hkN
        have hmid0 : 0 < c k + ll k / 2 := by linarith
        have hmidL : c k + ll k / 2 < L := by
          have h1 : ll k / 2 < ll k := by linarith
          have h2 : c k + ll k = c (k + 1) := hcll k hk'
          have h3 : c (k + 1) ≤ L := by
            rw [← hcN]; exact hcmono (k + 1) N (by omega) (by omega)
          linarith
        have hsin : Real.sin (Real.pi * (c k + ll k / 2) / L) ≠ 0 := by
          have hpos : 0 < Real.pi * (c k + ll k / 2) / L := by positivity
          have hlt : Real.pi * (c k + ll k / 2) / L < Real.pi := by
            rw [div_lt_iff₀ hL]
            nlinarith [Real.pi_pos]
          exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
        have hstr := indexIntegrand_testFieldS_pointwise_strict (cov := cov)
          (hcov := ‹ContMDiffCovariantDerivative cov ∞›)
          hmet htor hpinch (x₀ := x k) (u := up k) (w := wp k) (Y := Y k) (L := L) (a := c k)
          (t := ll k / 2)
          (mem_source_chartCurve (I := I) (hstage k hk' (ll k / 2) ⟨by linarith, by linarith⟩))
          (hYunit k hk' (ll k / 2) ⟨by linarith, by linarith⟩)
          (hYorth k hk' (ll k / 2) ⟨by linarith, by linarith⟩)
          (hwunit k hk' (ll k / 2) ⟨by linarith, by linarith⟩)
          (hYpar k hk' (ll k / 2) ⟨by linarith, by linarith⟩) hsin
        simpa only [ff, hffdef, ηk, ek] using hstr
    calc ∑ k ∈ Finset.range N, (-2 * ∫ t in (0:ℝ)..(ll k),
          indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) t)
        = -2 * ∑ k ∈ Finset.range N, (∫ t in (0:ℝ)..(ll k),
            indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) t) := by
          rw [Finset.mul_sum]
      _ < -2 * ∑ k ∈ Finset.range N, (∫ t in (0:ℝ)..(ll k), ff (c k + t)) := by
          refine mul_lt_mul_of_neg_left ?_ (by norm_num)
          exact Finset.sum_lt_sum (fun k hk => (hmono k hk).le)
            ⟨0, Finset.mem_range.mpr hNpos, hmono 0 (Finset.mem_range.mpr hNpos)⟩
      _ = -2 * ((L ^ 2 - Real.pi ^ 2) / (2 * L)) := by rw [hsum, hffint]
  -- the gap constant, uniform in `k`
  have hgapC : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k + 1 < N → ∀ᶠ s in 𝓝 (0:ℝ),
      Manifold.riemannianEDist I (σp k s) (σm (k + 1) s) ≤ ENNReal.ofReal (C * |s| ^ 3) := by
    choose Ck hCk using hgap
    refine ⟨(Finset.range N).sup' ⟨0, Finset.mem_range.mpr hNpos⟩
      (fun k => if h : k + 1 < N then Ck k h else 0), ?_, ?_⟩
    · have h1 : (0 : ℝ) ≤ (if h : 0 + 1 < N then Ck 0 h else 0) := by
        by_cases h : 0 + 1 < N
        · rw [dif_pos h]; exact (hCk 0 h).1
        · rw [dif_neg h]
      exact le_trans h1 (Finset.le_sup' (fun k => if h : k + 1 < N then Ck k h else (0:ℝ))
        (Finset.mem_range.mpr hNpos))
    · have hle : ∀ k (hk : k + 1 < N),
          Ck k hk ≤ (Finset.range N).sup' ⟨0, Finset.mem_range.mpr hNpos⟩
            (fun k => if h : k + 1 < N then Ck k h else 0) := by
        intro k hk
        have h1 := Finset.le_sup' (fun k => if h : k + 1 < N then Ck k h else (0:ℝ))
          (Finset.mem_range.mpr (by omega : k < N))
        rwa [dif_pos hk] at h1
      intro k hk
      obtain ⟨hCk0, hev⟩ := hCk k hk
      filter_upwards [hev] with s hs
      exact hs.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hle k hk) (pow_nonneg (abs_nonneg _) 3)))
  obtain ⟨Cg, hCg0, hCg⟩ := hgapC
  -- the two bounds on the pieces
  have hpieceb : ∀ᶠ s in 𝓝 (0:ℝ), ∀ k ∈ Finset.range N,
      Manifold.riemannianEDist I (σm k s) (σp k s)
        ≤ ENNReal.ofReal (Real.sqrt (ll k * Efun k s)) := by
    rw [Finset.eventually_all]
    intro k hk
    have hk' := Finset.mem_range.mp hk
    obtain ⟨a₁, a₂, ha₁, ha₂, hstayk⟩ := hmarg k hk'
    filter_upwards [Ioo_mem_nhds (show a₁ / 2 < 0 by linarith) (show 0 < a₂ / 2 by linarith)]
      with s hs
    have hstay' : ∀ t ∈ Icc 0 (ll k), fam2 (up k) (ηk k) (ζk k) s t
        ∈ (extChartAt I (x k)).target :=
      fun t ht => hstayk s ⟨by linarith [hs.1, ha₁], by linarith [hs.2, ha₂]⟩ t ht
    have h := edist_piece_le (cov := cov) hmet (hL₀ := hllpos k hk')
      (fun t ht => hup k hk' t (hIcccll k hk' ht)) (fun t ht => hwp k hk' t (hIcccll k hk' ht))
      (hηk k hk') (hζk k hk') (hekC k hk') (hζk'C k hk') hstay'
    simpa only [σm, σp, Efun] using h
  have hgapb : ∀ᶠ s in 𝓝 (0:ℝ), ∀ k ∈ Finset.range N, k + 1 < N →
      Manifold.riemannianEDist I (σp k s) (σm (k + 1) s) ≤ ENNReal.ofReal (Cg * |s| ^ 3) := by
    rw [Finset.eventually_all]
    intro k hk
    by_cases hkc : k + 1 < N
    · filter_upwards [hCg k hkc] with s hs
      intro _
      exact hs
    · filter_upwards with s hcon
      exact absurd hcon hkc
  -- the endpoints of the broken curve are those of `γ`
  have hσm_end : ∀ s : ℝ, σm 0 s = γ 0 := by
    intro s
    show (extChartAt I (x 0)).symm (fam2 (up 0) (ηk 0) (ζk 0) s 0) = γ 0
    have hη0 : ηk 0 0 = 0 := by
      simp only [ηk, testFieldS, hc0]
      norm_num
    have hζ0 : ζk 0 0 = 0 := by
      simp only [ζk, hη0, chrB_zero_fst, chrB_zero_snd, neg_zero]
    have h2 : fam2 (up 0) (ηk 0) (ζk 0) s 0 = up 0 0 := by
      simp only [fam2, hη0, hζ0, smul_zero, add_zero]
    rw [h2]
    show (extChartAt I (x 0)).symm (up 0 0) = γ 0
    rw [hpt0 0 hNpos, hc0]
  have hσp_end : ∀ s : ℝ, σp (N - 1) s = γ L := by
    intro s
    have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
    have hηN : ηk (N - 1) (ll (N - 1)) = 0 := by
      simp only [ηk, testFieldS]
      rw [hcll (N - 1) (by omega)]
      have hNN : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
      rw [hNN, hcN]
      have hpi : Real.pi * L / L = Real.pi := by
        rw [mul_div_assoc, div_self hL.ne', mul_one]
      rw [hpi, Real.sin_pi, zero_smul]
    have hζN : ζk (N - 1) (ll (N - 1)) = 0 := by
      simp only [ζk, hηN, chrB_zero_fst, chrB_zero_snd, neg_zero]
    have h2 : fam2 (up (N - 1)) (ηk (N - 1)) (ζk (N - 1)) s (ll (N - 1))
        = up (N - 1) (ll (N - 1)) := by
      simp only [fam2, hηN, hζN, smul_zero, add_zero]
    show (extChartAt I (x (N - 1))).symm (fam2 (up (N - 1)) (ηk (N - 1)) (ζk (N - 1)) s (ll (N - 1)))
      = γ L
    rw [h2]
    show (extChartAt I (x (N - 1))).symm (up (N - 1) (ll (N - 1))) = γ L
    rw [hpt1' (N - 1) (by omega), hN1, hcN]
  -- the chain of triangle inequalities
  have hchain : ∀ᶠ s in 𝓝 (0:ℝ), Manifold.riemannianEDist I (γ 0) (γ L)
      ≤ ∑ k ∈ Finset.range N, (ENNReal.ofReal (Real.sqrt (ll k * Efun k s))
          + ENNReal.ofReal (Cg * |s| ^ 3)) := by
    filter_upwards [hpieceb, hgapb] with s hp hg
    have h := edist_le_sum_pairs (I := I) (n := N)
      (a := fun k => if k < N then σm k s else γ L) (b := fun k => σp k s)
    have h0 : (if 0 < N then σm 0 s else γ L) = γ 0 := by
      rw [if_pos hNpos]
      exact hσm_end s
    have hN : (if N < N then σm N s else γ L) = γ L := by
      rw [if_neg (Nat.lt_irrefl N)]
    rw [h0, hN] at h
    refine h.trans (Finset.sum_le_sum (fun k hk => ?_))
    have hk' := Finset.mem_range.mp hk
    have hkN : (if k < N then σm k s else γ L) = σm k s := if_pos hk'
    by_cases hkc : k + 1 < N
    · have hkN1 : (if k + 1 < N then σm (k + 1) s else γ L) = σm (k + 1) s := if_pos hkc
      rw [hkN, hkN1]
      exact add_le_add (hp k hk) (hg k hk hkc)
    · have hk1 : k + 1 = N := by omega
      have hkN1 : (if k + 1 < N then σm (k + 1) s else γ L) = γ L := if_neg hkc
      rw [hkN, hkN1]
      have h1 : σp k s = γ L := by
        rw [show k = N - 1 from by omega]
        exact hσp_end s
      have hzero : Manifold.riemannianEDist I (σp k s) (γ L) = 0 := by
        rw [h1, Manifold.riemannianEDist_self]
      rw [hzero, add_zero]
      exact (hp k hk).trans (le_add_of_nonneg_right (by positivity))
  -- a real inequality, and AM–GM
  have hmain : ∀ᶠ s in 𝓝[>] (0:ℝ), L ≤ (L + Ftot s) / 2 + (N : ℝ) * (Cg * s ^ 3) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hchain] with s hs hs0
    have hterm : ∀ k ∈ Finset.range N, 0 ≤ Real.sqrt (ll k * Efun k s) + Cg * |s| ^ 3 :=
      fun k hk => add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCg0 (pow_nonneg (abs_nonneg _) _))
    have h1 : ENNReal.ofReal L ≤ ∑ k ∈ Finset.range N,
        (ENNReal.ofReal (Real.sqrt (ll k * Efun k s)) + ENNReal.ofReal (Cg * |s| ^ 3)) := by
      rw [← hmin]
      exact hs
    rw [show (∑ k ∈ Finset.range N, (ENNReal.ofReal (Real.sqrt (ll k * Efun k s))
          + ENNReal.ofReal (Cg * |s| ^ 3)))
        = ENNReal.ofReal (∑ k ∈ Finset.range N,
            (Real.sqrt (ll k * Efun k s) + Cg * |s| ^ 3)) from by
      rw [ENNReal.ofReal_sum_of_nonneg hterm]
      exact Finset.sum_congr rfl (fun k hk => (ENNReal.ofReal_add (Real.sqrt_nonneg _)
        (mul_nonneg hCg0 (pow_nonneg (abs_nonneg _) _))).symm)] at h1
    have h3 : L ≤ ∑ k ∈ Finset.range N, (Real.sqrt (ll k * Efun k s) + Cg * |s| ^ 3) :=
      (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hterm)).mp h1
    have h4 : ∑ k ∈ Finset.range N, (Real.sqrt (ll k * Efun k s) + Cg * |s| ^ 3)
        = (∑ k ∈ Finset.range N, Real.sqrt (ll k * Efun k s))
          + (N : ℝ) * (Cg * s ^ 3) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        abs_of_nonneg hs0.le]
    have ham : ∀ k ∈ Finset.range N,
        Real.sqrt (ll k * Efun k s) ≤ (ll k + Efun k s) / 2 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hx : 0 ≤ ll k := (hllpos k hk').le
      have hy : 0 ≤ Efun k s := by
        change 0 ≤ fam2Energy (I := I) (x k) (up k) (ηk k) (ζk k) (wp k) (ek k) (ζk' k) (ll k) s
        rw [fam2Energy_eq_fam2G]
        exact intervalIntegral.integral_nonneg (hllpos k hk').le
          (fun t ht => Submission.Minimal.chartGram_self_nonneg (I := I) (x k) _ _)
      nlinarith [Real.sq_sqrt (mul_nonneg hx hy), sq_nonneg (ll k - Efun k s),
        Real.sqrt_nonneg (ll k * Efun k s)]
    have h5 : ∑ k ∈ Finset.range N, Real.sqrt (ll k * Efun k s) ≤ (L + Ftot s) / 2 := by
      have h6 := Finset.sum_le_sum ham
      have h7 : ∑ k ∈ Finset.range N, (ll k + Efun k s) / 2 = (L + Ftot s) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hllsum]
      linarith [h6, h7]
    rw [h4] at h3
    linarith
  -- the final contradiction
  set cK : ℝ := (N : ℝ) * (2 * Cg) with hcKdef
  have hcK0 : 0 ≤ cK := by
    rw [hcKdef]; positivity
  have hdiffF : ∀ᶠ s in 𝓝 (0:ℝ), DifferentiableAt ℝ Ftot s := by
    have hmem : ∀ᶠ s in 𝓝 (0:ℝ), ∀ k ∈ Finset.range N, DifferentiableAt ℝ (Efun k) s := by
      rw [Finset.eventually_all]
      intro k hk
      obtain ⟨a₁, a₂, ha₁, ha₂, hstayk⟩ := hmarg k (Finset.mem_range.mp hk)
      filter_upwards [Ioo_mem_nhds (show a₁ / 2 < 0 by linarith) (show 0 < a₂ / 2 by linarith)]
        with s hs
      exact (fam2Energy_hasDerivAt (cov := cov) hmet (x₀ := x k) (L := ll k)
        (hL := (hllpos k (Finset.mem_range.mp hk)).le)
        (u := up k) (η := ηk k) (ζ := ζk k) (w := wp k) (e := ek k) (ζ' := ζk' k) (w' := wp' k)
        (a₁ := a₁) (a₂ := a₂) (δ₁ := a₁ / 2) (δ₂ := a₂ / 2) (s₀ := s)
        (by linarith [ha₁]) (by linarith [ha₂]) (by linarith [hs.1]) (by linarith [hs.2])
        (fun t ht => hup k (Finset.mem_range.mp hk) t (hIcccll k (Finset.mem_range.mp hk) ht))
        (fun t ht => hwp k (Finset.mem_range.mp hk) t (hIcccll k (Finset.mem_range.mp hk) ht))
        (hηk k (Finset.mem_range.mp hk)) (hζk k (Finset.mem_range.mp hk))
        (hekC k (Finset.mem_range.mp hk)) (hζk'C k (Finset.mem_range.mp hk))
        (A₀ := 0) (B₀ := ll k) (by exact le_refl 0) (by exact le_refl (ll k))
        hstayk).differentiableAt
    filter_upwards [hmem] with s hs
    show DifferentiableAt ℝ (fun s : ℝ => ∑ k ∈ Finset.range N, Efun k s) s
    rw [show (fun s : ℝ => ∑ k ∈ Finset.range N, Efun k s) = (∑ k ∈ Finset.range N, Efun k)
      from by funext t; rw [Finset.sum_apply]]
    exact DifferentiableAt.sum (fun k hk => hs k hk)
  have hH1 : HasDerivAt (fun s : ℝ => Ftot s - L + cK * s ^ 3) 0 0 := by
    have h2 : HasDerivAt (fun s : ℝ => cK * s ^ 3) 0 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s ^ 3) (0:ℝ) 0 := by
        have h := (hasDerivAt_id (0:ℝ)).pow 3
        simp only [id_eq] at h
        convert h using 1
        all_goals first | (ext x; simp) | ring
      have h2 := h1.const_mul cK
      convert h2 using 1
      all_goals first | (ext x; simp) | ring
    have h1 : HasDerivAt (fun s : ℝ => Ftot s - L) 0 0 := hF1.sub_const L
    have h := h1.add h2
    rw [show (fun s : ℝ => Ftot s - L + cK * s ^ 3)
      = (fun s : ℝ => Ftot s - L) + fun s : ℝ => cK * s ^ 3 from rfl]
    simpa using h
  have hH2 : HasDerivAt (deriv (fun s : ℝ => Ftot s - L + cK * s ^ 3))
      (∑ k ∈ Finset.range N, (-2 * ∫ t in (0:ℝ)..(ll k),
        indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) t)) 0 := by
    have hev : deriv (fun s : ℝ => Ftot s - L + cK * s ^ 3) =ᶠ[𝓝 (0:ℝ)]
        fun s => deriv Ftot s + 3 * cK * s ^ 2 := by
      filter_upwards [hdiffF] with s hs
      have h2 : DifferentiableAt ℝ (fun s : ℝ => cK * s ^ 3) s := by fun_prop
      have hB : deriv (fun s : ℝ => Ftot s - L) s = deriv Ftot s := (hs.hasDerivAt.sub_const L).deriv
      have h4 : deriv (fun s : ℝ => cK * s ^ 3) s = 3 * cK * s ^ 2 := by
        have h : HasDerivAt (fun s : ℝ => cK * s ^ 3) (3 * cK * s ^ 2) s := by
          have h1 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * s ^ 2) s := by
            have hh := (hasDerivAt_id s).pow 3
            simp only [id_eq] at hh
            convert hh using 1
            all_goals first | (ext x; simp) | ring
          have h2 := h1.const_mul cK
          convert h2 using 1
          all_goals first | (ext x; simp) | ring
        exact h.deriv
      rw [show (fun s : ℝ => Ftot s - L + cK * s ^ 3)
        = (fun s : ℝ => Ftot s - L) + fun s : ℝ => cK * s ^ 3 from rfl]
      rw [deriv_add (hs.sub_const L) h2, hB, h4]
    have h2 : HasDerivAt (fun s : ℝ => 3 * cK * s ^ 2) 0 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (0:ℝ) 0 := by
        have h := (hasDerivAt_id (0:ℝ)).pow 2
        simp only [id_eq] at h
        convert h using 1
        all_goals first | (ext x; simp) | ring
      have h2 := h1.const_mul (3 * cK)
      convert h2 using 1
      all_goals first | (ext x; simp) | ring
    refine hev.hasDerivAt_iff.mpr ?_
    have h := hF2.add h2
    rw [show (fun s : ℝ => deriv Ftot s + 3 * cK * s ^ 2)
      = (deriv Ftot) + fun s : ℝ => 3 * cK * s ^ 2 from rfl]
    simpa using h
  have hHnn : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 ≤ Ftot s - L + cK * s ^ 3 := by
    filter_upwards [hmain] with s hs
    rw [hcKdef]
    nlinarith [hs]
  have hneg : (∑ k ∈ Finset.range N, (-2 * ∫ t in (0:ℝ)..(ll k),
      indexIntegrand cov (x k) (up k) (ηk k) (wp k) (ek k) t)) < 0 := by
    have hpi : 0 ≤ (L ^ 2 - Real.pi ^ 2) / (2 * L) := by
      have h1 : Real.pi ^ 2 ≤ L ^ 2 := by nlinarith [hcon, Real.pi_pos]
      exact div_nonneg (by linarith) (by linarith)
    linarith [hint, hpi]
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg
    hH1 hH2 hneg
  rw [eventually_nhdsWithin_iff] at hHnn
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hHnn
  have hs0 : 0 < min δ₁ δ₂ / 2 := by positivity
  have hs1 : min δ₁ δ₂ / 2 < δ₁ := by
    have := min_le_left δ₁ δ₂; linarith
  have hs2 : min δ₁ δ₂ / 2 < δ₂ := by
    have := min_le_right δ₁ δ₂; linarith
  have h1 := hδ₁sub (show min δ₁ δ₂ / 2 ∈ Metric.ball (0:ℝ) δ₁ from by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith, hs1⟩) hs0
  have h2 := hδ₂ (min δ₁ δ₂ / 2) hs0 hs2
  have h3 : Ftot 0 - L + cK * (0:ℝ) ^ 3 = 0 := by rw [hF0]; ring
  linarith [h2, h3]


/-- **Myers' theorem.**  On a compact Riemannian manifold with `QuarterPinched cov` (so that all
sectional curvatures are `> 1`) the Riemannian distance between any two points is at most `π`. -/
theorem riemannianEDist_le_pi [Nontrivial E] [CompactSpace M]
    [PathConnectedSpace M] [RegularSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (hdim : 2 ≤ Module.finrank ℝ E) (p q : M) :
    Manifold.riemannianEDist I p q ≤ ENNReal.ofReal Real.pi := by
  obtain ⟨v, hvq, hvd⟩ := Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
    (cov := cov) hmet htor p q
  rcases eq_or_ne v 0 with hv0 | hvne
  · rw [hv0, norm_zero, ENNReal.ofReal_zero] at hvd
    rw [hvd]
    exact bot_le
  · set T : ℝ := ‖v‖ with hTdef
    have hT : 0 ≤ T := norm_nonneg v
    set ξ : TangentSpace I p := unitOf v hvne with hξdef
    have hξ : ‖ξ‖ = 1 := unitOf_norm v hvne
    set γ : ℝ → M := geodCurve (cov := cov) hmet T hT p ξ hξ with hγdef
    obtain ⟨hγ0, -, hγsm, hγgeo, hγsp⟩ := geodCurve_spec (cov := cov) hmet T hT p ξ hξ
    have hTξ : T • ξ = v := by
      rw [hTdef, hξdef, unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
    have hγT : γ T = q := by
      have h1 : γ T = GExp (cov := cov) hmet p (T • ξ) := by
        rw [GExp_eq_geodCurve (cov := cov) hmet hξ hT (r := T) hT le_rfl]
      rw [h1, hTξ, hvq]
    have hmin : Manifold.riemannianEDist I (γ 0) (γ T) = ENNReal.ofReal T := by
      rw [show γ 0 = p from hγ0, show γ T = q from hγT, hvd, hTdef]
    have hδ : 0 < geodDelta (cov := cov) hmet := geodDelta_pos (cov := cov) hmet
    have hVsub : Icc 0 T ⊆ Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) :=
      fun t ht => ⟨by linarith [hδ, ht.1], by linarith [hδ, ht.2]⟩
    have hπ := le_pi_of_minimising_geodesic (cov := cov) hmet htor hpinch hdim
      (V := Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet))
      isOpen_Ioo (by rw [hTdef]; exact norm_pos_iff.mpr hvne) hVsub hγsm hγgeo hγsp hmin
    rw [hvd, hTdef]
    exact ENNReal.ofReal_le_ofReal hπ.le

/-- **Myers' theorem, strict form.**  On a compact Riemannian manifold with `QuarterPinched cov`
(so that all sectional curvatures are `> 1` at every point) the Riemannian distance between any two
points is **strictly** less than `π`. -/
theorem riemannianEDist_lt_pi [Nontrivial E] [CompactSpace M]
    [PathConnectedSpace M] [RegularSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (hdim : 2 ≤ Module.finrank ℝ E) (p q : M) :
    Manifold.riemannianEDist I p q < ENNReal.ofReal Real.pi := by
  obtain ⟨v, hvq, hvd⟩ := Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
    (cov := cov) hmet htor p q
  rcases eq_or_ne v 0 with hv0 | hvne
  · rw [hv0, norm_zero, ENNReal.ofReal_zero] at hvd
    rw [hvd]
    exact (ENNReal.ofReal_pos.mpr Real.pi_pos)
  · set T : ℝ := ‖v‖ with hTdef
    have hT : 0 < T := by rw [hTdef]; exact norm_pos_iff.mpr hvne
    set ξ : TangentSpace I p := unitOf v hvne with hξdef
    have hξ : ‖ξ‖ = 1 := unitOf_norm v hvne
    set γ : ℝ → M := geodCurve (cov := cov) hmet T hT.le p ξ hξ with hγdef
    obtain ⟨hγ0, -, hγsm, hγgeo, hγsp⟩ := geodCurve_spec (cov := cov) hmet T hT.le p ξ hξ
    have hTξ : T • ξ = v := by
      rw [hTdef, hξdef, unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
    have hγT : γ T = q := by
      have h1 : γ T = GExp (cov := cov) hmet p (T • ξ) := by
        rw [GExp_eq_geodCurve (cov := cov) hmet hξ hT.le (r := T) hT.le le_rfl]
      rw [h1, hTξ, hvq]
    have hmin : Manifold.riemannianEDist I (γ 0) (γ T) = ENNReal.ofReal T := by
      rw [show γ 0 = p from hγ0, show γ T = q from hγT, hvd, hTdef]
    have hδ : 0 < geodDelta (cov := cov) hmet := geodDelta_pos (cov := cov) hmet
    have hVsub : Icc 0 T ⊆ Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) :=
      fun t ht => ⟨by linarith [hδ, ht.1], by linarith [hδ, ht.2]⟩
    have hπ := le_pi_of_minimising_geodesic (cov := cov) hmet htor hpinch hdim
      (V := Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet))
      isOpen_Ioo hT hVsub hγsm hγgeo hγsp hmin
    rw [hvd, hTdef]
    exact ENNReal.ofReal_lt_ofReal_iff Real.pi_pos |>.mpr hπ

end Main


end

end Submission.GlobalBM
