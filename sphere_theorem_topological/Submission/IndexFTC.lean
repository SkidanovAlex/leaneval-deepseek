import Submission.JacobiCover
import Submission.JacobiGlobal
import Submission.IndexIntrinsic3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Rauch
open Submission.RauchGlobal
open Submission.JacobiCoords
open Submission.BonnetMyers
open Submission.IntrinsicVariation
open Submission.IndexIntrinsic
open Submission.IndexIntrinsic2
open Submission.IndexIntrinsic3
open Submission.CurvatureVec
open Submission.CurvatureSym
open Submission.JacobiGlobal

/-!
# The index-side identities of `σ ≤ κ`

The two identities

* `∫_0^t idxAlong γ J (∇J) = 0` for a Jacobi field with `J 0 = J t = 0`,
* `∫_0^t bilAlong γ J W (∇J) (∇W) = ⟪∇J t, W t⟫` for a test field with `W 0 = 0`,

are the two inputs of the shortening argument of `ConjCut.CutConjInequality` (Roadmap §97.4, §101.5).
This module proves the first of them, globally (no chart covering assumptions on the user's side):

* `exists_isJacobiPiece_cover` — the finite chart cover of `[a,b]` carrying the `IsJacobiPiece` data
  (the cover of `Submission.JacobiCover` upgraded with the Jacobi equation, and the identification
  `∇J = covAlong cov J` with the chart formula via `covAlong_eq_chart`);
* **`integral_idxAlong_eq_zero`** — the first identity, by the chart-covered FTC
  `IndexIntrinsic2.integral_idxAlong_eq_zero_of_cover`.
-/

namespace Submission.IndexFTC

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- `HasDerivAt` at a point of an open set from `C^∞` there. -/
lemma hasDerivAt_deriv_of_contDiffOn {f : ℝ → E} {U : Set ℝ} {t : ℝ} (hU : IsOpen U) (ht : t ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) : HasDerivAt f (deriv f t) t :=
  (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hU ht hf).self_of_nhds

/-- **The finite chart cover of `[a,b]` carrying the `IsJacobiPiece` data**, with
`V := J` and `Z := covAlong cov J` (the global covariant derivative of the field along the curve). -/
theorem exists_isJacobiPiece_cover (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ s, IsJacobiAt cov γ J s) (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    ∃ (N : ℕ) (c A B : ℕ → ℝ),
      c 0 = a ∧ c N = b ∧ (∀ k < N, c k ≤ c (k + 1)) ∧
      (∀ k < N,
        IsJacobiPiece (I := I) cov γ J (covAlong cov J) (c k) (c (k + 1)) (A k) (B k)) := by
  obtain ⟨N, c, S, Em, A, B, z, hrest⟩ :=
    Submission.JacobiCover.exists_partition_jacobiCoords (cov := cov) htor hab
      (by norm_num : (0 : ℝ) < 2) (hγ.contMDiffOn : ContMDiffOn 𝓘(ℝ) I ∞ γ _)
      (fun s _ => hJ s)
  have hc0 : c 0 = a := hrest.1
  have hcN : c N = b := hrest.2.1
  have hmono : ∀ k < N, c k < c (k + 1) := hrest.2.2.1
  have hSE : ∀ k < N, S k < c k ∧ c (k + 1) < Em k := hrest.2.2.2.1
  have hAB : ∀ k < N, A k < c k ∧ c (k + 1) < B k := hrest.2.2.2.2.1
  have hroom : ∀ k < N, Icc (A k) (B k) ⊆ Ioo (S k) (Em k) := hrest.2.2.2.2.2.1
  have hsrc : ∀ k < N, ∀ t ∈ Icc (S k) (Em k), γ t ∈ (chartAt H (z k)).source :=
    hrest.2.2.2.2.2.2.2.1
  have hcdU : ∀ k < N, ContDiffOn ℝ ∞ (chartCoord (I := I) (z k) γ) (Icc (S k) (Em k)) :=
    hrest.2.2.2.2.2.2.2.2.1
  have hcdJ : ∀ k < N, ContDiffOn ℝ ∞ (chartCoords (I := I) (z k) γ J) (Icc (S k) (Em k)) :=
    hrest.2.2.2.2.2.2.2.2.2.1
  have hfv : ∀ k < N, ∀ t ∈ Icc (S k) (Em k),
      frameVector (I := I) (z k) (γ t) (chartCoords (I := I) (z k) γ J t) = J t :=
    hrest.2.2.2.2.2.2.2.2.2.2.1
  have hjacEq : ∀ k < N, ∀ t ∈ Icc (S k) (Em k),
      DtDsP cov (z k) (chartCoord (I := I) (z k) γ) (chartCoords (I := I) (z k) γ J)
        (deriv (chartCoord (I := I) (z k) γ)) (deriv (chartCoords (I := I) (z k) γ J)) t
      + chartCurv cov (z k) ((extChartAt I (z k)).symm (chartCoord (I := I) (z k) γ t))
          (chartCoords (I := I) (z k) γ J t) (deriv (chartCoord (I := I) (z k) γ) t) = 0 :=
    hrest.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨N, c, A, B, hc0, hcN, (fun k hk => (hmono k hk).le), ?_⟩
  intro k hk
  have hroomk : Icc (A k) (B k) ⊆ Ioo (S k) (Em k) := hroom k hk
  have hsck : S k < c k ∧ c (k + 1) < Em k := hSE k hk
  have hIo : IsOpen (Ioo (S k) (Em k)) := isOpen_Ioo
  -- `C^∞` on the open local interval
  have hUo : ContDiffOn ℝ ∞ (chartCoord (I := I) (z k) γ) (Ioo (S k) (Em k)) :=
    (hcdU k hk).mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hJo : ContDiffOn ℝ ∞ (chartCoords (I := I) (z k) γ J) (Ioo (S k) (Em k)) :=
    (hcdJ k hk).mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hUo1 : ContDiffOn ℝ ∞ (deriv (chartCoord (I := I) (z k) γ)) (Ioo (S k) (Em k)) :=
    hUo.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  have hUo2 : ContDiffOn ℝ ∞ (deriv (deriv (chartCoord (I := I) (z k) γ))) (Ioo (S k) (Em k)) :=
    hUo1.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  have hJo1 : ContDiffOn ℝ ∞ (deriv (chartCoords (I := I) (z k) γ J)) (Ioo (S k) (Em k)) :=
    hJo.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  have hJo2 : ContDiffOn ℝ ∞ (deriv (deriv (chartCoords (I := I) (z k) γ J)))
      (Ioo (S k) (Em k)) :=
    hJo1.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  have hevy : ∀ t ∈ Icc (A k) (B k), J t = frameVector (I := I) (z k) (γ t)
      (chartCoords (I := I) (z k) γ J t) :=
    fun t ht => (hfv k hk t ⟨(hroomk ht).1.le, (hroomk ht).2.le⟩).symm
  refine ⟨z k, chartCoord (I := I) (z k) γ, deriv (chartCoord (I := I) (z k) γ),
    deriv (deriv (chartCoord (I := I) (z k) γ)), chartCoords (I := I) (z k) γ J,
    deriv (chartCoords (I := I) (z k) γ J), deriv (deriv (chartCoords (I := I) (z k) γ J)),
    hAB k hk |>.1, hAB k hk |>.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `γ` is the chart curve
    intro t ht
    have hst : γ t ∈ (chartAt H (z k)).source :=
      hsrc k hk t ⟨(hroomk ht).1.le, (hroomk ht).2.le⟩
    show γ t = (extChartAt I (z k)).symm ((extChartAt I (z k)) (γ t))
    exact (PartialEquiv.left_inv (extChartAt I (z k)) (by rwa [extChartAt_source])).symm
  · -- `u' = w`
    intro t ht
    exact hasDerivAt_deriv_of_contDiffOn hIo (hroomk ht) hUo
  · -- `w' = w'`
    intro t ht
    exact hasDerivAt_deriv_of_contDiffOn hIo (hroomk ht) hUo1
  · -- continuity of `w'`
    exact (hUo2.continuousOn).mono (fun x hx => hroomk hx)
  · -- the chart target condition
    intro t ht
    have hst : γ t ∈ (chartAt H (z k)).source :=
      hsrc k hk t ⟨(hroomk ht).1.le, (hroomk ht).2.le⟩
    exact (extChartAt I (z k)).map_source (by rwa [extChartAt_source])
  · -- `J' = J'`
    intro t ht
    exact hasDerivAt_deriv_of_contDiffOn hIo (hroomk ht) hJo
  · -- continuity of `J'`
    exact (hJo1.continuousOn).mono (fun x hx => hroomk hx)
  · -- `J'' = J''`
    intro t ht
    exact hasDerivAt_deriv_of_contDiffOn hIo (hroomk ht) hJo1
  · -- continuity of `J''`
    exact (hJo2.continuousOn).mono (fun x hx => hroomk hx)
  · -- the Jacobi equation
    intro t ht
    exact hjacEq k hk t ⟨(hroomk ht).1.le, (hroomk ht).2.le⟩
  · -- `V = J`
    intro t ht
    exact hevy t ht
  · -- `∇J` is the chart formula
    intro t ht
    have htIo : t ∈ Ioo (S k) (Em k) := hroomk ht
    have hsrcEv : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (z k)).source := by
      filter_upwards [hIo.mem_nhds htIo] with s hs
      exact hsrc k hk s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have huTgt : ∀ᶠ s in 𝓝 t, chartCoord (I := I) (z k) γ s ∈ (extChartAt I (z k)).target := by
      filter_upwards [hsrcEv] with s hs
      exact (extChartAt I (z k)).map_source (by rwa [extChartAt_source])
    have hγeq : γ =ᶠ[𝓝 t] fun s => (extChartAt I (z k)).symm (chartCoord (I := I) (z k) γ s) := by
      filter_upwards [hsrcEv] with s hs
      exact (PartialEquiv.left_inv (extChartAt I (z k)) (by rwa [extChartAt_source])).symm
    have hu : ∀ᶠ s in 𝓝 t, HasDerivAt (chartCoord (I := I) (z k) γ)
        (deriv (chartCoord (I := I) (z k) γ) s) s :=
      Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hIo htIo hUo
    have hyv : ∀ᶠ s in 𝓝 t, frameVector (I := I) (z k) (γ s)
        (chartCoords (I := I) (z k) γ J s) = J s := by
      filter_upwards [hIo.mem_nhds htIo] with s hs
      exact hfv k hk s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hy' : ∀ᶠ s in 𝓝 t, HasDerivAt (chartCoords (I := I) (z k) γ J)
        (deriv (chartCoords (I := I) (z k) γ J) s) s :=
      Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hIo htIo hJo
    have hVsm : SmoothAlongAt (I := I) γ J t :=
      Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJ
        (hγ.contMDiffOn.mono (fun x _ => trivial))
    exact Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor
      (hγ.contMDiffOn.mono (fun x _ => trivial)) (hne t) hVsm
      (hsrc k hk t ⟨htIo.1.le, htIo.2.le⟩) hsrcEv huTgt hγeq hu hyv hy'

/-- **THE FIRST INDEX IDENTITY** (Roadmap §101.6 item 1).  For a Jacobi field `J` along a unit-speed
geodesic `γ` with `J a = J b = 0`, the integral of the intrinsic index integrand vanishes. -/
theorem integral_idxAlong_eq_zero (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ s, IsJacobiAt cov γ J s) (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hVa : J a = 0) (hVb : J b = 0) :
    ∫ t in a..b, idxAlong (cov := cov) γ J (covAlong cov J) t = 0 := by
  obtain ⟨N, c, A, B, hc0, hcN, hmono, hpiece⟩ :=
    exists_isJacobiPiece_cover (cov := cov) htor hJ hγ hne hab
  exact integral_idxAlong_eq_zero_of_cover (cov := cov) hmet htor hc0 hcN hmono hpiece hVa hVb


/-! ## The polarised identity (Roadmap §101.6 item 1, second half)

The same cover argument gives the polarised FTC `∫_0^t bilAlong γ J W (∇J) (∇W) = ⟪∇J t, W t⟫`
(the corner pairing of the shortening argument) for a test field `W` that is smooth along `γ`.
-/

/-- **The chart coordinates of a field smooth along the curve are `C^∞` in any chart containing
the curve.** -/
lemma contDiffOn_chartCoords_of_smoothAlongAt {z : M} {γ : ℝ → M}
    {W : (t : ℝ) → TangentSpace I (γ t)} {S Em : ℝ}
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hWs : ∀ t, SmoothAlongAt (I := I) γ W t)
    (hsrc : ∀ t ∈ Icc S Em, γ t ∈ (chartAt H z).source) :
    ContDiffOn ℝ ∞ (chartCoords (I := I) z γ W) (Icc S Em) := by
  intro t ht
  obtain ⟨U, hUopen, htU, hUsrc, hUcd⟩ := hWs t
  have hzsrc : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H z).source :=
    (hγ.continuous.continuousAt.preimage_mem_nhds
      ((chartAt H z).open_source.mem_nhds (hsrc t ht)))
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hzsrc
  have hVcd : ContDiffOn ℝ ∞ (chartCoords (I := I) (γ t) γ W) (U ∩ Metric.ball t r) :=
    hUcd.mono (fun s hs => hs.1)
  have hcdz : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ W) (U ∩ Metric.ball t r) :=
    Submission.ChartCoordsTrans.contDiffOn_chartCoords_of_chartCoords (I := I)
      (hUopen.inter isOpen_ball) (hγ.contMDiffOn) (fun s hs => hUsrc s hs.1)
      (fun s hs => hrsub hs.2) hVcd
  exact (hcdz.contDiffAt (IsOpen.mem_nhds (hUopen.inter isOpen_ball)
    ⟨htU, Metric.mem_ball_self hrpos⟩)).contDiffWithinAt

/-- **The per-piece `IsBilPiece` data**, built from the raw chart data of the cover. -/
lemma isBilPiece_of_data (htor : cov.torsion = 0)
    {γ : ℝ → M} {J W : (t : ℝ) → TangentSpace I (γ t)} {z : M}
    {S Em A B a b : ℝ}
    (hA : A < a) (hB : b < B) (hroom : Icc A B ⊆ Ioo S Em)
    (hsrc : ∀ t ∈ Icc S Em, γ t ∈ (chartAt H z).source)
    (hcdU : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Icc S Em))
    (hcdJ : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ J) (Icc S Em))
    (hcdW : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ W) (Icc S Em))
    (hfv : ∀ t ∈ Icc S Em, frameVector (I := I) z (γ t) (chartCoords (I := I) z γ J t) = J t)
    (hjacE : ∀ t ∈ Icc S Em, DtDsP cov z (chartCoord (I := I) z γ) (chartCoords (I := I) z γ J)
        (deriv (chartCoord (I := I) z γ)) (deriv (chartCoords (I := I) z γ J)) t
      + chartCurv cov z ((extChartAt I z).symm (chartCoord (I := I) z γ t))
          (chartCoords (I := I) z γ J t) (deriv (chartCoord (I := I) z γ) t) = 0)
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    (hJ : ∀ s, IsJacobiAt cov γ J s) (hWs : ∀ s, SmoothAlongAt (I := I) γ W s) :
    IsBilPiece (I := I) cov γ J (covAlong cov J) W (covAlong cov W) a b A B := by
  have hIo : IsOpen (Ioo S Em) := isOpen_Ioo
  have hγon : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (0 : ℝ) 1) :=
    hγ.contMDiffOn.mono (fun x _ => trivial)
  have hUo : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Ioo S Em) :=
    hcdU.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hJo : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ J) (Ioo S Em) :=
    hcdJ.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hWo : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ W) (Ioo S Em) :=
    hcdW.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hUo1 : ContDiffOn ℝ ∞ (deriv (chartCoord (I := I) z γ)) (Ioo S Em) :=
    hUo.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  have hJo1 : ContDiffOn ℝ ∞ (deriv (chartCoords (I := I) z γ J)) (Ioo S Em) :=
    hJo.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  have hWo1 : ContDiffOn ℝ ∞ (deriv (chartCoords (I := I) z γ W)) (Ioo S Em) :=
    hWo.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  have hsrcEv : ∀ t ∈ Icc A B, ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H z).source := by
    intro t ht
    filter_upwards [hIo.mem_nhds (hroom ht)] with s hs
    exact hsrc s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have huTgtEv : ∀ t ∈ Icc A B, ∀ᶠ s in 𝓝 t, chartCoord (I := I) z γ s ∈ (extChartAt I z).target := by
    intro t ht
    filter_upwards [hsrcEv t ht] with s hs
    exact (extChartAt I z).map_source (by rwa [extChartAt_source])
  have hγeqEv : ∀ t ∈ Icc A B,
      γ =ᶠ[𝓝 t] fun s => (extChartAt I z).symm (chartCoord (I := I) z γ s) := by
    intro t ht
    filter_upwards [hsrcEv t ht] with s hs
    exact (PartialEquiv.left_inv (extChartAt I z) (by rwa [extChartAt_source])).symm
  have huEv : ∀ t ∈ Icc A B, ∀ᶠ s in 𝓝 t, HasDerivAt (chartCoord (I := I) z γ)
      (deriv (chartCoord (I := I) z γ) s) s := fun t ht =>
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hIo (hroom ht) hUo
  have hJev : ∀ t ∈ Icc A B, ∀ᶠ s in 𝓝 t, HasDerivAt (chartCoords (I := I) z γ J)
      (deriv (chartCoords (I := I) z γ J) s) s := fun t ht =>
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hIo (hroom ht) hJo
  have hWev : ∀ t ∈ Icc A B, ∀ᶠ s in 𝓝 t, HasDerivAt (chartCoords (I := I) z γ W)
      (deriv (chartCoords (I := I) z γ W) s) s := fun t ht =>
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hIo (hroom ht) hWo
  refine ⟨z, chartCoord (I := I) z γ, deriv (chartCoord (I := I) z γ),
    deriv (deriv (chartCoord (I := I) z γ)), chartCoords (I := I) z γ J,
    deriv (chartCoords (I := I) z γ J), deriv (deriv (chartCoords (I := I) z γ J)),
    chartCoords (I := I) z γ W, deriv (chartCoords (I := I) z γ W),
    hA, hB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `γ` is the chart curve
    intro t ht
    have hst : γ t ∈ (chartAt H z).source := hsrc t ⟨(hroom ht).1.le, (hroom ht).2.le⟩
    show γ t = (extChartAt I z).symm ((extChartAt I z) (γ t))
    exact (PartialEquiv.left_inv (extChartAt I z) (by rwa [extChartAt_source])).symm
  · intro t ht
    exact hasDerivAt_deriv_of_contDiffOn hIo (hroom ht) hUo
  · intro t ht
    exact hasDerivAt_deriv_of_contDiffOn hIo (hroom ht) hUo1
  · intro t ht
    have hst : γ t ∈ (chartAt H z).source := hsrc t ⟨(hroom ht).1.le, (hroom ht).2.le⟩
    exact (extChartAt I z).map_source (by rwa [extChartAt_source])
  · intro t ht
    exact hasDerivAt_deriv_of_contDiffOn hIo (hroom ht) hJo
  · intro t ht
    exact hasDerivAt_deriv_of_contDiffOn hIo (hroom ht) hJo1
  · intro t ht
    exact hjacE t ⟨(hroom ht).1.le, (hroom ht).2.le⟩
  · intro t ht
    exact (hfv t ⟨(hroom ht).1.le, (hroom ht).2.le⟩).symm
  · intro t ht
    have hVsm : SmoothAlongAt (I := I) γ J t :=
      Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJ (hγ.contMDiffOn.mono (fun x _ => trivial))
    have hyv : ∀ᶠ s in 𝓝 t, frameVector (I := I) z (γ s)
        (chartCoords (I := I) z γ J s) = J s := by
      filter_upwards [hIo.mem_nhds (hroom ht)] with s hs
      exact hfv s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    exact Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor (hγ.contMDiffOn.mono (fun x _ => trivial)) (hne t) hVsm
      (hsrc t ⟨(hroom ht).1.le, (hroom ht).2.le⟩) (hsrcEv t ht) (huTgtEv t ht)
      (hγeqEv t ht) (huEv t ht) hyv (hJev t ht)
  · intro t ht
    exact hasDerivAt_deriv_of_contDiffOn hIo (hroom ht) hWo
  · exact (hWo1.continuousOn).mono hroom
  · intro t ht
    exact (frameVector_chartCoords (I := I)
      (hsrc t ⟨(hroom ht).1.le, (hroom ht).2.le⟩)).symm
  · intro t ht
    have hyv : ∀ᶠ s in 𝓝 t, frameVector (I := I) z (γ s)
        (chartCoords (I := I) z γ W s) = W s := by
      filter_upwards [hIo.mem_nhds (hroom ht)] with s hs
      exact frameVector_chartCoords (I := I) (hsrc s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
    exact Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor (hγ.contMDiffOn.mono (fun x _ => trivial)) (hne t) (hWs t)
      (hsrc t ⟨(hroom ht).1.le, (hroom ht).2.le⟩) (hsrcEv t ht) (huTgtEv t ht)
      (hγeqEv t ht) (huEv t ht) hyv (hWev t ht)

/-- **The polarised index identity** (Roadmap §101.6 item 1, second half): for a Jacobi field `J` and
a test field `W` smooth along the unit-speed geodesic `γ`, with `W 0 = 0`,
`∫_0^b bilAlong γ J W (∇J) (∇W) = ⟪∇J b, W b⟫`. -/
theorem integral_bilAlong_eq_sub (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J W : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ s, IsJacobiAt cov γ J s) (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    (hWs : ∀ s, SmoothAlongAt (I := I) γ W s) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, bilAlong (cov := cov) γ J W (covAlong cov J) (covAlong cov W) t
      = inner ℝ (covAlong cov J b) (W b) - inner ℝ (covAlong cov J a) (W a) := by
  obtain ⟨N, c, S, Em, A, B, z, hrest⟩ :=
    Submission.JacobiCover.exists_partition_jacobiCoords (cov := cov) htor hab
      (by norm_num : (0 : ℝ) < 2) (hγ.contMDiffOn : ContMDiffOn 𝓘(ℝ) I ∞ γ _)
      (fun s _ => hJ s)
  have hc0 : c 0 = a := hrest.1
  have hcN : c N = b := hrest.2.1
  have hmono : ∀ k < N, c k < c (k + 1) := hrest.2.2.1
  have hroom : ∀ k < N, Icc (A k) (B k) ⊆ Ioo (S k) (Em k) := hrest.2.2.2.2.2.1
  have hsrc : ∀ k < N, ∀ t ∈ Icc (S k) (Em k), γ t ∈ (chartAt H (z k)).source :=
    hrest.2.2.2.2.2.2.2.1
  have hcdU : ∀ k < N, ContDiffOn ℝ ∞ (chartCoord (I := I) (z k) γ) (Icc (S k) (Em k)) :=
    hrest.2.2.2.2.2.2.2.2.1
  have hcdJ : ∀ k < N, ContDiffOn ℝ ∞ (chartCoords (I := I) (z k) γ J) (Icc (S k) (Em k)) :=
    hrest.2.2.2.2.2.2.2.2.2.1
  have hfv : ∀ k < N, ∀ t ∈ Icc (S k) (Em k),
      frameVector (I := I) (z k) (γ t) (chartCoords (I := I) (z k) γ J t) = J t :=
    hrest.2.2.2.2.2.2.2.2.2.2.1
  have hjacEq : ∀ k < N, ∀ t ∈ Icc (S k) (Em k),
      DtDsP cov (z k) (chartCoord (I := I) (z k) γ) (chartCoords (I := I) (z k) γ J)
        (deriv (chartCoord (I := I) (z k) γ)) (deriv (chartCoords (I := I) (z k) γ J)) t
      + chartCurv cov (z k) ((extChartAt I (z k)).symm (chartCoord (I := I) (z k) γ t))
          (chartCoords (I := I) (z k) γ J t) (deriv (chartCoord (I := I) (z k) γ) t) = 0 :=
    hrest.2.2.2.2.2.2.2.2.2.2.2
  have hAB : ∀ k < N, A k < c k ∧ c (k + 1) < B k := hrest.2.2.2.2.1
  have hpiece : ∀ k < N,
      IsBilPiece (I := I) cov γ J (covAlong cov J) W (covAlong cov W) (c k) (c (k + 1))
        (A k) (B k) := by
    intro k hk
    refine isBilPiece_of_data (cov := cov) htor (hAB k hk).1 (hAB k hk).2 (hroom k hk)
      (hsrc k hk) (hcdU k hk) (hcdJ k hk)
      (contDiffOn_chartCoords_of_smoothAlongAt (I := I) (z := z k) hγ hWs (hsrc k hk))
      (hfv k hk) (hjacEq k hk) hγ hne hJ hWs
  exact integral_bilAlong_eq_sub_of_cover (cov := cov) hmet htor hc0 hcN
    (fun k hk => (hmono k hk).le) hpiece


/-! ## The polarisation expansion of the intrinsic index integrand

The last algebraic ingredient of the assembly (§101.6 item 3): expanding `idxAlong` along the
perturbation `(A + δB, C + δD)` produces the linear term given by `bilAlong`. -/

/-- **The polarisation expansion**: `idxAlong` is a quadratic form whose polarisation is `bilAlong`. -/
lemma idxAlong_add_smul (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (γ : ℝ → M) (A B C D : (t : ℝ) → TangentSpace I (γ t)) (δ t : ℝ) :
    idxAlong (cov := cov) γ (fun s => A s + δ • B s) (fun s => C s + δ • D s) t
      = idxAlong (cov := cov) γ A C t + 2 * δ * bilAlong (cov := cov) γ A B C D t
        + δ ^ 2 * idxAlong (cov := cov) γ B D t := by
  have hsa : inner ℝ (curvVec cov (γ t) (B t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t)) (A t)
      = inner ℝ (curvVec cov (γ t) (A t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t)) (B t) := by
    rw [inner_curvVec_self_adjoint (cov := cov) ‹ContMDiffCovariantDerivative cov ∞› htor hmet,
      real_inner_comm]
  simp only [bilAlong, idxAlong,
    curvVec_add_left (cov := cov) ‹ContMDiffCovariantDerivative cov ∞›,
    curvVec_smul_left (cov := cov) ‹ContMDiffCovariantDerivative cov ∞›,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [hsa, real_inner_comm (C t) (D t)]
  ring

end

end Submission.IndexFTC
