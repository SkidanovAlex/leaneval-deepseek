import ChallengeDeps
import Submission.GeoCore
import Submission.Metric
import Submission.MetricCont
import Submission.ChartArc
import Submission.Rigidity
import Mathlib

open scoped Manifold ENNReal ContDiff Topology
open Set Metric
open EMetric
open Bundle

namespace Submission

open LeanEval.Geometry

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

/-! # Metric Hopf-Rinow engine (reachability)

The engine is stated on a Riemannian manifold `M` (so that C1 paths of controlled length
exist) together with a per-point local *normal-ball structure* (hypotheses `LocHyps`):
radial identity, two-sided arcs, metric-ball-into-image, injectivity, small-ball compactness,
the *corner* estimate, global geodesic extension, two-sided rigidity and a unit direction at
every point.

The main result of this file: `reachable` (Lemma 53 of the classical Hopf-Rinow proof):
every point `y` with `edist p y < top` is reached from `p` by a unit geodesic `gamma` that
realises the distance on `[0, edist p y]`.


## ROADMAP for proving `reachable` (child task: fill the `sorry`)

Notation: write `d a b` for `edist a b`, `|v|` for `mnorm (ld.ge0 x) v`, `E x v` for
`ld.Exp x v`, `ρ x` for `ld.ρ0 x`.  All hypotheses `h : LocHyps ld`.

Let `x y : M` with `e := edist x y < ⊤`; `r := e.toReal` (`0 ≤ r`, `ofReal r = e`).

If `r = 0` then `y = x`; using `h.dir x` pick a unit `W` and `h.ext x W` gives a `UnitGeo`
curve through `x`; the claims are then trivial (only `t = 0` occurs).  Assume `r > 0`.

(0) **Local radial facts** (from `h.radial`, `h.arc`, `h.surj`, `h.inj`):
    - for `0 ≤ a ≤ b < ρx/2` and unit `W`: `d (E x (a•W)) (E x (b•W)) = ofReal (b-a)`; in
      particular `d x (E x (t•W)) = ofReal t` for `0 ≤ t < ρx`.
    - (sphere) for `0 < ε < ρx`: the metric sphere `S(x,ε) := {z | d x z = ofReal ε}`
      equals `E x '' {v | |v| = ε}`; it is nonempty (`h.dir` + `h.radial`) and compact
      (`h.ball_comp`: `S ⊆ closedBall x (ofReal ε)`, closed subset; closedness via
      continuity of `d x ·` and `isClosed_eq` or `EMetric.isClosed_closedBall`).
(1) **extend a unit arc**: for unit `W`, `h.ext x W` gives a `UnitGeo` curve `γ` with
    `γ 0 = x` and `γ t = E x (t•W)` for `|t| < ρ x`.  Such `γ` is *realising on* `[0, ρx/2]`:
    `d x (γ t) = ofReal t` for `0 ≤ t < ρx` (radial identity + agreement).
    (`UnitGeo` also gives global Lipschitz bounds: `Submission.UnitGeo.lipschitz_le`.)
(2) **initial sphere minimiser**: with `0 < ε < min (ρ x / 2) (r / 2)`:
    let `x0 ∈ S(x,ε)` be a minimiser of `d · y` on `S(x,ε)`
    (`IsCompact.exists_isMinOn`).  Then `d x0 y = ofReal (r - ε)`:
    - `≥`: triangle `e ≤ d x x0 + d x0 y`, `d x x0 = ofReal ε`, `e = ofReal r`; conclude with
      `ENNReal.ofReal_sub` and subtraction monotonicity (all values finite, or use
      `ENNReal.le_sub_of_add_le_left`-style; alternatively pass through `ENNReal.toReal`).
    - `≤`: **the crossing argument**.  Suppose `d x0 y > ofReal (r-ε)`.  Since
      `e = ofReal r < ofReal ε + d x0 y`, pick (using
      `Manifold.exists_lt_locally_constant_of_riemannianEDist_lt`; recall
      `edist = riemannianEDist` by `IsRiemannianManifold.out`) a continuous path
      `σ : ℝ → M` with `σ 0 = x`, `σ 1 = y`, `pathELength I σ 0 1 < ofReal ε + d x0 y`.
      By the real intermediate value theorem applied to `u ↦ (d x (σ u)).toReal` there is
      `u0 ∈ (0,1)` with `d x (σ u0) = ofReal ε`; let `z := σ u0 ∈ S(x,ε)`.  The sub-path
      bound `d z y ≤ pathELength I σ u0 1`
      (`Manifold.riemannianEDist_le_pathELength` on `Icc u0 1`, path monotonicity) gives
      `d z y < d x0 y`, contradicting minimality of `x0`.  [Only place using paths.]
(3) **choose the geodesic**: `x0 ∈ S(x,ε) = E x '' {|v|=ε}`; pick a unit `ŵ` with
    `E x (ε•ŵ) = x0`; let `c : ℝ → M` be the unit geodesic from `h.ext x ŵ`.  Then
    `c ε = x0` (agreement), so `d (c ε) y = ofReal (r - ε)`.
(4) **the good set**: `A := {t ∈ Icc 0 r | d (c t) y = ofReal (r - t)}`.
    - `0 ∈ A`; `A` is closed in `Icc 0 r` (continuity of `c` and of `d · y`, `isClosed_eq`);
    - if `t0 ∈ A` and `0 ≤ t ≤ t0` then `t ∈ A`: lower bound
      `d (c t) y ≥ ofReal (r - t)` from `e ≤ d x (c t) + d (c t) y` and `d x (c t) ≤ ofReal t`
      (`ofReal_sub`, sub-monotonicity); upper bound via Lipschitz and `t0 ∈ A`;
    - `ε ∈ A`.
(5) **extension lemma (no-kink step)**:  for every `t0 ∈ A` with `0 < t0 < r` there is
    `η > 0` with `t0 + η < r` and `t0 + η ∈ A`.
    Put `p0 := c t0`, `D := r - t0` (so `d p0 y = ofReal D`, and `d x (c t) = ofReal t` for
    `0 ≤ t ≤ t0`).  Apply `h.rig p0 c t0 rfl c_unit` to get the rigidity window `δ_rig` and
    unit direction `v` with `c t = E p0 ((t - t0)•v)` for `|t - t0| < δ_rig`.  Pick
    `ε0 := min (ρ p0 / 4) (D / 2) (δ_rig / 2)`.  Let `x0'` minimise `d · y` on
    `S(p0, ε0)`.  The crossing argument of (2) (with `p0` in place of `x`, `D` in place of
    `r`) gives `d x0' y = ofReal (D - ε0)`.  Then:
    - `d x x0' = ofReal (t0 + ε0)` (lower bound via the triangle through `y`; upper bound via
      `c` on `[0,t0]` followed by the radial arc `p0 → x0'` of length `ε0`);
    - let `ŵ0` be the unit direction of `x0'` from `p0` (`x0' = E p0 (ε0 • ŵ0)`).  **Show
      `v = ŵ0`** by contradiction using `h.corner p0 v ŵ0`: if `v ≠ ŵ0`, with
      `δ := min (δ_rig/2) (ε0/2) (t0/2) (δ0 v ŵ0)` (from the corner hypothesis) the shortcut
      `c (t0 - δ) = E p0 (-(δ•v))`, `E p0 (δ•ŵ0)`, `E p0 (ε0•ŵ0) = x0'` gives
      `d x x0' ≤ ofReal (t0-δ) + d (E p0 (-(δ•v))) (E p0 (δ•ŵ0)) + ofReal (ε0-δ)
              < ofReal (t0-δ) + ofReal (2δ) + ofReal (ε0-δ) = ofReal (t0+ε0)`,
      contradicting `d x x0' = ofReal (t0+ε0)`.
    - hence `c (t0 + ε0) = E p0 (ε0 • v) = E p0 (ε0 • ŵ0) = x0'` (rigidity window covers
      `ε0`), and `d (c (t0+ε0)) y = ofReal (D - ε0) = ofReal (r - (t0+ε0))`: `t0 + ε0 ∈ A`.
(6) **conclude**: `s := sup A` (in `ℝ`).  If `s < r` then `s ∈ A` (closed) and `0 < s` (as
    `ε ∈ A`); the extension lemma (5) at `t0 := s` contradicts maximality.  So `s = r`;
    since `A` is closed in `Icc 0 r`, `r ∈ A`: `d (c r) y = 0`, so `c r = y`
    (`EMetricSpace.eq_of_edist_eq_zero`).  Return `c`.

Useful API (all VERIFIED): `Submission.UnitGeo` (`isLocLinear`, `continuous`,
`lipschitz_le`), `Submission.Realises`, `Submission.mnorm`/`mnorm_nonneg`,
`Manifold.pathELength`, `Manifold.riemannianEDist_le_pathELength`,
`Manifold.exists_lt_locally_constant_of_riemannianEDist_lt`, `IsRiemannianManifold.out`,
`Manifold.pathELength_mono`, `EMetricSpace.eq_of_edist_eq_zero`,
`ENNReal.ofReal_sub`/`ofReal_add`/`toReal_ofReal`/`ofReal_toReal`,
`ENNReal.le_sub_of_add_le_left`, `isClosed_eq`, `IsCompact.exists_isMinOn`,
`EMetric.isClosed_closedBall`, `Metric.IsLocLinear.edist_le_of_le`.  You may add helpers and
prove the intermediate stages as separate `lemma`s in this file.  `edist = riemannianEDist I`
on `M`, and all distances that occur are `< ⊤`; you may pass through `ENNReal.toReal`.

Do NOT change the statement/name of `reachable`; no `sorry`/`admit`/axiom may remain.
-/

/-- per-point local structure: radius, chart bilinear form, radial map. -/
structure LocData (M : Type*) [EMetricSpace M] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  ρ0 : M → ℝ
  ge0 : M → E →L[ℝ] E →L[ℝ] ℝ
  Exp : M → E → M

/-- The local hypotheses of the engine, stated at every point of `M`. -/
structure LocHyps {M : Type*} [EMetricSpace M] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (ld : LocData M E) : Prop where
  rho_pos : ∀ x : M, 0 < ld.ρ0 x
  ge_symm : ∀ x : M, ∀ u v : E, (ld.ge0 x) u v = (ld.ge0 x) v u
  ge_pos : ∀ x : M, ∀ v : E, v ≠ 0 → 0 < (ld.ge0 x) v v
  radial : ∀ x : M, ∀ v : E, mnorm (ld.ge0 x) v < ld.ρ0 x →
      edist x (ld.Exp x v) = ENNReal.ofReal (mnorm (ld.ge0 x) v)
  arc : ∀ x : M, ∀ W : E, mnorm (ld.ge0 x) W = 1 → ∀ ⦃s t : ℝ⦄,
      |s| < ld.ρ0 x → |t| < ld.ρ0 x → s ≤ t →
      edist (ld.Exp x (s • W)) (ld.Exp x (t • W)) = ENNReal.ofReal (t - s)
  surj : ∀ x : M, ∀ y : M, edist x y < ENNReal.ofReal (ld.ρ0 x) →
      ∃ v : E, mnorm (ld.ge0 x) v < ld.ρ0 x ∧ ld.Exp x v = y
  inj : ∀ x : M, ∀ v w : E, mnorm (ld.ge0 x) v < ld.ρ0 x → mnorm (ld.ge0 x) w < ld.ρ0 x →
      ld.Exp x v = ld.Exp x w → v = w
  ball_comp : ∀ x : M, ∀ ρ : ℝ, 0 < ρ → ρ < ld.ρ0 x →
      IsCompact (closedBall x (ENNReal.ofReal ρ))
  corner : ∀ x : M, ∀ v1 v2 : E, mnorm (ld.ge0 x) v1 = 1 → mnorm (ld.ge0 x) v2 = 1 → v1 ≠ v2 →
      ∃ δ0 > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        edist (ld.Exp x (-(δ • v1))) (ld.Exp x (δ • v2)) < ENNReal.ofReal (2 * δ)
  ext : ∀ x : M, ∀ W : E, mnorm (ld.ge0 x) W = 1 → ∃ γ : ℝ → M,
      UnitGeo γ ∧ γ 0 = x ∧ ∀ t : ℝ, |t| < ld.ρ0 x → γ t = ld.Exp x (t • W)
  rig : ∀ x : M, ∀ γ : ℝ → M, ∀ t₀ : ℝ, γ t₀ = x → UnitGeo γ →
      ∃ δ > 0, δ ≤ ld.ρ0 x ∧ ∃ v : E, mnorm (ld.ge0 x) v = 1 ∧
        ∀ t : ℝ, |t - t₀| < δ → γ t = ld.Exp x ((t - t₀) • v)
  dir : ∀ x : M, ∃ W : E, mnorm (ld.ge0 x) W = 1

namespace Engine

section ManifoldContext

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
variable [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
variable [IsRiemannianManifold I M]

section EngineHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
variable [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
variable [IsRiemannianManifold I M]


/-- mnorm of a scalar multiple (quadratic form is bilinear). -/
lemma quad_smul (ld : LocData M E) (x : M) (a b : ℝ) (v w : E) :
    (ld.ge0 x) (a • v) (b • w) = (a * b) * (ld.ge0 x) v w := by
  rw [map_smul (ld.ge0 x) a v]
  change a • ((ld.ge0 x) v (b • w)) = (a * b) * (ld.ge0 x) v w
  rw [map_smul ((ld.ge0 x) v) b w]
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-- mnorm of a scalar multiple. -/
lemma mnorm_smul (ld : LocData M E) (x : M) (a : ℝ) (v : E) (hq : 0 ≤ (ld.ge0 x) v v) :
    mnorm (ld.ge0 x) (a • v) = |a| * mnorm (ld.ge0 x) v := by
  unfold mnorm
  have hq' : (ld.ge0 x) (a • v) (a • v) = (a * a) * (ld.ge0 x) v v := quad_smul ld x a a v v
  rw [hq']
  have hsc : (a * a) * (ld.ge0 x) v v = (|a| * |a|) * (ld.ge0 x) v v := by
    calc
      (a * a) * (ld.ge0 x) v v = (a ^ 2) * (ld.ge0 x) v v := by ring
      _ = (|a| ^ 2) * (ld.ge0 x) v v := by rw [sq_abs]
      _ = (|a| * |a|) * (ld.ge0 x) v v := by ring
  rw [hsc]
  rw [Real.sqrt_mul (mul_self_nonneg (|a|)) ((ld.ge0 x) v v)]
  have hsqrt : Real.sqrt (|a| * |a|) = |a| := by
    rw [show |a| * |a| = |a| ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg a)]
  rw [hsqrt]

/-- A metric-unit vector is nonzero. -/
lemma unit_ne_zero (ld : LocData M E) (x : M) (W : E)
    (hW : mnorm (ld.ge0 x) W = 1) : W ≠ 0 := by
  intro hz
  subst hz
  simp [mnorm] at hW

/-- The quadratic form of a metric-unit vector is nonnegative. -/
lemma quad_nonneg_of_unit (ld : LocData M E) (h : LocHyps ld) (x : M) (W : E)
    (hW : mnorm (ld.ge0 x) W = 1) : 0 ≤ (ld.ge0 x) W W := by
  exact le_of_lt (h.ge_pos x W (unit_ne_zero ld x W hW))

/-- radial distance identity for a unit direction: `edist x (Exp x (t • W)) = ofReal |t|`. -/
lemma edist_x_exp_smul (ld : LocData M E) (h : LocHyps ld) (x : M) (W : E)
    (hW : mnorm (ld.ge0 x) W = 1) {t : ℝ} (ht : |t| < ld.ρ0 x) :
    edist x (ld.Exp x (t • W)) = ENNReal.ofReal |t| := by
  have hmm : mnorm (ld.ge0 x) (t • W) = |t| := by
    rw [mnorm_smul ld x t W (quad_nonneg_of_unit ld h x W hW), hW]
    simp
  have hmm_lt : mnorm (ld.ge0 x) (t • W) < ld.ρ0 x := by
    rwa [← hmm] at ht
  have hd := h.radial x (t • W) hmm_lt
  rwa [hmm] at hd

/-- radial distance identity for nonnegative parameter. -/
lemma edist_x_exp_smul_of_nonneg (ld : LocData M E) (h : LocHyps ld) (x : M) (W : E)
    (hW : mnorm (ld.ge0 x) W = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < ld.ρ0 x) :
    edist x (ld.Exp x (t • W)) = ENNReal.ofReal t := by
  have habs : |t| < ld.ρ0 x := by rwa [abs_of_nonneg ht0]
  have hd := edist_x_exp_smul ld h x W hW habs
  have : |t| = t := abs_of_nonneg ht0
  rwa [this] at hd

/-- the two-sided arc identity. -/
lemma arc_edist (ld : LocData M E) (h : LocHyps ld) (x : M) (W : E)
    (hW : mnorm (ld.ge0 x) W = 1) {s t : ℝ} (hs : |s| < ld.ρ0 x) (ht : |t| < ld.ρ0 x)
    (hst : s ≤ t) :
    edist (ld.Exp x (s • W)) (ld.Exp x (t • W)) = ENNReal.ofReal (t - s) := by
  exact h.arc x W hW hs ht hst

/-- Every point `y` at radius `ε < ρ0 x` from `x` is `Exp x (ε • W)` for a metric-unit `W`. -/
lemma exists_unit_direction (ld : LocData M E) (h : LocHyps ld) (x y : M) {ε : ℝ}
    (hε0 : 0 < ε) (hxy : edist x y = ENNReal.ofReal ε) (hερ : ε < ld.ρ0 x) :
    ∃ W : E, mnorm (ld.ge0 x) W = 1 ∧ ld.Exp x (ε • W) = y := by
  have hρx0 : 0 < ld.ρ0 x := h.rho_pos x
  have hlt : edist x y < ENNReal.ofReal (ld.ρ0 x) := by
    rw [hxy]
    exact (ENNReal.ofReal_lt_ofReal_iff hρx0).mpr hερ
  rcases h.surj x y hlt with ⟨w, hwm, hwE⟩
  have hmm_eq : mnorm (ld.ge0 x) w = ε := by
    have hd := h.radial x w hwm
    have hε : edist x (ld.Exp x w) = ENNReal.ofReal ε := by rw [hwE, hxy]
    have hmm' : ENNReal.ofReal (mnorm (ld.ge0 x) w) = ENNReal.ofReal ε := by
      rw [← hd]
      exact hε
    exact (ENNReal.ofReal_eq_ofReal_iff (mnorm_nonneg (ld.ge0 x) w) (le_of_lt hε0)).mp hmm'
  let W : E := ε⁻¹ • w
  refine ⟨W, ?_, ?_⟩
  · have hwne : w ≠ 0 := by
      intro hz
      subst hz
      have : (0 : ℝ) = ε := by simpa [mnorm] using hmm_eq
      linarith
    have hq : 0 ≤ (ld.ge0 x) w w := le_of_lt (h.ge_pos x w hwne)
    dsimp [W]
    rw [mnorm_smul ld x (ε⁻¹) w hq, hmm_eq]
    rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hε0))]
    exact inv_mul_cancel₀ (ne_of_gt hε0)
  · dsimp [W]
    rw [← hwE]
    congr 1
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hε0)]
    simp



/-- The metric sphere of radius `ε < ρ0 x` around `x` is compact. -/
lemma sphere_compact (ld : LocData M E) (h : LocHyps ld) (x : M) {ε : ℝ} (hε0 : 0 < ε)
    (hερ : ε < ld.ρ0 x) : IsCompact {z : M | edist x z = ENNReal.ofReal ε} := by
  refine IsCompact.of_isClosed_subset (h.ball_comp x ε hε0 hερ) ?_ ?_
  · apply isClosed_eq
    · have hcc : Continuous (fun z : M => edist x z) :=
        continuous_edist.comp (continuous_const.prodMk continuous_id : Continuous (fun z : M => (x, z)))
      exact hcc
    · exact continuous_const
  · intro z hz
    change z ∈ Metric.closedEBall x (ENNReal.ofReal ε)
    rw [Metric.mem_closedEBall, edist_comm]
    exact le_of_eq hz

/-- The metric sphere of radius `ε < ρ0 x` around `x` is nonempty. -/
lemma sphere_nonempty (ld : LocData M E) (h : LocHyps ld) (x : M) {ε : ℝ} (hε0 : 0 < ε)
    (hερ : ε < ld.ρ0 x) : ({z : M | edist x z = ENNReal.ofReal ε}).Nonempty := by
  rcases h.dir x with ⟨W, hW⟩
  refine ⟨ld.Exp x (ε • W), ?_⟩
  have hεabs : |ε| = ε := abs_of_nonneg (le_of_lt hε0)
  have habs : |ε| < ld.ρ0 x := by
    rw [hεabs]
    exact hερ
  have hd := edist_x_exp_smul ld h x W hW habs
  simpa [hεabs] using hd

/-- On the compact sphere of radius `ε < ρ0 x` around `x`, the distance-to-`y` attains its
minimum; if `y` is at finite distance `r0 > ε`, the minimiser satisfies
`edist x0 y = ofReal (r0 - ε)`. -/
lemma sphere_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (ld : LocData M E) (h : LocHyps ld) (x y : M) (ε : ℝ) (hε0 : 0 < ε)
    (hερ : ε < ld.ρ0 x) (hfin : edist x y < ⊤) (hεr : ε < (edist x y).toReal) :
    ∃ x0 : M, edist x x0 = ENNReal.ofReal ε ∧
      edist x0 y = ENNReal.ofReal ((edist x y).toReal - ε) := by
  let r0 : ℝ := (edist x y).toReal
  let S : Set M := {z : M | edist x z = ENNReal.ofReal ε}
  have hScomp : IsCompact S := sphere_compact ld h x hε0 hερ
  have hSne : S.Nonempty := sphere_nonempty ld h x hε0 hερ
  have hfcont : ContinuousOn (fun z : M => edist z y) S := by
    have hcc : Continuous (fun z : M => edist z y) :=
      continuous_edist.comp (continuous_id.prodMk continuous_const : Continuous (fun z : M => (z, y)))
    exact hcc.continuousOn
  rcases hScomp.exists_isMinOn hSne (f := fun z : M => edist z y) hfcont with ⟨x0, hx0S, hx0min⟩
  refine ⟨x0, hx0S, ?_⟩
  have hxy_r0 : edist x y = ENNReal.ofReal r0 := by
    dsimp [r0]
    exact (ENNReal.ofReal_toReal (ne_of_lt hfin)).symm
  have hr0_nonneg : 0 ≤ r0 := by dsimp [r0]; exact ENNReal.toReal_nonneg
  have hfin0 : edist x0 y ≠ ⊤ := by
    have hb : edist x0 y ≤ ENNReal.ofReal ε + edist x y := by
      calc
        edist x0 y ≤ edist x0 x + edist x y := edist_triangle (x := x0) (y := x) (z := y)
        _ = ENNReal.ofReal ε + edist x y := by
          congr 1
          rw [edist_comm]
          exact hx0S
    have hb' : ENNReal.ofReal ε + edist x y < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hfin⟩
    exact ne_of_lt (lt_of_le_of_lt hb hb')
  have hge : ENNReal.ofReal (r0 - ε) ≤ edist x0 y := by
    have htri : edist x y ≤ edist x x0 + edist x0 y := edist_triangle (x := x) (y := x0) (z := y)
    have htri' : ENNReal.ofReal r0 ≤ ENNReal.ofReal ε + edist x0 y := by
      have hrew : edist x x0 + edist x0 y = ENNReal.ofReal ε + edist x0 y := by rw [hx0S]
      rwa [hxy_r0, hrew] at htri
    have hsum_top : ENNReal.ofReal ε + edist x0 y ≠ ⊤ := by
      exact ne_of_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, lt_top_iff_ne_top.mpr hfin0⟩)
    have htr := ENNReal.toReal_mono hsum_top htri'
    have hle_r : r0 ≤ ε + (edist x0 y).toReal := by
      simpa [ENNReal.toReal_ofReal hr0_nonneg,
        ENNReal.toReal_add (ne_top_of_lt ENNReal.ofReal_lt_top) hfin0,
        ENNReal.toReal_ofReal (le_of_lt hε0)] using htr
    have hge_real : r0 - ε ≤ (edist x0 y).toReal := by linarith
    rw [← ENNReal.ofReal_toReal hfin0]
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mpr hge_real
  apply le_antisymm ?_ hge
  -- the crossing argument for the upper bound
  apply le_of_not_gt
  intro hgt
  have hεsub : 0 ≤ r0 - ε := by linarith
  have h1 : edist x y = ENNReal.ofReal ε + ENNReal.ofReal (r0 - ε) := by
    calc
      edist x y = ENNReal.ofReal r0 := hxy_r0
      _ = ENNReal.ofReal (ε + (r0 - ε)) := by congr 1; ring
      _ = ENNReal.ofReal ε + ENNReal.ofReal (r0 - ε) := by rw [ENNReal.ofReal_add (le_of_lt hε0) hεsub]
  have hsum : edist x y < ENNReal.ofReal ε + edist x0 y := by
    calc
      edist x y = ENNReal.ofReal ε + ENNReal.ofReal (r0 - ε) := h1
      _ < ENNReal.ofReal ε + edist x0 y := ENNReal.add_lt_add_left (ne_top_of_lt ENNReal.ofReal_lt_top) hgt
  have hpath : Manifold.riemannianEDist I x y < ENNReal.ofReal ε + edist x0 y := by
    rwa [IsRiemannianManifold.out (I := I) x y] at hsum
  rcases Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := I) hpath (by norm_num : (0 : ℝ) < 1) with
    ⟨γ, hγ0, hγ1, hγsm, hγlen, _⟩
  have hγOn (ss : Set ℝ) : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ ss := hγsm.contMDiffOn
  have hγcont : Continuous γ := hγsm.continuous
  have htop1 : Manifold.pathELength I γ 0 1 < ⊤ :=
    lt_trans hγlen (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, lt_top_iff_ne_top.mpr hfin0⟩)
  have hγfin : ∀ u ∈ Icc (0 : ℝ) 1, edist x (γ u) ≠ ⊤ := by
    intro u hu
    have htmp : Manifold.riemannianEDist I x (γ u) ≤ Manifold.pathELength I γ 0 u :=
      Manifold.riemannianEDist_le_pathELength (I := I) (hγOn (Icc (0 : ℝ) u)) hγ0 rfl hu.1
    have hmono : Manifold.pathELength I γ 0 u ≤ Manifold.pathELength I γ 0 1 :=
      Manifold.pathELength_mono (a := (0 : ℝ)) (b := u) (a' := (0 : ℝ)) (b' := (1 : ℝ)) le_rfl hu.2
    have hed : edist x (γ u) < ⊤ := by
      have htmp' : edist x (γ u) ≤ Manifold.pathELength I γ 0 u := by
        rw [← IsRiemannianManifold.out (I := I) x (γ u)] at htmp
        exact htmp
      exact lt_of_le_of_lt htmp' (lt_of_le_of_lt hmono htop1)
    exact ne_of_lt hed
  have hcont_f : ContinuousOn (fun u : ℝ => edist x (γ u)) (Icc (0 : ℝ) 1) := by
    have hcc : Continuous (fun u : ℝ => edist x (γ u)) :=
      continuous_edist.comp (continuous_const.prodMk hγcont : Continuous (fun u : ℝ => (x, γ u)))
    exact hcc.continuousOn
  have hfcont : ContinuousOn (fun u : ℝ => (edist x (γ u)).toReal) (Icc (0 : ℝ) 1) := by
    have hmaps : Set.MapsTo (fun u : ℝ => edist x (γ u)) (Icc (0 : ℝ) 1)
        {a : ℝ≥0∞ | a ≠ ⊤} := by
      intro u hu
      exact hγfin u hu
    have hc : ContinuousOn (ENNReal.toReal ∘ (fun u : ℝ => edist x (γ u))) (Icc (0 : ℝ) 1) :=
      ContinuousOn.comp ENNReal.continuousOn_toReal hcont_f hmaps
    convert hc using 1
    funext u
    rfl
  have hf0 : (fun u : ℝ => (edist x (γ u)).toReal) 0 = 0 := by simp [hγ0]
  have hf1 : (fun u : ℝ => (edist x (γ u)).toReal) 1 = r0 := by
    dsimp
    rw [hγ1]
  have hmem : ε ∈ Set.Icc ((fun u : ℝ => (edist x (γ u)).toReal) 0)
      ((fun u : ℝ => (edist x (γ u)).toReal) 1) := by
    rw [hf0, hf1]
    exact ⟨le_of_lt hε0, hεr.le⟩
  rcases intermediate_value_Icc (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1) hfcont hmem with
    ⟨u0, hu0, hu0eq⟩
  let z : M := γ u0
  have hu00 : 0 ≤ u0 := hu0.1
  have hu01 : u0 ≤ 1 := hu0.2
  have hzfin : edist x z ≠ ⊤ := hγfin u0 hu0
  have hz_sphere : edist x z = ENNReal.ofReal ε := by
    have hz' : (edist x z).toReal = ε := by simpa [z] using hu0eq
    calc
      edist x z = ENNReal.ofReal (edist x z).toReal := (ENNReal.ofReal_toReal hzfin).symm
      _ = ENNReal.ofReal ε := by rw [hz']
  have hsplit : Manifold.pathELength I γ 0 u0 + Manifold.pathELength I γ u0 1 =
      Manifold.pathELength I γ 0 1 := Manifold.pathELength_add hu00 hu01
  have hsub_le : ENNReal.ofReal ε ≤ Manifold.pathELength I γ 0 u0 := by
    have hd : edist x (γ u0) ≤ Manifold.pathELength I γ 0 u0 := by
      have htmp : Manifold.riemannianEDist I x (γ u0) ≤ Manifold.pathELength I γ 0 u0 :=
        Manifold.riemannianEDist_le_pathELength (I := I) (hγOn (Icc (0 : ℝ) u0)) hγ0 rfl hu00
      rw [← IsRiemannianManifold.out (I := I) x (γ u0)] at htmp
      exact htmp
    rwa [hz_sphere] at hd
  have hP_lt : Manifold.pathELength I γ u0 1 < edist x0 y := by
    have h1' : ENNReal.ofReal ε + Manifold.pathELength I γ u0 1 < ENNReal.ofReal ε + edist x0 y := by
      calc
        ENNReal.ofReal ε + Manifold.pathELength I γ u0 1 ≤
            Manifold.pathELength I γ 0 u0 + Manifold.pathELength I γ u0 1 :=
                add_le_add_left hsub_le (Manifold.pathELength I γ u0 1)
        _ = Manifold.pathELength I γ 0 1 := hsplit
        _ < ENNReal.ofReal ε + edist x0 y := hγlen
    exact (ENNReal.add_lt_add_iff_left (ne_top_of_lt ENNReal.ofReal_lt_top : ENNReal.ofReal ε ≠ ⊤)).mp h1'
  have hdz : edist z y ≤ Manifold.pathELength I γ u0 1 := by
    have htmp : Manifold.riemannianEDist I (γ u0) y ≤ Manifold.pathELength I γ u0 1 :=
      Manifold.riemannianEDist_le_pathELength (I := I) (hγOn (Icc u0 1)) rfl hγ1 hu01
    have htmp' : edist (γ u0) y ≤ Manifold.pathELength I γ u0 1 := by
      rw [← IsRiemannianManifold.out (I := I) (γ u0) y] at htmp
      exact htmp
    simpa [z] using htmp' 
  have hz_lt : edist z y < edist x0 y := lt_of_le_of_lt (by simpa [z] using hdz) hP_lt
  have hmin : edist x0 y ≤ edist z y := by
    simpa [S] using (hx0min hz_sphere)
  exact (not_lt_of_ge hmin) hz_lt

/-- The "good set" predicate: `t ∈ [0, r]` and `c t` is at distance `r - t` from `y`. -/
def Good {M : Type*} [EMetricSpace M] (c : ℝ → M) (y : M) (r : ℝ) (t : ℝ) : Prop :=
  0 ≤ t ∧ t ≤ r ∧ edist (c t) y = ENNReal.ofReal (r - t)

/-- The good set is closed. -/
lemma good_isClosed (ld : LocData M E) (h : LocHyps ld) (y : M) (r : ℝ) (c : ℝ → M)
    (hc_unit : UnitGeo c) : IsClosed {t : ℝ | Good c y r t} := by
  have hcc : Continuous (fun t : ℝ => edist (c t) y) := by
    exact continuous_edist.comp
      ((UnitGeo.continuous hc_unit).prodMk continuous_const :
        Continuous (fun t : ℝ => (c t, y)))
  have hcont2 : Continuous (fun t : ℝ => ENNReal.ofReal (r - t)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_id)
  have hEqClosed : IsClosed {t : ℝ | edist (c t) y = ENNReal.ofReal (r - t)} :=
    isClosed_eq hcc hcont2
  rw [show {t : ℝ | Good c y r t} =
      Ici (0 : ℝ) ∩ Iic r ∩ {t : ℝ | edist (c t) y = ENNReal.ofReal (r - t)} by
    ext t
    simp [Good, and_assoc]]
  exact (isClosed_Ici.inter isClosed_Iic).inter hEqClosed

/-- If `t0` is good then every `0 ≤ s ≤ t0` is good, and `c` realises the distance from
`x` up to time `t0`. -/
lemma good_down (ld : LocData M E) (h : LocHyps ld) (x y : M) (r : ℝ) (c : ℝ → M)
    (hc_unit : UnitGeo c) (hc0 : c 0 = x) (hr_nonneg : 0 ≤ r) (hxyr : edist x y = ENNReal.ofReal r)
    {t0 s : ℝ} (ht0 : Good c y r t0) (hs0 : 0 ≤ s) (hst : s ≤ t0) :
    Good c y r s ∧ edist x (c s) = ENNReal.ofReal s := by
  have ht0le : 0 ≤ t0 := ht0.1
  have ht0r : t0 ≤ r := ht0.2.1
  have hct0y : edist (c t0) y = ENNReal.ofReal (r - t0) := ht0.2.2
  -- edist x (c t0) = ofReal t0
  have hxt0_le : edist x (c t0) ≤ ENNReal.ofReal t0 := by
    have hl := UnitGeo.lipschitz_le hc_unit ht0le
    simpa [hc0] using hl
  have hxt0_ge : ENNReal.ofReal t0 ≤ edist x (c t0) := by
    have htri : edist x y ≤ edist x (c t0) + edist (c t0) y :=
      edist_triangle (x := x) (y := c t0) (z := y)
    have htri' : ENNReal.ofReal r ≤ edist x (c t0) + ENNReal.ofReal (r - t0) := by
      simpa [hxyr, hct0y] using htri
    have hrt0 : 0 ≤ r - t0 := by linarith
    have hsub : ENNReal.ofReal r - ENNReal.ofReal (r - t0) = ENNReal.ofReal t0 := by
      rw [← ENNReal.ofReal_sub r hrt0]
      congr 1
      ring
    have hm : ENNReal.ofReal r - ENNReal.ofReal (r - t0) ≤ edist x (c t0) :=
      (tsub_le_iff_right.mpr htri')
    rwa [hsub] at hm
  have hxt0 : edist x (c t0) = ENNReal.ofReal t0 := le_antisymm hxt0_le hxt0_ge
  -- edist x (c s) = ofReal s
  have hxs_le : edist x (c s) ≤ ENNReal.ofReal s := by
    have hl := UnitGeo.lipschitz_le hc_unit hs0
    simpa [hc0] using hl
  have hcsct0 : edist (c s) (c t0) ≤ ENNReal.ofReal (t0 - s) := by
    simpa using (UnitGeo.lipschitz_le hc_unit hst)
  have hxs_ge : ENNReal.ofReal s ≤ edist x (c s) := by
    have htri2 : edist x (c t0) ≤ edist x (c s) + edist (c s) (c t0) :=
      edist_triangle (x := x) (y := c s) (z := c t0)
    have hle : ENNReal.ofReal t0 ≤ edist x (c s) + ENNReal.ofReal (t0 - s) := by
      calc
        ENNReal.ofReal t0 = edist x (c t0) := hxt0.symm
        _ ≤ edist x (c s) + edist (c s) (c t0) := htri2
        _ ≤ edist x (c s) + ENNReal.ofReal (t0 - s) :=
            add_le_add_right hcsct0 (edist x (c s))
    have ht0s : 0 ≤ t0 - s := by linarith
    have hsub : ENNReal.ofReal t0 - ENNReal.ofReal (t0 - s) = ENNReal.ofReal s := by
      rw [← ENNReal.ofReal_sub t0 ht0s]
      congr 1
      ring
    have hm : ENNReal.ofReal t0 - ENNReal.ofReal (t0 - s) ≤ edist x (c s) :=
      (tsub_le_iff_right.mpr hle)
    rwa [hsub] at hm
  have hxs : edist x (c s) = ENNReal.ofReal s := le_antisymm hxs_le hxs_ge
  -- edist (c s) y = ofReal (r - s)
  have hy_le : edist (c s) y ≤ ENNReal.ofReal (r - s) := by
    calc
      edist (c s) y ≤ edist (c s) (c t0) + edist (c t0) y :=
        edist_triangle (x := c s) (y := c t0) (z := y)
      _ ≤ ENNReal.ofReal (t0 - s) + ENNReal.ofReal (r - t0) := by
        rw [hct0y]
        exact add_le_add_left hcsct0 (ENNReal.ofReal (r - t0))
      _ = ENNReal.ofReal (r - s) := by
        have ht0s : 0 ≤ t0 - s := by linarith
        have hrt0 : 0 ≤ r - t0 := by linarith
        rw [← ENNReal.ofReal_add ht0s hrt0]
        congr 1
        ring
  have hy_ge : ENNReal.ofReal (r - s) ≤ edist (c s) y := by
    have htri3 : edist x y ≤ edist x (c s) + edist (c s) y :=
      edist_triangle (x := x) (y := c s) (z := y)
    have hle2 : ENNReal.ofReal r ≤ ENNReal.ofReal s + edist (c s) y := by
      calc
        ENNReal.ofReal r = edist x y := hxyr.symm
        _ ≤ edist x (c s) + edist (c s) y := htri3
        _ = ENNReal.ofReal s + edist (c s) y := by rw [hxs]
    have hs0' : 0 ≤ s := hs0
    have hsub : ENNReal.ofReal r - ENNReal.ofReal s = ENNReal.ofReal (r - s) := by
      rw [← ENNReal.ofReal_sub r hs0']
    have hm : ENNReal.ofReal r - ENNReal.ofReal s ≤ edist (c s) y :=
      (tsub_le_iff_right.mpr (by simpa [add_comm] using hle2))
    rwa [hsub] at hm
  have hcsy : edist (c s) y = ENNReal.ofReal (r - s) := le_antisymm hy_le hy_ge
  exact ⟨⟨hs0, le_trans hst ht0r, hcsy⟩, hxs⟩

/-- The no-kink extension step: from a good time `0 < t0 < r` one can move strictly forward
inside the good set. -/
lemma good_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (ld : LocData M E) (h : LocHyps ld) (x y : M) (r : ℝ) (c : ℝ → M)
    (hc_unit : UnitGeo c) (hc0 : c 0 = x) (hr_nonneg : 0 ≤ r) (hxyr : edist x y = ENNReal.ofReal r)
    {t0 : ℝ} (ht0 : Good c y r t0) (ht00 : 0 < t0) (ht0r : t0 < r) :
    ∃ η > 0, t0 + η < r ∧ Good c y r (t0 + η) := by
  have ht0le : 0 ≤ t0 := ht0.1
  have hct0y : edist (c t0) y = ENNReal.ofReal (r - t0) := ht0.2.2
  let p0 : M := c t0
  have hD : 0 < r - t0 := by linarith
  have hD_nonneg : 0 ≤ r - t0 := le_of_lt hD
  have hp0y : edist p0 y = ENNReal.ofReal (r - t0) := by simpa [p0] using hct0y
  have hto : (edist p0 y).toReal = r - t0 := by
    rw [hp0y]
    exact ENNReal.toReal_ofReal hD_nonneg
  have hx_t0 : edist x (c t0) = ENNReal.ofReal t0 := by
    have hgd := good_down ld h x y r c hc_unit hc0 hr_nonneg hxyr (t0 := t0) (s := t0) ht0 ht0le (le_rfl)
    exact hgd.2
  -- rigidity at p0
  rcases h.rig p0 c t0 (show c t0 = p0 from rfl) hc_unit with
    ⟨δ_rig, hδ_rig, hδ_rig_le, v, hv_unit, hv_formula⟩
  let ε0 : ℝ := min (min (ld.ρ0 p0 / 4) ((r - t0) / 2)) (δ_rig / 2)
  have hε0_pos : 0 < ε0 := by
    dsimp [ε0]
    exact lt_min (lt_min (div_pos (h.rho_pos p0) (by norm_num)) (half_pos hD)) (half_pos hδ_rig)
  have hε0_lt_ρ : ε0 < ld.ρ0 p0 := by
    have h1 : ε0 ≤ ld.ρ0 p0 / 4 := by
      dsimp [ε0]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : ld.ρ0 p0 / 4 < ld.ρ0 p0 := by linarith [h.rho_pos p0]
    exact lt_of_le_of_lt h1 h2
  have hε0_D : ε0 < r - t0 := by
    have h1 : ε0 ≤ (r - t0) / 2 := by
      dsimp [ε0]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    exact lt_of_le_of_lt h1 (half_lt_self hD)
  have hε0_lt_δ : ε0 < δ_rig := by
    have h1 : ε0 ≤ δ_rig / 2 := by
      dsimp [ε0]
      exact min_le_right _ _
    exact lt_of_le_of_lt h1 (half_lt_self hδ_rig)
  have hε0_le_ρ : |ε0| < ld.ρ0 p0 := by
    rw [abs_of_pos hε0_pos]
    exact hε0_lt_ρ
  have hfin : edist p0 y < ⊤ := by
    rw [hp0y]
    exact ENNReal.ofReal_lt_top
  have hε0_lt_toReal : ε0 < (edist p0 y).toReal := by
    rw [hto]
    exact hε0_D
  rcases sphere_min I (M := M) ld h p0 y ε0 hε0_pos hε0_lt_ρ hfin hε0_lt_toReal with
    ⟨x0', hx0'p0, hx0'y⟩
  have hx0'y' : edist x0' y = ENNReal.ofReal (r - t0 - ε0) := by
    simpa [hto] using hx0'y
  rcases exists_unit_direction ld h p0 x0' hε0_pos hx0'p0 hε0_lt_ρ with
    ⟨ŵ0, hŵ0_unit, hŵ0_exp⟩
  -- edist x x0' = ofReal (t0 + ε0)
  have hxx0'_le : edist x x0' ≤ ENNReal.ofReal (t0 + ε0) := by
    calc
      edist x x0' ≤ edist x (c t0) + edist (c t0) x0' :=
        edist_triangle (x := x) (y := c t0) (z := x0')
      _ = ENNReal.ofReal t0 + ENNReal.ofReal ε0 := by
        have hct0x0' : edist (c t0) x0' = ENNReal.ofReal ε0 := by simpa [p0] using hx0'p0
        rw [hx_t0, hct0x0']
      _ = ENNReal.ofReal (t0 + ε0) := by
        rw [← ENNReal.ofReal_add ht0le (le_of_lt hε0_pos)]
  have hxx0'_ge : ENNReal.ofReal (t0 + ε0) ≤ edist x x0' := by
    have htri : edist x y ≤ edist x x0' + edist x0' y :=
      edist_triangle (x := x) (y := x0') (z := y)
    have htri' : ENNReal.ofReal r ≤ edist x x0' + ENNReal.ofReal (r - t0 - ε0) := by
      simpa [hxyr, hx0'y'] using htri
    have hq0 : 0 ≤ r - t0 - ε0 := by linarith [hε0_D]
    have hred : ENNReal.ofReal (t0 + ε0) = ENNReal.ofReal r - ENNReal.ofReal (r - t0 - ε0) := by
      rw [← ENNReal.ofReal_sub r hq0]
      congr 1
      ring
    have hm : ENNReal.ofReal r - ENNReal.ofReal (r - t0 - ε0) ≤ edist x x0' :=
      (tsub_le_iff_right.mpr (by simpa [add_comm] using htri'))
    rwa [← hred] at hm
  have hxx0' : edist x x0' = ENNReal.ofReal (t0 + ε0) := le_antisymm hxx0'_le hxx0'_ge
  -- main: show c (t0 + ε0) = x0'
  have hstep : c (t0 + ε0) = x0' := by
    by_cases hv_eq : v = ŵ0
    · have habs : |(t0 + ε0) - t0| < δ_rig := by
        rw [show (t0 + ε0) - t0 = ε0 by ring, abs_of_pos hε0_pos]
        exact hε0_lt_δ
      have hc1 := hv_formula (t0 + ε0) habs
      calc
        c (t0 + ε0) = ld.Exp p0 (ε0 • v) := by
          simpa [show ((t0 + ε0) - t0) • v = ε0 • v by rw [show (t0 + ε0) - t0 = ε0 by ring]] using hc1
        _ = ld.Exp p0 (ε0 • ŵ0) := by rw [hv_eq]
        _ = x0' := hŵ0_exp
    · exfalso
      rcases h.corner p0 v ŵ0 hv_unit hŵ0_unit hv_eq with ⟨δ0, hδ0, hcorner⟩
      let δ : ℝ := min (min (t0 / 2) (ε0 / 2)) (min (δ_rig / 2) (δ0 / 2))
      have hδ_pos : 0 < δ := by
        dsimp [δ]
        exact lt_min (lt_min (half_pos ht00) (half_pos hε0_pos))
          (lt_min (half_pos hδ_rig) (half_pos hδ0))
      have hδ_t0 : δ < t0 := by
        have h1 : δ ≤ t0 / 2 := by
          dsimp [δ]
          exact le_trans (min_le_left _ _) (min_le_left _ _)
        exact lt_of_le_of_lt h1 (half_lt_self ht00)
      have hδ_ε0 : δ < ε0 := by
        have h1 : δ ≤ ε0 / 2 := by
          dsimp [δ]
          exact le_trans (min_le_left _ _) (min_le_right _ _)
        exact lt_of_le_of_lt h1 (half_lt_self hε0_pos)
      have hδε0 : δ ≤ ε0 := le_of_lt hδ_ε0
      have hδ_rig' : δ < δ_rig := by
        have h1 : δ ≤ δ_rig / 2 := by
          dsimp [δ]
          exact le_trans (min_le_right _ _) (min_le_left _ _)
        exact lt_of_le_of_lt h1 (half_lt_self hδ_rig)
      have hδ_δ0 : δ ≤ δ0 := by
        have h1 : δ ≤ δ0 / 2 := by
          dsimp [δ]
          exact le_trans (min_le_right _ _) (min_le_right _ _)
        linarith
      have hδ_ρ : |δ| < ld.ρ0 p0 := by
        rw [abs_of_pos hδ_pos]
        exact lt_trans hδ_ε0 hε0_lt_ρ
      have hε_ρ : |ε0| < ld.ρ0 p0 := hε0_le_ρ
      -- c (t0 - δ) = Exp p0 (-(δ • v))
      have habs : |(t0 - δ) - t0| < δ_rig := by
        have hmm : |(t0 - δ) - t0| = δ := by
          rw [show (t0 - δ) - t0 = -δ by ring, abs_neg, abs_of_pos hδ_pos]
        rwa [hmm]
      have hcA : c (t0 - δ) = ld.Exp p0 (-(δ • v)) := by
        have hf := hv_formula (t0 - δ) habs
        have hsm : ((t0 - δ) - t0) • v = -(δ • v) := by
          rw [show (t0 - δ) - t0 = -δ by ring]
          simp
        simpa [hsm] using hf
      -- distance facts along c
      have hs0δ : 0 ≤ t0 - δ := by linarith [hδ_t0]
      have hx_c : edist x (c (t0 - δ)) = ENNReal.ofReal (t0 - δ) := by
        have hgd := good_down ld h x y r c hc_unit hc0 hr_nonneg hxyr (t0 := t0) (s := t0 - δ) ht0 hs0δ (by linarith)
        exact hgd.2
      -- corner shortcut piece
      have htri1 : edist (c (t0 - δ)) (ld.Exp p0 (δ • ŵ0)) < ENNReal.ofReal (2 * δ) := by
        have hc := hcorner δ hδ_pos hδ_δ0
        rwa [← hcA] at hc
      -- radial piece Exp p0 (δ ŵ0) -> x0'
      have harc : edist (ld.Exp p0 (δ • ŵ0)) x0' = ENNReal.ofReal (ε0 - δ) := by
        have har := arc_edist ld h p0 ŵ0 hŵ0_unit (s := δ) (t := ε0) hδ_ρ hε_ρ hδε0
        simpa [hŵ0_exp] using har
      -- shortcut upper bound strictly below ofReal (t0 + ε0)
      have hsum_eq : ENNReal.ofReal (t0 - δ) +
          (ENNReal.ofReal (2 * δ) + ENNReal.ofReal (ε0 - δ)) = ENNReal.ofReal (t0 + ε0) := by
        have hA : 0 ≤ t0 - δ := by linarith [hδ_t0]
        have hB : 0 ≤ 2 * δ := by positivity
        have hC : 0 ≤ ε0 - δ := by linarith
        rw [← ENNReal.ofReal_add hB hC]
        rw [← ENNReal.ofReal_add hA (by linarith : 0 ≤ 2 * δ + (ε0 - δ))]
        congr 1
        ring
      have hshort : edist x x0' < ENNReal.ofReal (t0 + ε0) := by
        have hmid : edist (c (t0 - δ)) (ld.Exp p0 (δ • ŵ0)) + ENNReal.ofReal (ε0 - δ) <
            ENNReal.ofReal (2 * δ) + ENNReal.ofReal (ε0 - δ) := by
          have hcfin : ENNReal.ofReal (ε0 - δ) ≠ ⊤ := ne_top_of_lt ENNReal.ofReal_lt_top
          have hs := ENNReal.add_lt_add_left hcfin htri1
          simpa [add_comm] using hs
        have hout : ENNReal.ofReal (t0 - δ) + (edist (c (t0 - δ)) (ld.Exp p0 (δ • ŵ0)) +
            ENNReal.ofReal (ε0 - δ)) < ENNReal.ofReal (t0 - δ) +
            (ENNReal.ofReal (2 * δ) + ENNReal.ofReal (ε0 - δ)) := by
          have hfin2 : ENNReal.ofReal (t0 - δ) ≠ ⊤ := ne_top_of_lt ENNReal.ofReal_lt_top
          exact ENNReal.add_lt_add_left hfin2 hmid
        calc
          edist x x0' ≤ edist x (c (t0 - δ)) + edist (c (t0 - δ)) x0' :=
            edist_triangle (x := x) (y := c (t0 - δ)) (z := x0')
          _ ≤ edist x (c (t0 - δ)) + (edist (c (t0 - δ)) (ld.Exp p0 (δ • ŵ0)) +
              edist (ld.Exp p0 (δ • ŵ0)) x0') := by
            have ht2 := edist_triangle (x := c (t0 - δ)) (y := ld.Exp p0 (δ • ŵ0)) (z := x0')
            exact add_le_add_right ht2 (edist x (c (t0 - δ)))
          _ = ENNReal.ofReal (t0 - δ) + (edist (c (t0 - δ)) (ld.Exp p0 (δ • ŵ0)) +
              ENNReal.ofReal (ε0 - δ)) := by rw [hx_c, harc]
          _ < ENNReal.ofReal (t0 - δ) + (ENNReal.ofReal (2 * δ) + ENNReal.ofReal (ε0 - δ)) := hout
          _ = ENNReal.ofReal (t0 + ε0) := hsum_eq
      exact (not_lt_of_ge hxx0'_ge) hshort
  -- assemble: Good c y r (t0 + ε0)
  refine ⟨ε0, hε0_pos, ?_, ?_⟩
  · linarith [hε0_D]
  · have hyy : edist (c (t0 + ε0)) y = ENNReal.ofReal (r - (t0 + ε0)) := by
      have hz : r - (t0 + ε0) = r - t0 - ε0 := by ring
      rw [hstep, hx0'y', hz]
    exact ⟨by linarith, by linarith [hε0_D], hyy⟩

end EngineHelpers

theorem reachable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (ld : LocData M E) (h : LocHyps ld) (x y : M) (he : edist x y < ⊤) :
    ∃ γ : ℝ → M, UnitGeo γ ∧ γ 0 = x ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ (edist x y).toReal → edist x (γ t) = ENNReal.ofReal t) ∧
      edist (γ (edist x y).toReal) y = 0 := by
  classical
  let r : ℝ := (edist x y).toReal
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact ENNReal.toReal_nonneg
  have hxy_r : edist x y = ENNReal.ofReal r := by
    dsimp [r]
    exact (ENNReal.ofReal_toReal (ne_of_lt he)).symm
  by_cases hr : r = 0
  · -- the endpoint is x itself
    have hxy0 : edist x y = 0 := by
      rw [hxy_r, hr]
      exact ENNReal.ofReal_zero
    have hyx : y = x := EMetricSpace.eq_of_edist_eq_zero (by simpa [edist_comm] using hxy0)
    rcases h.dir x with ⟨W, hW⟩
    rcases h.ext x W hW with ⟨c, hc_unit, hc0, _hcAgree⟩
    refine ⟨c, hc_unit, hc0, ?_, ?_⟩
    · intro t ht0 ht
      have ht0' : t = 0 := by linarith
      subst t
      simp [hc0]
    · -- edist (c r) y = 0
      rw [hyx]
      simpa [hc0, hr]
  · -- 0 < r
    have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (fun h => hr h.symm)
    let ε : ℝ := min (ld.ρ0 x / 2) (r / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      exact lt_min (half_pos (h.rho_pos x)) (half_pos hr_pos)
    have hε_ρ : ε < ld.ρ0 x := by
      have h1 : ε ≤ ld.ρ0 x / 2 := by
        dsimp [ε]
        exact min_le_left _ _
      exact lt_of_le_of_lt h1 (half_lt_self (h.rho_pos x))
    have hε_r : ε < r := by
      have h1 : ε ≤ r / 2 := by
        dsimp [ε]
        exact min_le_right _ _
      exact lt_of_le_of_lt h1 (half_lt_self hr_pos)
    have hε_toReal : ε < (edist x y).toReal := by
      simpa [r] using hε_r
    rcases sphere_min I (M := M) ld h x y ε hε_pos hε_ρ he hε_toReal with ⟨x0, hx0S, hx0y⟩
    have hx0y' : edist x0 y = ENNReal.ofReal (r - ε) := by
      simpa [r] using hx0y
    rcases exists_unit_direction ld h x x0 hε_pos hx0S hε_ρ with ⟨W, hW, hWexp⟩
    rcases h.ext x W hW with ⟨c, hc_unit, hc0, hcAgree⟩
    have hε_abs : |ε| < ld.ρ0 x := by
      rw [abs_of_pos hε_pos]
      exact hε_ρ
    have hcε : c ε = x0 := by
      have hf := hcAgree ε hε_abs
      rwa [hWexp] at hf
    have hε_le_r : ε ≤ r := le_of_lt hε_r
    have hεGood : Good c y r ε := by
      refine ⟨le_of_lt hε_pos, hε_le_r, ?_⟩
      rw [hcε]
      exact hx0y'
    -- the good set
    let A : Set ℝ := {t : ℝ | Good c y r t}
    have hAclosed : IsClosed A := good_isClosed ld h y r c hc_unit
    have hAne : A.Nonempty := ⟨ε, hεGood⟩
    have hAbdd : BddAbove A := by
      refine ⟨r, ?_⟩
      intro t ht
      exact ht.2.1
    have hsup : sSup A ∈ A := IsClosed.csSup_mem hAclosed hAne hAbdd
    let s : ℝ := sSup A
    have hsGood : Good c y r s := by
      simpa [s, A] using hsup
    have hε_le_s : ε ≤ s := by
      dsimp [s]
      exact le_csSup hAbdd hεGood
    have hs_pos : 0 < s := lt_of_lt_of_le hε_pos hε_le_s
    have hs_le_r : s ≤ r := hsGood.2.1
    have hs_r : s = r := by
      by_contra hne
      have hs_lt_r : s < r := lt_of_le_of_ne hs_le_r hne
      rcases good_extension I (M := M) ld h x y r c hc_unit hc0 hr_nonneg hxy_r (t0 := s)
        hsGood hs_pos hs_lt_r with ⟨η, hη_pos, hη_lt, hηGood⟩
      have hsb : s + η ≤ sSup A := (isLUB_csSup hAne hAbdd).1 (by simpa [A] using hηGood)
      have hss : s + η ≤ s := by simpa [s] using hsb
      linarith
    have hrGood : Good c y r r := by
      have hrA : r ∈ A := by
        rw [← hs_r]
        exact hsup
      simpa [A] using hrA
    have hcry : edist (c r) y = 0 := by
      have hg := hrGood.2.2
      have hrr : r - r = 0 := by ring
      rw [hrr, ENNReal.ofReal_zero] at hg
      exact hg
    refine ⟨c, hc_unit, hc0, ?_, ?_⟩
    · intro t ht0 ht
      have hgd := good_down ld h x y r c hc_unit hc0 hr_nonneg hxy_r (t0 := r) (s := t) hrGood ht0 ht
      exact hgd.2
    · simpa [r] using hcry

end ManifoldContext

end Engine

end Submission
