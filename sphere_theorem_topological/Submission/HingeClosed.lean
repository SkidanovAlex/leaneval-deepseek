import Submission.HingePiece
import Submission.Minimising

/-!
# Toponogov's hinge comparison in the closed range

`HingePiece.gcompHolds_pi` provides the hinge comparison for hinges of size `< π`, i.e. with
`a + b < π`.  The Grove–Shiohama argument needs the boundary case `a + b = π` as well (for instance
to see that two points at distance `π` from `p` coincide, or that the angle/distance comparison
does not degenerate in the `π/2`-ball).  This file closes the range:

* `edist_GExp_smul_min_sub` — a sub-segment of a *minimising* ray is minimising;
* `gcompHolds_pi_le` — the hinge comparison with `a + b ≤ π`.

The boundary case is obtained as a limit: replace `a` by `aₙ = a(1 - 1/(n+1)) ↑ a`, apply the strict
comparison to `aₙ` (whose minimising identity is `edist_GExp_smul_min_sub`), and pass to the limit
using the continuity of the ray (`GExp_smul` + the continuity of `geodCurve`) and of
`d(p, ·)` (`HopfRinow.continuous_riemannianEDist_left`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace NNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HingeGlobal
open Submission.HingeKey
open Submission.HingePiece

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.HingeClosed

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **A sub-segment of a minimising ray is minimising.**  If the point at time `a` on the ray
`s ↦ GExp z (s • v)` is at distance `a` from `z` and `0 < c ≤ a`, then the point at time `c` is at
distance `c` from `z`. -/
lemma edist_GExp_smul_min_sub (hmet : IsMetricCompatible cov) (z : M) {v : TangentSpace I z}
    (hv : ‖v‖ = 1) {a c : ℝ} (hc : 0 < c) (hca : c ≤ a)
    (hmin : Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (a • v))
      = ENNReal.ofReal a) :
    Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (c • v))
      = ENNReal.ofReal c := by
  have hvne : v ≠ 0 := by
    rintro rfl
    simp at hv
  have ha : 0 < a := lt_of_lt_of_le hc hca
  set ξ : TangentSpace I z := unitOf v hvne with hξdef
  have hξ : ‖ξ‖ = 1 := unitOf_norm v hvne
  set T : ℝ := max ‖v‖ (a * ‖v‖) with hTdef
  have hT : 0 ≤ T := le_trans (norm_nonneg v) (le_max_left _ _)
  set Gp : ℝ → M := geodCurve (cov := cov) hmet T hT z ξ hξ with hGpdef
  have hδ := geodDelta_pos (cov := cov) hmet
  obtain ⟨hGp0, hGpv0, hGpsm, hGpgeo, hGpsp⟩ := geodCurve_spec (cov := cov) hmet T hT z ξ hξ
  have hGp0' : Gp 0 = z := hGp0
  have haT : a ≤ T := by
    have h1 : a * ‖v‖ ≤ T := le_max_right _ _
    rw [hv, mul_one] at h1
    exact h1
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) a,
      s ∈ Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) := by
    intro s hs
    exact Set.mem_Ioo.mpr ⟨by linarith [hs.1], by linarith [hs.2, haT]⟩
  have hmemv : ∀ s ∈ Set.Icc (0 : ℝ) a,
      s * ‖v‖ ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (max ‖v‖ (s * ‖v‖) + geodDelta (cov := cov) hmet) := by
    intro s hs
    have h1 : 0 ≤ s * ‖v‖ := mul_nonneg hs.1 (norm_nonneg v)
    have h2 : s * ‖v‖ ≤ max ‖v‖ (s * ‖v‖) := le_max_right _ _
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  -- the ray agrees with the geodesic `Gp`
  have hev : ∀ s ∈ Set.Icc (0 : ℝ) a, GExp (cov := cov) hmet z (s • v) = Gp (s * ‖v‖) := by
    intro s hs
    have h1 := GExp_smul (cov := cov) hmet z hvne hs.1
    have hT1 : 0 ≤ max ‖v‖ (s * ‖v‖) := le_trans (norm_nonneg v) (le_max_left _ _)
    have hle : max ‖v‖ (s * ‖v‖) ≤ T := max_le (le_max_left _ _)
      ((mul_le_mul_of_nonneg_right hs.2 (norm_nonneg v)).trans (le_max_right _ _))
    rw [h1]
    exact geodCurve_agree (cov := cov) hmet hT1 hT hle z ξ hξ (hmemv s hs)
  have hsp : ∀ t ∈ Set.Icc (0 : ℝ) a, ‖curveVelocity (I := I) Gp t‖ = 1 :=
    fun t ht => hGpsp t (hmem t ht)
  have hγ : CMDiff[Set.Icc (0 : ℝ) a] 1 Gp :=
    (hGpsm.mono (fun s hs => hmem s hs)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hmin' : Manifold.riemannianEDist I (Gp 0) (Gp a) = ENNReal.ofReal a := by
    have ha1 : a * ‖v‖ = a := by rw [hv, mul_one]
    have h1 : Gp a = GExp (cov := cov) hmet z (a • v) := by
      have h1a : Gp (a * ‖v‖) = GExp (cov := cov) hmet z (a • v) :=
        (hev a ⟨ha.le, le_rfl⟩).symm
      rwa [ha1] at h1a
    rw [hGp0', h1]
    exact hmin
  have hres := Submission.Minimising.riemannianEDist_eq_ofReal_of_unit_speed_of_minimising
    (I := I) (γ := Gp) ha.le hγ hsp hmin' 0 ⟨le_rfl, ha.le⟩ c ⟨hc.le, hca⟩ hc.le
  rw [hGp0', sub_zero] at hres
  have hc1 : c * ‖v‖ = c := by rw [hv, mul_one]
  have h2 : Gp c = GExp (cov := cov) hmet z (c • v) := by
    have h2a : Gp (c * ‖v‖) = GExp (cov := cov) hmet z (c • v) :=
      (hev c ⟨hc.le, hca⟩).symm
    rwa [hc1] at h2a
  rw [h2] at hres
  exact hres


/-- **Toponogov's hinge comparison in the closed range.**  The comparison also holds when the two
sides add up to exactly `π`.  The boundary case is obtained as a limit along the shrinking sides
`aₙ = a (1 - 1/(n+1)) ↑ a`, using `edist_GExp_smul_min_sub` for their minimising identity, the ray
bound `Submission.GExpRay.edist_GExp_smul_le` for `d(P, Pₙ) ≤ a - aₙ` and the continuity of
`modelDist1`. -/
theorem gcompHolds_pi_le
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {z : M} {a b : ℝ} {v w : TangentSpace I z}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ Real.pi) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hmina : Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (a • v))
      = ENNReal.ofReal a)
    (hminb : Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (b • w))
      = ENNReal.ofReal b) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
        (GExp (cov := cov) hmet z (b • w))
      ≤ ENNReal.ofReal (modelDist1 (hingeAngle v w) a b) := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact gcompHolds_pi_apply (cov := cov) hmet htor hpinch ha hb hlt hv hw hmina hminb
  · -- the boundary case: limit along shrinking sides
    set s : ℕ → ℝ := fun n => a * (1 - 1 / ((n : ℝ) + 2)) with hsdef
    have hden : ∀ n : ℕ, (1 : ℝ) < (n : ℝ) + 2 := by
      intro n
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hs_pos : ∀ n : ℕ, 0 < s n := by
      intro n
      have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      have h2 : 1 / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by linarith [hden n])]
        linarith [hden n]
      simp only [hsdef]
      exact mul_pos ha (by linarith)
    have hs_lt : ∀ n : ℕ, s n < a := by
      intro n
      have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      simp only [hsdef]
      nlinarith [ha, h1]
    have hs_tendsto : Filter.Tendsto s Filter.atTop (𝓝 a) := by
      have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
        have h2 := h0.comp (tendsto_add_atTop_nat 1)
        have h3 : (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
            = ((fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ∘ fun n : ℕ => n + 1) := by
          funext n
          simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
          ring
        rw [h3]
        exact h2
      have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
      simp only [sub_zero] at h2
      have h3 := h2.const_mul a
      simpa only [hsdef, mul_one] using h3
    have hs_min : ∀ n : ℕ,
        Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (s n • v))
          = ENNReal.ofReal (s n) :=
      fun n => edist_GExp_smul_min_sub (cov := cov) hmet z hv (hs_pos n) (hs_lt n).le hmina
    have hs_sum : ∀ n : ℕ, s n + b < Real.pi := by
      intro n
      have h := hs_lt n
      linarith
    have hcmp : ∀ n : ℕ,
        Manifold.riemannianEDist I (GExp (cov := cov) hmet z (s n • v))
            (GExp (cov := cov) hmet z (b • w))
          ≤ ENNReal.ofReal (modelDist1 (hingeAngle v w) (s n) b) :=
      fun n => gcompHolds_pi_apply (cov := cov) hmet htor hpinch (z := z)
        (hs_pos n) hb (hs_sum n) hv hw (hs_min n) hminb
    have hbound : ∀ n : ℕ,
        Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
            (GExp (cov := cov) hmet z (b • w))
          ≤ ENNReal.ofReal (a - s n) + ENNReal.ofReal (modelDist1 (hingeAngle v w) (s n) b) := by
      intro n
      have htri := Manifold.riemannianEDist_triangle (I := I)
        (x := GExp (cov := cov) hmet z (a • v)) (y := GExp (cov := cov) hmet z (s n • v))
        (z := GExp (cov := cov) hmet z (b • w))
      have hray := Submission.GExpRay.edist_GExp_smul_le (cov := cov) hmet z hv
        (hs_pos n).le ha.le (hs_lt n).le
      calc Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
            (GExp (cov := cov) hmet z (b • w))
          ≤ Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
              (GExp (cov := cov) hmet z (s n • v))
            + Manifold.riemannianEDist I (GExp (cov := cov) hmet z (s n • v))
              (GExp (cov := cov) hmet z (b • w)) := htri
        _ = Manifold.riemannianEDist I (GExp (cov := cov) hmet z (s n • v))
              (GExp (cov := cov) hmet z (a • v))
            + Manifold.riemannianEDist I (GExp (cov := cov) hmet z (s n • v))
              (GExp (cov := cov) hmet z (b • w)) := by
            rw [Manifold.riemannianEDist_comm]
        _ ≤ ENNReal.ofReal (a - s n)
            + ENNReal.ofReal (modelDist1 (hingeAngle v w) (s n) b) :=
            add_le_add hray (hcmp n)
    -- the target value
    set D : ℝ := modelDist1 (hingeAngle v w) a b with hDdef
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    set δ : ℝ≥0 := ε / 2 with hδdef
    have hδpos : (0 : ℝ≥0) < δ := by
      rw [hδdef]; positivity
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
    -- eventually `a - s n < δ`
    have hev1 : ∀ᶠ n : ℕ in Filter.atTop, a - s n < (δ : ℝ) := by
      have h1 : Filter.Tendsto (fun n : ℕ => a - s n) Filter.atTop (𝓝 (a - a)) :=
        (tendsto_const_nhds (x := a)).sub hs_tendsto
      rw [sub_self] at h1
      exact h1 (isOpen_Iio.mem_nhds (by simpa using hδR))
    -- eventually `modelDist1 ... (s n) b < D + δ`
    have hev2 : ∀ᶠ n : ℕ in Filter.atTop,
        modelDist1 (hingeAngle v w) (s n) b < D + (δ : ℝ) := by
      have hcont : Filter.Tendsto (fun t : ℝ => modelDist1 (hingeAngle v w) t b) (𝓝 a) (𝓝 D) := by
        have h1 : Continuous (fun t : ℝ => modelDist1 (hingeAngle v w) t b) := by
          simp only [modelDist1]
          exact Real.continuous_arccos.comp
            (((Real.continuous_cos.mul continuous_const).add
              ((Real.continuous_sin.mul continuous_const).mul continuous_const)))
        exact h1.continuousAt
      have h2 : D < D + (δ : ℝ) := by linarith [hδR]
      exact (hcont.comp hs_tendsto) (isOpen_Iio.mem_nhds h2)
    obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
    have hbnd := hbound n
    have h1 : ENNReal.ofReal (a - s n) ≤ (δ : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := δ)]
      exact ENNReal.ofReal_le_ofReal hn1.le
    have h2 : ENNReal.ofReal (modelDist1 (hingeAngle v w) (s n) b)
        ≤ ENNReal.ofReal D + (δ : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := δ)]
      rw [← ENNReal.ofReal_add (p := D) (q := (δ : ℝ))
        (by rw [hDdef]; exact Real.arccos_nonneg _) (le_of_lt hδR)]
      exact ENNReal.ofReal_le_ofReal hn2.le
    calc Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
          (GExp (cov := cov) hmet z (b • w))
        ≤ ENNReal.ofReal (a - s n)
          + ENNReal.ofReal (modelDist1 (hingeAngle v w) (s n) b) := hbnd
      _ ≤ (δ : ℝ≥0∞) + (ENNReal.ofReal D + (δ : ℝ≥0∞)) := add_le_add h1 h2
      _ = ENNReal.ofReal D + ((δ : ℝ≥0∞) + (δ : ℝ≥0∞)) := by abel
      _ = ENNReal.ofReal D + (ε : ℝ≥0∞) := by
          congr 1
          rw [← ENNReal.coe_add, ENNReal.coe_inj]
          rw [hδdef]
          exact add_halves ε
      _ = ENNReal.ofReal (modelDist1 (hingeAngle v w) a b) + (ε : ℝ≥0∞) := by rw [hDdef]

end

end Submission.HingeClosed
