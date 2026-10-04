import Submission.GExpGlob
import Submission.CutWitness
import Submission.InjRadius
import Submission.GSField
import Submission.Commons.Topology.continuousWithinAt_of_unique_edist_eq

set_option backward.isDefEq.respectTransparency.types false

/-!
# The exponential map below the injectivity radius: characterisation and continuity

This file develops the part of the theory of `GExp` that is available **below the injectivity
radius** `m` of a point `p`:

* `edist_GExp_smul_le_mul_norm` — the ray bound for an arbitrary velocity vector;
* `edist_GExp_eq_norm_of_le_of_injAtLeast` — **the rays of length `≤ m` are minimising**: for
  `‖w‖ ≤ m`, `d(p, GExp p w) = ‖w‖`;
* `edist_GExp_half_of_le_of_injAtLeast` — the distance between the points of the ray at
  parameters `v/2` and `v` is `‖v‖/2`;
* **`eq_GExp_iff_edist_of_injAtLeast`** — the *characterisation of the ray point by two distance
  spheres*: for `‖v‖ ≤ inj(p)`, a point `y` is `GExp p v` if and only if
  `d(p,y) = ‖v‖` and `d(GExp p (v/2), y) = ‖v‖/2`.  This is the key tool that turns a statement
  about the exponential map into a statement about distances;
* **`continuousOn_GExp_closedBall_of_injAtLeast`** — the exponential map at `p` is continuous on the
  closed ball of every radius `≤ inj(p)`.  The proof is a doubling argument: the characterisation
  above exhibits `GExp p v` as the *unique* solution of two distance equations whose data depend
  continuously on `v/2`, so the general continuous-selection lemma
  (`Commons.Topology.continuousWithinAt_of_unique_edist_eq`) gives continuity at radius `2T` from
  continuity at radius `T`.

The doubled radius is the natural limit of this method: the characterisation is only valid while the
rays are minimising, i.e. up to the injectivity radius.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.GExpRay
open Submission.CutWitness
open Submission.InjRadius
open Submission.GSField
open Submission.ChartBounds

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpRay2

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## The ray bound for arbitrary velocities -/

/-- **The ray bound for an arbitrary velocity vector.**  For `0 ≤ a ≤ b` the two points of the ray
`s ↦ GExp z (s • v)` are at Riemannian distance at most `(b - a) * ‖v‖`. -/
theorem edist_GExp_smul_le_mul_norm (hmet : IsMetricCompatible cov) (z : M)
    {v : TangentSpace I z} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
        (GExp (cov := cov) hmet z (b • v)) ≤ ENNReal.ofReal ((b - a) * ‖v‖) := by
  by_cases hv : v = 0
  · subst hv
    rw [smul_zero, smul_zero, GExp_zero, Manifold.riemannianEDist_self, norm_zero, mul_zero,
      ENNReal.ofReal_zero]
  · have hξ : ‖unitOf v hv‖ = 1 := unitOf_norm v hv
    have h1 : ‖v‖ • unitOf v hv = v := by
      show ‖v‖ • unitOf v hv = v
      rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
    have hscale : ∀ c : ℝ, c • v = (c * ‖v‖) • unitOf v hv := by
      intro c
      calc c • v = c • (‖v‖ • unitOf v hv) := by rw [h1]
        _ = (c * ‖v‖) • unitOf v hv := by rw [smul_smul]
    have h := edist_GExp_smul_le (cov := cov) hmet z hξ
      (mul_nonneg ha (norm_nonneg v)) (mul_nonneg (le_trans ha hab) (norm_nonneg v))
      (mul_le_mul_of_nonneg_right hab (norm_nonneg v))
    rw [← hscale a, ← hscale b] at h
    have hsub : b * ‖v‖ - a * ‖v‖ = (b - a) * ‖v‖ := by ring
    rwa [hsub] at h

/-! ## Rays up to the injectivity radius are minimising -/

/-- **Rays of length at most the injectivity radius are minimising.**  If the exponential map is
injective on the open ball of radius `m` at `p`, then for every `w` with `‖w‖ ≤ m` the point
`GExp p w` is at distance exactly `‖w‖` from `p`, i.e. the ray of `w` is a minimising geodesic. -/
theorem edist_GExp_eq_norm_of_le_of_injAtLeast (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m) {w : TangentSpace I p} (hw : ‖w‖ ≤ m) :
    Manifold.riemannianEDist I p (GExp (cov := cov) hmet p w) = ENNReal.ofReal ‖w‖ := by
  by_cases hw0 : w = 0
  · subst hw0
    rw [GExp_zero, Manifold.riemannianEDist_self, norm_zero, ENNReal.ofReal_zero]
  · by_contra hcon
    have hlt : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p w) < ENNReal.ofReal ‖w‖ :=
      lt_of_le_of_ne (edist_GExp_le_norm (cov := cov) hmet w) hcon
    set η : TangentSpace I p := unitOf w hw0 with hηdef
    have hη : ‖η‖ = 1 := unitOf_norm w hw0
    have hηne : η ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hη
      norm_num at hη
    have hscale : ‖w‖ • η = w := by
      rw [hηdef]
      show ‖w‖ • unitOf w hw0 = w
      rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw0), one_smul]
    have hnot : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (‖w‖ • η))
        < ENNReal.ofReal ‖w‖ := by
      rw [hscale]
      exact hlt
    obtain ⟨s, hs, hslt⟩ := exists_lt_of_not_minimising_ray (cov := cov) hmet hη
      (norm_pos_iff.mpr hw0) hnot
    have hsle : s < m := lt_of_lt_of_le hs.2 hw
    have hsn : ‖s • η‖ = s := by
      rw [norm_smul, Real.norm_of_nonneg hs.1.le, hη, mul_one]
    have heq := edist_GExp_eq_norm_of_injAtLeast (cov := cov) hmet htor hinj
      (by rw [hsn]; exact hsle) (smul_ne_zero hs.1.ne' hηne)
    rw [hsn] at heq
    exact absurd heq (ne_of_lt hslt)

/-- **The distance between the points of a ray at parameters `v/2` and `v`.**  For `‖v‖ ≤ inj(p)`
this is exactly `‖v‖/2`. -/
theorem edist_GExp_half_of_le_of_injAtLeast (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m) {v : TangentSpace I p} (hvm : ‖v‖ ≤ m) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v))
        (GExp (cov := cov) hmet p v) = ENNReal.ofReal (‖v‖ / 2) := by
  have h2 : ‖(1 / 2 : ℝ) • v‖ ≤ m := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith [norm_nonneg v]
  have hle := edist_GExp_smul_le_mul_norm (cov := cov) hmet p (v := v) (a := (1 / 2 : ℝ))
    (b := 1) (by norm_num) (by norm_num)
  have hle' : Manifold.riemannianEDist I (GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v))
      (GExp (cov := cov) hmet p v) ≤ ENNReal.ofReal (‖v‖ / 2) := by
    have h1 : (1 - 1 / 2) * ‖v‖ = ‖v‖ / 2 := by ring
    simpa only [one_smul, h1] using hle
  refine le_antisymm hle' ?_
  set D : ℝ≥0∞ := Manifold.riemannianEDist I (GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v))
    (GExp (cov := cov) hmet p v) with hDdef
  have hDtop : D ≠ ⊤ := by
    rw [hDdef]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle'
  have hd1 := edist_GExp_eq_norm_of_le_of_injAtLeast (cov := cov) hmet htor hinj hvm
  have hd2 : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v))
      = ENNReal.ofReal (‖v‖ / 2) := by
    have h := edist_GExp_eq_norm_of_le_of_injAtLeast (cov := cov) hmet htor hinj h2
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    rwa [show (1 / 2 : ℝ) * ‖v‖ = ‖v‖ / 2 by ring] at h
  have htri := Manifold.riemannianEDist_triangle (I := I) (x := p)
    (y := GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v)) (z := GExp (cov := cov) hmet p v)
  rw [hd1, hd2] at htri
  have hsumtop : (ENNReal.ofReal (‖v‖ / 2) + D) ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hDtop⟩
  have hreal := ENNReal.toReal_mono hsumtop htri
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hDtop] at hreal
  rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ‖v‖ / 2)] at hreal
  rw [ENNReal.toReal_ofReal (norm_nonneg v)] at hreal
  have hgeq : ‖v‖ / 2 ≤ D.toReal := by linarith
  have : ENNReal.ofReal (‖v‖ / 2) ≤ ENNReal.ofReal D.toReal := ENNReal.ofReal_le_ofReal hgeq
  rwa [ENNReal.ofReal_toReal hDtop] at this

/-! ## The characterisation of the ray point by two distance spheres -/

/-- **The ray point is characterised by two distance spheres.**  Let the exponential map at `p` be
injective on the open ball of radius `m` and let `‖v‖ ≤ m`.  Then for any point `y`:

  `y = GExp p v`  ⟺  `d(p,y) = ‖v‖` and `d(GExp p (v/2), y) = ‖v‖/2`.

The proof of `⇐` is the "no corner" lemma applied to the broken minimising path
`p → GExp p (v/2) → y`: the two distance equalities make the broken path minimising, and a
minimising broken geodesic has no corner. -/
theorem eq_GExp_iff_edist_of_injAtLeast (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m) {v : TangentSpace I p} (hvm : ‖v‖ ≤ m)
    (y : M) :
    y = GExp (cov := cov) hmet p v ↔
      (Manifold.riemannianEDist I p y = ENNReal.ofReal ‖v‖ ∧
        Manifold.riemannianEDist I (GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v)) y
          = ENNReal.ofReal (‖v‖ / 2)) := by
  constructor
  · intro hy
    subst hy
    exact ⟨edist_GExp_eq_norm_of_le_of_injAtLeast (cov := cov) hmet htor hinj hvm,
      edist_GExp_half_of_le_of_injAtLeast (cov := cov) hmet htor hinj hvm⟩
  · rintro ⟨h1, h2⟩
    by_cases hv0 : v = 0
    · subst hv0
      rw [norm_zero, ENNReal.ofReal_zero] at h1
      rw [GExp_zero]
      haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
      have h1' : Manifold.riemannianEDist I y p = 0 := by
        rw [Manifold.riemannianEDist_comm]; exact h1
      exact (Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp h1'
    · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      set w : TangentSpace I p := unitOf v hv0 with hwdef
      have hw : ‖w‖ = 1 := unitOf_norm v hv0
      have ht_eq : ((1 / 2 : ℝ) • v) = (‖v‖ / 2) • w := by
        rw [hwdef]
        show (1 / 2 : ℝ) • v = (‖v‖ / 2) • unitOf v hv0
        rw [unitOf, smul_smul]
        congr 1
        field_simp
      have ht0 : 0 < ‖v‖ / 2 := by linarith
      have htr : ‖v‖ / 2 < ‖v‖ := by linarith
      have hz : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p ((‖v‖ / 2) • w))
          = ENNReal.ofReal (‖v‖ / 2) := by
        have h := edist_GExp_eq_norm_of_le_of_injAtLeast (cov := cov) hmet htor hinj
          (w := (‖v‖ / 2) • w) ?_
        · rwa [norm_smul, Real.norm_of_nonneg ht0.le, hw, mul_one] at h
        · rw [norm_smul, Real.norm_of_nonneg ht0.le, hw, mul_one]
          linarith
      have hz2 : Manifold.riemannianEDist I (GExp (cov := cov) hmet p ((‖v‖ / 2) • w)) y
          = ENNReal.ofReal (‖v‖ - ‖v‖ / 2) := by
        have h2' := h2
        rw [ht_eq] at h2'
        rw [h2']
        congr 1
        ring
      have hres := eq_GExp_of_minimising_broken (cov := cov) hmet htor (x₀ := p) (p := y)
        (r := ‖v‖) (t := ‖v‖ / 2) (w := w) hw (norm_nonneg v) ht0 htr hz hz2 h1
      have hvw : ‖v‖ • w = v := by
        rw [hwdef]
        show ‖v‖ • unitOf v hv0 = v
        rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul]
      rw [hres, hvw]

/-! ## The injectivity radius at a point is positive -/

/-- **The chart metric at the base point dominates the model norm.**  There is `lam > 0` such that
the model norm of a tangent vector at `p` is at most `‖v‖ / √lam`. -/
theorem exists_model_norm_le_fibre_div (p : M) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : TangentSpace I p,
      (fun z : E => ‖z‖) (show E from v) ≤ ‖v‖ / Real.sqrt lam := by
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) p
    (K := ({p} : Set M)) isCompact_singleton ⟨p, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact mem_chart_source H p)
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨lam, hlam, fun v => ?_⟩
  have h1 : lam * ((fun z : E => ‖z‖) (show E from v)) ^ 2 ≤ ‖v‖ ^ 2 := by
    have hb := (hbnd p (by simp) (show E from v)).1
    rwa [Submission.Distance.chartGram_self_apply (I := I) p (show E from v) (show E from v),
      real_inner_self_eq_norm_sq] at hb
  have h4 : Real.sqrt (lam * ((fun z : E => ‖z‖) (show E from v)) ^ 2)
      ≤ Real.sqrt (‖v‖ ^ 2) := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_mul hlam.le,
    Real.sqrt_sq (show (0 : ℝ) ≤ (fun z : E => ‖z‖) (show E from v) from norm_nonneg _),
    Real.sqrt_sq (norm_nonneg v)] at h4
  rw [le_div_iff₀ hsqlam]
  linarith

/-- **The injectivity radius at a point is positive.**  The chart exponential map is injective on a
neighbourhood of the origin (`exists_injOn_expMap_nhds`); the chart metric at `p` compares the two
norms (`exists_model_norm_le_fibre_div`), so a *fibre* ball of a suitable radius maps into that
neighbourhood, where `GExp p` agrees with `expMap p`. -/
theorem exists_pos_injAtLeast (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (p : M) :
    ∃ m : ℝ, 0 < m ∧ InjAtLeast hmet p m := by
  obtain ⟨U, hUopen, h0U, hUinj⟩ := exists_injOn_expMap_nhds (cov := cov) p
  obtain ⟨ρ₃, hρ₃, hρ₃U⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds h0U)
  obtain ⟨ρ₁, hρ₁, hagree⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet p
  obtain ⟨lam, hlam, hconv⟩ := exists_model_norm_le_fibre_div (I := I) p
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨min ρ₁ (Real.sqrt lam * ρ₃) / 2, ?_, ?_⟩
  · have h : 0 < min ρ₁ (Real.sqrt lam * ρ₃) := lt_min hρ₁ (by positivity)
    linarith
  · intro u v hu hv huv
    have hmin : 0 < min ρ₁ (Real.sqrt lam * ρ₃) := lt_min hρ₁ (by positivity)
    have hmle : min ρ₁ (Real.sqrt lam * ρ₃) / 2 ≤ Real.sqrt lam * ρ₃ := by
      have h : min ρ₁ (Real.sqrt lam * ρ₃) ≤ Real.sqrt lam * ρ₃ := min_le_right _ _
      linarith
    have hmle₁ : min ρ₁ (Real.sqrt lam * ρ₃) / 2 ≤ ρ₁ := by
      have h : min ρ₁ (Real.sqrt lam * ρ₃) ≤ ρ₁ := min_le_left _ _
      linarith
    have hmem : ∀ w : TangentSpace I p, ‖w‖ < min ρ₁ (Real.sqrt lam * ρ₃) / 2 →
        (show E from w) ∈ U ∧ GExp (cov := cov) hmet p w = expMap cov p w := by
      intro w hw
      have hmod : (fun z : E => ‖z‖) (show E from w) < ρ₃ := by
        have h1 := hconv w
        have h2 : ‖w‖ / Real.sqrt lam < (min ρ₁ (Real.sqrt lam * ρ₃) / 2) / Real.sqrt lam :=
          div_lt_div_of_pos_right hw hsqlam
        have h3 : (min ρ₁ (Real.sqrt lam * ρ₃) / 2) / Real.sqrt lam ≤ ρ₃ := by
          have h : min ρ₁ (Real.sqrt lam * ρ₃) ≤ Real.sqrt lam * ρ₃ := min_le_right _ _
          have h2' : min ρ₁ (Real.sqrt lam * ρ₃) / 2 ≤ Real.sqrt lam * ρ₃ / 2 := by linarith
          have h3' : (min ρ₁ (Real.sqrt lam * ρ₃) / 2) / Real.sqrt lam
              ≤ (Real.sqrt lam * ρ₃ / 2) / Real.sqrt lam :=
            div_le_div_of_nonneg_right h2' hsqlam.le
          have h4 : (Real.sqrt lam * ρ₃ / 2) / Real.sqrt lam = ρ₃ / 2 := by field_simp
          rw [h4] at h3'
          linarith
        exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)
      exact ⟨hρ₃U (by rw [Metric.mem_ball, dist_zero_right]; exact hmod),
        hagree w (lt_of_lt_of_le hw hmle₁)⟩
    obtain ⟨-, hGu⟩ := hmem u hu
    obtain ⟨-, hGv⟩ := hmem v hv
    have hexp : expMap cov p (show E from u) = expMap cov p (show E from v) := by
      rw [← hGu, ← hGv]
      exact huv
    exact hUinj (hmem u hu).1 (hmem v hv).1 hexp

/-! ## Continuity of the exponential map below the injectivity radius -/


/-- **The exponential map is continuous on the closed ball of every radius `≤ inj(p)`.**

The proof is the *doubling argument*: `GExp p v` is, for `‖v‖ ≤ inj(p)`, the unique point `y` with
`d(p,y) = ‖v‖` and `d(GExp p (v/2), y) = ‖v‖/2`; the two data are continuous functions of `v`
whenever `GExp p` is continuous at radius `T ≥ ‖v‖/2`, and the general continuous-selection lemma
then produces continuity at radius `2T`.  Starting from the chart-local smoothness of `GExp` at the
origin and doubling up to `inj(p)` gives the claim. -/
theorem continuousOn_GExp_closedBall_of_injAtLeast (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m) :
    ∀ U : ℝ, U ≤ m → ContinuousOn (fun v : TangentSpace I p => GExp (cov := cov) hmet p v)
      (Metric.closedBall (0 : TangentSpace I p) U) := by
  -- the base case: on a small ball `GExp p` agrees with the smooth chart exponential map
  obtain ⟨ρ₁, hρ₁, hagree⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet p
  obtain ⟨ρ₂, hρ₂, hsmooth⟩ := Submission.Geodesic.exists_radius_contMDiffAt_expMap (cov := cov) p
  obtain ⟨lam, hlam, hconv⟩ := exists_model_norm_le_fibre_div (I := I) p
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  set δ : ℝ := min ρ₁ (Real.sqrt lam * ρ₂) / 2 with hδdef
  have hδpos : 0 < δ := by
    have h : 0 < min ρ₁ (Real.sqrt lam * ρ₂) := lt_min hρ₁ (by positivity)
    rw [hδdef]
    linarith
  have hδρ₁ : δ < ρ₁ := by
    have h : min ρ₁ (Real.sqrt lam * ρ₂) ≤ ρ₁ := min_le_left _ _
    rw [hδdef]
    linarith
  have hδmod : δ / Real.sqrt lam < ρ₂ := by
    have h1 : δ ≤ Real.sqrt lam * ρ₂ / 2 := by
      have h : min ρ₁ (Real.sqrt lam * ρ₂) ≤ Real.sqrt lam * ρ₂ := min_le_right _ _
      rw [hδdef]
      linarith
    have h3 : δ / Real.sqrt lam ≤ ρ₂ / 2 := by
      calc δ / Real.sqrt lam ≤ (Real.sqrt lam * ρ₂ / 2) / Real.sqrt lam :=
            div_le_div_of_nonneg_right h1 hsqlam.le
        _ = ρ₂ / 2 := by field_simp
    linarith
  have hbase : ContinuousOn (fun v : TangentSpace I p => GExp (cov := cov) hmet p v)
      (Metric.closedBall (0 : TangentSpace I p) δ) := by
    have hcont : ContinuousOn (fun v : TangentSpace I p => expMap cov p v)
        (Metric.closedBall (0 : TangentSpace I p) δ) := by
      intro v hv
      have hvle : ‖v‖ ≤ δ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv
      have hmod : (fun z : E => ‖z‖) (show E from v) < ρ₂ := by
        have h := hconv v
        have hle : ‖v‖ / Real.sqrt lam ≤ δ / Real.sqrt lam :=
          div_le_div_of_nonneg_right hvle hsqlam.le
        linarith
      have hc : ContinuousAt (fun w : E => expMap cov p w) (show E from v) :=
        (hsmooth (show E from v) hmod).continuousAt
      exact hc.continuousWithinAt
    refine hcont.congr (fun v hv => ?_)
    have hvle : ‖v‖ ≤ δ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv
    exact hagree v (lt_of_le_of_lt hvle hδρ₁)
  -- the doubling step
  have step : ∀ T : ℝ, 0 < T → 2 * T ≤ m →
      ContinuousOn (fun v : TangentSpace I p => GExp (cov := cov) hmet p v)
        (Metric.closedBall (0 : TangentSpace I p) T) →
      ContinuousOn (fun v : TangentSpace I p => GExp (cov := cov) hmet p v)
        (Metric.closedBall (0 : TangentSpace I p) (2 * T)) := by
    intro T hT hTm hcontT
    haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    have hmpos : 0 < m := by linarith
    refine fun v₀ hv₀ => ?_
    have hv0m : ‖v₀‖ ≤ m := by
      have h : ‖v₀‖ ≤ 2 * T := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv₀
      linarith
    -- continuity of the reference map `v ↦ GExp p (v/2)`
    have hmap : Set.MapsTo (fun v : TangentSpace I p => (1 / 2 : ℝ) • v)
        (Metric.closedBall (0 : TangentSpace I p) (2 * T))
        (Metric.closedBall (0 : TangentSpace I p) T) := by
      intro v hv
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hv ⊢
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      linarith
    have ha : ContinuousWithinAt
        (fun v : TangentSpace I p => GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v))
        (Metric.closedBall (0 : TangentSpace I p) (2 * T)) v₀ :=
      (hcontT.comp (continuous_const_smul (1 / 2 : ℝ)).continuousOn hmap).continuousWithinAt hv₀
    have hα : ContinuousWithinAt (fun v : TangentSpace I p => ENNReal.ofReal ‖v‖)
        (Metric.closedBall (0 : TangentSpace I p) (2 * T)) v₀ :=
      (ENNReal.continuous_ofReal.comp continuous_norm).continuousWithinAt
    have hβ : ContinuousWithinAt (fun v : TangentSpace I p => ENNReal.ofReal (‖v‖ / 2))
        (Metric.closedBall (0 : TangentSpace I p) (2 * T)) v₀ :=
      (ENNReal.continuous_ofReal.comp (continuous_norm.div_const 2)).continuousWithinAt
    have hg : ∀ v ∈ Metric.closedBall (0 : TangentSpace I p) (2 * T),
        edist p (GExp (cov := cov) hmet p v) = ENNReal.ofReal ‖v‖ ∧
          edist (GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v)) (GExp (cov := cov) hmet p v)
            = ENNReal.ofReal (‖v‖ / 2) := by
      intro v hv
      have hvm : ‖v‖ ≤ m := by
        have h : ‖v‖ ≤ 2 * T := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv
        linarith
      rw [Submission.EDist.edist_eq_riemannianEDist (I := I) p (GExp (cov := cov) hmet p v),
        Submission.EDist.edist_eq_riemannianEDist (I := I)
          (GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v)) (GExp (cov := cov) hmet p v)]
      exact ⟨edist_GExp_eq_norm_of_le_of_injAtLeast (cov := cov) hmet htor hinj hvm,
        edist_GExp_half_of_le_of_injAtLeast (cov := cov) hmet htor hinj hvm⟩
    have huniq : ∀ y : M, edist p y = ENNReal.ofReal ‖v₀‖ →
        edist (GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v₀)) y = ENNReal.ofReal (‖v₀‖ / 2) →
        y = GExp (cov := cov) hmet p v₀ := by
      intro y hy1 hy2
      rw [Submission.EDist.edist_eq_riemannianEDist (I := I) p y] at hy1
      rw [Submission.EDist.edist_eq_riemannianEDist (I := I)
        (GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v₀)) y] at hy2
      exact (eq_GExp_iff_edist_of_injAtLeast (cov := cov) hmet htor hinj hv0m y).mpr ⟨hy1, hy2⟩
    exact (Commons.Topology.continuousWithinAt_of_unique_edist_eq (s :=
        Metric.closedBall (0 : TangentSpace I p) (2 * T))
      (p := p) (a := fun v : TangentSpace I p => GExp (cov := cov) hmet p ((1 / 2 : ℝ) • v))
      (g := fun v : TangentSpace I p => GExp (cov := cov) hmet p v)
      (α := fun v : TangentSpace I p => ENNReal.ofReal ‖v‖)
      (β := fun v : TangentSpace I p => ENNReal.ofReal (‖v‖ / 2))
      (z₀ := v₀) (y₀ := GExp (cov := cov) hmet p v₀) hv₀ ha hα hβ hg huniq).2
  -- the doubling induction
  have hS : ∀ N : ℕ, ∀ T : ℝ, T ≤ 2 ^ N * δ → T ≤ m →
      ContinuousOn (fun v : TangentSpace I p => GExp (cov := cov) hmet p v)
        (Metric.closedBall (0 : TangentSpace I p) T) := by
    intro N
    induction N with
    | zero =>
      intro T hTδ _
      refine hbase.mono ?_
      intro v hv
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hv ⊢
      linarith
    | succ N ih =>
      intro T hTδ hTm
      by_cases hle : T ≤ 2 ^ N * δ
      · exact ih T hle hTm
      · have hpow : (2 : ℝ) ^ (N + 1) * δ = 2 * (2 ^ N * δ) := by
          rw [pow_succ]
          ring
        have hhalf_le : T / 2 ≤ 2 ^ N * δ := by
          rw [hpow] at hTδ
          linarith
        have hhalfm : T / 2 ≤ m := by linarith
        have hhalfTm : 2 * (T / 2) ≤ m := by linarith
        have hres := step (T / 2) (by linarith) hhalfTm (ih (T / 2) hhalf_le hhalfm)
        have h2T : 2 * (T / 2) = T := by ring
        rwa [h2T] at hres
  -- assemble
  intro U hUm
  obtain ⟨N, hN⟩ : ∃ N : ℕ, U ≤ 2 ^ N * δ := by
    by_cases h : U ≤ δ
    · exact ⟨0, by simpa using h⟩
    · push Not at h
      have h2 : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      obtain ⟨N, hN⟩ := (h2.eventually_ge_atTop (U / δ)).exists
      refine ⟨N, ?_⟩
      rw [div_le_iff₀ hδpos] at hN
      linarith
  exact hS N U hN hUm

end

end Submission.GExpRay2
