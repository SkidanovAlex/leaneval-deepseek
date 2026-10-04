import Submission.LensLoop
import Submission.GExpJoint
import Submission.CurveField
import Submission.UniformInj
import Submission.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The doubling step for the smoothness of the exponential map

`Submission.GExpJoint` proves that `(q,u) ↦ GExp q (frameVector z q u)` is `C^∞` in the *model*
coordinates of one chart, for `‖u‖` bounded by a constant depending on the chart-flow datum.  This
file provides the two ingredients of the **uniform** base case of the doubling induction
(`exists_pos_smoothOnBall`) and the **midpoint decomposition** of a `GExp`-ray that the induction
step is built on.

## Contents

* `GExp_eq_chartFlow_of_phase` — the chart-flow description of `GExp` on the phase domain, without
  any hypothesis on the base point beyond membership in the chart source;
* `frameVector_smul'`, `frameVector_eq_zero` — elementary frame lemmas;
* `gexpChart`, `SmoothOnBall`, `exists_pos_smoothOnBall` — the induction statement and its **base
  case**: a single radius `δ > 0` on which the family is `C^∞` in the coordinates of *every* chart
  of a finite atlas (the uniformity is what the induction needs);
* `GExp_ray_eq_unit_ray`, `GExp_split` — the ray splits at its midpoint;
* `midPt`, `halfVel`, `midPt_eq`, `halfVel_eq`, `halfVel_eq_half_deriv`, `halfVel_eq_clm`,
  `deriv_ray_eq_clm_of_split`, `half_smul_inv_smul` — the "second half" of the ray, its chart
  coordinate, and the chain rule identifying that coordinate with the remaining vector of the unit
  ray (the two ingredients of the doubling step, whose assembly is documented in
  `Submission/Roadmap.lean` §82).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpFlow
open Submission.GExpGlob
open Submission.CurveField
open Submission.LensLoop
open Submission.ChartBounds
open Submission.ChartConnection
open Submission.UniformInj

namespace Submission.GExpSmooth

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

lemma frameVector_smul' {z q : M} (c : ℝ) (u : E) :
    frameVector (I := I) z q (c • u) = c • frameVector (I := I) z q u := by
  rw [frameVector, frameVector]
  exact (Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) z) q).map_smul c u

lemma frameVector_eq_zero {z q : M} (hq : q ∈ (extChartAt I z).source) {u : E}
    (h : frameVector (I := I) z q u = 0) : u = 0 := by
  have h2 : (trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ q
      (frameVector (I := I) z q u) = u := clm_frameVector (I := I) (z₀ := z) hq u
  rw [h] at h2
  simpa using h2.symm

/-- The chart-composed exponential map at the chart `z`. -/
noncomputable def gexpChart (hmet : IsMetricCompatible cov) (z : M) : M × E → M :=
  fun p => GExp (cov := cov) hmet p.1 (frameVector (I := I) z p.1 p.2)

/-- **The induction statement.**  For every chart `z i` of the atlas and every `q ∈ Z i`, the family
`(q,u) ↦ GExp q (frameVector (z i) q u)` is `C^∞` at `(q,u)` for all `u` with fibre norm `< R`. -/
def SmoothOnBall (hmet : IsMetricCompatible cov) {n : ℕ} (z : Fin n → M) (Z : Fin n → Set M)
    (R : ℝ) : Prop :=
  ∀ (i : Fin n) (q : M) (u : E), q ∈ Z i → ‖frameVector (I := I) (z i) q u‖ < R →
    ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (gexpChart (cov := cov) hmet (z i)) (q, u)

variable {Z : Set M}

/-- The chart-flow description of `GExp` needs no hypothesis on the base point beyond membership in
the chart source. -/
theorem GExp_eq_chartFlow_of_phase (hmet : IsMetricCompatible cov)
    {z : M} (D : ChartFlowData (cov := cov) (I := I) z Z) {q : M}
    (hqs : q ∈ (extChartAt I z).source) {u : E}
    (hph : ((extChartAt I z) q, flowScale D • u) ∈ D.O) :
    GExp (cov := cov) hmet q (frameVector (I := I) z q u) = chartFlowExp (cov := cov) D q u := by
  by_cases hu : u = 0
  · subst hu
    have ht : |(flowScale D)⁻¹| ≤ D.ρ := by
      rw [inv_flowScale, abs_of_pos (div_pos D.hρ two_pos)]
      linarith [D.hρ]
    have htgt : (extChartAt I z) q ∈ (extChartAt I z).target :=
      (extChartAt I z).map_source (by simpa using hqs)
    have hgeo0 : chartGeodesicVectorField (cov := cov) z ((extChartAt I z) q, (0 : E)) = 0 := by
      have h := chartGeodesicVectorField_smul (cov := cov) z (c := 0)
        (((extChartAt I z) q, (0 : E))) htgt
      simpa using h
    have hspray : chartSpray (cov := cov) z ((extChartAt I z) q, (0 : E)) = ((0 : E), (0 : E)) := by
      rw [chartSpray_apply, hgeo0]
    have hph' : ((extChartAt I z) q, (0 : E)) ∈ D.O := by simpa using hph
    have hconst : ∀ t : ℝ, |t| ≤ D.ρ →
        HasDerivAt (fun _ : ℝ => (((extChartAt I z) q, (0 : E)) : E × E))
          (chartSpray (cov := cov) z (((extChartAt I z) q, (0 : E)))) t := by
      intro t ht
      rw [hspray]
      exact hasDerivAt_const t (((extChartAt I z) q, (0 : E)))
    have h := D.huniq ((extChartAt I z) q, (0 : E)) hph'
      (fun _ : ℝ => (((extChartAt I z) q, (0 : E)) : E × E)) hconst rfl (flowScale D)⁻¹ ht
    have hpos : (D.α ((extChartAt I z) q, (0 : E)) (flowScale D)⁻¹).1 = (extChartAt I z) q :=
      (congrArg Prod.fst h).symm
    rw [frameVector_zero' (I := I) z q, GExp_zero]
    show q = (extChartAt I z).symm ((D.α ((extChartAt I z) q, flowScale D • (0 : E))
      (flowScale D)⁻¹).1)
    rw [show flowScale D • (0 : E) = (0 : E) from by simp, hpos]
    exact ((extChartAt I z).left_inv hqs).symm
  · exact GExp_eq_chartFlow (cov := cov) hmet D hqs u hph hu

/-- **The base case of the induction**: there is a uniform radius on which the family
`(q,u) ↦ GExp q (frameVector (z i) q u)` is `C^∞`.  The proof uses the chart geodesic flow of each
piece of the finite atlas: the chart-flow model is smooth on `Z i × {‖u‖ ≤ ρ_i/4}` and it agrees
with `GExp` there. -/
theorem exists_pos_smoothOnBall (hmet : IsMetricCompatible cov) {n : ℕ} (z : Fin n → M)
    (Z : Fin n → Set M) (hZc : ∀ i, IsCompact (Z i))
    (hZsrc : ∀ i, Z i ⊆ (chartAt H (z i)).source) (hcov : Set.univ ⊆ ⋃ i, Z i) :
    ∃ δ : ℝ, 0 < δ ∧ SmoothOnBall (cov := cov) hmet z Z δ := by
  classical
  have hsub : ∀ i, Z i ⊆ (extChartAt I (z i)).source :=
    fun i q hq => by simpa using hZsrc i hq
  choose D _ using fun i => exists_chartFlowData (cov := cov) (I := I) (z₀ := z i) (Z := Z i)
    (hZc i) (hZsrc i)
  have hηmem : ∀ i q, q ∈ Z i → ∀ u : E, ‖u‖ ≤ 1 / (2 * flowScale (D i)) →
      ((extChartAt I (z i)) q, flowScale (D i) • u) ∈ (D i).O := by
    intro i q hq u hu
    refine (D i).hKO ⟨⟨q, hq, rfl⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (flowScale_pos (D i))]
    have hc : flowScale (D i) ≠ 0 := flowScale_ne_zero (D i)
    have h1 : flowScale (D i) * (1 / (2 * flowScale (D i))) = 1 / 2 := by field_simp
    calc flowScale (D i) * ‖u‖ ≤ flowScale (D i) * (1 / (2 * flowScale (D i))) :=
          mul_le_mul_of_nonneg_left hu (flowScale_pos (D i)).le
      _ = 1 / 2 := h1
      _ ≤ 1 := by norm_num
  let η : Fin n → ℝ := fun i => 1 / (2 * flowScale (D i))
  have hηpos : ∀ i, 0 < η i := fun i => by
    show (0 : ℝ) < 1 / (2 * flowScale (D i))
    exact div_pos one_pos (by linarith [flowScale_pos (D i)])
  have hgram : ∀ i, ∃ lam : ℝ, 0 < lam ∧ ∀ q ∈ Z i, ∀ w : E,
      lam * ‖w‖ ^ 2 ≤ chartGram (I := I) (z i) q w w := by
    intro i
    by_cases hne : (Z i).Nonempty
    · obtain ⟨lam, hlam, _Λ, _hΛ, hb⟩ :=
        exists_chartGram_bounds (I := I) (z i) (hZc i) hne (hZsrc i)
      exact ⟨lam, hlam, fun q hq w => (hb q hq w).1⟩
    · exact ⟨1, one_pos, fun q hq _ => absurd ⟨q, hq⟩ hne⟩
  choose lam hlampos hlamle using hgram
  -- the key pointwise statement
  have key : ∀ (i : Fin n) (q : M) (u : E), q ∈ Z i →
      ‖frameVector (I := I) (z i) q u‖ < η i * Real.sqrt (lam i) →
      ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (gexpChart (cov := cov) hmet (z i)) (q, u) := by
    intro i q u hq hu
    have hsqpos : 0 < Real.sqrt (lam i) := Real.sqrt_pos.mpr (hlampos i)
    have hsqrt : ‖u‖ * Real.sqrt (lam i) ≤ ‖frameVector (I := I) (z i) q u‖ := by
      have h2 : (Real.sqrt (lam i) * ‖u‖) ^ 2 = lam i * ‖u‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hlampos i).le]
      calc ‖u‖ * Real.sqrt (lam i) = Real.sqrt (lam i) * ‖u‖ := by ring
        _ = Real.sqrt ((Real.sqrt (lam i) * ‖u‖) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ = Real.sqrt (lam i * ‖u‖ ^ 2) := by rw [h2]
        _ ≤ Real.sqrt (chartGram (I := I) (z i) q u u) := Real.sqrt_le_sqrt (hlamle i q hq u)
        _ = ‖frameVector (I := I) (z i) q u‖ :=
            (norm_frameVector (I := I) (z₀ := z i) (q := q) u).symm
    have hnorm : ‖u‖ < η i :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt hsqrt hu) hsqpos.le
    have hphase : ((extChartAt I (z i)) q, flowScale (D i) • u) ∈ (D i).O :=
      hηmem i q hq u hnorm.le
    have hcd : ((extChartAt I (z i)) q, flowScale (D i) • u) ∈ chartData (I := I) (z i) (Z i) := by
      refine ⟨⟨q, hq, rfl⟩, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (flowScale_pos (D i))]
      have hcpos : 0 < flowScale (D i) := flowScale_pos (D i)
      have hcη : flowScale (D i) * η i = 1 / 2 := by
        show flowScale (D i) * (1 / (2 * flowScale (D i))) = 1 / 2
        field_simp
      nlinarith [hnorm, hcpos, norm_nonneg u, hcη]
    have h1 : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞
        (fun p : M × E => chartFlowExp (cov := cov) (D i) p.1 p.2) (q, u) :=
      Submission.GExpJoint.contMDiffAt_chartFlowExp_joint (cov := cov) (D i)
        (by simpa using hZsrc i hq) hcd
    refine h1.congr_of_eventuallyEq ?_
    have hcont : ContinuousAt
        (fun p : M × E => ((extChartAt I (z i)) p.1, flowScale (D i) • p.2)) (q, u) :=
      ((((continuousOn_extChartAt (I := I) (z i)).continuousAt
          (by rw [extChartAt_source]
              exact (chartAt H (z i)).open_source.mem_nhds (hZsrc i hq))).comp
            (continuousAt_fst : ContinuousAt (fun p : M × E => p.1) (q, u))).prodMk
        (continuousAt_const.smul
          (continuousAt_snd : ContinuousAt (fun p : M × E => p.2) (q, u))))
    filter_upwards [hcont.eventually (((D i).hO).mem_nhds hphase),
      (continuousAt_fst : ContinuousAt (fun p : M × E => p.1) (q, u)).eventually
        (((chartAt H (z i)).open_source).mem_nhds (hZsrc i hq))] with p hp hps
    exact (GExp_eq_chartFlow_of_phase (cov := cov) hmet (D i) (by rw [extChartAt_source]; exact hps) hp)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, one_pos, fun i => Fin.elim0 i⟩
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let f : Fin n → ℝ := fun i => η i * Real.sqrt (lam i)
    let sf : Finset ℝ := (Finset.univ : Finset (Fin n)).image f
    have hfpos : ∀ i, 0 < f i := fun i =>
      mul_pos (hηpos i) (Real.sqrt_pos.mpr (hlampos i))
    have hne : sf.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    refine ⟨sf.min' hne, ?_, ?_⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem sf hne)
      rw [← hi]; exact hfpos i
    · intro i q u hq hu
      have hle : sf.min' hne ≤ f i :=
        (Finset.isLeast_min' sf hne).2 (Finset.mem_image_of_mem f (Finset.mem_univ i))
      exact key i q u hq (lt_of_lt_of_le hu hle)

/-! ## The midpoint split of a `GExp` ray -/

/-- The ray in the direction `w` is the *unit* ray reparametrised by the factor `‖w‖`. -/
lemma GExp_ray_eq_unit_ray (hmet : IsMetricCompatible cov) {q : M} {w : TangentSpace I q}
    (hw : w ≠ 0) (s : ℝ) :
    GExp (cov := cov) hmet q (s • w)
      = GExp (cov := cov) hmet q ((s * ‖w‖) • (‖w‖⁻¹ • w)) := by
  have hr : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  congr 1
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hr, mul_one]

/-- **The midpoint split of a `GExp` ray.**  For `w ≠ 0` the point `GExp q w` is obtained from the
midpoint `GExp q ((‖w‖/2) • (‖w‖⁻¹ • w))` by travelling for the remaining length `‖w‖/2` in the
direction of the unit ray `t ↦ GExp q (t • (‖w‖⁻¹ • w))`. -/
theorem GExp_split (hmet : IsMetricCompatible cov) {q : M} {w : TangentSpace I q} (hw : w ≠ 0) :
    GExp (cov := cov) hmet q w
      = GExp (cov := cov) hmet (GExp (cov := cov) hmet q ((‖w‖ / 2) • (‖w‖⁻¹ • w)))
          ((‖w‖ / 2) • curveVelocity (I := I)
            (fun r : ℝ => GExp (cov := cov) hmet q (r • (‖w‖⁻¹ • w))) (‖w‖ / 2)) := by
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hrne : ‖w‖ ≠ 0 := ne_of_gt hr
  have hξ : ‖(‖w‖⁻¹ • w : TangentSpace I q)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_cancel₀ hrne]
  have hs : 0 < ‖w‖ / 2 := by positivity
  have ht : 0 ≤ ‖w‖ / 2 := hs.le
  have h := GExp_add_smul (cov := cov) hmet (p := q) (ξ := ‖w‖⁻¹ • w) hξ hs ht
  have h1 : (‖w‖ / 2 + ‖w‖ / 2) • (‖w‖⁻¹ • w) = w := by
    rw [add_halves, smul_smul, mul_inv_cancel₀ hrne, one_smul]
  rw [h1] at h
  exact h

/-- **The coordinate velocity of the ray at the midpoint**, in the parametrisation `s ↦ s • w`, is
the chart coordinate of the remaining vector of the unit ray. -/
theorem deriv_ray_eq_clm_of_split (hmet : IsMetricCompatible cov) {q : M} {w : TangentSpace I q}
    (hw : w ≠ 0) {y : M}
    (hy : GExp (cov := cov) hmet q ((‖w‖ / 2) • (‖w‖⁻¹ • w)) ∈ (chartAt H y).source) :
    (1 / 2 : ℝ) • deriv (fun s : ℝ =>
        (extChartAt I y) (GExp (cov := cov) hmet q (s • w))) (1 / 2)
      = ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ
          (GExp (cov := cov) hmet q ((‖w‖ / 2) • (‖w‖⁻¹ • w))))
        ((‖w‖ / 2) • curveVelocity (I := I)
          (fun r : ℝ => GExp (cov := cov) hmet q (r • (‖w‖⁻¹ • w))) (‖w‖ / 2)) := by
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hrne : ‖w‖ ≠ 0 := ne_of_gt hr
  -- the chain rule: the `w`-ray is the unit ray reparametrised
  have hfun : (fun s : ℝ => (extChartAt I y) (GExp (cov := cov) hmet q (s • w)))
      = (fun s : ℝ => (extChartAt I y) (GExp (cov := cov) hmet q ((s * ‖w‖) • (‖w‖⁻¹ • w)))) := by
    funext s
    rw [GExp_ray_eq_unit_ray (cov := cov) hmet hw s]
  have hfun' : (fun s : ℝ => (extChartAt I y) (GExp (cov := cov) hmet q ((s * ‖w‖) • (‖w‖⁻¹ • w))))
      = (fun s : ℝ => (extChartAt I y) (GExp (cov := cov) hmet q ((‖w‖ * s) • (‖w‖⁻¹ • w)))) := by
    funext s; rw [mul_comm]
  have hξn : ‖(‖w‖⁻¹ • w : TangentSpace I q)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_cancel₀ hrne]
  have hv : (‖w‖⁻¹ • w : TangentSpace I q) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξn
    norm_num at hξn
  have hηmd : MDifferentiableAt 𝓘(ℝ) I
      (fun r : ℝ => GExp (cov := cov) hmet q (r • (‖w‖⁻¹ • w))) (‖w‖ / 2) :=
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hv).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by simp)
  have hchain : deriv (fun s : ℝ =>
        (extChartAt I y) (GExp (cov := cov) hmet q ((s * ‖w‖) • (‖w‖⁻¹ • w)))) (1 / 2)
      = ‖w‖ • deriv (fun t : ℝ =>
          (extChartAt I y) (GExp (cov := cov) hmet q (t • (‖w‖⁻¹ • w)))) (‖w‖ / 2) := by
    rw [hfun']
    have h := deriv_comp_mul_left ‖w‖
      (fun t : ℝ => (extChartAt I y) (GExp (cov := cov) hmet q (t • (‖w‖⁻¹ • w)))) (1 / 2)
    rw [show ‖w‖ * (1 / 2) = ‖w‖ / 2 from by ring] at h
    exact h
  have hclm : deriv (fun t : ℝ =>
        (extChartAt I y) (GExp (cov := cov) hmet q (t • (‖w‖⁻¹ • w)))) (‖w‖ / 2)
      = ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ
          (GExp (cov := cov) hmet q ((‖w‖ / 2) • (‖w‖⁻¹ • w))))
        (curveVelocity (I := I)
          (fun r : ℝ => GExp (cov := cov) hmet q (r • (‖w‖⁻¹ • w))) (‖w‖ / 2)) := by
    have h := deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (I := I)
      (x := y) (γ := fun r : ℝ => GExp (cov := cov) hmet q (r • (‖w‖⁻¹ • w)))
      (t := ‖w‖ / 2) hηmd hy
    exact h
  rw [hfun, hchain, hclm, smul_smul]
  congr 1
  rw [map_smul]
  congr 1
  ring

/-! ## The auxiliary maps of the doubling step -/

/-- The midpoint of the ray of `u` in the chart at `z`. -/
noncomputable def midPt (hmet : IsMetricCompatible cov) (z : M) (q : M) (u : E) : M :=
  GExp (cov := cov) hmet q
    ((‖frameVector (I := I) z q u‖ / 2) •
      ((‖frameVector (I := I) z q u‖)⁻¹ • frameVector (I := I) z q u))

lemma midPt_apply (hmet : IsMetricCompatible cov) (z : M) (q : M) (u : E) :
    midPt (cov := cov) hmet z q u
      = GExp (cov := cov) hmet q
          ((‖frameVector (I := I) z q u‖ / 2) •
            ((‖frameVector (I := I) z q u‖)⁻¹ • frameVector (I := I) z q u)) := rfl

/-- The chart coordinate (in the chart at `z'`) of the velocity of the second half of the ray. -/
noncomputable def halfFun (hmet : IsMetricCompatible cov) (z' z : M) : (E × E) × ℝ → E :=
  fun t => (extChartAt I z') (GExp (cov := cov) hmet ((extChartAt I z).symm t.1.1)
    (frameVector (I := I) z ((extChartAt I z).symm t.1.1) (t.2 • t.1.2)))

noncomputable def halfVel (hmet : IsMetricCompatible cov) (z' z : M) (q : M) (u : E) : E :=
  (1 / 2 : ℝ) • (fderiv ℝ (halfFun (cov := cov) hmet z' z)
    (((extChartAt I z) q, u), 1 / 2)) (((0 : E), (0 : E)), (1 : ℝ))

/-- The half-vector of `u` is the vector whose coordinates are `u/2`. -/
lemma half_smul_inv_smul {q : M} (w : TangentSpace I q) :
    (‖w‖ / 2) • (‖w‖⁻¹ • w) = (1 / 2 : ℝ) • w := by
  rcases eq_or_ne w 0 with h0 | hw
  · subst h0; simp
  · have hr : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    rw [smul_smul, show ‖w‖ / 2 * ‖w‖⁻¹ = 1 / 2 from by field_simp]

/-- The inner function of `halfVel`, written out. -/
lemma halfVel_eq (hmet : IsMetricCompatible cov) (z' z : M) (q : M) (u : E) :
    halfVel (cov := cov) hmet z' z q u
      = (1 / 2 : ℝ) • (fderiv ℝ (halfFun (cov := cov) hmet z' z)
          (((extChartAt I z) q, u), 1 / 2)) (((0 : E), (0 : E)), (1 : ℝ)) := rfl

lemma midPt_eq (hmet : IsMetricCompatible cov) (z : M) (q : M) (u : E) :
    midPt (cov := cov) hmet z q u
      = GExp (cov := cov) hmet q
          ((‖frameVector (I := I) z q u‖ / 2) •
            ((‖frameVector (I := I) z q u‖)⁻¹ • frameVector (I := I) z q u)) := rfl

/-- **The chain rule for the inner function of `halfVel`.**  The `fderiv` of the ray in the
coordinates of the chart at `z'` in the time direction is the derivative of the chart coordinate of
the ray. -/
lemma halfVel_eq_half_deriv (hmet : IsMetricCompatible cov) {z z' : M} {q : M} {u : E}
    (hq : q ∈ (extChartAt I z).source)
    (hdiff : DifferentiableAt ℝ (halfFun (cov := cov) hmet z' z)
      (((extChartAt I z) q, u), 1 / 2)) :
    halfVel (cov := cov) hmet z' z q u
      = (1 / 2 : ℝ) • deriv (fun s : ℝ =>
          (extChartAt I z') (GExp (cov := cov) hmet q (s • frameVector (I := I) z q u))) (1 / 2) := by
  have hcurve : HasDerivAt (fun s : ℝ => (((((extChartAt I z) q, u), s) : (E × E) × ℝ)))
      ((((0 : E), (0 : E)), (1 : ℝ))) (1 / 2) :=
    (hasDerivAt_const _ (((extChartAt I z) q, u))).prodMk (hasDerivAt_id' (1 / 2))
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt (1 / 2) hcurve
  have hcongr : (halfFun (cov := cov) hmet z' z ∘ fun s : ℝ => (((((extChartAt I z) q, u), s) : (E × E) × ℝ)))
      = (fun s : ℝ =>
          (extChartAt I z') (GExp (cov := cov) hmet q (s • frameVector (I := I) z q u))) := by
    funext s
    show (extChartAt I z') (GExp (cov := cov) hmet ((extChartAt I z).symm ((extChartAt I z) q))
      (frameVector (I := I) z ((extChartAt I z).symm ((extChartAt I z) q)) (s • u)))
      = (extChartAt I z') (GExp (cov := cov) hmet q (s • frameVector (I := I) z q u))
    rw [show (extChartAt I z).symm ((extChartAt I z) q) = q from
      (extChartAt I z).left_inv hq]
    rw [frameVector_smul']
  have hA : (fderiv ℝ (halfFun (cov := cov) hmet z' z)
        (((extChartAt I z) q, u), 1 / 2)) ((((0 : E), (0 : E)), (1 : ℝ)))
      = deriv (fun s : ℝ =>
          (extChartAt I z') (GExp (cov := cov) hmet q (s • frameVector (I := I) z q u))) (1 / 2) := by
    rw [← hcomp.deriv]
    rw [hcongr]
  rw [halfVel_eq, hA]

/-- **`halfVel` is the chart coordinate of the remaining vector of the unit ray.** -/
theorem halfVel_eq_clm (hmet : IsMetricCompatible cov) {z z' : M} {q : M} {u : E}
    (hq : q ∈ (extChartAt I z).source) (hw : frameVector (I := I) z q u ≠ 0)
    (hy : midPt (cov := cov) hmet z q u ∈ (chartAt H z').source)
    (hdiff : DifferentiableAt ℝ (halfFun (cov := cov) hmet z' z)
      (((extChartAt I z) q, u), 1 / 2)) :
    halfVel (cov := cov) hmet z' z q u
      = ((trivializationAt E (TangentSpace I) z').continuousLinearMapAt ℝ
          (midPt (cov := cov) hmet z q u))
          ((‖frameVector (I := I) z q u‖ / 2) • curveVelocity (I := I)
            (fun r : ℝ => GExp (cov := cov) hmet q
              (r • ((‖frameVector (I := I) z q u‖)⁻¹ • frameVector (I := I) z q u)))
            (‖frameVector (I := I) z q u‖ / 2)) := by
  rw [halfVel_eq_half_deriv (cov := cov) hmet hq hdiff]
  exact deriv_ray_eq_clm_of_split (cov := cov) hmet hw hy


/-! ## The doubling step -/

/-- **Smoothness of the chart coordinate of the ray.**  Under the induction hypothesis at the half
vector, the chart coordinate of the ray `s ↦ GExp q (s • w)` is `C^∞`. -/
theorem contDiffAt_halfFun (hmet : IsMetricCompatible cov) {z z' q : M} {u : E}
    (hqsrc : q ∈ (chartAt H z).source)
    (h1 : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (gexpChart (cov := cov) hmet z) (q, (1 / 2 : ℝ) • u))
    (hy : midPt (cov := cov) hmet z q u ∈ (chartAt H z').source) :
    ContDiffAt ℝ ∞ (halfFun (cov := cov) hmet z' z) (((extChartAt I z) q, u), (1 / 2 : ℝ)) := by
  classical
  have hsrcnhds : (chartAt H z).source ∈ 𝓝 q := (chartAt H z).open_source.mem_nhds hqsrc
  have hqsrc' : q ∈ (extChartAt I z).source := by rw [extChartAt_source]; exact hqsrc
  have htarget : (extChartAt I z) q ∈ (extChartAt I z).target :=
    (extChartAt I z).map_source hqsrc'
  have hleft : (extChartAt I z).symm ((extChartAt I z) q) = q :=
    (extChartAt I z).left_inv hqsrc'
  have hψ : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I z).symm ((extChartAt I z) q) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) z).contMDiffAt
      ((isOpen_extChartAt_target z).mem_nhds htarget)
  let pt : (E × E) × ℝ := (((extChartAt I z) q, u), (1 / 2 : ℝ))
  have hfst1 : ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) ∞
      (fun t : (E × E) × ℝ => t.1.1) pt :=
    ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) ℝ)).contMDiffAt
  have hsnd1 : ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) ∞
      (fun t : (E × E) × ℝ => t.1.2) pt :=
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) ℝ)).contMDiffAt
  have hsnd2 : ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : (E × E) × ℝ => t.2) pt :=
    (ContinuousLinearMap.snd ℝ (E × E) ℝ).contMDiffAt
  have hψc : ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) I ∞
      (fun t : (E × E) × ℝ => (extChartAt I z).symm t.1.1) pt :=
    hψ.comp pt hfst1
  have hsc : ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) ∞
      (fun t : (E × E) × ℝ => t.2 • t.1.2) pt :=
    hsnd2.smul hsnd1
  have hinner : ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun t : (E × E) × ℝ => ((extChartAt I z).symm t.1.1, t.2 • t.1.2)) pt :=
    hψc.prodMk hsc
  have h1' : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (gexpChart (cov := cov) hmet z)
      ((extChartAt I z).symm ((extChartAt I z) q), (1 / 2 : ℝ) • u) := by
    rw [hleft]
    exact h1
  have hA : ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) I ∞
      (fun t : (E × E) × ℝ => GExp (cov := cov) hmet ((extChartAt I z).symm t.1.1)
        (frameVector (I := I) z ((extChartAt I z).symm t.1.1) (t.2 • t.1.2))) pt :=
    h1'.comp pt hinner
  have hφ0 : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I z') (midPt (cov := cov) hmet z q u) :=
    (contMDiffOn_extChartAt (I := I) (x := z') (n := ∞)).contMDiffAt
      ((chartAt H z').open_source.mem_nhds hy)
  have hpt : midPt (cov := cov) hmet z q u
      = GExp (cov := cov) hmet q (frameVector (I := I) z q ((1 / 2 : ℝ) • u)) := by
    rw [midPt_eq]; congr 1; rw [half_smul_inv_smul, frameVector_smul']
  have hφ : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I z')
      (GExp (cov := cov) hmet ((extChartAt I z).symm ((extChartAt I z) q))
        (frameVector (I := I) z ((extChartAt I z).symm ((extChartAt I z) q))
          ((1 / 2 : ℝ) • u))) := by
    rw [hleft]
    rwa [hpt] at hφ0
  have hres := hφ.comp pt hA
  have hres2 : ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) ∞
      (halfFun (cov := cov) hmet z' z) pt := by
    change ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) ∞
      (fun t : (E × E) × ℝ => (extChartAt I z')
        (GExp (cov := cov) hmet ((extChartAt I z).symm t.1.1)
          (frameVector (I := I) z ((extChartAt I z).symm t.1.1) (t.2 • t.1.2)))) pt
    exact hres
  exact (contMDiffAt_iff_contDiffAt).mp hres2

/-- **The doubling step, core.**  If the family is `C^∞` at the *half* vector of `(q₀,u₀)` and at
the midpoint state `(midPt, halfVel)` in the chart at the midpoint, then it is `C^∞` at `(q₀,u₀)`. -/
theorem contMDiffAt_gexpChart_of_half (hmet : IsMetricCompatible cov) {n : ℕ} (z : Fin n → M)
    {i j : Fin n} {q₀ : M} {u₀ : E}
    (hq₀ : q₀ ∈ (chartAt H (z i)).source)
    (hjsrc : midPt (cov := cov) hmet (z i) q₀ u₀ ∈ (chartAt H (z j)).source)
    (hw : frameVector (I := I) (z i) q₀ u₀ ≠ 0)
    (h1 : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (gexpChart (cov := cov) hmet (z i))
      (q₀, (1 / 2 : ℝ) • u₀))
    (h2 : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (gexpChart (cov := cov) hmet (z j))
      (midPt (cov := cov) hmet (z i) q₀ u₀, halfVel (cov := cov) hmet (z j) (z i) q₀ u₀)) :
    ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (gexpChart (cov := cov) hmet (z i)) (q₀, u₀) := by
  classical
  have hsrcnhds : (extChartAt I (z i)).source ∈ 𝓝 q₀ := by
    rw [extChartAt_source]
    exact (chartAt H (z i)).open_source.mem_nhds (by simpa using hq₀)
  have hq₀src : q₀ ∈ (extChartAt I (z i)).source := by rw [extChartAt_source]; exact hq₀
  have htarget : (extChartAt I (z i)) q₀ ∈ (extChartAt I (z i)).target :=
    (extChartAt I (z i)).map_source hq₀src
  -- the two projection maps
  have hfstp : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (fun p : M × E => p.1) (q₀, u₀) :=
    contMDiffAt_fst
  have hsndp : ContMDiffAt (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun p : M × E => p.2) (q₀, u₀) :=
    contMDiffAt_snd
  have hhalfE : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : E => (1 / 2 : ℝ) • x) u₀ :=
    (show ContDiffAt ℝ ∞ (fun x : E => (1 / 2 : ℝ) • x) u₀ from by fun_prop).contMDiffAt
  have hproj : ContMDiffAt (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × E => (p.1, (1 / 2 : ℝ) • p.2)) (q₀, u₀) :=
    hfstp.prodMk (hhalfE.comp (q₀, u₀) hsndp)
  have hmid : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞
      (fun p : M × E => gexpChart (cov := cov) hmet (z i) (p.1, (1 / 2 : ℝ) • p.2))
      (q₀, u₀) :=
    h1.comp (q₀, u₀) hproj
  have hF : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞
      (fun p : M × E => midPt (cov := cov) hmet (z i) p.1 p.2) (q₀, u₀) := by
    refine hmid.congr_of_eventuallyEq ?_
    filter_upwards with p
    simp only [gexpChart, midPt_eq]
    congr 1
    rw [half_smul_inv_smul, frameVector_smul']
  -- the inner function and its differential
  have hleft : (extChartAt I (z i)).symm ((extChartAt I (z i)) q₀) = q₀ :=
    (extChartAt I (z i)).left_inv hq₀src
  have hpt : midPt (cov := cov) hmet (z i) q₀ u₀
      = GExp (cov := cov) hmet q₀ (frameVector (I := I) (z i) q₀ ((1 / 2 : ℝ) • u₀)) := by
    rw [midPt_eq]
    congr 1
    rw [half_smul_inv_smul, frameVector_smul']
  have hφ0 : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (z j))
      (GExp (cov := cov) hmet q₀ (frameVector (I := I) (z i) q₀ ((1 / 2 : ℝ) • u₀))) := by
    have hc : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (z j))
        (midPt (cov := cov) hmet (z i) q₀ u₀) :=
      (contMDiffOn_extChartAt (I := I) (x := z j) (n := ∞)).contMDiffAt
        ((chartAt H (z j)).open_source.mem_nhds hjsrc)
    rwa [hpt] at hc
  have hΛ := contDiffAt_halfFun (cov := cov) hmet hq₀ h1 hjsrc
  -- the midpoint state is eventually differentiable
  obtain ⟨s, hs, hscd⟩ := (hΛ.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)).contDiffOn
    (le_refl (2 : ℕ∞ω)) (by intro h; exact absurd h (by norm_num))
  have hargcont : ContinuousAt (fun p : M × E => (((extChartAt I (z i)) p.1, p.2), (1 / 2 : ℝ)))
      (q₀, u₀) :=
    ((((continuousOn_extChartAt (I := I) (z i)).continuousAt hsrcnhds).comp
      (continuousAt_fst : ContinuousAt (fun p : M × E => p.1) (q₀, u₀))).prodMk
      (continuousAt_snd : ContinuousAt (fun p : M × E => p.2) (q₀, u₀))).prodMk continuousAt_const
  have hev : ∀ᶠ p : M × E in 𝓝 (q₀, u₀),
      DifferentiableAt ℝ (halfFun (cov := cov) hmet (z j) (z i))
        (((extChartAt I (z i)) p.1, p.2), (1 / 2 : ℝ)) := by
    have hssub : interior s ⊆ s := interior_subset
    have hopen : IsOpen (interior s) := isOpen_interior
    have hmem : interior s ∈ 𝓝 (((extChartAt I (z i)) q₀, u₀), (1 / 2 : ℝ)) :=
      isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs)
    filter_upwards [hargcont.eventually hmem] with p hp
    exact (hscd.mono hssub).contDiffAt (hopen.mem_nhds hp) |>.differentiableAt (by norm_num)
  -- the second-half map is smooth
  have hW : ContMDiffAt (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : M × E => halfVel (cov := cov) hmet (z j) (z i) p.1 p.2) (q₀, u₀) := by
    have hfd : ContDiffAt ℝ ∞ (fderiv ℝ (halfFun (cov := cov) hmet (z j) (z i)))
        (((extChartAt I (z i)) q₀, u₀), 1 / 2) :=
      hΛ.fderiv_right (le_refl (∞ : ℕ∞ω))
    have hval : ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) ∞ (fun t : (E × E) × ℝ =>
        (fderiv ℝ (halfFun (cov := cov) hmet (z j) (z i)) t) (((0 : E), (0 : E)), (1 : ℝ)))
        (((extChartAt I (z i)) q₀, u₀), 1 / 2) :=
      (hfd.clm_apply contDiffAt_const).contMDiffAt
    have hchart : ContMDiffAt (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : M × E => (extChartAt I (z i)) p.1) (q₀, u₀) :=
      ((contMDiffOn_extChartAt (I := I) (x := z i) (n := ∞)).contMDiffAt
        ((chartAt H (z i)).open_source.mem_nhds (by simpa using hq₀))).comp (q₀, u₀) hfstp
    have hEℝ : ContMDiffAt (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun _ : M × E => (1 / 2 : ℝ)) (q₀, u₀) :=
      contMDiffAt_const (x := (q₀, u₀))
    have hargcont' : ContMDiffAt (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, (E × E) × ℝ) ∞
        (fun p : M × E => (((extChartAt I (z i)) p.1, p.2), (1 / 2 : ℝ))) (q₀, u₀) :=
      (hchart.prodMk_space hsndp).prodMk_space hEℝ
    have hcomp := hval.comp (q₀, u₀) hargcont'
    have hEℝ' : ContMDiffAt (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun _ : M × E => (1 / 2 : ℝ)) (q₀, u₀) := contMDiffAt_const (x := (q₀, u₀))
    have hsm := hEℝ'.smul hcomp
    have hsm' : ContMDiffAt (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : M × E => (1 / 2 : ℝ) • (fderiv ℝ (halfFun (cov := cov) hmet (z j) (z i))
          (((extChartAt I (z i)) p.1, p.2), (1 / 2 : ℝ))) (((0 : E), (0 : E)), (1 : ℝ)))
        (q₀, u₀) := by
      refine hsm.congr_of_eventuallyEq ?_
      filter_upwards with p
      rfl
    simpa only [halfVel, halfFun] using hsm'
  -- the identity holds eventually
  have hsrc1 : ∀ᶠ p : M × E in 𝓝 (q₀, u₀), p.1 ∈ (extChartAt I (z i)).source :=
    (continuousAt_fst : ContinuousAt (fun p : M × E => p.1) (q₀, u₀)).eventually hsrcnhds
  have hsrc2 : ∀ᶠ p : M × E in 𝓝 (q₀, u₀),
      midPt (cov := cov) hmet (z i) p.1 p.2 ∈ (chartAt H (z j)).source :=
    hF.continuousAt.eventually ((chartAt H (z j)).open_source.mem_nhds hjsrc)
  have hid : (fun p : M × E => gexpChart (cov := cov) hmet (z i) p)
      =ᶠ[𝓝 (q₀, u₀)] (fun p : M × E => gexpChart (cov := cov) hmet (z j)
        (midPt (cov := cov) hmet (z i) p.1 p.2, halfVel (cov := cov) hmet (z j) (z i) p.1 p.2)) := by
    filter_upwards [hsrc1, hsrc2, hev] with p hp1 hp2 hp3
    have hp1' : p.1 ∈ (extChartAt I (z i)).source := hp1
    by_cases hw0 : frameVector (I := I) (z i) p.1 p.2 = 0
    · have hu0 : p.2 = 0 := frameVector_eq_zero (I := I) hp1' hw0
      obtain ⟨q, u⟩ := p
      subst hu0
      have hL : gexpChart (cov := cov) hmet (z i) (q, 0) = q := by
        simp only [gexpChart, frameVector_zero' (I := I) (z i) q, GExp_zero]
      have hmid0 : midPt (cov := cov) hmet (z i) q 0 = q := by
        rw [midPt_eq, frameVector_zero' (I := I) (z i) q]
        simp
      have hvel0 : halfVel (cov := cov) hmet (z j) (z i) q 0 = 0 := by
        rw [halfVel_eq_half_deriv (cov := cov) hmet hp1' hp3]
        have hc : (fun s : ℝ => (extChartAt I (z j))
            (GExp (cov := cov) hmet q (s • frameVector (I := I) (z i) q 0)))
            = fun _ : ℝ => (extChartAt I (z j)) (GExp (cov := cov) hmet q 0) := by
          funext s; rw [frameVector_zero' (I := I) (z i) q, smul_zero]
        rw [hc, deriv_const, smul_zero]
      have hR : gexpChart (cov := cov) hmet (z j)
          (midPt (cov := cov) hmet (z i) q 0, halfVel (cov := cov) hmet (z j) (z i) q 0) = q := by
        rw [hmid0, hvel0]
        simp only [gexpChart, frameVector_zero' (I := I) (z j) q, GExp_zero]
      rw [hL, hR]
    · push_neg at hw0
      obtain ⟨q, u⟩ := p
      have hsplit := GExp_split (cov := cov) hmet hw0
      have hclm := halfVel_eq_clm (cov := cov) hmet hp1' hw0 hp2 hp3
      have hfr : frameVector (I := I) (z j) (midPt (cov := cov) hmet (z i) q u)
          (halfVel (cov := cov) hmet (z j) (z i) q u)
          = ((‖frameVector (I := I) (z i) q u‖ / 2) • curveVelocity (I := I)
              (fun r : ℝ => GExp (cov := cov) hmet q
                (r • ((‖frameVector (I := I) (z i) q u‖)⁻¹ • frameVector (I := I) (z i) q u)))
              (‖frameVector (I := I) (z i) q u‖ / 2)) := by
        rw [hclm]
        exact frameVector_clm (I := I) (z₀ := z j) (q := midPt (cov := cov) hmet (z i) q u)
          (by simpa using hp2) _
      simp only [gexpChart]
      rw [hfr]
      exact hsplit
  have hcomp : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞
      (fun p : M × E => gexpChart (cov := cov) hmet (z j)
        (midPt (cov := cov) hmet (z i) p.1 p.2, halfVel (cov := cov) hmet (z j) (z i) p.1 p.2))
      (q₀, u₀) := h2.comp (q₀, u₀) (hF.prodMk hW)
  exact hcomp.congr_of_eventuallyEq hid


/-- **The doubling step.**  If the family is `C^∞` on the fibre ball of radius `R` in the
coordinates of every chart of the atlas, then it is `C^∞` on the fibre ball of radius `2R`. -/
theorem smoothOnBall_step (hmet : IsMetricCompatible cov) {n : ℕ} (z : Fin n → M) (Z : Fin n → Set M)
    (hZsrc : ∀ i, Z i ⊆ (chartAt H (z i)).source) (hcov : Set.univ ⊆ ⋃ i, Z i) {R : ℝ}
    (hR : SmoothOnBall (cov := cov) hmet z Z R) :
    SmoothOnBall (cov := cov) hmet z Z (2 * R) := by
  intro i q₀ u₀ hq₀ hu₀
  by_cases hR0 : R ≤ 0
  · exfalso
    exact absurd (lt_of_lt_of_le hu₀ (by linarith : 2 * R ≤ 0)) (not_lt.mpr (norm_nonneg _))
  push Not at hR0
  by_cases hsmall : ‖frameVector (I := I) (z i) q₀ u₀‖ < R
  · exact hR i q₀ u₀ hq₀ hsmall
  push Not at hsmall
  have hsrc : q₀ ∈ (extChartAt I (z i)).source := by
    rw [extChartAt_source]; exact hZsrc i hq₀
  have hwne : frameVector (I := I) (z i) q₀ u₀ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsmall
    linarith
  -- the half vector is in the known ball
  have hhalf : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (gexpChart (cov := cov) hmet (z i))
      (q₀, (1 / 2 : ℝ) • u₀) := by
    refine hR i q₀ ((1 / 2 : ℝ) • u₀) hq₀ ?_
    rw [frameVector_smul', norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  -- the midpoint is in some atlas piece
  obtain ⟨j, hj⟩ : ∃ j : Fin n, midPt (cov := cov) hmet (z i) q₀ u₀ ∈ Z j := by
    obtain ⟨j, hj⟩ :=
      Set.mem_iUnion.mp (hcov (Set.mem_univ (midPt (cov := cov) hmet (z i) q₀ u₀)))
    exact ⟨j, hj⟩
  -- the second half of the ray
  have hξnorm : ‖(‖frameVector (I := I) (z i) q₀ u₀‖⁻¹ • frameVector (I := I) (z i) q₀ u₀ :
      TangentSpace I q₀)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (norm_pos_iff.mpr hwne),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwne)]
  have hξne : (‖frameVector (I := I) (z i) q₀ u₀‖⁻¹ • frameVector (I := I) (z i) q₀ u₀ :
      TangentSpace I q₀) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξnorm
    norm_num at hξnorm
  have hVnorm : ‖(‖frameVector (I := I) (z i) q₀ u₀‖ / 2) • curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet q₀
        (r • ((‖frameVector (I := I) (z i) q₀ u₀‖)⁻¹ • frameVector (I := I) (z i) q₀ u₀)))
      (‖frameVector (I := I) (z i) q₀ u₀‖ / 2)‖ < R := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < ‖frameVector (I := I) (z i) q₀ u₀‖ / 2),
      norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q₀ hξne (by positivity), hξnorm, mul_one]
    linarith
  -- the induction hypothesis at the midpoint
  have h2 : ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (gexpChart (cov := cov) hmet (z j))
      (midPt (cov := cov) hmet (z i) q₀ u₀, halfVel (cov := cov) hmet (z j) (z i) q₀ u₀) := by
    refine hR j (midPt (cov := cov) hmet (z i) q₀ u₀)
      (halfVel (cov := cov) hmet (z j) (z i) q₀ u₀) hj ?_
    have hnorm : ‖frameVector (I := I) (z j) (midPt (cov := cov) hmet (z i) q₀ u₀)
        (halfVel (cov := cov) hmet (z j) (z i) q₀ u₀)‖
        = ‖(‖frameVector (I := I) (z i) q₀ u₀‖ / 2) • curveVelocity (I := I)
            (fun r : ℝ => GExp (cov := cov) hmet q₀
              (r • ((‖frameVector (I := I) (z i) q₀ u₀‖)⁻¹ • frameVector (I := I) (z i) q₀ u₀)))
            (‖frameVector (I := I) (z i) q₀ u₀‖ / 2)‖ := by
      rw [halfVel_eq_clm (cov := cov) hmet hsrc hwne (hZsrc j hj)
        ((contDiffAt_halfFun (cov := cov) hmet (hZsrc i hq₀) hhalf (hZsrc j hj)).differentiableAt
          (by norm_num))]
      exact congrArg Norm.norm (frameVector_clm (I := I) (z₀ := z j)
        (q := midPt (cov := cov) hmet (z i) q₀ u₀) (by simpa using hZsrc j hj) _)
    rw [hnorm]
    exact hVnorm
  exact contMDiffAt_gexpChart_of_half (cov := cov) hmet z (hZsrc i hq₀) (hZsrc j hj) hwne hhalf h2

/-- **The exponential family is `C^∞` at every state.**  For a finite atlas `(z i, Z i)` of compact
chart pieces covering `M`, the family `(q,u) ↦ GExp q (frameVector (z i) q u)` is `C^∞` at
`(q,u)` for every `q ∈ Z i` and every `u`. -/
theorem contMDiffAt_gexpChart_all (hmet : IsMetricCompatible cov) {n : ℕ} (z : Fin n → M)
    (Z : Fin n → Set M) (hZsrc : ∀ i, Z i ⊆ (chartAt H (z i)).source)
    (hcov : Set.univ ⊆ ⋃ i, Z i) (δ : ℝ) (hδ : 0 < δ)
    (hbase : SmoothOnBall (cov := cov) hmet z Z δ)
    (i : Fin n) (q : M) (u : E) (hq : q ∈ Z i) :
    ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞ (gexpChart (cov := cov) hmet (z i)) (q, u) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖frameVector (I := I) (z i) q u‖ < 2 ^ k * δ := by
    have ht : Tendsto (fun k : ℕ => δ * (2 : ℝ) ^ k) atTop atTop :=
      Tendsto.const_mul_atTop hδ (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    obtain ⟨k, hk⟩ := (ht.eventually_gt_atTop ‖frameVector (I := I) (z i) q u‖).exists
    exact ⟨k, by rwa [mul_comm] at hk⟩
  have hstep : ∀ m : ℕ, SmoothOnBall (cov := cov) hmet z Z (2 ^ m * δ) := by
    intro m
    induction m with
    | zero => simpa using hbase
    | succ l ih =>
        have h2 : (2 : ℝ) * (2 ^ l * δ) = 2 ^ (l + 1) * δ := by ring
        rw [← h2]
        exact smoothOnBall_step (cov := cov) hmet z Z hZsrc hcov ih
  exact hstep k i q u hq hk

/-- **The exponential map is `C^∞` at every tangent vector** (smoothness in the velocity alone). -/
theorem contMDiffAt_GExp (hmet : IsMetricCompatible cov) {n : ℕ} (z : Fin n → M)
    (Z : Fin n → Set M) (hZsrc : ∀ i, Z i ⊆ (chartAt H (z i)).source)
    (hcov : Set.univ ⊆ ⋃ i, Z i) (δ : ℝ) (hδ : 0 < δ)
    (hbase : SmoothOnBall (cov := cov) hmet z Z δ)
    (p : M) (v : TangentSpace I p) :
    ContMDiffAt 𝓘(ℝ, E) I ∞ (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
      (show E from v) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ p))
  have hsrc : p ∈ (extChartAt I (z i)).source := by
    rw [extChartAt_source]; exact hZsrc i hi
  let clmE : E →L[ℝ] E := (trivializationAt E (TangentSpace I) (z i)).continuousLinearMapAt ℝ p
  have hclm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun w : E => clmE w) (show E from v) :=
    clmE.contMDiffAt
  have hpair : ContMDiffAt 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E)) ∞
      (fun w : E => (p, clmE w)) (show E from v) :=
    (contMDiffAt_const (x := (show E from v)) (c := p)).prodMk hclm
  have hcomp := (contMDiffAt_gexpChart_all (cov := cov) hmet z Z hZsrc hcov δ hδ hbase i p
    (clmE v) hi).comp (show E from v) hpair
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with w
  simp only [gexpChart, Function.comp_apply]
  show GExp (cov := cov) hmet p w = GExp (cov := cov) hmet p (frameVector (I := I) (z i) p (clmE w))
  have hfe : frameVector (I := I) (z i) p (clmE w) = w :=
    frameVector_clm (I := I) (z₀ := z i) (q := p) hsrc w
  rw [hfe]


/-- **The exponential map of a compact Riemannian manifold is `C^∞` at every tangent vector.**  This
is the "no hypotheses" form of `contMDiffAt_GExp`: the finite atlas comes from
`Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt` and the base radius from
`exists_pos_smoothOnBall`. -/
theorem exists_contMDiffAt_GExp (hmet : IsMetricCompatible cov) (p : M) (v : TangentSpace I p) :
    ContMDiffAt 𝓘(ℝ, E) I ∞ (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
      (show E from v) := by
  obtain ⟨n, z, Z, hZc, hZsrc, hcov⟩ :=
    Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt (I := I) (M := M)
  obtain ⟨δ, hδ, hbase⟩ := exists_pos_smoothOnBall (cov := cov) hmet z Z hZc hZsrc hcov
  exact contMDiffAt_GExp (cov := cov) hmet z Z hZsrc hcov δ hδ hbase p v

end

end Submission.GExpSmooth
