import ChallengeDeps
import Submission.GeoCore
import Submission.ChartArc
import Submission.Rigidity
import Mathlib

open scoped Manifold ENNReal ContDiff Topology
open Set Metric
open EMetric
open Bundle

/-!
# Child task: per-point metric normal-ball package (`nb_pkg`)

Prove COMPLETELY the theorem
`Submission.NBChild.nb_pkg` below.  It extracts a clean *metric* normal-ball package from
`Submission.arc_rigidity` (VERIFIED) at every point `p : M` of the Riemannian manifold.

The conclusion, with `x₀ := extChartAt I p p` and `ge0 := ge x₀` the chart bilinear form and
`mnorm ge0 v := Real.sqrt (ge0 v v)`:

* `ρ0 > 0`, `ge0` positive definite & symmetric;
* `Exp : E → M` (the exponential/radial map at `p`) with `Exp 0 = p` and:
  (r)  `mnorm ge0 v < ρ0 → edist p (Exp v) = ofReal (mnorm ge0 v)`        (radial identity)
  (a)  unit `W` (`mnorm ge0 W = 1`), `|s|,|t| < ρ0`, `s ≤ t`:
       `edist (Exp (s•W)) (Exp (t•W)) = ofReal (t-s)`                     (two-sided arc)
  (s)  `edist p y < ofReal ρ0 → ∃ v, mnorm ge0 v < ρ0 ∧ Exp v = y`        (onto metric ball)
  (i)  injectivity on `{v | mnorm ge0 v < ρ0}`
  (c)  `∀ ρ, 0 < ρ → ρ < ρ0 → IsCompact (closedBall p (ofReal ρ))`        (small balls compact)
-/

namespace Submission
namespace NBChild

open LeanEval.Geometry

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

open Submission

theorem nb_pkg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (p : M) :
    ∃ ρ0 > 0, ∃ ge0 : E →L[ℝ] E →L[ℝ] ℝ,
      (∀ v : E, v ≠ 0 → 0 < ge0 v v) ∧
      (∀ u v : E, ge0 u v = ge0 v u) ∧
      ∃ Exp : E → M, Exp 0 = p ∧
        (∀ v : E, mnorm ge0 v < ρ0 → edist p (Exp v) = ENNReal.ofReal (mnorm ge0 v)) ∧
        (∀ W : E, mnorm ge0 W = 1 → ∀ ⦃s t : ℝ⦄, |s| < ρ0 → |t| < ρ0 → s ≤ t →
           edist (Exp (s • W)) (Exp (t • W)) = ENNReal.ofReal (t - s)) ∧
        (∀ y : M, edist p y < ENNReal.ofReal ρ0 → ∃ v : E, mnorm ge0 v < ρ0 ∧ Exp v = y) ∧
        (∀ v w : E, mnorm ge0 v < ρ0 → mnorm ge0 w < ρ0 → Exp v = Exp w → v = w) ∧
        (∀ ρ : ℝ, 0 < ρ → ρ < ρ0 → IsCompact (closedBall p (ENNReal.ofReal ρ))) := by
  classical
  rcases arc_rigidity (I := I) (M := M) p with
    ⟨ρ0', hρ0'0, ge, hgeC, hgeSymm, hgePos, hgeAgree, hrest⟩
  rcases hrest with ⟨r, hr0, ExpM, S, invM, hExpM0, hSnhds, hS_in, hExpCont, hInj,
    hSurj, hInvS, hInvExp, hRadial, hrest2⟩
  rcases hrest2 with ⟨ρa, hρa0, hρale, hArcM, hRigid⟩
  let x₀ : E := extChartAt I p p
  let ge0 : E →L[ℝ] E →L[ℝ] ℝ := ge x₀
  have hge0pos : ∀ v : E, v ≠ 0 → 0 < ge0 v v := by
    intro v hv
    exact hgePos x₀ v hv
  have hge0sym : ∀ u v : E, ge0 u v = ge0 v u := hgeSymm x₀
  have hBnonneg : ∀ v : E, 0 ≤ ge0 v v := by
    intro v
    by_cases hv : v = 0
    · subst v; simp
    · exact le_of_lt (hge0pos v hv)
  rcases unit_norm_bound ge0 hge0pos with ⟨K, hK0, hKbound⟩
  have hKbound' : ∀ v : E, ‖v‖ ≤ K * mnorm ge0 v := by
    intro v
    have hb := unit_norm_bound_all ge0 hge0pos K hK0.le (fun V hV => hKbound V hV) v
    simpa [mnorm] using hb
  -- the chart metric norm is a continuous function of the vector
  have hmn_cont : Continuous (fun v : E => mnorm ge0 v) := by
    dsimp [mnorm]
    exact Real.continuous_sqrt.comp (by
      have hcu : Continuous (fun p : E × E => ge0 p.1 p.2) :=
        ContinuousLinearMap.continuous₂ ge0
      exact hcu.comp (continuous_diag : Continuous (Function.diag : E → E × E)))
  -- finite metric-ball radius inside S
  rcases Metric.nhds_basis_eball.mem_iff.mp hSnhds with ⟨cInf, hcInf0, hcInfsub⟩
  let cf : ℝ≥0∞ := min cInf 1
  have hcf0 : 0 < cf := lt_min hcInf0 (by norm_num)
  have hcflt1 : cf ≤ (1 : ℝ≥0∞) := min_le_right _ _
  have hcftop : cf ≠ (⊤ : ℝ≥0∞) := ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hcflt1
  let cp : ℝ := cf.toReal
  have hcp0 : 0 < cp := ENNReal.toReal_pos (ne_of_gt hcf0) hcftop
  have hcp_sub : {y : M | edist p y < ENNReal.ofReal cp} ⊆ S := by
    intro y hy
    have hy' : edist y p < ENNReal.ofReal cp := by simpa [edist_comm] using hy
    have hle : ENNReal.ofReal cp ≤ cInf := by
      rw [ENNReal.ofReal_toReal hcftop]
      exact min_le_left _ _
    exact hcInfsub (lt_of_lt_of_le hy' hle)
  -- small radius
  let ρ0 : ℝ := min (min (ρa / 2) (r / (2 * K))) (cp / 2)
  have hρ00 : 0 < ρ0 := by
    dsimp [ρ0]
    exact lt_min (lt_min (half_pos hρa0) (div_pos hr0 (by positivity))) (half_pos hcp0)
  have hρ0_le_ρa : ρ0 ≤ ρa := by
    dsimp [ρ0]
    have h1 : ρa / 2 < ρa := half_lt_self hρa0
    have h2 : min (ρa / 2) (r / (2 * K)) ≤ ρa / 2 := min_le_left _ _
    have h3 : min (min (ρa / 2) (r / (2 * K))) (cp / 2) ≤ ρa / 2 :=
      le_trans (min_le_left _ _) h2
    linarith
  have hρ0_r : K * ρ0 < r := by
    have hle : ρ0 ≤ r / (2 * K) := by
      dsimp [ρ0]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hm : K * (r / (2 * K)) = r / 2 := by
      field_simp [ne_of_gt hK0]
    have h1 : K * ρ0 ≤ r / 2 := (mul_le_mul_of_nonneg_left hle hK0.le).trans_eq hm
    linarith [hr0]
  have hρ0_lt_cp : ρ0 < cp := by
    have h1 : ρ0 ≤ cp / 2 := by
      dsimp [ρ0]
      exact min_le_right _ _
    linarith [hcp0]
  have hρ0lecp : ρ0 ≤ cp := le_of_lt hρ0_lt_cp
  -- metric ball in Euclidean ball(0,r)
  have hmetric_in_euclid : ∀ v : E, mnorm ge0 v < ρ0 → v ∈ ball (0 : E) r := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h1 : ‖v‖ ≤ K * mnorm ge0 v := hKbound' v
    have h2 : K * mnorm ge0 v < K * ρ0 := mul_lt_mul_of_pos_left hv hK0
    exact lt_of_le_of_lt h1 (lt_trans h2 hρ0_r)

  -- now produce the exports
  refine ⟨ρ0, hρ00, ge0, hge0pos, hge0sym, ExpM, hExpM0, ?_, ?_, ?_, ?_, ?_⟩
  · -- radial identity
    intro v hv
    have hvE : v ∈ ball (0 : E) r := hmetric_in_euclid v hv
    have hrad := hRadial v hvE
    simpa [x₀, ge0, mnorm] using hrad
  · -- two-sided arc identity
    intro W hWunit s t hs ht hst
    have hsρa : |s| < ρa := lt_of_lt_of_le hs hρ0_le_ρa
    have htρa : |t| < ρa := lt_of_lt_of_le ht hρ0_le_ρa
    have harc := hArcM W (by simpa [x₀, ge0, mnorm] using hWunit) (s := s) (t := t)
      hst hsρa htρa
    simpa [x₀, ge0, mnorm] using harc
  · -- surjectivity onto the metric ball
    intro y hy
    have hycp : edist p y < ENNReal.ofReal cp :=
      lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hρ0lecp)
    have hyS : y ∈ S := hcp_sub hycp
    rcases hInvS y hyS with ⟨hvE, hExpInv⟩
    let v : E := invM y
    have hradv : edist p y = ENNReal.ofReal (mnorm ge0 v) := by
      have hrad := hRadial (invM y) hvE
      rw [hExpInv] at hrad
      simpa [ge0, x₀, mnorm, v] using hrad
    have hvρ0 : mnorm ge0 v < ρ0 := by
      have hlt' : ENNReal.ofReal (mnorm ge0 v) < ENNReal.ofReal ρ0 := by
        rw [← hradv]
        exact hy
      exact (ENNReal.ofReal_lt_ofReal_iff hρ00).mp hlt'
    refine ⟨v, hvρ0, ?_⟩
    simpa [v] using hExpInv
  · -- injectivity
    intro v w hv hw heq
    have hvE : v ∈ ball (0 : E) r := hmetric_in_euclid v hv
    have hwE : w ∈ ball (0 : E) r := hmetric_in_euclid w hw
    have hsub : (⟨v, hvE⟩ : {v : E // v ∈ ball (0 : E) r}) = ⟨w, hwE⟩ := by
      apply hInj
      simpa using heq
    exact congrArg Subtype.val hsub
  · -- compact small closed balls
    intro ρ hρpos hρlt
    let ell : Set E := {v : E | mnorm ge0 v ≤ ρ}
    have hEllClosed : IsClosed ell := by
      change IsClosed ((fun v : E => mnorm ge0 v) ⁻¹' (Set.Iic ρ))
      exact IsClosed.preimage hmn_cont isClosed_Iic
    have hEllEucl : ell ⊆ Metric.closedBall (0 : E) (K * ρ) := by
      intro v hv
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have h1 : ‖v‖ ≤ K * mnorm ge0 v := hKbound' v
      have h2 : mnorm ge0 v ≤ ρ := hv
      have h3 : K * mnorm ge0 v ≤ K * ρ := mul_le_mul_of_nonneg_left h2 hK0.le
      exact le_trans h1 h3
    have hEllCompact : IsCompact ell :=
      (isCompact_closedBall (x := (0 : E)) (r := K * ρ)).of_isClosed_subset
        hEllClosed hEllEucl
    have hEllDom : ell ⊆ ball (0 : E) r := by
      intro v hv
      exact hmetric_in_euclid v (lt_of_le_of_lt hv hρlt)
    have hContEll : ContinuousOn ExpM ell := hExpCont.mono hEllDom
    have hImCompact : IsCompact (ExpM '' ell) :=
      IsCompact.image_of_continuousOn hEllCompact hContEll
    -- closedBall p (ofReal ρ) = ExpM '' ell
    have hsub_fwd : closedBall p (ENNReal.ofReal ρ) ⊆ ExpM '' ell := by
      intro y hy
      have hyE : edist y p ≤ ENNReal.ofReal ρ := hy
      have hyc : edist p y ≤ ENNReal.ofReal ρ := by
        rw [edist_comm]
        exact hyE
      have hycp : edist p y < ENNReal.ofReal cp :=
        lt_of_le_of_lt hyc ((ENNReal.ofReal_lt_ofReal_iff hcp0).mpr (lt_trans hρlt hρ0_lt_cp))
      have hyS : y ∈ S := hcp_sub hycp
      rcases hInvS y hyS with ⟨hvE, hExpInv⟩
      let v : E := invM y
      have hradv : edist p y = ENNReal.ofReal (mnorm ge0 v) := by
        have hrad := hRadial (invM y) hvE
        rw [hExpInv] at hrad
        simpa [ge0, x₀, mnorm, v] using hrad
      have hmnle : mnorm ge0 v ≤ ρ := by
        have hle' : ENNReal.ofReal (mnorm ge0 v) ≤ ENNReal.ofReal ρ := by
          rw [← hradv]
          exact hyc
        exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hρpos)).mp hle'
      refine ⟨v, hmnle, ?_⟩
      simpa [v] using hExpInv
    have hsub_back : ExpM '' ell ⊆ closedBall p (ENNReal.ofReal ρ) := by
      rintro y ⟨v, hv, rfl⟩
      have hvE : v ∈ ball (0 : E) r := hmetric_in_euclid v (lt_of_le_of_lt hv hρlt)
      have hrad := hRadial v hvE
      have hmnle : edist (ExpM v) p ≤ ENNReal.ofReal ρ := by
        calc
          edist (ExpM v) p = edist p (ExpM v) := by rw [edist_comm]
          _ = ENNReal.ofReal (mnorm ge0 v) := by simpa [x₀, ge0, mnorm] using hrad
          _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hv
      exact hmnle
    have hEq : closedBall p (ENNReal.ofReal ρ) = ExpM '' ell :=
      subset_antisymm hsub_fwd hsub_back
    rw [hEq]
    exact hImCompact

end NBChild
end Submission
