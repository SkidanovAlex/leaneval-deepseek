import Submission.GSConcaveSeg
import Submission.Commons.Analysis.Convex.midpoint_double
import Submission.Commons.Analysis.Convex.concaveOn_Icc_of_local_midpoint

/-!
# Concavity of `d(p,·)` along a far minimising segment, without the `T/2 + D ≤ π` restriction

`Submission.GSConcaveSeg.concaveOn_dist_geodCurve` proves the concavity of `t ↦ d(p, γ t)` along a
minimising geodesic which is *far* from `p`, but only under `T/2 + D ≤ π` (with `T` the length and
`D` an upper bound for `d(p,·)`), because its midpoint inequality is the hinge comparison at the
midpoint `m`, which is only available when the half-length plus `d(p,m)` is at most `π`.

The restriction is removable: the hinge comparison at the midpoint is available *locally* (small
half-width `a`, since `d(p,m) < π` as soon as `D < π`), and a locally midpoint-concave continuous
function on an interval is concave (the doubling argument of `midpoint_double`: applying the
midpoint inequality at half the width, at the midpoint, and at the two quarter points yields the
midpoint inequality at the full width).

## Contents

* `midpoint_double` — one doubling step (pure real analysis);
* `concaveOn_Icc_of_local_midpoint` — local midpoint concavity implies concavity on `[0,T]`;
* `concaveOn_dist_geodCurve_of_lt_pi` — the unrestricted concavity of `d(p,·)`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HingeGlobal
open Submission.HingeKey
open Submission.HingePiece
open Submission.HingeClosed
open Submission.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSConcaveGen

noncomputable section

/-! ## The pure real-analysis localization -/

/-- **One doubling step.**  See `Commons.Analysis.Convex.midpoint_double`. -/
theorem midpoint_double {F : ℝ → ℝ} {T u : ℝ} (hu : 0 < u)
    (h : ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → t - s = u →
      F s + F t ≤ 2 * F ((s + t) / 2)) :
    ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → t - s = 2 * u →
      F s + F t ≤ 2 * F ((s + t) / 2) :=
  Commons.Analysis.Convex.midpoint_double hu h

/-- **Local midpoint concavity implies concavity.**  See
`Commons.Analysis.Convex.concaveOn_Icc_of_local_midpoint`. -/
theorem concaveOn_Icc_of_local_midpoint {F : ℝ → ℝ} {T U : ℝ} (hT : 0 ≤ T) (hU : 0 < U)
    (hcont : ContinuousOn F (Set.Icc 0 T))
    (hloc : ∀ u ∈ Set.Ioc 0 U, ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      t - s = 2 * u → F s + F t ≤ 2 * F ((s + t) / 2)) :
    ConcaveOn ℝ (Set.Icc 0 T) F :=
  Commons.Analysis.Convex.concaveOn_Icc_of_local_midpoint hT hU hcont hloc

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Concavity of `d(p,·)` along a far minimising segment, unrestricted.**  If the minimising
geodesic `γ = geodCurve hmet T hT q ξ hξ` stays at distance `≥ π/2` from `p` and at distance `< π`
from `p`, then `t ↦ d(p, γ t)` is concave on `[0,T]`.

Compared with `GSConcaveSeg.concaveOn_dist_geodCurve` the hypothesis `T/2 + D ≤ π` is replaced by
the pointwise strict bound `< π`: the hinge comparison at the midpoint is used only for *small*
half-widths (where the hypothesis `a + d(p,m) ≤ π` is automatic), and the doubling argument
`concaveOn_Icc_of_local_midpoint` upgrades the local midpoint inequality to concavity. -/
theorem concaveOn_dist_geodCurve_of_lt_pi
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {T : ℝ} {q : M} {ξ : TangentSpace I q} (hξ : ‖ξ‖ = 1)
    (hT : 0 ≤ T)
    (hmin : Manifold.riemannianEDist I q
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) T) = ENNReal.ofReal T)
    (hcont : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) t)).toReal) (Set.Icc 0 T))
    (hfar : ∀ t ∈ Set.Icc (0:ℝ) T, Real.pi / 2 ≤ (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) t)).toReal)
    (hlt : ∀ t ∈ Set.Icc (0:ℝ) T, (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) t)).toReal < Real.pi) :
    ConcaveOn ℝ (Set.Icc (0:ℝ) T) (fun t : ℝ => (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) t)).toReal) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  set G : ℝ → M := geodCurve (cov := cov) hmet T hT q ξ hξ with hGdef
  have hsub : ∀ a ∈ Set.Icc (0:ℝ) T, ∀ b ∈ Set.Icc (0:ℝ) T, a ≤ b →
      Manifold.riemannianEDist I (G a) (G b) = ENNReal.ofReal (b - a) := by
    have h := geodCurve_sub_arc_minimising' (cov := cov) hmet (T := T) hT hξ (s := T) hT le_rfl hmin
    intro a ha b hb hab
    exact h a ha b hb hab
  obtain ⟨t₁, ht₁, ht₁max⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT) hcont
  have hFmax : (Manifold.riemannianEDist I p (G t₁)).toReal < Real.pi := hlt t₁ ht₁
  have hmax : ∀ y ∈ Set.Icc (0:ℝ) T,
      (Manifold.riemannianEDist I p (G y)).toReal ≤
        (Manifold.riemannianEDist I p (G t₁)).toReal := fun y hy => ht₁max hy
  have hU : 0 < (Real.pi - (Manifold.riemannianEDist I p (G t₁)).toReal) / 2 := by linarith
  refine concaveOn_Icc_of_local_midpoint hT hU hcont ?_
  intro u hu s t hs ht hst
  have hupos : 0 < u := hu.1
  have humem : u ≤ (Real.pi - (Manifold.riemannianEDist I p (G t₁)).toReal) / 2 := hu.2
  set m : ℝ := (s + t) / 2 with hmdef
  have hsu : s ≤ m := by rw [hmdef]; linarith
  have hmt' : m ≤ t := by rw [hmdef]; linarith
  have hms : m - s = u := by rw [hmdef]; linarith
  have hmt : t - m = u := by rw [hmdef]; linarith
  have hm0 : 0 ≤ m := le_trans hs.1 hsu
  have hmT : m ≤ T := le_trans hmt' ht.2
  have hmmem : m ∈ Set.Icc (0:ℝ) T := ⟨hm0, hmT⟩
  -- the velocity at `m`
  set vel : TangentSpace I (G m) := curveVelocity (I := I) G m with hveldef
  have hvel1 : ‖vel‖ = 1 := by
    rw [hveldef]
    exact norm_curveVelocity_geodCurve (cov := cov) hmet hT q ξ hξ hm0 hmT
  set ux : TangentSpace I (G m) := -vel with huxdef
  have hux1 : ‖ux‖ = 1 := by rw [huxdef, norm_neg, hvel1]
  have hback : GExp (cov := cov) hmet (G m) (u • ux) = G s := by
    have h := GExp_neg_curveVelocity_geodCurve (cov := cov) hmet hξ hT hm0 hmT hupos.le
      (by linarith [hms, hs.1] : u ≤ m)
    rw [show m - u = s from by linarith [hms]] at h
    simpa only [huxdef, hveldef] using h
  have hfwd : GExp (cov := cov) hmet (G m) (u • (-ux)) = G t := by
    have h := GExp_add_curveVelocity_geodCurve (cov := cov) hmet hξ hT hm0 hmT hupos.le
      (by linarith [hmt, ht.2] : m + u ≤ T)
    rw [show m + u = t from by linarith [hmt]] at h
    simpa only [huxdef, hveldef, neg_neg] using h
  -- Hopf–Rinow at `(G m, p)`
  obtain ⟨vp, hpG, hpd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor (G m) p
  set r : ℝ := ‖vp‖ with hrdef
  have hr_eq : Manifold.riemannianEDist I (G m) p = ENNReal.ofReal r := by
    rw [hrdef]; exact hpd
  have hrnn : 0 ≤ r := norm_nonneg vp
  have hrm : (Manifold.riemannianEDist I p (G m)).toReal = r := by
    rw [Manifold.riemannianEDist_comm, hr_eq, ENNReal.toReal_ofReal hrnn]
  have hrfar : Real.pi / 2 ≤ r := by rw [← hrm]; exact hfar m hmmem
  have hrpos : 0 < r := lt_of_lt_of_le (by linarith [Real.pi_pos]) hrfar
  have hrmax : r ≤ (Manifold.riemannianEDist I p (G t₁)).toReal := by
    rw [← hrm]; exact ht₁max hmmem
  have hur : u + r ≤ Real.pi := by linarith [humem, hrmax, hFmax]
  have hvpn : vp ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hrdef; rw [hrdef] at hrpos
    exact lt_irrefl 0 hrpos
  set up : TangentSpace I (G m) := unitOf vp hvpn with hupdef
  have hup1 : ‖up‖ = 1 := unitOf_norm vp hvpn
  have huup : r • up = vp := by
    rw [hupdef, hrdef, unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvpn), one_smul]
  have hpup : p = GExp (cov := cov) hmet (G m) (r • up) := by rw [huup]; exact hpG.symm
  have hga : Manifold.riemannianEDist I (G s) (G m) = ENNReal.ofReal u := by
    rw [hsub s hs m hmmem hsu, hms]
  have hgb : Manifold.riemannianEDist I (G m) (G t) = ENNReal.ofReal u := by
    rw [hsub m hmmem t ht hmt', hmt]
  have hminx : Manifold.riemannianEDist I (G m)
      (GExp (cov := cov) hmet (G m) (u • ux)) = ENNReal.ofReal u := by
    rw [hback, Manifold.riemannianEDist_comm, hga]
  have hminy : Manifold.riemannianEDist I (G m)
      (GExp (cov := cov) hmet (G m) (u • (-ux))) = ENNReal.ofReal u := by
    rw [hfwd, hgb]
  have hminp : Manifold.riemannianEDist I (G m)
      (GExp (cov := cov) hmet (G m) (r • up)) = ENNReal.ofReal r := by
    rw [← hpup]; exact hr_eq
  have hconc := Submission.GSConcave.edist_add_midpoint_le (cov := cov) hmet htor hpinch
    (m := G m) (p := p) (a := u) (r := r) (ux := ux) (up := up)
    hupos hrpos hur hrfar hux1 hup1 hminx hminy hminp
  rw [hback, hfwd, ← hpup] at hconc
  -- convert to real numbers
  have hfin1 : Manifold.riemannianEDist I p (G s) ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor p (G s)).ne
  have hfin2 : Manifold.riemannianEDist I p (G t) ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor p (G t)).ne
  have hsum : (Manifold.riemannianEDist I p (G s)).toReal
      + (Manifold.riemannianEDist I p (G t)).toReal ≤ 2 * r := by
    rw [Manifold.riemannianEDist_comm (I := I) (x := G s) (y := p),
      Manifold.riemannianEDist_comm (I := I) (x := G t) (y := p),
      (ENNReal.ofReal_toReal hfin1).symm, (ENNReal.ofReal_toReal hfin2).symm] at hconc
    rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg] at hconc
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by linarith : (0:ℝ) ≤ 2 * r)).mp hconc
    linarith
  have hmidpoint : (Manifold.riemannianEDist I p (G s)).toReal
      + (Manifold.riemannianEDist I p (G t)).toReal
      ≤ 2 * (Manifold.riemannianEDist I p (G ((s + t) / 2))).toReal := by
    have hm : (s + t) / 2 = m := by rw [hmdef]
    rw [hm, hrm]
    exact hsum
  exact hmidpoint


end

end Submission.GSConcaveGen
