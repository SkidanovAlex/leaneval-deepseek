import Submission.Work.RiemLib.JacobiTensor
import Submission.Work.RiemLib.CurvatureSym
import Submission.Work.RiemLib.IndexForm
import Submission.Work.RiemLib.ConjPoint
import Submission.Work.RiemLib.RauchCompare
import Submission.Work.RiemLib.Commons.Analysis.Calculus.le_of_deriv_mul_le_of_tendsto_div
import Submission.Work.RiemLib.Commons.Analysis.Calculus.tendsto_inv_smul_of_tendsto_deriv
import Submission.Work.RiemLib.Commons.Analysis.Normed.Operator.tendsto_inverse_of_tendsto_one
import Submission.Work.RiemLib.Commons.Analysis.ODE.riccati_le_cot
import Submission.Work.RiemLib.Commons.Analysis.Calculus.tendsto_cot_asymptotic_of_mul_tendsto_one
import Submission.Work.RiemLib.Gauss
import Submission.Work.RiemLib.Minimal
import Submission.Work.RiemLib.SecondVariation
import Submission.Work.RiemLib.SecondVar2
import Submission.Work.RiemLib.GeodesicExtend
import Submission.Work.RiemLib.Commons.Analysis.Calculus.hasDerivAt_deriv_partial_swap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The variation field of the geodesic flow is the Jacobi field

Let `Φ` be a two-parameter family of chart geodesics in the chart at `x₀`: for each `t`, the curve
`s ↦ Φ (s,t)` solves the chart geodesic equation in `E × E`, with `Φ (0,t) = (coords x₀, v + t • x)`
for small `t`.  Its *variation field*

`Y₀ s = ∂_t (Φ (s,t)).1 |_{t = 0}`

satisfies the chart Jacobi system with initial data `Y₀ 0 = 0`, `DY₀ 0 = x`; hence it coincides with
the column `D.Y · x` of the Jacobi tensor of `Submission/JacobiTensor.lean`.  Consequently

`(d exp_{x₀})_v (x) = frameVector x₀ (expMap x₀ v) ((D.Y 1) x)`,

the classical identification of the differential of the exponential map with Jacobi fields, which
is the missing link between `RauchUpper` (Rauch's comparison theorem, stated for the Jacobi tensor)
and the geometric comparison theorems (Toponogov, Hessian comparison, the chordal bound for `exp`).

## Main results

* `HasChartGeodesic.of_variation` : the chart geodesic attached to the family `Φ`;
* `variationField_eq_jacobiTensor` : the variation field is the Jacobi tensor column;
* `mfderiv_expMap_eq_jacobiTensor` : `(d exp_{x₀})_v x` is `D.Y 1 x`.

## Method

The key point is that the pair `(Y₀, DY₀)` solves the linear system `jacobiSys` of
`Submission/JacobiTensor.lean`.  The two ingredients are the *symmetry of second derivatives*
(applied to the two components of `Φ`: `∂_s∂_t = ∂_t∂_s`, which gives `Y₀' = Z₀` and computes
`Z₀'` by differentiating the geodesic equation in `t`), and the definition of the chart curvature
`chartCurv` (which is exactly the linearisation of the geodesic vector field).  Uniqueness of the
linear ODE (`Commons.Analysis.ODE.exists_linearODE_solution_Icc`) then identifies the pairs.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.JacobiTensor
open Submission.Rauch
open Submission.SecondVariation
open Submission.SecondVar2
open Commons.Analysis.ODE
open Commons.Analysis.Calculus

namespace Submission.FlowJacobi

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- The chart position of the family `Φ` at `t = 0`. -/
def gc (Φ : ℝ × ℝ → E × E) : ℝ → E := fun s => (Φ (s, 0)).1

/-- The chart velocity of the family `Φ` at `t = 0`. -/
def gv (Φ : ℝ × ℝ → E × E) : ℝ → E := fun s => (Φ (s, 0)).2

/-- The manifold point of the family `Φ` at `t = 0`. -/
def gp (x₀ : M) (Φ : ℝ × ℝ → E × E) : ℝ → M := fun s => (extChartAt I x₀).symm ((Φ (s, 0)).1)

@[simp] lemma gc_apply (Φ : ℝ × ℝ → E × E) (s : ℝ) : gc Φ s = (Φ (s, 0)).1 := rfl
@[simp] lemma gv_apply (Φ : ℝ × ℝ → E × E) (s : ℝ) : gv Φ s = (Φ (s, 0)).2 := rfl

/-- The curve `s ↦ (Φ (s,0))` is a chart geodesic with the data of the family. -/
theorem hasChartGeodesic_of_variation {x₀ : M} {v : E} {δ : ℝ} {Φ : ℝ × ℝ → E × E}
    (hδ : 0 < δ)
    (hΦ0 : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).1 = (extChartAt I x₀) x₀)
    (hΦv : (Φ (0, 0)).2 = v)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s) :
    HasChartGeodesic cov x₀ v (gc Φ) (gv Φ) := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (Φ (0, 0)).1 = (extChartAt I x₀) x₀
    exact hΦ0 0 h0
  · show (Φ (0, 0)).2 = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀ v
    rw [hΦv, continuousLinearMapAt_trivializationAt_self]
    rfl
  · intro t ht
    exact hTGT 0 h0 t ht
  · intro t ht
    exact (hODE 0 h0 t ht).fst
  · intro t ht
    exact (hODE 0 h0 t ht).snd


/-- The variation field of the family: the derivative of the first component in `t`. -/
def Yp (Φ : ℝ × ℝ → E × E) : ℝ → E := fun s => deriv (fun t : ℝ => (Φ (s, t)).1) 0

/-- The derivative of the velocity of the family in `t`. -/
def Zp (Φ : ℝ × ℝ → E × E) : ℝ → E := fun s => deriv (fun t : ℝ => (Φ (s, t)).2) 0

@[simp] lemma Yp_apply (Φ : ℝ × ℝ → E × E) (s : ℝ) :
    Yp Φ s = deriv (fun t : ℝ => (Φ (s, t)).1) 0 := rfl

@[simp] lemma Zp_apply (Φ : ℝ × ℝ → E × E) (s : ℝ) :
    Zp Φ s = deriv (fun t : ℝ => (Φ (s, t)).2) 0 := rfl

section Variation

variable {x₀ : M} {δ : ℝ} {Φ : ℝ × ℝ → E × E}

lemma tgt_eventually (hδ : 0 < δ)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2, (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (Φ (s, t)).1 ∈ (extChartAt I x₀).target := by
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)]
    with t ht
  exact hTGT t ht s hs

lemma hasDerivAt_variation (hδ : 0 < δ)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2, (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (Yp Φ) (Zp Φ s) s := by
  have hF1 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (Φ p).1) (s, 0) :=
    (ContinuousLinearMap.fst ℝ E E).contDiff.contDiffAt.comp (s, 0)
      ((hSM s hs).of_le (by decide))
  have h := hasDerivAt_deriv_partial_swap (F := fun p : ℝ × ℝ => (Φ p).1) hF1
  have hev : (fun t : ℝ => deriv (fun σ : ℝ => (Φ (σ, t)).1) s) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (Φ (s, t)).2) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)]
      with t ht
    exact (Submission.Gauss.hasDerivAt_fst (hODE t ht s hs)).deriv
  rw [hev.deriv_eq] at h
  exact h

lemma hasDerivAt_variation_vel (hδ : 0 < δ)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2, (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (Zp Φ) (deriv (fun t : ℝ => chartGeodesicVectorField cov x₀ (Φ (s, t))) 0) s := by
  have hF2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (Φ p).2) (s, 0) :=
    (ContinuousLinearMap.snd ℝ E E).contDiff.contDiffAt.comp (s, 0)
      ((hSM s hs).of_le (by decide))
  have h := hasDerivAt_deriv_partial_swap (F := fun p : ℝ × ℝ => (Φ p).2) hF2
  have hev : (fun t : ℝ => deriv (fun σ : ℝ => (Φ (σ, t)).2) s) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => chartGeodesicVectorField cov x₀ (Φ (s, t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)]
      with t ht
    exact (Submission.Gauss.hasDerivAt_snd (hODE t ht s hs)).deriv
  rw [hev.deriv_eq] at h
  exact h

/-- **The derivative of the geodesic vector field along the variation** — the linearised geodesic
equation. -/
lemma deriv_chartGeodesicVectorField (hδ : 0 < δ)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2, (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    deriv (fun t : ℝ => chartGeodesicVectorField cov x₀ (Φ (s, t))) 0
      = - (dB cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) (Yp Φ s) (gv Φ s) (gv Φ s)
            + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) (Zp Φ s) (gv Φ s)
            + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) (gv Φ s) (Zp Φ s)) := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hcomp : ContDiffAt ℝ ∞ (fun t : ℝ => Φ (s, t)) 0 :=
    (hSM s hs).comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hdt : DifferentiableAt ℝ (fun t : ℝ => Φ (s, t)) 0 := hcomp.differentiableAt (by norm_num)
  have hu : HasDerivAt (fun t : ℝ => (Φ (s, t)).1) (Yp Φ s) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (Φ (s, t)).1) (deriv (fun t : ℝ => (Φ (s, t)).1) 0) 0 :=
      hdt.fst.hasDerivAt
    exact h1
  have ha : HasDerivAt (fun t : ℝ => (Φ (s, t)).2) (Zp Φ s) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (Φ (s, t)).2) (deriv (fun t : ℝ => (Φ (s, t)).2) 0) 0 :=
      hdt.snd.hasDerivAt
    exact h1
  have htgt : (Φ (s, 0)).1 ∈ (extChartAt I x₀).target := hTGT 0 h0 s hs
  have hstay : ∀ᶠ t in 𝓝 (0 : ℝ), (Φ (s, t)).1 ∈ (extChartAt I x₀).target :=
    tgt_eventually (x₀ := x₀) hδ hTGT hs
  have hchr := hasDerivAt_chrB_curve (cov := cov) hu ha ha htgt hstay
  have hfun : (fun t : ℝ => chartGeodesicVectorField cov x₀ (Φ (s, t)))
      = (fun t : ℝ => - chrB cov x₀ ((extChartAt I x₀).symm ((Φ (s, t)).1)) ((Φ (s, t)).2)
          ((Φ (s, t)).2)) := by
    funext t; rfl
  rw [hfun]
  exact hchr.neg.deriv

end Variation


/-- The chart curvature, written in the form produced by the linearised geodesic equation. -/
lemma chartCurv_eq_linForm (htor : cov.torsion = 0) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) (X Y : E) :
    chartCurv cov x₀ p X Y
      = dB cov x₀ p X Y Y - dB cov x₀ p Y X Y
        + chrB cov x₀ p X (chrB cov x₀ p Y Y) - chrB cov x₀ p (chrB cov x₀ p X Y) Y := by
  have h1 : dB cov x₀ p Y Y X = dB cov x₀ p Y X Y := dB_comm_snd (cov := cov) htor hp Y Y X
  have h2 : chrB cov x₀ p (chrB cov x₀ p Y Y) X = chrB cov x₀ p X (chrB cov x₀ p Y Y) :=
    chrB_comm (cov := cov) htor hp (chrB cov x₀ p Y Y) X
  have h3 : chrB cov x₀ p Y X = chrB cov x₀ p X Y := chrB_comm (cov := cov) htor hp Y X
  rw [chartCurv, h1, h2, h3]

/-- **The algebraic content of the linearised geodesic equation**: the derivative of the gradient
of the geodesic energy along a variation is the (negative of the) chart curvature term of the
Jacobi equation. -/
lemma linearization_identity (htor : cov.torsion = 0) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) (X X' Z : E) :
    (-(dB cov x₀ p X Z Z + chrB cov x₀ p X' Z + chrB cov x₀ p Z X')
      + (dB cov x₀ p Z X Z + chrB cov x₀ p X' Z + chrB cov x₀ p X (- chrB cov x₀ p Z Z)))
      = - chrB cov x₀ p (X' + chrB cov x₀ p X Z) Z - chartCurv cov x₀ p X Z := by
  have hlin := chartCurv_eq_linForm (cov := cov) htor x₀ hp X Z
  rw [hlin]
  have hcomm : chrB cov x₀ p Z X' = chrB cov x₀ p X' Z := chrB_comm (cov := cov) htor hp Z X'
  have hneg : (- chrB cov x₀ p Z Z) = (-1 : ℝ) • chrB cov x₀ p Z Z := (neg_one_smul ℝ _).symm
  have hadd := chrB_add_fst (cov := cov) x₀ p X' (chrB cov x₀ p X Z) Z hp
  rw [hcomm, hneg, chrB_smul_snd, neg_one_smul, hadd]
  abel

/-- The first-order Jacobi system in *vector* form: the linearised geodesic equation on the pair
(field, covariant derivative). -/
noncomputable def jacobiSysVec (x₀ : M) (u w : ℝ → E) (t : ℝ) : (E × E) →L[ℝ] (E × E) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.snd ℝ E E - (gammaOp (cov := cov) x₀ u w t).comp
      (ContinuousLinearMap.fst ℝ E E))
    (-((gammaOp (cov := cov) x₀ u w t).comp (ContinuousLinearMap.snd ℝ E E))
      - (curvOp (cov := cov) x₀ u w t).comp (ContinuousLinearMap.fst ℝ E E))

lemma jacobiSysVec_apply (x₀ : M) (u w : ℝ → E) (t : ℝ) (y z : E) :
    jacobiSysVec (cov := cov) x₀ u w t (y, z)
      = (z - gammaOp (cov := cov) x₀ u w t y,
          -gammaOp (cov := cov) x₀ u w t z - curvOp (cov := cov) x₀ u w t y) := by
  unfold jacobiSysVec
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply]
  rfl

lemma norm_jacobiSysVec_le (x₀ : M) (u w : ℝ → E) (t : ℝ) (y z : E) :
    ‖jacobiSysVec (cov := cov) x₀ u w t (y, z)‖
      ≤ (1 + 2 * ‖gammaOp (cov := cov) x₀ u w t‖ + ‖curvOp (cov := cov) x₀ u w t‖)
          * ‖(y, z)‖ := by
  rw [jacobiSysVec_apply]
  have hG := (gammaOp (cov := cov) x₀ u w t).le_opNorm y
  have hGz := (gammaOp (cov := cov) x₀ u w t).le_opNorm z
  have hR := (curvOp (cov := cov) x₀ u w t).le_opNorm y
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖z - gammaOp (cov := cov) x₀ u w t y‖
        ≤ ‖z‖ + ‖gammaOp (cov := cov) x₀ u w t y‖ := norm_sub_le _ _
      _ ≤ ‖z‖ + ‖gammaOp (cov := cov) x₀ u w t‖ * ‖y‖ := by linarith
      _ ≤ (1 + 2 * ‖gammaOp (cov := cov) x₀ u w t‖ + ‖curvOp (cov := cov) x₀ u w t‖)
            * max ‖y‖ ‖z‖ := by
          have h1 : ‖y‖ ≤ max ‖y‖ ‖z‖ := le_max_left _ _
          have h2 : ‖z‖ ≤ max ‖y‖ ‖z‖ := le_max_right _ _
          have h0 : 0 ≤ max ‖y‖ ‖z‖ := le_trans (norm_nonneg y) h1
          have hgn : 0 ≤ ‖gammaOp (cov := cov) x₀ u w t‖ := norm_nonneg _
          have hrn : 0 ≤ ‖curvOp (cov := cov) x₀ u w t‖ := norm_nonneg _
          nlinarith [norm_nonneg z, norm_nonneg y]
  · calc ‖-gammaOp (cov := cov) x₀ u w t z - curvOp (cov := cov) x₀ u w t y‖
        ≤ ‖-gammaOp (cov := cov) x₀ u w t z‖ + ‖curvOp (cov := cov) x₀ u w t y‖ :=
          norm_sub_le _ _
      _ = ‖gammaOp (cov := cov) x₀ u w t z‖ + ‖curvOp (cov := cov) x₀ u w t y‖ := by
          rw [norm_neg]
      _ ≤ ‖gammaOp (cov := cov) x₀ u w t‖ * ‖z‖
            + ‖curvOp (cov := cov) x₀ u w t‖ * ‖y‖ := by linarith
      _ ≤ (1 + 2 * ‖gammaOp (cov := cov) x₀ u w t‖ + ‖curvOp (cov := cov) x₀ u w t‖)
            * max ‖y‖ ‖z‖ := by
          have h1 : ‖y‖ ≤ max ‖y‖ ‖z‖ := le_max_left _ _
          have h2 : ‖z‖ ≤ max ‖y‖ ‖z‖ := le_max_right _ _
          have h0 : 0 ≤ max ‖y‖ ‖z‖ := le_trans (norm_nonneg y) h1
          have hgn : 0 ≤ ‖gammaOp (cov := cov) x₀ u w t‖ := norm_nonneg _
          have hrn : 0 ≤ ‖curvOp (cov := cov) x₀ u w t‖ := norm_nonneg _
          nlinarith [norm_nonneg z, norm_nonneg y]

/-- **The variation field of the geodesic flow is the Jacobi field.**  The `t`-derivative at
`t = 0` of the first component of the two-parameter family solves the Jacobi system with initial
data `(0, x)`, hence agrees with the column `D.Y · x` of any Jacobi tensor with `Y 0 = 0`,
`U 0 = 1`. -/
theorem variationField_eq_jacobiTensor (htor : cov.torsion = 0)
    {x₀ : M} {v x : E} {δ : ℝ} {Φ : ℝ × ℝ → E × E}
    (hδ : 0 < δ)
    (hΦ0 : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).1 = (extChartAt I x₀) x₀)
    (hΦv : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).2 = v + t • x)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2, (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hU : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt U (-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
        - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) :
    ∀ s ∈ Icc (-1 : ℝ) 1, deriv (fun t : ℝ => (Φ (s, t)).1) 0 = (Y s) x := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hgc : HasChartGeodesic cov x₀ v (gc Φ) (gv Φ) :=
    hasChartGeodesic_of_variation (cov := cov) hδ hΦ0 (by
      have := hΦv 0 h0; simpa using this) hTGT hODE
  -- a bound on the coefficient on `[-1, 1]`
  have hsub : Icc (-1 : ℝ) 1 ⊆ Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hwcont : ContinuousOn (gv Φ) (Icc (-1 : ℝ) 1) :=
    HasDerivAt.continuousOn fun t ht => hgc.2.2.2.2 t (hsub ht)
  have hGon : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t) (Icc (-1 : ℝ) 1) :=
    (continuousOn_gammaOp (cov := cov) htor hgc).mono hsub
  have hRon : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t) (Icc (-1 : ℝ) 1) :=
    continuousOn_curvOp (cov := cov)
      (HasDerivAt.continuousOn fun t ht => hgc.2.2.2.1 t (hsub ht)) hwcont
      (fun t ht => hgc.2.2.1 t (hsub ht))
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn hGon
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn hRon
  have hbound : ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t‖
        ≤ max 0 (1 + 2 * C1 + C2) := by
    intro t ht
    have h6 : ‖jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t‖
        ≤ 1 + 2 * ‖gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t‖
          + ‖curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t‖ := by
      refine _root_.ContinuousLinearMap.opNorm_le_bound _
        (by positivity) fun p => ?_
      obtain ⟨y, z⟩ := p
      exact norm_jacobiSysVec_le (cov := cov) x₀ (gc Φ) (gv Φ) t y z
    have h4 : ‖gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t‖ ≤ C1 := hC1 t ht
    have h5 : ‖curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t‖ ≤ C2 := hC2 t ht
    refine le_trans h6 (le_trans (by linarith) (le_max_right _ _))
  -- the second-order pair attached to the variation
  set Ufun : ℝ → E := fun r => Zp Φ r
    + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) (Yp Φ r) (gv Φ r) with hUfun
  have hpair2 : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun r : ℝ => (Yp Φ r, Ufun r))
        (jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t, Ufun t)) t := by
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 := hsub ht
    have hsrc : (extChartAt I x₀).symm ((Φ (t, 0)).1) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (x₀ := x₀) (u := fun _ => (Φ (t, 0)).1) (t := 0)
        (hTGT 0 h0 t ht2)
    have hu : HasDerivAt (gc Φ) (gv Φ t) t := Submission.Gauss.hasDerivAt_fst (hODE 0 h0 t ht2)
    have hw : HasDerivAt (gv Φ) (chartGeodesicVectorField cov x₀ (Φ (t, 0))) t :=
      Submission.Gauss.hasDerivAt_snd (hODE 0 h0 t ht2)
    have hGCtarget : gc Φ t ∈ (extChartAt I x₀).target := hgc.2.2.1 t ht2
    have hGCtarget_ev : ∀ᶠ r in 𝓝 t, gc Φ r ∈ (extChartAt I x₀).target := by
      filter_upwards [isOpen_Ioo.mem_nhds ht2] with r hr
      exact hgc.2.2.1 r hr
    have hy : HasDerivAt (Yp Φ) (Zp Φ t) t :=
      hasDerivAt_variation (cov := cov) hδ hTGT hODE hSM ht2
    have hz := hasDerivAt_variation_vel (cov := cov) hδ hTGT hODE hSM ht2
    have hzval := deriv_chartGeodesicVectorField (cov := cov) hδ hTGT hODE hSM ht2
    have hchr : HasDerivAt
        (fun r : ℝ => chrB cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) (Yp Φ r) (gv Φ r))
        (dB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (Yp Φ t) (gv Φ t)
          + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Zp Φ t) (gv Φ t)
          + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t)
              (chartGeodesicVectorField cov x₀ (Φ (t, 0)))) t :=
      hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (u := gc Φ) (a := Yp Φ) (b := gv Φ)
        (v := gv Φ t) (a' := Zp Φ t) (b' := chartGeodesicVectorField cov x₀ (Φ (t, 0)))
        hu hy hw hGCtarget hGCtarget_ev
    have hUderiv : HasDerivAt Ufun
        (deriv (fun r : ℝ => chartGeodesicVectorField cov x₀ (Φ (t, r))) 0
          + (dB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (Yp Φ t) (gv Φ t)
            + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Zp Φ t) (gv Φ t)
            + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t)
                (chartGeodesicVectorField cov x₀ (Φ (t, 0))))) t := by
      have h := hz.add hchr
      rw [hUfun]
      exact h
    have hgam : gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t)
        = chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t) (gv Φ t) :=
      gammaOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc (Yp Φ t)
    have hgamU : gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Ufun t)
        = chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Ufun t) (gv Φ t) :=
      gammaOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc (Ufun t)
    have hcurv : curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t)
        = chartCurv cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t) (gv Φ t) :=
      curvOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc (Yp Φ t)
    have hbase := hy.prodMk hUderiv
    rw [jacobiSysVec_apply]
    refine hbase.congr_deriv ?_
    refine Prod.ext ?_ ?_
    · simp only [hgam, hUfun]
      abel
    · have hgv : chartGeodesicVectorField cov x₀ (Φ (t, 0))
          = - chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (gv Φ t) := rfl
      have hid := linearization_identity (cov := cov) htor x₀ hsrc (Yp Φ t) (Zp Φ t) (gv Φ t)
      rw [hzval, hgamU, hcurv, hgv, hUfun, hid]
  -- initial data
  have hYp0 : Yp Φ 0 = 0 := by
    have hev : (fun r : ℝ => (Φ (0, r)).1) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (extChartAt I x₀) x₀) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0) hΦ0
    rw [Yp_apply, hev.deriv_eq, deriv_const]
  have hZp0 : Zp Φ 0 = x := by
    have hev : (fun r : ℝ => (Φ (0, r)).2) =ᶠ[𝓝 (0 : ℝ)] (fun r => v + r • x) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0) hΦv
    rw [Zp_apply, hev.deriv_eq]
    have hd : HasDerivAt (fun r : ℝ => v + r • x) x 0 := by
      have h1 : HasDerivAt (fun r : ℝ => v + r • x) ((0 : E) + (1 : ℝ) • x) 0 :=
        (hasDerivAt_const (x := (0 : ℝ)) (c := v)).add ((hasDerivAt_id (0 : ℝ)).smul_const x)
      rw [zero_add, one_smul] at h1
      exact h1
    exact hd.deriv
  have hUfun0 : Ufun 0 = x := by
    simp only [hUfun, hYp0, hZp0, map_zero, chrB_zero_fst, add_zero]
  -- the columns of the Jacobi tensor
  have hpair1 : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun r : ℝ => ((Y r) x, (U r) x))
        (jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t ((Y t) x, (U t) x)) t := by
    intro t ht
    have h1 : HasDerivAt (fun r : ℝ => (Y r) x)
        ((U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) x + (Y t) 0) t :=
      (hY t ht).clm_apply (hasDerivAt_const (x := t) x)
    have h1' : HasDerivAt (fun r : ℝ => (Y r) x)
        ((U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) x) t := by
      simpa using h1
    have h2 : HasDerivAt (fun r : ℝ => (U r) x)
        ((-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
          - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) x + (U t) 0) t :=
      (hU t ht).clm_apply (hasDerivAt_const (x := t) x)
    have h2' : HasDerivAt (fun r : ℝ => (U r) x)
        ((-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
          - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) x) t := by
      simpa using h2
    have hbase := h1'.prodMk h2'
    rw [jacobiSysVec_apply]
    refine hbase.congr_deriv ?_
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply]
  have hinit : (Yp Φ 0, Ufun 0) = ((Y 0) x, (U 0) x) := by
    have h1 : (Y 0) x = (0 : E) := by rw [hY0]; simp
    have h2 : (U 0) x = x := by rw [hU0]; simp
    rw [hYp0, hUfun0, h1, h2]
  -- uniqueness of the linear ODE on `[-1, 1]`
  have huniq := eqOn_of_hasDerivAt_linearODE (A := jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ))
    (M := ⟨max 0 (1 + 2 * C1 + C2), le_max_left _ _⟩) hbound
    (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1) hpair2 hpair1 hinit
  intro s hs
  have hfin : (Yp Φ s, Ufun s) = ((Y s) x, (U s) x) := huniq hs
  exact (Prod.ext_iff.mp hfin).1

/-- **The differential of the exponential map is given by Jacobi fields.**  For the two-parameter
family of geodesics with initial velocities `v + t x`, the differential of `exp` at `v` in the
direction `x` is the value at time `1` of the column of the Jacobi tensor in the direction `x`. -/
theorem mfderiv_expMap_eq_jacobiTensor (htor : cov.torsion = 0)
    {x₀ : M} {v x : E} {δ : ℝ} {Φ : ℝ × ℝ → E × E}
    (hδ : 0 < δ)
    (hΦ0 : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).1 = (extChartAt I x₀) x₀)
    (hΦv : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).2 = v + t • x)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2, (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    (hEXP : ∀ s : ℝ, |s| ≤ 1 → ∀ t ∈ Ioo (-δ) δ,
      expMap cov x₀ (s • (v + t • x)) = (extChartAt I x₀).symm ((Φ (s, t)).1))
    (hvsm : MDifferentiableAt 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) v)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hU : ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt U (-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
        - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) :
    (mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) v) x
      = frameVector (I := I) x₀ (expMap cov x₀ v) ((Y 1) x) := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hs1 : (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hYval : deriv (fun t : ℝ => (Φ (1, t)).1) 0 = (Y 1) x :=
    variationField_eq_jacobiTensor (cov := cov) htor hδ hΦ0 hΦv hTGT hODE hSM hY hU hY0 hU0 1 h1
  -- the exponential curve agrees with the chart curve near `0`
  have hγeq : (fun r : ℝ => expMap cov x₀ (v + r • x))
      =ᶠ[𝓝 (0 : ℝ)] (fun r => (extChartAt I x₀).symm ((Φ (1, r)).1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with r hr
    have hh := hEXP 1 (by norm_num) r hr
    simpa using hh
  -- the derivative of the straight curve in the tangent space
  have hσ : HasDerivAt (fun r : ℝ => v + r • x) x 0 := by
    have h2 : HasDerivAt (fun r : ℝ => v + r • x) ((0 : E) + (1 : ℝ) • x) 0 :=
      (hasDerivAt_const (x := (0 : ℝ)) (c := v)).add ((hasDerivAt_id (0 : ℝ)).smul_const x)
    rw [zero_add, one_smul] at h2
    exact h2
  have hvsm' : MDifferentiableAt 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) (v + (0 : ℝ) • x) := by
    simpa using hvsm
  have hvel : curveVelocity (I := I) (fun r : ℝ => expMap cov x₀ (v + r • x)) 0
      = (mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) v) x := by
    have h := Submission.Minimal.curveVelocity_eq_exp_deriv (cov := cov) (x₀ := x₀)
      (σ := fun r : ℝ => v + r • x) (σ' := fun _ => x) (γ := fun r => expMap cov x₀ (v + r • x))
      (t := 0) hσ hvsm' (Filter.EventuallyEq.refl _ _)
    refine h.trans ?_
    rw [zero_smul, add_zero]
  -- the chart curve
  have htgt : (Φ (1, 0)).1 ∈ (extChartAt I x₀).target := hTGT 0 h0 1 hs1
  have hstay : ∀ᶠ r in 𝓝 (0 : ℝ), (Φ (1, r)).1 ∈ (extChartAt I x₀).target :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0) (fun r hr => hTGT r hr 1 hs1)
  have hdiff : DifferentiableAt ℝ (fun r : ℝ => (Φ (1, r)).1) 0 := by
    have hc : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (Φ p).1) (1, 0) :=
      (ContinuousLinearMap.fst ℝ E E).contDiff.contDiffAt.comp (1, 0)
        ((hSM 1 hs1).of_le (by decide))
    have hcomp : ContDiffAt ℝ ∞ (fun r : ℝ => (Φ (1, r)).1) 0 :=
      hc.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
    exact hcomp.differentiableAt (by norm_num)
  have hu : HasDerivAt (fun r : ℝ => (Φ (1, r)).1) ((Y 1) x) 0 := by
    have h := hdiff.hasDerivAt
    rw [hYval] at h
    exact h
  have hchartvel := curveVelocity_chartCurve (I := I) (x₀ := x₀)
    (u := fun r : ℝ => (Φ (1, r)).1) (v := (Y 1) x) (t := 0) hu htgt hstay
  have hpoint : expMap cov x₀ v = (extChartAt I x₀).symm ((Φ (1, 0)).1) := by
    have hh := hEXP 1 (by norm_num) 0 h0
    simpa using hh
  calc (mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) v) x
      = curveVelocity (I := I) (fun r : ℝ => expMap cov x₀ (v + r • x)) 0 := hvel.symm
    _ = curveVelocity (I := I) (fun r : ℝ => (extChartAt I x₀).symm ((Φ (1, r)).1)) 0 :=
        Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hγeq
    _ = frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (1, 0)).1)) ((Y 1) x) := hchartvel
    _ = frameVector (I := I) x₀ (expMap cov x₀ v) ((Y 1) x) := by rw [hpoint]

/-- **Existence form**: the differential of the exponential map at `v` in the direction `x` is the
value at time `1` of the column `D.Y · x` of the Jacobi tensor along the chart geodesic with
initial velocity `v`. -/
theorem exists_expMap_mfderiv_eq_jacobiTensor (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, ‖v‖ < ρ → ∀ x : E,
      ∃ (u w : ℝ → E) (Y U : ℝ → E →L[ℝ] E),
        HasChartGeodesic cov x₀ v u w ∧
        (∀ s : ℝ, |s| ≤ 1 → expMap cov x₀ (s • v) = (extChartAt I x₀).symm (u s)) ∧
        Y 0 = 0 ∧ U 0 = 1 ∧
        (∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
          HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) ∧
        (∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
          HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
            - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) ∧
        (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x
          = frameVector (I := I) x₀ (expMap cov x₀ v) ((Y 1) x) := by
  obtain ⟨ρ₁, hρ₁, hvar⟩ := Submission.Gauss.exists_geodesicVariation (cov := cov) x₀
  obtain ⟨ρ₂, hρ₂, hsm⟩ := exists_radius_contMDiffAt_expMap (cov := cov) x₀
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun v hv x => ?_⟩
  have hv1 : ‖v‖ < ρ₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v‖ < ρ₂ := lt_of_lt_of_le hv (min_le_right _ _)
  obtain ⟨δ, Φ, hδ, hP0, hPv, hODE, hTGT, hSM, hEXP⟩ := hvar v hv1 x
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hgc : HasChartGeodesic cov x₀ v (gc Φ) (gv Φ) :=
    hasChartGeodesic_of_variation (cov := cov) hδ hP0 (by
      have := hPv 0 h0; simpa using this) hTGT hODE
  obtain ⟨Y, U, hY0, hU0, hY, hU⟩ :=
    exists_jacobiSystem (cov := cov) htor hgc (by norm_num : (-(3/2) : ℝ) < 3/2)
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (by norm_num : (0 : ℝ) ∈ Icc (-(3/2) : ℝ) (3/2))
  refine ⟨gc Φ, gv Φ, Y, U, hgc, ?_, hY0, hU0, hY, hU, ?_⟩
  · intro s hs
    have hh := hEXP s hs 0 h0
    simpa using hh
  · exact mfderiv_expMap_eq_jacobiTensor (cov := cov) htor hδ hP0 hPv hTGT hODE hSM hEXP
      ((hsm v hv2).mdifferentiableAt (by simp))
      (fun t ht => hY t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (fun t ht => hU t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hY0 hU0

end

end Submission.FlowJacobi
