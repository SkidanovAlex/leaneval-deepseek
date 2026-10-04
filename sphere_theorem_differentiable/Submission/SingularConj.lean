import Submission.ConjCut
import Submission.RayJacobi
import Submission.RayChart
import Submission.GExpLocalInj

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.RauchGlobal
open Submission.GeodesicExtend
open Submission.ChartConnection
open Submission.RayJacobi
open Submission.RayChart
open Submission.GExpLocalInj

namespace Submission.SingularConj

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

/-! ## 1. The derivative of the chart model of `exp_p` at the origin -/

/-- **`d(extChartAt I p ∘ GExp p)_0 = id`**: the chart model of the exponential map has the identity
as its Fréchet derivative at the origin. -/
theorem fderiv_chartGExp_zero (hmet : IsMetricCompatible cov) (p : M) :
    fderiv ℝ (fun v : E => (extChartAt I p)
      (GExp (cov := cov) hmet p (show TangentSpace I p from v))) (0:E)
      = ContinuousLinearMap.id ℝ E := by
  have hg0 : (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)) (0:E) = p := by
    simpa using GlobalExp.GExp_zero (cov := cov) hmet p
  have hpsrc : (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)) (0:E)
      ∈ (chartAt H p).source := by
    rw [hg0]; exact mem_chart_source H p
  have h1 : MDifferentiableAt 𝓘(ℝ, E) I
      (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)) (0:E) :=
    (contMDiffAt_GExp_one (cov := cov) hmet p (0:E)).mdifferentiableAt one_ne_zero
  have h2 : MDifferentiableAt I 𝓘(ℝ, E) (↑(extChartAt I p) : M → E)
      ((fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)) (0:E)) :=
    mdifferentiableAt_extChartAt (I := I) (x := p)
      (y := (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)) (0:E)) hpsrc
  have hmf0 : mfderiv 𝓘(ℝ, E) I
      (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)) (0:E)
      = ContinuousLinearMap.id ℝ E :=
    mfderiv_GExp_zero (cov := cov) hmet p
  have h3 := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E))
    (f := fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v))
    (g := (↑(extChartAt I p) : M → E)) (0:E) h2 h1
  have h2' : mfderiv I 𝓘(ℝ, E) (↑(extChartAt I p) : M → E)
      ((fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)) (0:E))
      = ContinuousLinearMap.id ℝ E := by
    rw [hg0]; exact mfderiv_extChartAt_self
  have h4 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (((↑(extChartAt I p) : M → E)) ∘
      (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v))) (0:E)
      = ContinuousLinearMap.id ℝ E := by
    rw [h3, h2', hmf0]
    ext x
    rfl
  have hcomp : ((↑(extChartAt I p) : M → E) ∘
      (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)))
      = (fun v : E => (extChartAt I p)
        (GExp (cov := cov) hmet p (show TangentSpace I p from v))) := rfl
  rw [← hcomp]
  have h5 := h4
  simp only [mfderiv_eq_fderiv] at h5
  first | exact h5 | (ext v; exact congrArg (fun T => T v) h5) | (convert h5 using 1) | simpa using h5

/-! ## 2. An operator close to the identity is injective -/

/-- A continuous linear operator within operator-norm distance `1/2` of the identity is injective. -/
theorem eq_zero_of_norm_sub_id_lt {A : E →L[ℝ] E}
    (h : ‖A - ContinuousLinearMap.id ℝ E‖ < 1/2) {y : E} (hy : A y = 0) : y = 0 := by
  have hb : ‖(ContinuousLinearMap.id ℝ E - A) y‖ ≤ (1/2) * ‖y‖ := by
    have h1 := (ContinuousLinearMap.id ℝ E - A).le_opNorm y
    have hnorm : ‖ContinuousLinearMap.id ℝ E - A‖ = ‖A - ContinuousLinearMap.id ℝ E‖ := by
      rw [show (ContinuousLinearMap.id ℝ E - A) = -(A - ContinuousLinearMap.id ℝ E) from by
        abel, norm_neg]
    rw [hnorm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h.le (norm_nonneg y))
  have htri : ‖y‖ ≤ ‖A y‖ + ‖(ContinuousLinearMap.id ℝ E - A) y‖ := by
    have h2 := norm_add_le (A y) ((ContinuousLinearMap.id ℝ E - A) y)
    have heq : A y + (ContinuousLinearMap.id ℝ E - A) y = y := by
      rw [sub_apply, ContinuousLinearMap.id_apply]; abel
    rwa [heq] at h2
  rw [hy, norm_zero, zero_add] at htri
  have hz : ‖y‖ = 0 := by linarith [norm_nonneg y]
  exact norm_eq_zero.mp hz

/-! ## 3. The chart model of `exp_p` is injective on a ball -/

/-- **`fderiv (extChartAt I p ∘ GExp p)` is injective near the origin**: the quantitative form of
`d exp_0 = id`. -/
theorem exists_pos_fderiv_chartGExp_injective (hmet : IsMetricCompatible cov) (p : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : E, ‖w‖ < δ →
      Function.Injective (fderiv ℝ (fun v : E => (extChartAt I p)
        (GExp (cov := cov) hmet p (show TangentSpace I p from v))) w) := by
  have hpsrc : GExp (cov := cov) hmet p (0 : TangentSpace I p) ∈ (chartAt H p).source := by
    rw [GlobalExp.GExp_zero]; exact mem_chart_source H p
  have hcc : ContDiffAt ℝ 1 (fun v : E => (extChartAt I p)
      (GExp (cov := cov) hmet p (show TangentSpace I p from v))) (0:E) := by
    have h1 : ContMDiffAt 𝓘(ℝ, E) I 1
        (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)) (0:E) :=
      contMDiffAt_GExp_one (cov := cov) hmet p (0:E)
    have h2 : ContMDiffAt I 𝓘(ℝ, E) 1 (fun q : M => (extChartAt I p) q)
        (GExp (cov := cov) hmet p (0 : TangentSpace I p)) :=
      contMDiffAt_extChartAt' (I := I) (n := 1) (x := p)
        (x' := GExp (cov := cov) hmet p (0 : TangentSpace I p)) hpsrc
    exact (contMDiffAt_iff_contDiffAt).mp (h2.comp (0:E) h1)
  have hcont : ContinuousAt (fderiv ℝ (fun v : E => (extChartAt I p)
      (GExp (cov := cov) hmet p (show TangentSpace I p from v)))) (0:E) :=
    hcc.continuousAt_fderiv one_ne_zero
  have hderiv0 := fderiv_chartGExp_zero (cov := cov) hmet p
  have h5 : ∀ᶠ w : E in 𝓝 (0:E),
      ‖fderiv ℝ (fun v : E => (extChartAt I p)
        (GExp (cov := cov) hmet p (show TangentSpace I p from v))) w
        - ContinuousLinearMap.id ℝ E‖ < 1/2 := by
    have h1 : Tendsto (fderiv ℝ (fun v : E => (extChartAt I p)
        (GExp (cov := cov) hmet p (show TangentSpace I p from v))))
        (𝓝 (0:E)) (𝓝 (ContinuousLinearMap.id ℝ E)) := by
      simpa only [ContinuousAt, hderiv0] using hcont
    have h2 : Tendsto (fun w : E => fderiv ℝ (fun v : E => (extChartAt I p)
        (GExp (cov := cov) hmet p (show TangentSpace I p from v))) w
        - ContinuousLinearMap.id ℝ E) (𝓝 (0:E)) (𝓝 0) := by
      have hh := h1.sub_const (ContinuousLinearMap.id ℝ E)
      simpa using hh
    have h3 : Tendsto (fun w : E => ‖fderiv ℝ (fun v : E => (extChartAt I p)
        (GExp (cov := cov) hmet p (show TangentSpace I p from v))) w
        - ContinuousLinearMap.id ℝ E‖) (𝓝 (0:E)) (𝓝 0) := by
      simpa using h2.norm
    exact h3.eventually (isOpen_Iio.mem_nhds (by norm_num : (0:ℝ) < 1/2))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp h5
  refine ⟨δ, hδ, fun w hw a b hab => ?_⟩
  have hlt : ‖fderiv ℝ (fun v : E => (extChartAt I p)
      (GExp (cov := cov) hmet p (show TangentSpace I p from v))) w
      - ContinuousLinearMap.id ℝ E‖ < 1/2 := hδsub (by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact hw)
  have hzero : fderiv ℝ (fun v : E => (extChartAt I p)
      (GExp (cov := cov) hmet p (show TangentSpace I p from v))) w (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_norm_sub_id_lt hlt hzero)

/-! ## 4. The model derivative of the variation field -/

/-- **The chart model of `J σ` is `fderiv (extChartAt I p ∘ GExp p) (σ•u) (σ•η)`.**  If the variation
field `J σ` — the `r`-derivative at `0` of `r ↦ GExp p (σ • (u + r • η))` — vanishes, then so does
the model derivative.  This is the chain rule together with the linearity of the chart differential:
the chart `extChartAt I p` is a chart, so its differential is *linear*, hence sends `0` to `0`. -/
theorem model_deriv_of_variation (hmet : IsMetricCompatible cov) (p : M)
    {u η : TangentSpace I p} {σ : ℝ}
    (hmem : GExp (cov := cov) hmet p (σ • u) ∈ (chartAt H p).source)
    (hzero : curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet p (σ • (u + r • η))) 0 = 0) :
    fderiv ℝ (fun v : E => (extChartAt I p)
      (GExp (cov := cov) hmet p (show TangentSpace I p from v)))
      (show E from (σ • u)) (show E from (σ • η)) = 0 := by
  have hmf : mfderiv 𝓘(ℝ, E) I
      (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
      (show E from (σ • u)) (show E from (σ • η)) = 0 := by
    have h1 : HasDerivAt (fun r : ℝ => u + r • η) η (0:ℝ) := by
      have h := (hasDerivAt_id (0:ℝ)).smul_const η
      simpa using h.const_add u
    have hder : HasDerivAt (fun r : ℝ => σ • (u + r • η)) (σ • η) (0:ℝ) :=
      h1.const_smul σ
    have hmd : MDifferentiableAt 𝓘(ℝ, E) I
        (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
        (σ • (u + (0:ℝ) • η)) :=
      (contMDiffAt_GExp_one (cov := cov) hmet p (σ • (u + (0:ℝ) • η))).mdifferentiableAt
        one_ne_zero
    have hchain := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp (I := I)
      (f := fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
      (σ := fun r : ℝ => σ • (u + r • η)) (σ' := fun _ : ℝ => (show E from (σ • η)))
      (γ := fun r : ℝ => GExp (cov := cov) hmet p (σ • (u + r • η))) hder hmd
      (Filter.Eventually.of_forall (fun r => rfl))
    have hmain : (mfderiv 𝓘(ℝ, E) I
        (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
        (σ • (u + (0:ℝ) • η))) (show E from (σ • η)) = 0 := by
      rw [← hchain]
      exact hzero
    have hpt : σ • (u + (0:ℝ) • η) = (show E from (σ • u)) := by
      rw [zero_smul, add_zero]
    rw [hpt] at hmain
    exact hmain
  have h1 : MDifferentiableAt 𝓘(ℝ, E) I
      (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v))
      (show E from (σ • u)) :=
    (contMDiffAt_GExp_one (cov := cov) hmet p (σ • u)).mdifferentiableAt one_ne_zero
  have h2 : MDifferentiableAt I 𝓘(ℝ, E) (↑(extChartAt I p) : M → E)
      ((fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v))
        (show E from (σ • u))) :=
    mdifferentiableAt_extChartAt (I := I) (x := p)
      (y := (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v))
        (show E from (σ • u))) hmem
  have h3 := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E))
    (f := fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v))
    (g := (↑(extChartAt I p) : M → E)) (show E from (σ • u)) h2 h1
  set fE : E → M := fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v) with hfE
  set gE : M → E := (↑(extChartAt I p) : M → E) with hgE
  have hfEc : fE = fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v) := hfE
  have hgEc : gE = (↑(extChartAt I p) : M → E) := hgE
  have hval : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (gE ∘ fE) (show E from (σ • u))) (show E from (σ • η))
      = (mfderiv I 𝓘(ℝ, E) gE (fE (show E from (σ • u))))
          ((mfderiv 𝓘(ℝ, E) I fE (show E from (σ • u))) (show E from (σ • η))) := by
    rw [hfEc, hgEc]
    rw [show (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)) =
        fE from hfEc.symm]
    rw [show ((↑(extChartAt I p) : M → E)) = gE from hgEc.symm]
    rw [h3]
    rfl
  have hmf' : (mfderiv 𝓘(ℝ, E) I fE (show E from (σ • u))) (show E from (σ • η)) = 0 := by
    rw [hfEc]
    exact hmf
  have key : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (((↑(extChartAt I p) : M → E)) ∘
      (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)))
      (show E from (σ • u))) (show E from (σ • η)) = 0 := by
    rw [show (((↑(extChartAt I p) : M → E)) ∘
        (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v))) = (gE ∘ fE) from by
      rw [hgEc, hfEc]]
    rw [hval, hmf', map_zero]
  have hcomp : (((↑(extChartAt I p) : M → E)) ∘
      (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v)))
      = (fun v : E => (extChartAt I p)
        (GExp (cov := cov) hmet p (show TangentSpace I p from v))) := rfl
  rw [hcomp] at key
  rw [mfderiv_eq_fderiv] at key
  exact key

/-! ## 5. Curvature-free nontriviality of the variation field -/

/-- **The variation field of the ray family is not identically zero, without any curvature
hypothesis.**  For a unit vector `u` and a non-zero perturbation direction `η`, the `r`-variation
field `σ ↦ ∂_r|_{r=0} GExp p (σ • (u + r • η))` is non-zero for every small positive `σ`: near `0`
the derivative of `GExp p` is the identity in a chart. -/
theorem exists_pos_variation_ne_zero (hmet : IsMetricCompatible cov) {p : M}
    {u η : TangentSpace I p} (hu : ‖u‖ = 1) (hη : η ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Ioo (0:ℝ) δ,
      curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (σ • (u + r • η))) 0 ≠ 0 := by
  classical
  obtain ⟨δ₁, hδ₁, hδ₁inj⟩ := exists_pos_fderiv_chartGExp_injective (cov := cov) hmet p
  have hcont0 : ContinuousAt (fun w : E =>
      GExp (cov := cov) hmet p (show TangentSpace I p from w)) (0:E) :=
    (contMDiffAt_GExp_one (cov := cov) hmet p (0:E)).continuousAt
  have hpsrc0 : GExp (cov := cov) hmet p (0 : TangentSpace I p) ∈ (chartAt H p).source := by
    rw [GlobalExp.GExp_zero]; exact mem_chart_source H p
  have hsrc_ev : ∀ᶠ w : E in 𝓝 (0:E), GExp (cov := cov) hmet p (show TangentSpace I p from w)
      ∈ (chartAt H p).source :=
    hcont0.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hpsrc0)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hsrc_ev
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  set mu : ℝ := ‖(show E from u)‖ with hmu
  have hmupos : 0 < mu := by
    rw [hmu]
    exact norm_pos_iff.mpr (fun h => hu0 h)
  refine ⟨min (δ₁ / (mu + 1)) (ρ / (mu + 1)),
    lt_min (div_pos hδ₁ (by linarith)) (div_pos hρ (by linarith)), fun σ hσ => ?_⟩
  have hσpos : 0 < σ := hσ.1
  have hσδ : σ < δ₁ / (mu + 1) := lt_of_lt_of_le hσ.2 (min_le_left _ _)
  have hσρ : σ < ρ / (mu + 1) := lt_of_lt_of_le hσ.2 (min_le_right _ _)
  have hσmu₁ : σ * mu < δ₁ := by
    have h1 : σ * mu < (δ₁ / (mu + 1)) * mu := mul_lt_mul_of_pos_right hσδ hmupos
    have h2 : (δ₁ / (mu + 1)) * mu ≤ δ₁ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [hmupos, hδ₁]
    linarith
  have hσmu₂ : σ * mu < ρ := by
    have h1 : σ * mu < (ρ / (mu + 1)) * mu := mul_lt_mul_of_pos_right hσρ hmupos
    have h2 : (ρ / (mu + 1)) * mu ≤ ρ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [hmupos, hρ]
    linarith
  have hmodel : ‖(show E from (σ • u))‖ = σ * mu := by
    rw [show (show E from (σ • u)) = σ • (show E from u) from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos hσpos, hmu]
  have hσu₁ : ‖(show E from (σ • u))‖ < δ₁ := by rw [hmodel]; exact hσmu₁
  have hball : (show E from (σ • u)) ∈ Metric.ball (0:E) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [hmodel]
    exact hσmu₂
  have hmem : GExp (cov := cov) hmet p (σ • u) ∈ (chartAt H p).source := hρsub hball
  intro hzero
  have hfm := model_deriv_of_variation (cov := cov) hmet p hmem hzero
  have hzj : (show E from (σ • η)) = 0 :=
    hδ₁inj (show E from (σ • u)) hσu₁ (by rw [hfm, map_zero])
  have hnm : σ ≠ 0 := ne_of_gt hσpos
  refine hη ?_
  have h := congrArg (fun z : E => σ⁻¹ • z) hzj
  simpa [smul_smul, inv_mul_cancel₀ hnm, one_smul] using h

/-! ## 6. A singular differential of `GExp p` produces a conjugate time -/

/-- **The κ-side bridge, curvature-free.**  If the differential of `GExp p` is singular at a non-zero
vector `v`, then `‖v‖` is a **conjugate time** of the ray `s ↦ GExp p (s • unitOf v)`: the kernel
direction produces a non-trivial Jacobi field along the ray vanishing at `0` and at `‖v‖`.  This is
one half of the classical equivalence "`v` is conjugate to `p` ⟺ `d exp_p` is singular at `v`", and
it needs **no curvature hypothesis** (unlike `Submission.RayConj`'s length bound, whose proof uses
Rauch's theorem to see the non-triviality of the same Jacobi field). -/
theorem singular_imp_conjTime (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) :
    Submission.ConjCut.SingularImpConjTime (I := I) hmet htor := by
  intro p v hv hsing
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu1 : ‖unitOf v hv‖ = 1 := unitOf_norm v hv
  have hu0 : unitOf v hv ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hu1; norm_num at hu1
  obtain ⟨ξ, hξ0, hξker⟩ :=
    Submission.RayConj.exists_ne_zero_apply_eq_zero (I := I) (q := p) hsing
  set η : TangentSpace I p := ‖v‖⁻¹ • ξ with heta_def
  have heta0 : η ≠ 0 := by
    rw [heta_def]
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hv)) hξ0
  have heta_eq : ‖v‖ • η = ξ := by
    rw [heta_def, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hvu : ‖v‖ • unitOf v hv = v := by
    rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  refine ⟨hvpos, ?_⟩
  refine ⟨(fun s : ℝ => curveVelocity (I := I)
    (fun r : ℝ => GExp (cov := cov) hmet p (s • (unitOf v hv + r • η))) 0), ?_, ?_, ?_, ?_⟩
  · -- the variation field is a Jacobi field
    intro s
    exact isJacobiAt_GExp_variation (cov := cov) hmet htor hu0 hu1 s
  · -- `J 0 = 0`
    change curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet p ((0:ℝ) • (unitOf v hv + r • η))) 0 = 0
    have hev : (fun r : ℝ => GExp (cov := cov) hmet p ((0:ℝ) • (unitOf v hv + r • η)))
        =ᶠ[𝓝 (0:ℝ)] (fun _ : ℝ => p) := by
      filter_upwards with r
      rw [zero_smul, GlobalExp.GExp_zero]
    rw [Submission.RayJacobi.curveVelocity_congr (I := I) hev]
    exact curveVelocity_const (I := I) p 0
  · -- `J ‖v‖ = 0`, by the chain rule and the kernel condition
    change curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet p (‖v‖ • (unitOf v hv + r • η))) 0 = 0
    have h1 : HasDerivAt (fun r : ℝ => unitOf v hv + r • η) η (0:ℝ) := by
      have h := (hasDerivAt_id (0:ℝ)).smul_const η
      simpa using h.const_add (unitOf v hv)
    have h2 : HasDerivAt (fun r : ℝ => ‖v‖ • (unitOf v hv + r • η)) (‖v‖ • η) (0:ℝ) :=
      h1.const_smul ‖v‖
    have hσ : HasDerivAt (fun r : ℝ => ‖v‖ • (unitOf v hv + r • η)) ξ (0:ℝ) := by
      rw [← heta_eq]
      exact h2
    have hmd : MDifferentiableAt 𝓘(ℝ, E) I
        (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
        (‖v‖ • (unitOf v hv + (0:ℝ) • η)) :=
      (contMDiffAt_GExp_one (cov := cov) hmet p
        (‖v‖ • (unitOf v hv + (0:ℝ) • η))).mdifferentiableAt one_ne_zero
    have hchain := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp (I := I)
      (f := fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
      (σ := fun r : ℝ => ‖v‖ • (unitOf v hv + r • η)) (σ' := fun _ : ℝ => ξ)
      (γ := fun r : ℝ => GExp (cov := cov) hmet p (‖v‖ • (unitOf v hv + r • η))) hσ hmd
      (Filter.Eventually.of_forall (fun r => rfl))
    rw [hchain]
    rw [show ‖v‖ • (unitOf v hv + (0:ℝ) • η) = v from by rw [zero_smul, add_zero]; exact hvu]
    exact hξker
  · -- non-triviality
    obtain ⟨δ, hδpos, hδne⟩ := exists_pos_variation_ne_zero (cov := cov) hmet (p := p)
      (u := unitOf v hv) (η := η) hu1 heta0
    have hσpos : 0 < min δ ‖v‖ / 2 := by positivity
    have hσltδ : min δ ‖v‖ / 2 < δ := by
      have h : min δ ‖v‖ ≤ δ := min_le_left _ _
      linarith
    have hσltT : min δ ‖v‖ / 2 < ‖v‖ := by
      have h : min δ ‖v‖ ≤ ‖v‖ := min_le_right _ _
      linarith
    exact ⟨min δ ‖v‖ / 2, ⟨hσpos, hσltT⟩, hδne _ ⟨hσpos, hσltδ⟩⟩

end

end Submission.SingularConj

/-! ## 7. The κ-side bridge, discharged

With `singular_imp_conjTime` the hypothesis `SingularImpConjTime` of
`Submission.ConjCut.isInvertible_mfderiv_of_mem_segmentDomain` is now a *theorem*, so that the
invertibility of `d GExp_p` on the tangential segment domain depends on the single remaining classical
input `σ ≤ κ` (`Submission.ConjCut.CutConjInequality`). -/

namespace Submission.SingularConj

noncomputable section

open Submission.ConjCut

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

/-- **Unconditional κ-side bridge**: `SingularImpConjTime` holds for any torsion-free metric
compatible connection. -/
theorem singularImpConjTime_of_torsion_free (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) :
    SingularImpConjTime (I := I) hmet htor :=
  singular_imp_conjTime (cov := cov) hmet htor

/-- **Invertibility of `d GExp_p` on the tangential segment domain**, with the κ-side bridge no longer
a hypothesis: only `σ ≤ κ` (`CutConjInequality`) remains. -/
theorem isInvertible_mfderiv_of_mem_segmentDomain_of_cutConj (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (hcc : CutConjInequality (I := I) hmet htor)
    {p : M} {v : TangentSpace I p}
    (hv : v ∈ Submission.SegmentDomain.segmentDomain hmet p) (hv0 : v ≠ 0) :
    (mfderiv 𝓘(ℝ, E) I
      (fun u : E => GExp (cov := cov) hmet p (show TangentSpace I p from u))
      (show E from v)).IsInvertible :=
  Submission.ConjCut.isInvertible_mfderiv_of_mem_segmentDomain (I := I) hmet htor
    (singular_imp_conjTime (cov := cov) hmet htor) hcc hv hv0

end

end Submission.SingularConj
