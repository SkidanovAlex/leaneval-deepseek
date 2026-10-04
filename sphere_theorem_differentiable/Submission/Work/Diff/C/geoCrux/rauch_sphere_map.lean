import Mathlib
import Submission.Work.Diff.C.geoCrux.RauchDefs
import Submission.Work.Diff.C.geoCrux.RauchInputDefs
import Submission.Work.Diff.C.geoCrux.cut_inject
import Submission.Work.Diff.C.geoCrux.radial_modulus
import Submission.Work.Diff.C.geoCrux.rauch_arith
import Submission.Work.Diff.C.geoCrux.rauch_num
import Submission.Work.Diff.C.geoCrux.small_radius_bound
import Submission.Work.Diff.C.geoCrux.tan_ratio_bounds
import Submission.Work.Diff.C.dmRadialBridge
import Submission.Work.Diff.C.far_sphere_size
import Submission.Work.Diff.C.ray_minimising_near_perturbation
import Submission.Work.Diff.C.JacobiLogDeriv
import Submission.Work.Diff.C.modulus_le_sin_add_sqrt
import Submission.Work.Diff.C.rgrad_fcos
import Submission.RayJacobi
import Submission.ChartGeoAt
import Submission.ConjEnergy
import Submission.EnergyRayCover
import Submission.GExpSmooth
import Submission.LensLoop
import Submission.GExpVelocity
import Submission.GExpRay
import Submission.CutTime

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter
open Submission.GlobalExp Submission.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## The one-dimensional anchored Sturm comparison

We re-derive the elementary part of `Work.Diff.C.modulus_le_sin_add_sqrt` in the *anchored* form
needed here: the comparison is started at an interior scale `δ` with the anchor hypothesis
`v δ ≤ exp A · sin δ` instead of the model asymptotics at `0`. -/

/-- **Derivative of the comparison function** at an interior point: the derivative of
`Ψ t = log (v t) - log (sin t) - ε log (tan (t/2))` is `w t - cot t - ε / sin t`. -/
theorem psiDeriv_anchored {v w : ℝ → ℝ} {ε t : ℝ}
    (hder : HasDerivAt (fun z : ℝ => Real.log (v z)) (w t) t)
    (ht : 0 < t) (htπ : t < Real.pi) :
    HasDerivAt (fun s : ℝ => Real.log (v s) - Real.log (Real.sin s)
      - ε * Real.log (Real.tan (s / 2))) (w t - Real.cot t - ε / Real.sin t) t := by
  have hsinpos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht htπ
  have hlogsin : HasDerivAt (fun s : ℝ => Real.log (Real.sin s)) (Real.cot t) t := by
    have h := (Real.hasDerivAt_sin t).log hsinpos.ne'
    rw [Real.cot_eq_cos_div_sin]
    exact h
  have hlogtan : HasDerivAt (fun s : ℝ => Real.log (Real.tan (s / 2))) (1 / Real.sin t) t := by
    have ht2 : t / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
    have hcos : Real.cos (t / 2) ≠ 0 := (Real.cos_pos_of_mem_Ioo ht2).ne'
    have hsin2 : 0 < Real.sin (t / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have htan : Real.tan (t / 2) ≠ 0 := by
      rw [Real.tan_eq_sin_div_cos]
      exact div_ne_zero hsin2.ne' hcos
    have hlin : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    have h2 : HasDerivAt (Real.tan ∘ fun s : ℝ => s / 2)
        ((1 / Real.cos (t / 2) ^ 2) * (1 / 2)) t :=
      (Real.hasDerivAt_tan hcos).comp t hlin
    have hcomp : (Real.tan ∘ fun s : ℝ => s / 2) = (fun s : ℝ => Real.tan (s / 2)) := rfl
    rw [hcomp] at h2
    have h := h2.log htan
    convert h using 1
    rw [Real.tan_eq_sin_div_cos]
    have hs2 : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
      have h := Real.sin_two_mul (t / 2)
      rwa [show 2 * (t / 2) = t from by ring] at h
    rw [hs2]
    field_simp
  have hsub := (hder.sub hlogsin).sub (hlogtan.const_mul ε)
  convert hsub using 1
  ring

/-- **The anchored Sturm comparison.**  Let `0 < δ < d < π`, `ε ≥ 0`, and let `v > 0` on `(0,d)`,
`v d > 0`, with `(log v)' ≤ cot t + ε/sin t` on `(0,d)` and the anchor `v δ ≤ exp A · sin δ`.
Then `v d ≤ exp A · sin d · (tan (d/2)/tan (δ/2))^ε`. -/
theorem modulus_anchored {v w : ℝ → ℝ} {ε δ d A : ℝ}
    (hδ : 0 < δ) (hδd : δ < d) (hε : 0 ≤ ε) (hdπ : d < Real.pi)
    (hpos : ∀ t ∈ Set.Ioo (0 : ℝ) d, 0 < v t) (hdpos : 0 < v d)
    (hder : ∀ t ∈ Set.Icc δ d, HasDerivAt (fun s : ℝ => Real.log (v s)) (w t) t)
    (hwb : ∀ t ∈ Set.Ioo (0 : ℝ) d, w t ≤ Real.cot t + ε / Real.sin t)
    (hanchor : v δ ≤ Real.exp A * Real.sin δ) :
    v d ≤ Real.exp A * Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε := by
  have hδd' : δ ≤ d := hδd.le
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith)
  have hsd : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi (by linarith) hdπ
  have hvd : 0 < v δ := hpos δ ⟨hδ, hδd⟩
  set Ψ : ℝ → ℝ := fun s => Real.log (v s) - Real.log (Real.sin s)
    - ε * Real.log (Real.tan (s / 2)) with hΨ
  have hderΨ : ∀ t ∈ Set.Ioo δ d, HasDerivAt Ψ (w t - Real.cot t - ε / Real.sin t) t := by
    intro t ht
    exact psiDeriv_anchored (v := v) (w := w) (ε := ε)
      (hder t ⟨ht.1.le, ht.2.le⟩) (lt_trans hδ ht.1) (lt_trans ht.2 hdπ)
  have hcontΨ : ContinuousOn Ψ (Set.Icc δ d) := by
    have h1 : ContinuousOn (fun s : ℝ => Real.log (v s)) (Set.Icc δ d) :=
      fun x hx => ((hder x hx).continuousAt).continuousWithinAt
    have h2 : ContinuousOn (fun s : ℝ => Real.log (Real.sin s)) (Set.Icc δ d) :=
      Real.continuous_sin.continuousOn.log (fun x hx =>
        (Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hδ hx.1)
          (lt_of_le_of_lt hx.2 hdπ)).ne')
    have h3 : ContinuousOn (fun s : ℝ => Real.log (Real.tan (s / 2))) (Set.Icc δ d) := by
      have hsin : ContinuousOn (fun s : ℝ => Real.sin (s / 2)) (Set.Icc δ d) :=
        Real.continuous_sin.comp_continuousOn ((continuous_id.div_const 2).continuousOn)
      have hcos : ContinuousOn (fun s : ℝ => Real.cos (s / 2)) (Set.Icc δ d) :=
        Real.continuous_cos.comp_continuousOn ((continuous_id.div_const 2).continuousOn)
      have hcne : ∀ x ∈ Set.Icc δ d, Real.cos (x / 2) ≠ 0 := fun x hx =>
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).ne'
      have hdiv : ContinuousOn (fun s : ℝ => Real.sin (s / 2) / Real.cos (s / 2))
          (Set.Icc δ d) := hsin.div hcos hcne
      have ht : ContinuousOn (fun s : ℝ => Real.tan (s / 2)) (Set.Icc δ d) := by
        simpa only [Real.tan_eq_sin_div_cos] using hdiv
      exact ht.log (fun x hx => by
        rw [Real.tan_eq_sin_div_cos]
        exact div_ne_zero
          (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])).ne'
          (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).ne')
    have h4 : ContinuousOn (fun s : ℝ => ε * Real.log (Real.tan (s / 2))) (Set.Icc δ d) :=
      continuousOn_const.mul h3
    rw [hΨ]
    exact (h1.sub h2).sub h4
  have hanti : AntitoneOn Ψ (Set.Icc δ d) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc δ d) hcontΨ ?_ ?_
    · rw [interior_Icc]
      intro x hx
      exact ((hderΨ x hx).differentiableAt).differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hderΨ x hx).deriv]
      have hx0 : x ∈ Set.Ioo (0 : ℝ) d := ⟨lt_trans hδ hx.1, hx.2⟩
      have hspos : 0 < Real.sin x :=
        Real.sin_pos_of_pos_of_lt_pi hx0.1 (lt_of_lt_of_le hx0.2 hdπ.le)
      have h1 := hwb x hx0
      have h2 : 0 ≤ ε / Real.sin x := div_nonneg hε hspos.le
      linarith
  have hle : Ψ d ≤ Ψ δ :=
    hanti ⟨le_refl δ, hδd'⟩ ⟨hδd', le_refl d⟩ hδd'
  have hle' : Real.log (v d) - Real.log (Real.sin d) - ε * Real.log (Real.tan (d / 2))
      ≤ Real.log (v δ) - Real.log (Real.sin δ) - ε * Real.log (Real.tan (δ / 2)) := hle
  have hlogv : Real.log (v d) ≤ Real.log (v δ) + (Real.log (Real.sin d) - Real.log (Real.sin δ))
      + ε * (Real.log (Real.tan (d / 2)) - Real.log (Real.tan (δ / 2))) := by linarith
  have htanpos : 0 < Real.tan (d / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have htanposδ : 0 < Real.tan (δ / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have htarget_log : Real.log (v δ * (Real.sin d / Real.sin δ)
      * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε)
      = Real.log (v δ) + (Real.log (Real.sin d) - Real.log (Real.sin δ))
        + ε * (Real.log (Real.tan (d / 2)) - Real.log (Real.tan (δ / 2))) := by
    have hb : 0 < Real.tan (d / 2) / Real.tan (δ / 2) := div_pos htanpos htanposδ
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul hvd.ne' (by positivity),
      Real.log_div hsd.ne' hsδ.ne',
      Real.log_rpow hb,
      Real.log_div htanpos.ne' htanposδ.ne']
  have hprod : v d ≤ v δ * (Real.sin d / Real.sin δ)
      * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε := by
    rw [← Real.log_le_log_iff hdpos (by positivity)]
    rw [htarget_log]
    exact hlogv
  have hfinal : v δ * (Real.sin d / Real.sin δ)
      * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε
      ≤ Real.exp A * Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε := by
    have h1 : v δ * (Real.sin d / Real.sin δ) ≤ Real.exp A * Real.sin d := by
      have h2 : v δ / Real.sin δ ≤ Real.exp A := by
        rw [div_le_iff₀ hsδ]
        exact hanchor
      have h3 : v δ * (Real.sin d / Real.sin δ) = (v δ / Real.sin δ) * Real.sin d := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_right h2 hsd.le
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by positivity) _)
  linarith [hprod, hfinal]

/-! ## Calculus helpers for the radial ray -/

/-- `rdist q · = arccos ∘ fcos q` when the diameter is at most `π`. -/
lemma rdist_eq_arccos_fcos (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    (q z : M) :
    rdist (I := I) (M := M) q z = Real.arccos (fcos (I := I) (M := M) q z) := by
  have h1 : 0 ≤ rdist (I := I) (M := M) q z := ENNReal.toReal_nonneg
  have h2 : rdist (I := I) (M := M) q z ≤ Real.pi := hdiam q z
  have h3 : fcos (I := I) (M := M) q z = Real.cos (rdist (I := I) (M := M) q z) := rfl
  rw [h3, Real.arccos_cos h1 h2]

/-- **The distance function is smooth where `fcos` is**: `rdist q = arccos ∘ fcos q` and `arccos` is
smooth away from `±1`. -/
lemma cmDiffAt_rdist_of_cmDiffAt_fcos
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {q x : M} (hx0 : 0 < rdist (I := I) (M := M) q x)
    (hxπ : rdist (I := I) (M := M) q x < Real.pi)
    (h : CMDiffAt ∞ (fcos (I := I) (M := M) q) x) :
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) x := by
  have hne1 : fcos (I := I) (M := M) q x ≠ -1 := by
    intro hc
    have hcos : Real.cos (rdist (I := I) (M := M) q x) = -1 := by simpa [fcos] using hc
    have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (x := rdist (I := I) (M := M) q x)
      (y := Real.pi) hx0.le le_rfl hxπ
    rw [Real.cos_pi] at hlt
    linarith [hcos, hlt]
  have hne2 : fcos (I := I) (M := M) q x ≠ 1 := by
    intro hc
    have hcos : Real.cos (rdist (I := I) (M := M) q x) = 1 := by simpa [fcos] using hc
    have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (x := (0 : ℝ))
      (y := rdist (I := I) (M := M) q x) le_rfl hxπ.le hx0
    rw [Real.cos_zero] at hlt
    linarith [hcos, hlt]
  have hfuneq : (fun z : M ↦ rdist (I := I) (M := M) q z)
      = fun z : M ↦ Real.arccos (fcos (I := I) (M := M) q z) :=
    funext fun z => rdist_eq_arccos_fcos (I := I) (M := M) hdiam q z
  rw [hfuneq]
  have harccos : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.arccos (fcos (I := I) (M := M) q x) := by
    rw [contMDiffAt_iff_contDiffAt]
    exact Real.contDiffAt_arccos hne1 hne2
  exact harccos.comp x h

/-- **The gradient of the distance is a unit vector** on the region where the eikonal identity holds
for `fcos q` (this is `hgrad` transferred through `rgrad (fcos q) = -sin (rdist q) • rgrad (rdist q)`). -/
lemma unit_grad_rdist {q x : M}
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) x)
    (hgrad : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
      (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
      = 1 - (fcos (I := I) (M := M) q x) ^ 2)
    (h0 : 0 < rdist (I := I) (M := M) q x) (hπ : rdist (I := I) (M := M) q x < Real.pi) :
    Inner.inner ℝ (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) x)
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) x) = 1 := by
  have hrg := Work.Diff.C.rgrad_fcos (I := I) (M := M) (q := q) hsm
  have hsin : Real.sin (rdist (I := I) (M := M) q x) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi h0 hπ).ne'
  have htrig : 1 - (Real.cos (rdist (I := I) (M := M) q x)) ^ 2
      = Real.sin (rdist (I := I) (M := M) q x) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (rdist (I := I) (M := M) q x)
    linarith
  have hgrad' : -Real.sin (rdist (I := I) (M := M) q x)
      * (-Real.sin (rdist (I := I) (M := M) q x)
        * Inner.inner ℝ (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) x)
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) x))
      = Real.sin (rdist (I := I) (M := M) q x) ^ 2 := by
    rw [hrg, real_inner_smul_left, real_inner_smul_right] at hgrad
    simpa [fcos, htrig] using hgrad
  have hkey : Inner.inner ℝ (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) x)
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) x)
      * (Real.sin (rdist (I := I) (M := M) q x) * Real.sin (rdist (I := I) (M := M) q x))
      = 1 * (Real.sin (rdist (I := I) (M := M) q x)
        * Real.sin (rdist (I := I) (M := M) q x)) := by
    rw [one_mul]
    have h := hgrad'
    ring_nf at h ⊢
    exact h
  exact mul_right_cancel₀ (mul_ne_zero hsin hsin) hkey

/-- The norm of a tangent vector is insensitive to a propositional equality of base points. -/
lemma norm_congr_point {X Y : M} (h : X = Y) (a : E) :
    ‖(show TangentSpace I X from a)‖ = ‖(show TangentSpace I Y from a)‖ := by
  subst h
  rfl

/-- **The derivative of the geodesic-sphere map** at `σ = 0` is (in norm) the value at time `ρ` of the
radial variation field of the family of rays out of `q`.  Both are the differential of `GExp q` at
`ρ • v` in the direction `ρ • w`: the one-sided chain rules for the curves
`σ ↦ ρ • (cos σ • v + sin σ • w)` and `r ↦ ρ • (v + r • w)`, which are tangent at `0`. -/
lemma norm_curveVelocity_sphereMap_eq (hmet : IsMetricCompatible cov) {q : M} {ρ : ℝ}
    (v w : TangentSpace I q) :
    ‖curveVelocity (I := I) (fun σ : ℝ =>
        GExp (cov := cov) hmet q (ρ • (Real.cos σ • v + Real.sin σ • w))) 0‖
      = ‖curveVelocity (I := I) (fun r : ℝ =>
          GExp (cov := cov) hmet q (ρ • (v + r • w))) 0‖ := by
  let F : E → M := fun z : E => GExp (cov := cov) hmet q z
  let c₁ : ℝ → E := fun σ : ℝ => (ρ • (Real.cos σ • v + Real.sin σ • w) : E)
  let c₂ : ℝ → E := fun r : ℝ => (ρ • (v + r • w) : E)
  let g₁ : ℝ → M := fun σ : ℝ =>
    GExp (cov := cov) hmet q (ρ • (Real.cos σ • v + Real.sin σ • w))
  let g₂ : ℝ → M := fun r : ℝ => GExp (cov := cov) hmet q (ρ • (v + r • w))
  have hF : ∀ y : E, MDiffAt F y := fun y =>
    (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet q y).mdifferentiableAt
      (by decide)
  have hd1 : HasDerivAt c₁ (ρ • w : E) 0 := by
    have h1 : HasDerivAt (fun σ : ℝ => Real.cos σ • (show E from v)) (0 : E) 0 := by
      have := (Real.hasDerivAt_cos (0 : ℝ)).smul_const (show E from v)
      simpa using this
    have h2 : HasDerivAt (fun σ : ℝ => Real.sin σ • (show E from w)) (show E from w) 0 := by
      have := (Real.hasDerivAt_sin (0 : ℝ)).smul_const (show E from w)
      simpa using this
    have h3 : HasDerivAt (fun σ : ℝ =>
        Real.cos σ • (show E from v) + Real.sin σ • (show E from w)) (show E from w) 0 := by
      have h := h1.add h2
      rw [zero_add] at h
      refine h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
      funext σ
      rfl
    exact h3.const_smul ρ
  have hd2 : HasDerivAt c₂ (ρ • w : E) 0 := by
    have h1 : HasDerivAt (fun r : ℝ => r • (show E from w)) (show E from w) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (show E from w)
    have h2 : HasDerivAt (fun r : ℝ => (show E from v) + r • (show E from w))
        (show E from w) 0 := h1.const_add (show E from v)
    exact h2.const_smul ρ
  have hpt1 : c₁ 0 = (ρ • v : E) := by simp [c₁]
  have hpt2 : c₂ 0 = (ρ • v : E) := by simp [c₂]
  have hc1 := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp
    (I := I) (f := F) (σ := c₁) (σ' := fun _ : ℝ => (ρ • w : TangentSpace I q))
    (γ := g₁) hd1 (hF (c₁ 0)) (Filter.Eventually.of_forall fun _ => rfl)
  have hc2 := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp
    (I := I) (f := F) (σ := c₂) (σ' := fun _ : ℝ => (ρ • w : TangentSpace I q))
    (γ := g₂) hd2 (hF (c₂ 0)) (Filter.Eventually.of_forall fun _ => rfl)
  rw [hpt1] at hc1
  rw [hpt2] at hc2
  have hA : (show TangentSpace I (F (ρ • v)) from curveVelocity (I := I) g₁ 0)
      = (show TangentSpace I (F (ρ • v)) from curveVelocity (I := I) g₂ 0) := by
    rw [hc1, hc2]
  have e1 : ‖curveVelocity (I := I) g₁ 0‖
      = ‖(show TangentSpace I (F (ρ • v)) from curveVelocity (I := I) g₁ 0)‖ :=
    norm_congr_point (I := I) (congrArg F hpt1) (curveVelocity (I := I) g₁ 0)
  have e2 : ‖curveVelocity (I := I) g₂ 0‖
      = ‖(show TangentSpace I (F (ρ • v)) from curveVelocity (I := I) g₂ 0)‖ :=
    norm_congr_point (I := I) (congrArg F hpt2) (curveVelocity (I := I) g₂ 0)
  calc ‖curveVelocity (I := I) g₁ 0‖
      = ‖(show TangentSpace I (F (ρ • v)) from curveVelocity (I := I) g₁ 0)‖ := e1
    _ = ‖(show TangentSpace I (F (ρ • v)) from curveVelocity (I := I) g₂ 0)‖ := by rw [hA]
    _ = ‖curveVelocity (I := I) g₂ 0‖ := e2.symm

/-! ## The reduction: from the two geometric inputs and the arithmetic to `RauchSphereMapProp`

This is the assembly.  It is stated with the binders *explicitly unfolded* (in a `variable`
context) rather than through the closed `Prop`s of `geoCrux/RauchInputDefs.lean`: a **local hypothesis
whose type is an `abbrev`-`Prop`** has its implicit universe arguments frozen at the binder, so
`hcut (E := E)` fails with a universe mismatch.  With the binders unfolded the hypotheses live at the
theorem's own universes and everything matches; the final theorem instantiates them from the three
delegated lemmas (`cut_inject`, `radial_modulus`, `rauch_arith`), whose universes are instantiated
freshly at the call site.

The steps: ray minimality up to `L` (`hInj`); smoothness of `rdist q` and the eikonal identity
(`hsmC`, `hgrad`, `rdist = arccos ∘ fcos`); `rgrad (rdist q) = γ'` (`curveVelocity_GExp_eq_smul_rgrad`
+ `curveVelocity_comp_mul`); the bridge `Work.Diff.C.dmRadialBridge` and the shape bound
`Work.Diff.C.rhess_rdist_bound_of_hHess`, giving `(log ‖Z t‖)' ≤ cot t + (c/4)/sin t`; the anchored
comparison `modulus_anchored`; and the numeric inequality `rauch_arith`. -/

/-- Cancellation of a non-zero scalar multiple in a real vector space. -/
lemma smul_eq_of_smul_eq {G : Type*} [AddCommGroup G] [Module ℝ G] {t : ℝ} (ht : t ≠ 0)
    {a b : G} (h : t • a = t • b) : a = b := by
  have h2 := congrArg (fun z : G => t⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ ht, one_smul] using h2

universe u v w

theorem rauch_sphere_map_core
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    (hInj : ∀ q : M, Submission.InjRadius.InjAtLeast hmet q
      (Real.pi - Real.arccos (1 - c)))
    (hmod : ∀ (q : M) (v w : TangentSpace I q),
      Inner.inner ℝ v v = 1 → Inner.inner ℝ w w = 1 → Inner.inner ℝ v w = 0 →
      ∀ t ∈ Set.Ioc (0 : ℝ) (Real.pi - Real.arccos (1 - c)),
        Real.sin t / 2 ≤ ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • w))) 0‖ ∧
        ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • w))) 0‖
          ≤ Real.sin t
            + 3 * (ε₁ * (1 + (Real.log (2 / t)) ^ 2) + t ^ 2) * t)
    (harith : ∀ {A R s : ℝ}, A ≤ 6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4) →
      R ≤ 8 / c → 1 ≤ R → 0 ≤ s → s ≤ 1 →
        Real.exp A * R ^ (c / 4) * s ≤ s + 40 * (Real.sqrt c + ε₁ * Real.pi))
    (q : M) (ρ : ℝ) (hρ : 0 < ρ) (hρle : ρ ≤ Real.pi - Real.arccos (1 - c))
    (v w : TangentSpace I q) (hv : Inner.inner ℝ v v = 1) (hw : Inner.inner ℝ w w = 1)
    (hvw : Inner.inner ℝ v w = 0) :
    ‖curveVelocity (I := I) (fun σ : ℝ =>
        GExp (cov := cov) hmet q (ρ • (Real.cos σ • v + Real.sin σ • w))) 0‖
      ≤ Real.sin ρ + 40 * (Real.sqrt c + ε₁ * Real.pi) := by
  classical
  have hv_ne : v ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp at hv
  have hv1 : ‖v‖ = 1 := by
    have h : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq v]; exact hv
    nlinarith [norm_nonneg v]
  -- the radius `L = π - arccos (1-c)`
  set L : ℝ := Real.pi - Real.arccos (1 - c) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    have h1 : Real.arccos (1 - c) ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by linarith)
    linarith [Real.pi_pos]
  have hLpi : L < Real.pi := by
    rw [hLdef]
    have h1 : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  have hcosL : Real.cos L = -1 + c := by
    rw [hLdef, Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
    ring
  have hρL : ρ ≤ L := hρle
  -- the derivative of the sphere map is the radial variation field at time `ρ`
  rw [norm_curveVelocity_sphereMap_eq (I := I) (M := M) (cov := cov) hmet (q := q) (ρ := ρ) v w]
  set Z : (t : ℝ) → TangentSpace I (GExp (cov := cov) hmet q (t • v)) :=
    fun t : ℝ => curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet q (t • (v + r • w))) 0 with hZdef
  -- the same field as a real function of the time, the form in which `hmod` states it
  set zf : ℝ → ℝ := fun t : ℝ => ‖curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet q (t • (v + r • w))) 0‖ with hzfdef
  change zf ρ ≤ Real.sin ρ + 40 * (Real.sqrt c + ε₁ * Real.pi)
  have hZpt : ∀ t : ℝ, (fun r : ℝ => GExp (cov := cov) hmet q (t • (v + r • w))) 0
      = GExp (cov := cov) hmet q (t • v) := fun t => by
    show GExp (cov := cov) hmet q (t • (v + (0 : ℝ) • w)) = _
    rw [zero_smul, add_zero]
  have hzfZ : ∀ t : ℝ, zf t = ‖Z t‖ := by
    intro t
    have h2 : ‖Z t‖ = ‖curveVelocity (I := I)
        (fun r : ℝ => GExp (cov := cov) hmet q (t • (v + r • w))) 0‖ := by
      rw [hZdef]
      exact (norm_congr_point (I := I) (hZpt t) _).symm
    exact h2.symm
  -- ## the modulus bounds of `hmod`
  have hZmod : ∀ t ∈ Set.Ioc (0 : ℝ) L,
      Real.sin t / 2 ≤ zf t ∧ zf t ≤ Real.sin t
        + 3 * (ε₁ * (1 + (Real.log (2 / t)) ^ 2) + t ^ 2) * t := by
    intro t ht
    have h := hmod q v w hv hw hvw t (by rw [hLdef]; exact ht)
    simpa only [hzfdef] using h
  -- ## the ray is minimising up to `L`
  have hmin_ray : ∀ t : ℝ, 0 < t → t < L →
      rdist (I := I) (M := M) q (GExp (cov := cov) hmet q (t • v)) = t := by
    intro t ht0 htL
    have hnorm : ‖(t • v : TangentSpace I q)‖ = t := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le, hv1, mul_one]
    have hne : (t • v : TangentSpace I q) ≠ 0 := by
      intro h0
      have h1 : ‖(t • v : TangentSpace I q)‖ = 0 := by rw [h0, norm_zero]
      rw [hnorm] at h1
      exact absurd h1 (ne_of_gt ht0)
    have h := Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast (I := I) (M := M) (cov := cov)
      hmet htor (hInj q) (u := t • v) (by rw [hnorm]; exact htL) hne
    rw [Work.Diff.C.rdist, h, ENNReal.toReal_ofReal (norm_nonneg _), hnorm]
  -- ## `fcos q` on the ray
  have hfcos_le : ∀ t : ℝ, 0 < t → t < L →
      -1 + c ≤ fcos (I := I) (M := M) q (GExp (cov := cov) hmet q (t • v)) := by
    intro t ht0 htL
    have hrd := hmin_ray t ht0 htL
    have hcost : Real.cos L ≤ Real.cos t :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht0.le hLpi.le htL.le
    rw [fcos, hrd, ← hcosL]
    exact hcost
  have hfcos_lt : ∀ t : ℝ, 0 < t → t < L →
      -1 + c < fcos (I := I) (M := M) q (GExp (cov := cov) hmet q (t • v)) := by
    intro t ht0 htL
    have hrd := hmin_ray t ht0 htL
    have hcost : Real.cos L < Real.cos t :=
      Real.cos_lt_cos_of_nonneg_of_le_pi ht0.le hLpi.le htL
    rw [fcos, hrd, ← hcosL]
    exact hcost
  -- ## smoothness of `rdist q` along the ray and the eikonal identity
  have hrdπ : ∀ t : ℝ, 0 < t → t < ρ → rdist (I := I) (M := M) q
      (GExp (cov := cov) hmet q (t • v)) < Real.pi := by
    intro t ht0 htρ
    have htL : t < L := lt_of_lt_of_le htρ hρL
    rw [hmin_ray t ht0 htL]
    exact lt_of_lt_of_le htρ (le_trans hρL hLpi.le)
  have hsm_pt : ∀ t : ℝ, 0 < t → t < ρ → CMDiffAt ∞
      (fun z : M ↦ rdist (I := I) (M := M) q z) (GExp (cov := cov) hmet q (t • v)) := by
    intro t ht0 htρ
    have htL : t < L := lt_of_lt_of_le htρ hρL
    have hrd := hmin_ray t ht0 htL
    refine cmDiffAt_rdist_of_cmDiffAt_fcos (I := I) (M := M) hdiam ?_ ?_ ?_
    · rw [hrd]; exact ht0
    · exact hrdπ t ht0 htρ
    · exact hsmC q _ (hfcos_le t ht0 htL)
  have hunit_pt : ∀ t : ℝ, 0 < t → t < ρ → Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (GExp (cov := cov) hmet q (t • v)))
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (GExp (cov := cov) hmet q (t • v))) = 1 := by
    intro t ht0 htρ
    have htL : t < L := lt_of_lt_of_le htρ hρL
    have hrd := hmin_ray t ht0 htL
    refine unit_grad_rdist (I := I) (M := M) (q := q) (x := GExp (cov := cov) hmet q (t • v))
      (hsm_pt t ht0 htρ) (hgrad q _ (hfcos_lt t ht0 htL)) ?_ ?_
    · rw [hrd]; exact ht0
    · exact hrdπ t ht0 htρ
  -- ## the ray velocity is the gradient of the distance
  have hvel_pt : ∀ t : ℝ, 0 < t → t < ρ →
      rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (GExp (cov := cov) hmet q (t • v))
        = curveVelocity (I := I) (fun s : ℝ ↦ GExp (cov := cov) hmet q (s • v)) t := by
    intro t ht0 htρ
    have htL : t < L := lt_of_lt_of_le htρ hρL
    have hnormv : ‖(t • v : TangentSpace I q)‖ = t := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le, hv1, mul_one]
    have htv_ne : (t • v : TangentSpace I q) ≠ 0 := by
      intro h0
      have h1 : ‖(t • v : TangentSpace I q)‖ = 0 := by rw [h0, norm_zero]
      rw [hnormv] at h1
      exact absurd h1 (ne_of_gt ht0)
    have hmin : Manifold.riemannianEDist I q (GExp (cov := cov) hmet q (t • v))
        = ENNReal.ofReal t := by
      have h := Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast (I := I) (M := M) (cov := cov)
        hmet htor (hInj q) (u := t • v) (by rw [hnormv]; exact htL) htv_ne
      rwa [hnormv] at h
    have hcv := Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad (I := I) (M := M) (cov := cov) hmet
      (p := q) (u := t • v) htv_ne (by rw [hnormv]; exact hmin)
      (by rw [one_smul]; exact hsm_pt t ht0 htρ)
      (by rw [one_smul]; exact hunit_pt t ht0 htρ)
    rw [hnormv, one_smul] at hcv
    have hscale : curveVelocity (I := I) (fun s : ℝ ↦ GExp (cov := cov) hmet q (s • (t • v))) 1
        = t • curveVelocity (I := I) (fun s : ℝ ↦ GExp (cov := cov) hmet q (s • v)) t := by
      have hfun : (fun s : ℝ => GExp (cov := cov) hmet q (s • (t • v)))
          = fun s : ℝ => (fun r : ℝ => GExp (cov := cov) hmet q (r • v)) (t * s) := by
        funext s
        rw [smul_smul, mul_comm s t]
      rw [hfun]
      have hcm := Submission.GlobalExp.curveVelocity_comp_mul (I := I)
        (γ := fun r : ℝ => GExp (cov := cov) hmet q (r • v)) (c := t) (t := 1)
        ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hv_ne).contMDiffAt
          |>.mdifferentiableAt (by decide))
      rw [mul_one] at hcm
      simpa using hcm
    have hcancel : t • (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (GExp (cov := cov) hmet q (t • v)))
        = t • (curveVelocity (I := I) (fun s : ℝ ↦ GExp (cov := cov) hmet q (s • v)) t) := by
      rw [← hcv, hscale]
    exact smul_eq_of_smul_eq (ne_of_gt ht0) hcancel
  -- ## non-vanishing of `Z` on `(0,L]`
  have hzfpos : ∀ t : ℝ, 0 < t → t ≤ L → 0 < zf t := by
    intro t ht0 htL
    have h := (hZmod t ⟨ht0, htL⟩).1
    have hspos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (lt_of_le_of_lt htL hLpi)
    linarith
  have hZne : ∀ t : ℝ, 0 < t → t ≤ L → Z t ≠ 0 := by
    intro t ht0 htL
    have h := hzfpos t ht0 htL
    rw [hzfZ t] at h
    exact norm_pos_iff.mp h
  -- ## the bridge `⟨∇_t Z, Z⟩ = Hess (rdist q) (Z, Z)`
  have hbridge : ∀ t : ℝ, 0 < t → t < ρ →
      Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t)
        = rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
            (GExp (cov := cov) hmet q (t • v)) (Z t) (Z t) := by
    intro t ht0 htρ
    have htL : t < L := lt_of_lt_of_le htρ hρL
    have hminW : ∀ᶠ s in 𝓝 (0 : ℝ),
        rdist (I := I) (M := M) q (GExp (cov := cov) hmet q (t • (v + s • w)))
          = ‖(t • (v + s • w) : TangentSpace I q)‖ := by
      have hcont_norm : Continuous fun s : ℝ => ‖(t • (v + s • w) : TangentSpace I q)‖ := by
        fun_prop
      have hnorm0 : ‖(t • (v + (0 : ℝ) • w) : TangentSpace I q)‖ = t := by
        rw [zero_smul, add_zero, norm_smul, Real.norm_of_nonneg ht0.le, hv1, mul_one]
      have hmem : (0 : ℝ) ∈ {b : ℝ | ‖(t • (v + b • w) : TangentSpace I q)‖ < L} := by
        show ‖(t • (v + (0 : ℝ) • w) : TangentSpace I q)‖ < L
        rw [hnorm0]; exact htL
      have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ‖(t • (v + s • w) : TangentSpace I q)‖ < L :=
        (isOpen_lt hcont_norm continuous_const).mem_nhds hmem
      have hcont_w : Continuous fun s : ℝ => (v + s • w : TangentSpace I q) := by fun_prop
      have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), v + s • w ≠ 0 :=
        hcont_w.continuousAt.eventually (isOpen_ne.mem_nhds (by simpa using hv_ne))
      filter_upwards [hev, hev2] with s hs hs2
      have hne : (t • (v + s • w) : TangentSpace I q) ≠ 0 := by
        intro h0
        rcases (smul_eq_zero.mp h0) with h1 | h1
        · exact absurd h1 (ne_of_gt ht0)
        · exact hs2 h1
      have h := Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast (I := I) (M := M) (cov := cov)
        hmet htor (hInj q) (u := t • (v + s • w)) hs hne
      rw [Work.Diff.C.rdist, h, ENNReal.toReal_ofReal (norm_nonneg _)]
    have hbr := Work.Diff.C.dmRadialBridge (I := I) (M := M) (cov := cov) hmet htor
      (p := q) (d := t) ht0 (u := v) (η := w) hv hvw
      (hsm_pt t ht0 htρ) (by simpa only [hZdef] using hvel_pt t ht0 htρ)
      (by
        rw [← contMDiffOn_univ]
        intro s _
        have hpair : ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, ℝ × ℝ)) ∞ (fun s' : ℝ => (t, s')) s := by
          have hcd : ContDiffAt ℝ ∞ (fun s' : ℝ => (t, s')) s :=
            contDiffAt_const.prodMk contDiffAt_id
          rw [contMDiffAt_iff_contDiffAt]; exact hcd
        exact (Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet (p := q) (u := v)
          (η := w) t s).comp s hpair)
      (by simpa only [hZdef] using hZne t ht0 (le_of_lt htL)) hminW
    simpa only [hZdef] using hbr
  -- ## the log-derivative of `‖Z·‖`
  have hlog : ∀ t : ℝ, 0 < t → t ≤ ρ → HasDerivAt (fun s : ℝ => Real.log ‖Z s‖)
      (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t)
        / Inner.inner ℝ (Z t) (Z t)) t := by
    intro t ht0 htρ
    refine Work.Diff.C.jld_log_norm_hasDerivAt (I := I) (M := M) (cov := cov) hmet htor
      (γ := fun s : ℝ => GExp (cov := cov) hmet q (s • v)) (J := Z) ?_ ?_ ?_ ?_
    · exact Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hv_ne
    · intro s
      exact Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor (p := q)
        (u := v) (η := w) hv_ne hv1 s
    · intro s
      exact Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hv_ne s
    · exact hZne t ht0 (le_trans htρ hρL)
  have hlogzf : ∀ t : ℝ, 0 < t → t ≤ ρ → HasDerivAt (fun s : ℝ => Real.log (zf s))
      (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t)
        / Inner.inner ℝ (Z t) (Z t)) t := by
    intro t ht0 htρ
    exact (hlog t ht0 htρ).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (funext fun s => by rw [hzfZ s]))
  -- ## the Riccati bound on the log-derivative
  have hwb : ∀ t ∈ Set.Ioo (0 : ℝ) ρ,
      Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t)
        / Inner.inner ℝ (Z t) (Z t) ≤ Real.cot t + (c / 4) / Real.sin t := by
    intro t ht
    have htL : t < L := lt_of_lt_of_le ht.2 hρL
    have hrd := hmin_ray t ht.1 htL
    have hspos : 0 < Real.sin t :=
      Real.sin_pos_of_pos_of_lt_pi ht.1 (lt_of_lt_of_le ht.2 (le_trans hρL hLpi.le))
    have hZpos : 0 < Inner.inner ℝ (Z t) (Z t) := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.mpr (hZne t ht.1 (le_of_lt htL))) 2
    have horth := Work.Diff.C.dmRadialOrthogonal (I := I) (M := M) (cov := cov) hmet htor
      (p := q) (d := t) (u := v) (η := w) hv hvw
    have horthZ : Inner.inner ℝ (Z t) (rgrad (I := I) (M := M)
        (fun z : M ↦ rdist (I := I) (M := M) q z)
          (GExp (cov := cov) hmet q (t • v))) = 0 := by
      rw [hvel_pt t ht.1 ht.2]
      simpa only [hZdef] using horth
    have hVfcos : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
        (GExp (cov := cov) hmet q (t • v))) (Z t) = 0 := by
      have hrf := Work.Diff.C.rgrad_fcos (I := I) (M := M) (q := q) (hsm_pt t ht.1 ht.2)
      rw [hrf, real_inner_smul_left, real_inner_comm, horthZ, mul_zero]
    have hshape := Work.Diff.C.rhess_rdist_bound_of_hHess (I := I) (M := M) (cov := cov)
      (c := c) (ε := ε₁) (q := q) (hHess q) (hfcos_lt t ht.1 htL) (hsm_pt t ht.1 ht.2)
      (by rw [hrd]; exact ht.1) (hrdπ t ht.1 ht.2) (Z t) hVfcos
    have h1 : rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (GExp (cov := cov) hmet q (t • v)) (Z t) (Z t)
        ≤ (Real.cot t + ε₁ / Real.sin t) * Inner.inner ℝ (Z t) (Z t) := by
      rw [hrd] at hshape
      have h2 := (abs_le.mp hshape).2
      linarith
    have h3 : ε₁ / Real.sin t ≤ (c / 4) / Real.sin t := by
      have h4 : ε₁ ≤ c / 4 := by nlinarith [hnum2, Real.pi_gt_three, hε₁]
      exact div_le_div_of_nonneg_right h4 hspos.le
    rw [hbridge t ht.1 ht.2, div_le_iff₀ hZpos]
    calc rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (GExp (cov := cov) hmet q (t • v)) (Z t) (Z t)
        ≤ (Real.cot t + ε₁ / Real.sin t) * Inner.inner ℝ (Z t) (Z t) := h1
      _ ≤ (Real.cot t + (c / 4) / Real.sin t) * Inner.inner ℝ (Z t) (Z t) := by
          refine mul_le_mul_of_nonneg_right ?_ hZpos.le
          linarith [h3]
  -- ## the two cases
  have hρπ : ρ < Real.pi := lt_of_le_of_lt hρL hLpi
  by_cases hcase : ρ ≤ Real.sqrt (c / 4)
  · -- ### Case 1: `ρ ≤ √(c/4)`: the modulus bound at `t = ρ` is already good enough
    have h := (hZmod ρ ⟨hρ, hρL⟩).2
    have hnum : 3 * (ε₁ * (1 + (Real.log (2 / ρ)) ^ 2) + ρ ^ 2) * ρ
        ≤ 40 * (Real.sqrt c + ε₁ * Real.pi) :=
      small_radius_bound (c := c) (ε₁ := ε₁) (ρ := ρ) hc hc1 hε₁ hρ hcase
    linarith
  · -- ### Case 2: `√(c/4) < ρ`: the anchored comparison
    push Not at hcase
    set δ : ℝ := Real.sqrt (c / 4) with hδdef
    have hδpos : 0 < δ := Real.sqrt_pos_of_pos (by linarith)
    have hδsq : δ ^ 2 = c / 4 := by rw [hδdef, Real.sq_sqrt (by linarith)]
    have hδρ : δ < ρ := hcase
    have hδπ : δ < Real.pi := lt_of_lt_of_le hδρ hρπ.le
    have hδle : δ ≤ 1 / 4 := by
      rw [hδdef, Real.sqrt_le_iff]
      exact ⟨by norm_num, by nlinarith [hc1]⟩
    have hsinδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos hδπ
    have hδsin : δ / Real.sin δ ≤ 2 := by
      have h2 : δ / 2 ≤ Real.sin δ := by
        have h := Real.sin_gt_sub_cube hδpos
        have h3 : δ ^ 3 / 6 ≤ δ / 2 := by nlinarith [hδle, hδpos, sq_nonneg δ]
        linarith
      rw [div_le_iff₀ hsinδ]
      linarith
    have hδeq : δ = Real.sqrt c / 2 := by
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [hδdef, Real.sqrt_div' c (y := 4) (by norm_num), h4]
    have hlogeq : Real.log (2 / δ) = Real.log (4 / Real.sqrt c) := by
      have hsc : Real.sqrt c ≠ 0 := (Real.sqrt_pos_of_pos hc).ne'
      congr 1
      rw [hδeq]
      field_simp
      norm_num
    -- the anchor, from the modulus bound at `δ`
    set A : ℝ := 3 * (δ / Real.sin δ) * (ε₁ * (1 + (Real.log (2 / δ)) ^ 2) + δ ^ 2) with hAdef
    have hZδ := hZmod δ ⟨hδpos, le_of_lt (lt_of_lt_of_le hδρ hρL)⟩
    have hanchor : zf δ ≤ Real.exp A * Real.sin δ := by
      have h1 : (1 : ℝ) + 3 * (δ / Real.sin δ) * (ε₁ * (1 + (Real.log (2 / δ)) ^ 2) + δ ^ 2)
          ≤ Real.exp (3 * (δ / Real.sin δ)
            * (ε₁ * (1 + (Real.log (2 / δ)) ^ 2) + δ ^ 2)) := by
        linarith [Real.add_one_le_exp (3 * (δ / Real.sin δ)
          * (ε₁ * (1 + (Real.log (2 / δ)) ^ 2) + δ ^ 2))]
      have h3 : 3 * (ε₁ * (1 + (Real.log (2 / δ)) ^ 2) + δ ^ 2) * δ
          = Real.sin δ * (3 * (δ / Real.sin δ)
            * (ε₁ * (1 + (Real.log (2 / δ)) ^ 2) + δ ^ 2)) := by
        field_simp
      have h2 : zf δ ≤ Real.sin δ
          * (1 + 3 * (δ / Real.sin δ) * (ε₁ * (1 + (Real.log (2 / δ)) ^ 2) + δ ^ 2)) := by
        linarith [hZδ.2, h3.le, h3.ge]
      rw [hAdef]
      calc zf δ ≤ Real.sin δ
            * (1 + 3 * (δ / Real.sin δ) * (ε₁ * (1 + (Real.log (2 / δ)) ^ 2) + δ ^ 2)) := h2
        _ ≤ Real.sin δ * Real.exp (3 * (δ / Real.sin δ)
              * (ε₁ * (1 + (Real.log (2 / δ)) ^ 2) + δ ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 hsinδ.le
        _ = Real.exp (3 * (δ / Real.sin δ)
              * (ε₁ * (1 + (Real.log (2 / δ)) ^ 2) + δ ^ 2)) * Real.sin δ := by ring
    -- the `A`-bound required by `harith`
    have hA : A ≤ 6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4) := by
      have h2 : (0 : ℝ) < ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4 := by
        have : (0 : ℝ) < c / 4 := by linarith
        nlinarith [hε₁]
      rw [hAdef, hlogeq, hδsq]
      nlinarith [hδsin, h2]
    -- positivity
    have hposZ : ∀ t ∈ Set.Ioo (0 : ℝ) ρ, 0 < zf t := fun t ht =>
      hzfpos t ht.1 (le_of_lt (lt_of_lt_of_le ht.2 hρL))
    have hdposZ : 0 < zf ρ := hzfpos ρ hρ hρL
    -- the anchored comparison
    have hmain := modulus_anchored (v := zf)
      (w := fun t : ℝ => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t)
        / Inner.inner ℝ (Z t) (Z t))
      (ε := c / 4) (δ := δ) (d := ρ) (A := A)
      hδpos hδρ (by linarith) hρπ hposZ hdposZ
      (fun t ht => hlogzf t (lt_of_lt_of_le hδpos ht.1) ht.2) hwb hanchor
    -- the ratio bounds
    set R : ℝ := Real.tan (ρ / 2) / Real.tan (δ / 2) with hRdef
    have hrat : 1 ≤ Real.tan (ρ / 2) / Real.tan (Real.sqrt (c / 4) / 2) ∧
        Real.tan (ρ / 2) / Real.tan (Real.sqrt (c / 4) / 2) ≤ 8 / c :=
      tan_ratio_bounds (c := c) (ρ := ρ) hc hc1 hρ hρL hcase
    have hR1 : 1 ≤ R := by
      rw [hRdef]
      have := hrat.1
      rwa [← hδdef] at this
    have hR2 : R ≤ 8 / c := by
      rw [hRdef]
      have := hrat.2
      rwa [← hδdef] at this
    have hsin0 : 0 ≤ Real.sin ρ := Real.sin_nonneg_of_nonneg_of_le_pi hρ.le hρπ.le
    have hsin1 : Real.sin ρ ≤ 1 := Real.sin_le_one ρ
    have harith' := harith (A := A) (R := R) (s := Real.sin ρ) hA hR2 hR1 hsin0 hsin1
    calc zf ρ ≤ Real.exp A * Real.sin ρ * R ^ (c / 4) := hmain
      _ = Real.exp A * R ^ (c / 4) * Real.sin ρ := by ring
      _ ≤ Real.sin ρ + 40 * (Real.sqrt c + ε₁ * Real.pi) := harith'

/-- **The Rauch bound for the derivative of the geodesic-sphere map.**

Assembled from the three solved inputs: `Work.Diff.C.geoCrux.cut_inject` (`InjAtLeast` up to
`π - arccos (1-c)`), `Work.Diff.C.geoCrux.radial_modulus` (the modulus of the radial variation field
`Z t = ∂_r GExp q (t • (v + r • w))|_0` is `sin t` up to the additive error
`3 (ε₁ (1 + log(2/t)²) + t²) t`) and the arithmetic input `Work.Diff.C.geoCrux.rauch_arith`; the
actual reduction lives in `rauch_sphere_map_core` above. -/
theorem rauch_sphere_map : Work.Diff.C.GeoCrux.RauchSphereMapProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q ρ hρ hρle v w hv hw hvw
  refine rauch_sphere_map_core (E := E) (H := H) (I := I) (M := M) (hmet := hmet)
    (htor := htor) (hc := hc) (hc1 := hc1) (hε₁ := hε₁) (hnum2 := hnum2) (hsmC := hsmC)
    (hHess := hHess) (hcont := hcont) (hgrad := hgrad) (hdiam := hdiam)
    (hInj := ?_) (hmod := ?_) (harith := ?_) (q := q) (ρ := ρ) (hρ := hρ) (hρle := hρle)
    (v := v) (w := w) (hv := hv) (hw := hw) (hvw := hvw)
  · intro q
    exact Work.Diff.C.geoCrux.cut_inject (E := E) (H := H) (I := I) (M := M) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad hdiam q
  · intro q v w hv hw hvw t ht
    exact Work.Diff.C.geoCrux.radial_modulus (E := E) (H := H) (I := I) (M := M) hmet htor hc
      hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q v w hv hw hvw t ht
  · intro A R s hA hR hR1 hs0 hs1
    exact Work.Diff.C.geoCrux.rauch_arith_alt hc hc1 hε₁ hnum2 hs0 hs1 hA hR hR1

end Work.Diff.C.geoCrux
