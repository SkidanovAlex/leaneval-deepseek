import Submission.Model
import Submission.ModelCore
import Submission.ModelFlowCont
import Submission.ModelVarFrechet
import Submission.ModelVarConv
import Submission.ModelDerivId
import Submission.ModelJacobi
import Submission.ModelJacLin
import Submission.ModelUniq
import Submission.ModelExp
import Submission.ModelAlg
import Submission.ModelScale
import Submission.ModelSpeed
import Submission.ModelGauss
import Submission.ExpCore
import Submission.DiffeoInv
import Submission.MinimalityWrap
import Submission.ModelExpDiffeo2
import Submission.ModelExpC1
import Submission.ModelNormalBall
import Mathlib

/-!
# Geodesic-certified normal ball at the model level (interface for ChartNormal)

Task: prove `model_normal_geodesic` (rigid statement; do not alter).  It refines
`Submission.Model.model_normal_ball` with **certified radial geodesics**: for a C³ symmetric
positive-definite invertible metric family `g`, a base point `x₀` and an *arbitrary* positive
`δa`, it returns a radius `ρ`, a flow `Φ` of the geodesic field on the radius-2 data ball over
`Ioo (-ρ) ρ`, an exposed flow-time `τe > 0` with `τe ≤ ρ`, and an exponential map `exp` such that

* `exp 0 = x₀`, `ContDiffOn ℝ 1 exp (ball 0 ρ)`, `HasFDerivAt exp id 0`;
* the flow formula `exp v = (Φ (x₀, (1 / τe) • v) τe).1` holds for every `v ∈ ball 0 ρ`;
* `exp` restricts to a C¹ diffeomorphism of an open `U ∋ 0` onto an open `V ∋ x₀`
  (`U,V` returned open, with C¹ inverse `inv` on `V`), and the **staying-curve minimality**:
  every C¹ curve `c : [0,1] → E` from `x₀` to `exp v` that stays inside `V` has
  `Real.sqrt ((g x₀) v v) ≤ mgLength g c 0 1` (for all `v ∈ U`);
* for every `v ∈ ball 0 ρ` a **certified radial geodesic** `(cv, velv)` on the unit interval:
  `cv 0 = x₀`, `cv 1 = exp v`, `HasDerivAt cv (velv t) t` for all `t ∈ Icc 0 1`, constant
  metric speed `Real.sqrt ((g (cv t)) (velv t) (velv t)) = Real.sqrt ((g x₀) v v)`, staying
  inside `ball x₀ δa`, and `cv` is C¹ on an open set containing `[0,1]`.

## Proof

Copy the construction of `model_normal_ball` (internal flow `Φ` on `closedBall (x₀,0) 1` from
`flow_unit_ball_cont`, internal exp-time `τ`, `exp := expOf x₀ Φ τ`, C¹/diffeomorphism data via
`c1_local_inverse_ball`, radial-Gauss bound and minimality via `radial_minimality`, then a merged
flow `Φm` on the radius-2 data ball over the window `Icc (-T) T`).  Choose the *exposed* time
`τe := min (min (τ * δc / 4) (δa / 4)) (T / 4)` and return `ρ := τe`; then the formula is proved
by the geodesic time-scaling identity (`exp_ray_scaling`) and the geodesic curves are

    cv t   := (Φ (x₀, (1/τe) • v) (τe * t)).1
    velv t := τe • (Φ (x₀, (1/τe) • v) (τe * t)).2

whose `HasDerivAt`/speed/staying/C¹ clauses come from the chain rule, `speed_const`, the
all-time closedBall-2 containment of the inner flow, and `contDiffOn_one_iff_derivWithin`.

Keep the name `model_normal_geodesic`; the file must contain no unproved placeholders.
-/

open ContinuousLinearMap
open scoped ContDiff Topology BigOperators
open Set Metric Filter
open MeasureTheory intervalIntegral

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

lemma flow_speed_sq_const (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf) (Φ : E × E → ℝ → E × E)
    (hΦ2 : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    {ε : ℝ} (hε : 0 < ε) (hεTf : ε ≤ Tf)
    {z : E × E} (hz : z ∈ closedBall (x₀, 0) 1) {s : ℝ} (hs : s ∈ Ioo (-ε) ε) :
    (g ((Φ z s).1)) ((Φ z s).2) ((Φ z s).2) = (g ((Φ z 0).1)) ((Φ z 0).2) ((Φ z 0).2) := by
  let c : ℝ → E := fun u => (Φ z u).1
  let vel : ℝ → E := fun u => (Φ z u).2
  have hsplit := split_flow_geodesic g hg hinv (x₀, 0) hTf (closedBall (x₀, 0) 1) Φ hΦ2 (z := z) hz
  have hsub : Ioo (-ε) ε ⊆ Ioo (-Tf) Tf := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2, hεTf]
  have hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t := by
    intro t ht
    exact (hsplit.1 t (hsub ht))
  have hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t := by
    intro t ht
    simpa [c, vel] using (hsplit.2 t (hsub ht))
  have hsp := speed_const g hg hinv hsym (ε := ε) hε (c := c) (v := vel) hc hv
  have hval := const_deriv_value (ε := ε) hε
    (f := fun u : ℝ => (g (c u)) (vel u) (vel u)) (c := (0 : ℝ)) hsp (t := s) hs
  have h0 : (g (c 0)) (vel 0) (vel 0) = (g ((Φ z 0).1)) ((Φ z 0).2) ((Φ z 0).2) := rfl
  simpa [c, vel, h0] using hval

/-- derivative of the reparametrized flow curve -/
lemma flow_reparam_hasDerivAt (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf)
    (Φ : E × E → ℝ → E × E) {z : E × E} (hz : z ∈ closedBall (x₀, 0) 1)
    (hΦ2 : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    {τe t : ℝ} (ht : τe * t ∈ Icc (-Tf) Tf) :
    HasDerivAt (fun u : ℝ => (Φ z (τe * u)).1) (τe • (Φ z (τe * t)).2) t := by
  have h1 : HasDerivAt (Φ z) (odeField g (Φ z (τe * t))) (τe * t) := (hΦ2 z hz).2 (τe * t) ht
  have hlin : HasDerivAt (fun u : ℝ => τe * u) τe t := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) t).const_mul τe)
  have hcomp : HasDerivAt (fun u : ℝ => (Φ z) (τe * u)) (τe • odeField g (Φ z (τe * t))) t := by
    exact h1.scomp (x := t) (h := fun u : ℝ => τe * u) (h' := τe) hlin
  have hf := hcomp.hasFDerivAt.fst.hasDerivAt
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, odeField,
    smul_smul] using hf

/-- squared metric speed of the reparametrized radial curve equals (g x₀) v v -/
lemma flow_curve_speed (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf) (Φ : E × E → ℝ → E × E)
    (hΦ2 : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    {τe : ℝ} (hτe : 0 < τe) (hτeTf : τe < Tf)
    {v : E} (hv : ‖v‖ ≤ τe) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    (g ((Φ (x₀, τe⁻¹ • v) (τe * t₀)).1))
      (τe • (Φ (x₀, τe⁻¹ • v) (τe * t₀)).2)
      (τe • (Φ (x₀, τe⁻¹ • v) (τe * t₀)).2) = (g x₀) v v := by
  let z : E × E := (x₀, τe⁻¹ • v)
  have hz : z ∈ closedBall (x₀, 0) 1 := by
    simpa [z] using slice_data_mem x₀ τe hτe hv
  have hs : τe * t₀ ∈ Ioo (-Tf) Tf := by
    have ht₀l : 0 ≤ τe * t₀ := mul_nonneg (le_of_lt hτe) (mem_Icc.mp ht₀).1
    have ht₀r : τe * t₀ ≤ τe := by
      have ht1 : t₀ ≤ 1 := (mem_Icc.mp ht₀).2
      nlinarith [hτe]
    constructor <;> nlinarith [ht₀l, ht₀r, hτeTf]
  have hconst := flow_speed_sq_const g hg hinv hsym x₀ (Tf := Tf) hTf Φ hΦ2 (ε := Tf) hTf le_rfl
    (z := z) hz (s := τe * t₀) hs
  have hz0 : (Φ z 0) = z := (hΦ2 z hz).1
  have hz0fst : (Φ z 0).1 = x₀ := by simpa [z] using congrArg Prod.fst hz0
  have hz0snd : (Φ z 0).2 = τe⁻¹ • v := by simpa [z] using congrArg Prod.snd hz0
  have hmain : (g ((Φ z (τe * t₀)).1))
      (τe • (Φ z (τe * t₀)).2) (τe • (Φ z (τe * t₀)).2) = (g x₀) v v := by
    rw [bilin_smul_left (g ((Φ z (τe * t₀)).1)) τe ((Φ z (τe * t₀)).2)
      (τe • (Φ z (τe * t₀)).2)]
    rw [bilin_smul_right (g ((Φ z (τe * t₀)).1)) τe ((Φ z (τe * t₀)).2)
      ((Φ z (τe * t₀)).2)]
    rw [hconst]
    simp [hz0fst, hz0snd]
    field_simp [ne_of_gt hτe]
  simpa [z] using hmain

/-- the first component of a flow starting in closedBall (x₀,0) 1 stays within distance 2·τe of x₀ -/
lemma flow_curve_stay (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf)
    (Φ : E × E → ℝ → E × E) {z : E × E} (hz : z ∈ closedBall (x₀, 0) 1) (hz1 : z.1 = x₀)
    (hΦall : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       ∀ t : ℝ, Φ z t ∈ closedBall (x₀, 0) 2)
    {τe : ℝ} (hτe : 0 < τe) (hτeTf : τe < Tf) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    ‖(Φ z (τe * t₀)).1 - x₀‖ ≤ 2 * τe := by
  let q : ℝ → E := fun u => (Φ z u).1
  have hq0 : q 0 = x₀ := by simpa [q, hz1] using congrArg Prod.fst (hΦall z hz).1
  have hwin (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (τe * t₀)) : x ∈ Icc (-Tf) Tf := by
    have hx0 : 0 ≤ x := (mem_Icc.mp hx).1
    have hx1 : x ≤ τe * t₀ := (mem_Icc.mp hx).2
    have h1 : τe * t₀ ≤ τe := by
      have ht1 : t₀ ≤ 1 := (mem_Icc.mp ht₀).2
      nlinarith [hτe]
    constructor <;> nlinarith [hx0, hx1, h1, hτeTf]
  have hder (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (τe * t₀)) :
      HasDerivWithinAt q ((Φ z x).2) (Icc (0 : ℝ) (τe * t₀)) x := by
    have hd := (hΦall z hz).2.1 x (hwin x hx)
    have hqder : HasDerivAt q ((Φ z x).2) x := by
      have hf := hd.hasFDerivAt.fst.hasDerivAt
      simpa [q, odeField] using hf
    exact hqder.hasDerivWithinAt
  have hbnd (x : ℝ) (hx : x ∈ Ico (0 : ℝ) (τe * t₀)) : ‖(Φ z x).2‖ ≤ 2 := by
    have hmem : (Φ z x) ∈ closedBall (x₀, 0) 2 := (hΦall z hz).2.2 x
    have hdst : ‖(Φ z x) - (x₀, 0)‖ ≤ 2 := by
      rw [mem_closedBall, dist_eq_norm] at hmem
      simpa using hmem
    calc
      ‖(Φ z x).2‖ = ‖((Φ z x) - (x₀, (0 : E))).2‖ := by simp
      _ ≤ ‖(Φ z x) - (x₀, (0 : E))‖ := norm_snd_le _
      _ ≤ 2 := hdst
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment' (f := q) (f' := fun x => (Φ z x).2)
    (a := (0 : ℝ)) (b := τe * t₀) (C := (2 : ℝ)) hder hbnd (τe * t₀) (by
      have ht0l : 0 ≤ τe * t₀ := mul_nonneg (le_of_lt hτe) (mem_Icc.mp ht₀).1
      constructor <;> linarith)
  have hstep : τe * t₀ ≤ τe := by
    have ht1 : t₀ ≤ 1 := (mem_Icc.mp ht₀).2
    nlinarith [hτe]
  have hqval : q (τe * t₀) = (Φ z (τe * t₀)).1 := rfl
  rw [hqval, hq0] at hmain
  nlinarith [hmain, hstep]

/-- the reparametrized radial curve is C¹ on Ioo (-2) 2 -/
lemma flow_curve_contDiffOn (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf)
    (Φ : E × E → ℝ → E × E) {z : E × E} (hz : z ∈ closedBall (x₀, 0) 1)
    (hΦ2 : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    {τe : ℝ} (hτe : 0 < τe) (h2τe : 2 * τe ≤ Tf) :
    ContDiffOn ℝ 1 (fun u : ℝ => (Φ z (τe * u)).1) (Ioo (-2) 2) := by
  let cv : ℝ → E := fun u => (Φ z (τe * u)).1
  let velv : ℝ → E := fun u => τe • (Φ z (τe * u)).2
  have hwin (t : ℝ) (ht : t ∈ Ioo (-2) 2) : τe * t ∈ Icc (-Tf) Tf := by
    have h1 : |t| < 2 := abs_lt.mpr ht
    have h2 : |τe * t| ≤ |τe| * |t| := (abs_mul τe t).le
    have h3 : |τe| * |t| ≤ |τe| * 2 := mul_le_mul_of_nonneg_left (le_of_lt h1) (abs_nonneg τe)
    have h4 : |τe| * 2 = 2 * τe := by rw [abs_of_pos hτe]; ring
    have habs : |τe * t| ≤ Tf := by nlinarith [h2, h3, h4, h2τe]
    exact abs_le.mp habs
  have hdiff (t : ℝ) (ht : t ∈ Ioo (-2) 2) : DifferentiableAt ℝ cv t := by
    have hd := flow_reparam_hasDerivAt g hg hinv x₀ (Tf := Tf) hTf Φ (z := z) hz hΦ2
      (τe := τe) (t := t) (hwin t ht)
    exact hd.differentiableAt
  have hdiffOn : DifferentiableOn ℝ cv (Ioo (-2) 2) := by
    intro t ht
    exact (hdiff t ht).differentiableWithinAt
  have hflow_contAt (t : ℝ) (ht : t ∈ Ioo (-2) 2) : ContinuousAt (fun u : ℝ => Φ z (τe * u)) t := by
    have hc1 : ContinuousAt (fun u : ℝ => τe * u) t := by
      exact (hasDerivAt_id (𝕜 := ℝ) t).const_mul τe |>.continuousAt
    have hc2 : ContinuousAt (Φ z) (τe * t) := by
      have hderiv : HasDerivAt (Φ z) (odeField g (Φ z (τe * t))) (τe * t) :=
        (hΦ2 z hz).2 (τe * t) (hwin t ht)
      exact hderiv.continuousAt
    exact hc2.comp hc1
  have hvelv_contAt (t : ℝ) (ht : t ∈ Ioo (-2) 2) : ContinuousAt velv t := by
    have hcont2 : ContinuousAt (fun u : ℝ => (Φ z (τe * u)).2) t := (hflow_contAt t ht).snd
    have hsmul : ContinuousAt (fun u : ℝ => τe • (Φ z (τe * u)).2) t :=
      hcont2.const_smul τe
    simpa [velv] using hsmul
  have hcontVelv : ContinuousOn velv (Ioo (-2) 2) := by
    intro t ht
    exact (hvelv_contAt t ht).continuousWithinAt
  have hdv (t : ℝ) (ht : t ∈ Ioo (-2) 2) : derivWithin cv (Ioo (-2) 2) t = velv t := by
    have hd := flow_reparam_hasDerivAt g hg hinv x₀ (Tf := Tf) hTf Φ (z := z) hz hΦ2
      (τe := τe) (t := t) (hwin t ht)
    have hd' : deriv cv t = velv t := by simpa [cv, velv] using hd.deriv
    rw [derivWithin_of_isOpen isOpen_Ioo ht]
    exact hd'
  have hcontDeriv : ContinuousOn (fun t => derivWithin cv (Ioo (-2) 2) t) (Ioo (-2) 2) := by
    apply ContinuousOn.congr hcontVelv
    intro t ht
    exact hdv t ht
  have hfinal : ContDiffOn ℝ 1 cv (Ioo (-2) 2) := by
    exact (contDiffOn_one_iff_derivWithin (isOpen_Ioo.uniqueDiffOn (s := Ioo (-2) 2))).2
      ⟨hdiffOn, hcontDeriv⟩
  simpa [cv] using hfinal



theorem model_normal_geodesic (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) (δa : ℝ) (hδa : 0 < δa) :
    ∃ ρ > 0, ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
         ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      ∃ τe > 0, τe ≤ ρ ∧
      ∃ exp : E → E, exp 0 = x₀ ∧
        ContDiffOn ℝ 1 exp (ball 0 ρ) ∧
        HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 ∧
        (∀ v ∈ ball 0 ρ, exp v = (Φ (x₀, (1 / τe) • v) τe).1) ∧
        (∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 x₀,
           IsOpen U ∧ IsOpen V ∧
           Set.MapsTo exp U V ∧ Function.Injective (fun v : U => exp v.1) ∧
           Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
           ∃ inv : E → E,
             (∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y) ∧
             (∀ v ∈ U, inv (exp v) = v) ∧
             ContDiffOn ℝ 1 inv V ∧
             (∀ v ∈ U, ∀ c : ℝ → E,
                c 0 = x₀ → c 1 = exp v →
                (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
                (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ V) →
                Real.sqrt ((g x₀) v v) ≤ mgLength g c 0 1)) ∧
        -- geodesic radial curves, staying inside `ball x₀ δa`:
        (∀ v ∈ ball 0 ρ, ∃ cv velv : ℝ → E,
           cv 0 = x₀ ∧ cv 1 = exp v ∧
           (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt cv (velv t) t) ∧
           (∀ t ∈ Icc (0 : ℝ) 1,
              Real.sqrt ((g (cv t)) (velv t) (velv t)) = Real.sqrt ((g x₀) v v)) ∧
           (∀ t ∈ Icc (0 : ℝ) 1, cv t ∈ ball x₀ δa) ∧
           (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 cv O)) := by
  classical
  let z₀ : E × E := (x₀, 0)
  rcases geodesic_flow g hg hinv z₀ with ⟨Tg, hTg, Cg, hCg0, Φg, hΦgall⟩
  rcases hΦgall with ⟨hΦg2, hΦgtimelip, hΦgtaylor⟩
  rcases flow_unit_ball_cont g hg hinv z₀ with ⟨Tf, hTf, Lf, Φ, hΦall, hLip⟩
  rcases field_fderiv_bound g hg hinv z₀ 2 (by norm_num) with ⟨K0, hK0, hK⟩
  rcases flow_map_contDiffOn g hg hinv z₀ Tf hTf Lf Φ hΦall hLip with
    ⟨τc, hτcpos, hτcle, δc, hδcpos, hδcle, hCdiff, hDcont⟩
  -- sum bound for the finitely many basis-vector norms (used for the smallness constraint)
  let S : ℝ := Finset.univ.sum (fun i : Fin (Module.finrank ℝ (E × E)) =>
    (‖Module.finBasis ℝ (E × E) i‖ + 1))
  have hS0 : 0 ≤ S := Finset.sum_nonneg (by intro i hi; positivity)
  let M : ℝ := S + 1
  have hMpos : 0 < M := by dsimp [M]; linarith
  have hKp : 0 < K0 + 1 := by linarith
  have hBM (i : Fin (Module.finrank ℝ (E × E))) :
      ‖Module.finBasis ℝ (E × E) i‖ + 1 ≤ M := by
    dsimp [M]
    have h1 : ‖Module.finBasis ℝ (E × E) i‖ + 1 ≤ S := by
      dsimp [S]
      refine Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin (Module.finrank ℝ (E × E)) => ‖Module.finBasis ℝ (E × E) j‖ + 1) ?_ ?_
      · intro j hj
        positivity
      · simp
    linarith
  let τ : ℝ := min τc (1 / (8 * (K0 + 1) * M))
  have hden : 0 < 8 * (K0 + 1) * M := by
    have h1 : 0 < K0 + 1 := hKp
    positivity
  have hτpos : 0 < τ := by
    dsimp [τ]
    exact lt_min hτcpos (one_div_pos.mpr hden)
  have hτleτc : τ ≤ τc := by dsimp [τ]; exact min_le_left _ _
  have hτTf4 : 4 * τ ≤ Tf := by
    have h2 : τ ≤ τc := hτleτc
    nlinarith [hτcle]
  have hτTf : τ < Tf := by
    have h2 : τ ≤ τc := hτleτc
    nlinarith [hτcle, hTf]
  have hUb : ∀ i : Fin (Module.finrank ℝ (E × E)),
      4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τ ≤ 1 := by
    intro i
    have hb : ‖Module.finBasis ℝ (E × E) i‖ + 1 ≤ M := hBM i
    have hτle : τ ≤ 1 / (8 * (K0 + 1) * M) := by
      dsimp [τ]
      exact min_le_right _ _
    have hnonneg : 0 ≤ 4 * (K0 + 1) * M := by positivity
    have hm : 4 * (K0 + 1) * (‖Module.finBasis ℝ (E × E) i‖ + 1) * τ
        ≤ 4 * (K0 + 1) * M * τ := by gcongr
    have hm2 : 4 * (K0 + 1) * M * τ ≤ 1 := by
      calc
        4 * (K0 + 1) * M * τ ≤ 4 * (K0 + 1) * M * (1 / (8 * (K0 + 1) * M)) :=
          mul_le_mul_of_nonneg_left hτle hnonneg
        _ = 1 / 2 := by
          field_simp [ne_of_gt hKp, ne_of_gt hMpos]
          ring
        _ ≤ 1 := by norm_num
    exact le_trans hm hm2
  let exp : E → E := expOf x₀ Φ τ
  have hΦ2 : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    exact ⟨(hΦall z hz).1, (hΦall z hz).2.1⟩
  have hρEpos : 0 < τ * δc / 2 := by positivity
  have hExpC1 : ContDiffOn ℝ 1 exp (ball 0 (τ * δc / 2)) := by
    dsimp [exp]
    exact exp_contDiffOn_ball g hg hinv x₀ Φ (τ := τ) (τc := τc) (δc := δc) hCdiff hδcpos
      hτpos hτleτc
  have hExpId : HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 := by
    dsimp [exp]
    exact expOf_hasFDerivAt_id g hg hinv x₀ hTf Φ hΦ2 (τ := τ) (ρ := τ * δc / 2) hτpos hτTf
      hρEpos hExpC1
  rcases exp_fderiv_invertible_on x₀ exp (ρE := τ * δc / 2) hρEpos hExpC1 hExpId with
    ⟨ρi, hρi, hρiE, hInvd⟩
  let ρS : ℝ := min (min ρi (τ / 8)) (τ * δc / 2)
  have hρSpos : 0 < ρS := by dsimp [ρS]; positivity
  have hρSle_i : ρS ≤ ρi := by dsimp [ρS]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρSle_E : ρS ≤ τ * δc / 2 := by dsimp [ρS]; exact min_le_right _ _
  have hρSle_τ : ρS ≤ τ / 8 := by dsimp [ρS]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hExpC1S : ContDiffOn ℝ 1 exp (ball 0 ρS) := hExpC1.mono (ball_subset_ball hρSle_E)
  have hInvdS : ∀ v ∈ ball 0 ρS, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ exp v := by
    intro v hv
    exact hInvd v (ball_subset_ball hρSle_i hv)
  have hExp0 : exp 0 = x₀ := by
    dsimp [exp]
    have hτmem : τ ∈ Ioo (-Tf) Tf := by constructor <;> linarith
    have hrest := flow_rest_point g hg hinv hTf (x₀ := x₀) (Φ := Φ) hΦ2 τ hτmem
    simpa [expOf] using congrArg Prod.fst hrest
  rcases c1_local_inverse_ball (x₀ := x₀) exp (ρE := ρS) hρSpos hExpC1S hExp0 hExpId hInvdS with
    ⟨U, hU_nhds, hU_open, hU_ball, V, hV_nhds, hV_open, hVeq, inv, hMapsTo, hInj, hSurj, hContU,
      hInv1, hInv2, hContDiffInv⟩
  have hU0 : (0 : E) ∈ U := mem_of_mem_nhds hU_nhds
  have hVx0 : x₀ ∈ V := mem_of_mem_nhds hV_nhds
  let F : E → ℝ := fun z : E => Real.sqrt ((g x₀) (inv z) (inv z))
  have hFdiff : ∀ y ∈ V, y ≠ x₀ → DifferentiableAt ℝ F y := by
    intro y hyV hyne
    have hc1 : ContDiffAt ℝ 1 inv y := by
      rw [hV_open.contDiffOn_iff] at hContDiffInv
      exact hContDiffInv hyV
    have hinv0 : inv y ≠ 0 := by
      intro hz
      apply hyne
      have hy' : exp (inv y) = y := (hInv1 y hyV).2
      rw [← hy', hz, hExp0]
    have hposval : 0 < ((g x₀) (inv y)) (inv y) := by
      exact hpos x₀ (inv y) hinv0
    have hd := radialComp_differentiableAt (B := g x₀) (inv := inv) y hc1 hposval
    simpa [F] using hd
  have hFcont : ContinuousOn F V := by
    intro y hyV
    have hc1 : ContDiffAt ℝ 1 inv y := by
      rw [hV_open.contDiffOn_iff] at hContDiffInv
      exact hContDiffInv hyV
    have hc : ContinuousAt (fun z : E => Real.sqrt ((g x₀) (inv z) (inv z))) y :=
      radialComp_continuousAt (B := g x₀) (inv := inv) y hc1.continuousAt
    have hc' : ContinuousAt F y := by simpa [F] using hc
    exact hc'.continuousWithinAt
  -- radial clause: |fderiv F y X| ≤ mgSpeed g y X
  have hFb : ∀ y ∈ V, y ≠ x₀ → ∀ X : E, ‖(fderiv ℝ F y) X‖ ≤ mgSpeed g y X := by
    intro y hyV hyne X
    have hvU : inv y ∈ U := (hInv1 y hyV).1
    have hvexp : exp (inv y) = y := (hInv1 y hyV).2
    let v : E := inv y
    have hvb : v ∈ ball (0 : E) ρS := hU_ball hvU
    have hvexp' : exp v = y := by simpa [v] using hvexp
    have hvne : v ≠ 0 := by
      intro hz
      apply hyne
      rw [← hvexp', hz]
      exact hExp0
    have hvin : (x₀, τ⁻¹ • v) ∈ ball (x₀, 0) (1 / 4) := by
      have hvS : ‖v‖ < ρS := by
        have hd : dist v 0 < ρS := mem_ball.mp hvb
        simpa [dist_eq_norm] using hd
      have hvlt : ‖v‖ < τ / 8 := lt_of_lt_of_le hvS hρSle_τ
      rw [mem_ball, dist_eq_norm]
      have hnorm : ‖(x₀, τ⁻¹ • v) - (x₀, 0)‖ = ‖τ⁻¹ • v‖ := by simp
      rw [hnorm]
      have hposτ : 0 < τ⁻¹ := by positivity
      have hsmul : ‖τ⁻¹ • v‖ ≤ τ⁻¹ * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hposτ)]
      have h2 : τ⁻¹ * ‖v‖ < 1 / 4 := by
        have hle : τ⁻¹ * ‖v‖ < τ⁻¹ * (τ / 8) :=
          mul_lt_mul_of_pos_left hvlt hposτ
        have hstep : τ⁻¹ * (τ / 8) = 1 / 8 := by
          field_simp [ne_of_gt hτpos]
        rw [hstep] at hle
        linarith
      exact lt_of_le_of_lt hsmul h2
    rcases fderiv_exp_surj (ρ := ρS) hρSpos v hvb hInvdS X with ⟨W, hXW⟩
    let R : E → ℝ := fun z : E => Real.sqrt ((g x₀) z z)
    have hFR : ∀ x ∈ U, F (exp x) = R x := by
      intro x hxU
      dsimp [F, R]
      rw [hInv2 x hxU]
    have hFyD : DifferentiableAt ℝ F (exp v) := by
      have hyE : exp v ≠ x₀ := by rw [hvexp']; exact hyne
      have hmem : exp v ∈ V := by rw [hvexp']; exact hyV
      exact hFdiff (exp v) hmem hyE
    have hExpD : DifferentiableAt ℝ exp v := by
      have hcv : ContDiffAt ℝ 1 exp v := hExpC1S.contDiffAt (Metric.isOpen_ball.mem_nhds hvb)
      exact hcv.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have hRD : DifferentiableAt ℝ R v := by
      have hd := radialComp_differentiableAt (B := g x₀) (inv := fun z : E => z) v
        (by
          have hcv : ContDiffAt ℝ 1 (fun z : E => z) v := (contDiff_id : ContDiff ℝ 1 (fun z : E => z)).contDiffAt
          exact hcv) (by simpa using hpos x₀ v hvne)
      simpa [R] using hd
    have hdcomp := fderiv_comp_eq_on_open (F := F) (R := R) (exp := exp) (U := U) hU_open hvU
      hFR hFyD hExpD hRD
    have hval : (fderiv ℝ F y) X = (fderiv ℝ R v) W := by
      calc
        (fderiv ℝ F y) X = (fderiv ℝ F (exp v)) ((fderiv ℝ exp v) W) := by rw [← hvexp', hXW]
        _ = ((fderiv ℝ F (exp v)).comp (fderiv ℝ exp v)) W := rfl
        _ = (fderiv ℝ R v) W := by rw [hdcomp]
    have hb := radial_bound_main g hg hinv hsym hpos x₀ (Tf := Tf) hTf (Lf := Lf) (Φ := Φ)
      hΦall hLip (K0 := K0) hK0 hK (δ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      (τ := τ) hτpos hτTf4 hUb (v := v) (W := W) hvin hvne
    have hbX : ‖(fderiv ℝ R v) W‖ ≤ Real.sqrt ((g y) X X) := by
      have h1 : ‖(fderiv ℝ R v) W‖ ≤
          Real.sqrt ((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W)
            ((fderiv ℝ (expOf x₀ Φ τ)) v W)) := by
        simpa [R] using hb
      have heqv : exp v = expOf x₀ Φ τ v := by rfl
      have hXeq : (fderiv ℝ (expOf x₀ Φ τ)) v W = X := by
        simpa [exp] using hXW
      have hyeq : expOf x₀ Φ τ v = y := by rw [← heqv]; exact hvexp'
      rw [hXeq] at h1
      rw [hyeq] at h1
      simpa using h1
    have hmain : ‖(fderiv ℝ F y) X‖ ≤ Real.sqrt ((g y) X X) := by
      rw [hval]
      exact hbX
    simpa [mgSpeed] using hmain
  -- hypotheses for the generic minimality wrapper (expressed via radialCoord)
  have hFeq : (radialCoord g x₀ inv) = F := by
    funext z
    simp [F, radialCoord]
  have hFRC_cont : ContinuousOn (radialCoord g x₀ inv) V := by
    simpa [hFeq] using hFcont
  have hFRC_diff : ∀ y ∈ V, y ≠ x₀ → DifferentiableAt ℝ (radialCoord g x₀ inv) y := by
    intro y hy hne
    have hd := hFdiff y hy hne
    simpa [hFeq] using hd
  have hFRC_b : ∀ y ∈ V, y ≠ x₀ → ∀ X : E,
      ‖(fderiv ℝ (radialCoord g x₀ inv) y) X‖ ≤ mgSpeed g y X := by
    intro y hy hne X
    have hd := hFb y hy hne X
    simpa [hFeq] using hd
  have hinj0 : ∀ v ∈ U, exp v = x₀ → v = 0 := by
    intro v hvU hx0
    have h0U' : (0 : E) ∈ U := hU0
    have heq : exp v = exp (0 : E) := by simpa [hExp0] using hx0
    have hsub : (⟨v, hvU⟩ : U) = ⟨(0 : E), h0U'⟩ := hInj (by simpa using heq)
    exact congrArg Subtype.val hsub
  have hMin : ∀ v ∈ U, ∀ c : ℝ → E,
      c 0 = x₀ → c 1 = exp v →
      (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
      (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ V) →
      Real.sqrt ((g x₀) v v) ≤ mgLength g c 0 1 := by
    intro v hvU c hc0 hc1 hO hcV
    exact radial_minimality g hg hinv hsym hpos x₀ (exp := exp) (inv := inv) (U := U) (V := V)
      hExp0 hU0 hInv2 hinj0 hVx0 hFRC_cont hFRC_diff hFRC_b v hvU c hc0 hc1 hO hcV
  -- the radial clause in the exact statement form
  have hRad : ∀ y ∈ V, y ≠ x₀ → ∀ X : E,
      ‖(fderiv ℝ (fun z : E => Real.sqrt ((g x₀) (inv z) (inv z))) y) X‖ ≤
        Real.sqrt ((g y) X X) := by
    intro y hy hne X
    have hd := hFb y hy hne X
    simpa [F, mgSpeed] using hd
  -- merged flow over the radius-2 data ball
  let T : ℝ := min Tf Tg
  have hTpos : 0 < T := by dsimp [T]; exact lt_min hTf hTg
  let Φm : E × E → ℝ → E × E := fun z t =>
    if hz1 : z ∈ closedBall (x₀, 0) 1 then Φ z t
    else if hz2 : z ∈ closedBall (x₀, 0) 2 then Φg z t
    else (exp (t • z.2), 0)
  have hTleTf : T ≤ Tf := by dsimp [T]; exact min_le_left _ _
  have hTleTg : T ≤ Tg := by dsimp [T]; exact min_le_right _ _
  have hΦm2 : ∀ z ∈ closedBall (x₀, 0) 2, Φm z 0 = z ∧
      ∀ t ∈ Icc (-T) T, HasDerivAt (Φm z) (odeField g (Φm z t)) t := by
    intro z hz
    by_cases hz1 : z ∈ closedBall (x₀, 0) 1
    · have hfun : Φm z = Φ z := by
        funext s
        dsimp [Φm]
        rw [if_pos hz1]
      constructor
      · rw [hfun]
        exact (hΦall z hz1).1
      · intro t ht
        have ht' : t ∈ Icc (-Tf) Tf := by
          constructor <;> nlinarith [ht.1, ht.2, hTleTf]
        rw [hfun]
        exact (hΦall z hz1).2.1 t ht'
    · have hz2 : z ∈ closedBall (x₀, 0) 2 := hz
      have hfun : Φm z = Φg z := by
        funext s
        dsimp [Φm]
        rw [if_neg hz1, if_pos hz2]
      constructor
      · rw [hfun]
        exact (hΦg2 z hz2).1
      · intro t ht
        have ht' : t ∈ Icc (-Tg) Tg := by
          constructor <;> nlinarith [ht.1, ht.2, hTleTg]
        rw [hfun]
        exact (hΦg2 z hz2).2 t ht'
  have hrestτ : Φ (x₀, 0) τ = (x₀, 0) := by
    have hτmem : τ ∈ Ioo (-Tf) Tf := by constructor <;> linarith
    exact flow_rest_point g hg hinv hTf (x₀ := x₀) (Φ := Φ) hΦ2 τ hτmem

  -- exposed flow-time τe and the returned radius
  let τe : ℝ := min (min (τ * δc / 4) (δa / 4)) (T / 4)
  have h1p : 0 < τ * δc / 4 := div_pos (mul_pos hτpos hδcpos) (by norm_num)
  have h2p : 0 < δa / 4 := div_pos hδa (by norm_num)
  have h3p : 0 < T / 4 := div_pos hTpos (by norm_num)
  have hτepos : 0 < τe := by dsimp [τe]; exact lt_min (lt_min h1p h2p) h3p
  have hτe_le_τδ4 : τe ≤ τ * δc / 4 := by
    dsimp [τe]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hτe_le_δ4 : τe ≤ δa / 4 := by
    dsimp [τe]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hτe_le_T4 : τe ≤ T / 4 := by
    dsimp [τe]
    exact min_le_right _ _
  have hτe_le_τ : τe ≤ τ := by
    have h1 : τ * δc / 4 ≤ τ * (1 / 8) / 4 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hδcle (le_of_lt hτpos)) (by norm_num : (0 : ℝ) ≤ 4)
    have h2 : τ * (1 / 8) / 4 ≤ τ := by
      have hposτ4 : 0 ≤ τ * (1 / 8) / 4 := by positivity
      nlinarith
    exact le_trans (le_trans hτe_le_τδ4 h1) h2
  have h2τe_Tf : 2 * τe ≤ Tf := by
    have h1 : τe ≤ T / 4 := hτe_le_T4
    nlinarith [h1, hTleTf, hTf]
  have hτe_Tf : τe < Tf := by nlinarith [h2τe_Tf, hTf]
  have hτe_δ : 2 * τe < δa := by
    have h1 : 2 * τe ≤ δa / 2 := by
      have hτeδ : τe ≤ δa / 4 := hτe_le_δ4
      nlinarith
    nlinarith [hδa]
  let ρ : ℝ := τe
  have hρpos : 0 < ρ := by dsimp [ρ]; exact hτepos
  have hρT : ρ ≤ T := by
    dsimp [ρ]
    exact le_trans hτe_le_T4 (by nlinarith [hTpos])
  have hΦmflow : ∀ z ∈ closedBall (x₀, 0) 2, Φm z 0 = z ∧
      ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (Φm z) (odeField g (Φm z t)) t := by
    intro z hz
    constructor
    · exact (hΦm2 z hz).1
    · intro t ht
      have ht' : t ∈ Icc (-T) T := by
        constructor <;> linarith [ht.1, ht.2, hρT]
      exact (hΦm2 z hz).2 t ht'
  have hρE_le : ρ ≤ τ * δc / 2 := by
    dsimp [ρ]
    have hle : τ * δc / 4 ≤ τ * δc / 2 := by
      have hnon : 0 ≤ τ * δc := mul_nonneg (le_of_lt hτpos) (le_of_lt hδcpos)
      nlinarith
    exact le_trans hτe_le_τδ4 hle
  have hExpC1ρ : ContDiffOn ℝ 1 exp (ball (0 : E) ρ) := by
    exact hExpC1.mono (ball_subset_ball hρE_le)
  have hz1_of (v : E) (hv : v ∈ ball (0 : E) ρ) : (x₀, (1 / τe) • v) ∈ closedBall (x₀, 0) 1 := by
    have hvle : ‖v‖ ≤ τe := by
      have hlt : ‖v‖ < ρ := by simpa [dist_eq_norm] using (mem_ball.mp hv)
      dsimp [ρ] at hlt
      exact le_of_lt hlt
    have hz := slice_data_mem x₀ τe hτepos hvle
    have heq : (x₀, (1 / τe) • v) = (x₀, τe⁻¹ • v) := by
      congr 1
      simp [one_div]
    simpa [heq] using hz
  have hFormula : ∀ v ∈ ball (0 : E) ρ,
      exp v = (Φm (x₀, (1 / τe) • v) τe).1 := by
    intro v hv
    have hvle : ‖v‖ ≤ τe := by
      have hlt : ‖v‖ < ρ := by simpa [dist_eq_norm] using (mem_ball.mp hv)
      dsimp [ρ] at hlt
      exact le_of_lt hlt
    have hw : ‖τe⁻¹ • v‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ τe⁻¹)]
      have hm : τe⁻¹ * ‖v‖ ≤ τe⁻¹ * τe :=
        mul_le_mul_of_nonneg_left hvle (by positivity : 0 ≤ τe⁻¹)
      have h1 : τe⁻¹ * τe = 1 := by field_simp [ne_of_gt hτepos]
      nlinarith
    have hz : (x₀, τe⁻¹ • v) ∈ closedBall (x₀, 0) 1 :=
      mem_pair_ball x₀ 1 (by norm_num) (τe⁻¹ • v) hw
    let a : ℝ := τe / τ
    have ha_abs : |a| ≤ 1 := by
      dsimp [a]
      rw [abs_div, abs_of_pos hτepos, abs_of_pos hτpos]
      rw [div_le_iff₀ hτpos]
      simpa using hτe_le_τ
    have ha0 : a ≠ 0 := by
      dsimp [a]
      exact div_ne_zero (ne_of_gt hτepos) (ne_of_gt hτpos)
    have ht : τ ∈ Ioo (-Tf) Tf := by constructor <;> linarith
    have hsc := exp_ray_scaling g hg hinv x₀ (T := Tf) hTf Φ
      (by intro z hz; exact ⟨(hΦall z hz).1, (hΦall z hz).2.1⟩)
      (τe⁻¹ • v) hw (a := a) ha_abs ha0 (t := τ) ht
    have hconv : (x₀, a • (τe⁻¹ • v)) = (x₀, τ⁻¹ • v) := by
      dsimp [a]
      rw [smul_smul]
      congr 1
      field_simp [ne_of_gt hτpos, ne_of_gt hτepos]
    have hstep1 : exp v = (Φ (x₀, a • (τe⁻¹ • v)) τ).1 := by
      dsimp [exp]
      change (Φ (x₀, τ⁻¹ • v) τ).1 = (Φ (x₀, a • (τe⁻¹ • v)) τ).1
      rw [← hconv]
    have hmul : a * τ = τe := by
      dsimp [a]
      field_simp [ne_of_gt hτpos]
    have hstep2 : (Φ (x₀, τe⁻¹ • v) (a * τ)).1 = (Φ (x₀, τe⁻¹ • v) τe).1 := by
      rw [hmul]
    have hmain1 : exp v = (Φ (x₀, τe⁻¹ • v) τe).1 := by
      rw [hstep1, hsc, hstep2]
    have heq : (x₀, (1 / τe) • v) = (x₀, τe⁻¹ • v) := by
      congr 1
      simp [one_div]
    have hz1' : (x₀, (1 / τe) • v) ∈ closedBall (x₀, 0) 1 := by
      simpa [heq] using hz
    have hfun : Φm (x₀, (1 / τe) • v) τe = Φ (x₀, (1 / τe) • v) τe := by
      dsimp [Φm]
      rw [if_pos hz1']
    have hmain2 : exp v = (Φ (x₀, (1 / τe) • v) τe).1 := by
      rw [← heq] at hmain1
      exact hmain1
    calc
      exp v = (Φ (x₀, (1 / τe) • v) τe).1 := hmain2
      _ = (Φm (x₀, (1 / τe) • v) τe).1 := by rw [← hfun]
  -- geodesic radial curves
  have hGeo : ∀ v ∈ ball (0 : E) ρ, ∃ cv velv : ℝ → E,
      cv 0 = x₀ ∧ cv 1 = exp v ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt cv (velv t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
         Real.sqrt ((g (cv t)) (velv t) (velv t)) = Real.sqrt ((g x₀) v v)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, cv t ∈ ball x₀ δa) ∧
      (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 cv O) := by
    intro v hv
    let z : E × E := (x₀, (1 / τe) • v)
    have hz1 : z ∈ closedBall (x₀, 0) 1 := by simpa [z] using hz1_of v hv
    let cv : ℝ → E := fun t => (Φ z (τe * t)).1
    let velv : ℝ → E := fun t => τe • (Φ z (τe * t)).2
    have hvle : ‖v‖ ≤ τe := by
      have hlt : ‖v‖ < ρ := by simpa [dist_eq_norm] using (mem_ball.mp hv)
      dsimp [ρ] at hlt
      exact le_of_lt hlt
    have hz1' : z.1 = x₀ := by simp [z]
    have hcv0 : cv 0 = x₀ := by
      have hz0 : Φ z 0 = z := (hΦ2 z hz1).1
      simpa [cv, z] using congrArg Prod.fst hz0
    have hcv1 : cv 1 = exp v := by
      have hz1m : (x₀, (1 / τe) • v) ∈ closedBall (x₀, 0) 1 := by simpa [z] using hz1
      have hform := hFormula v hv
      have hfun : Φm (x₀, (1 / τe) • v) τe = Φ (x₀, (1 / τe) • v) τe := by
        dsimp [Φm]
        rw [if_pos hz1m]
      have hcv1' : cv 1 = (Φ z τe).1 := by simpa [cv]
      calc
        cv 1 = (Φ z τe).1 := hcv1'
        _ = (Φ (x₀, (1 / τe) • v) τe).1 := by rfl
        _ = exp v := by rw [← hfun]; exact hform.symm
    have hwin (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : τe * t ∈ Icc (-Tf) Tf := by
      constructor <;> nlinarith [hτe_Tf, (mem_Icc.mp ht).1, (mem_Icc.mp ht).2, hτepos]
    have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt cv (velv t) t := by
      have hd := flow_reparam_hasDerivAt g hg hinv x₀ (Tf := Tf) hTf Φ (z := z) hz1
        (fun z hz => ⟨(hΦall z hz).1, (hΦall z hz).2.1⟩) (τe := τe) (t := t) (hwin t ht)
      simpa [cv, velv] using hd
    have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        Real.sqrt ((g (cv t)) (velv t) (velv t)) = Real.sqrt ((g x₀) v v) := by
      have hsp := flow_curve_speed g hg hinv hsym x₀ (Tf := Tf) hTf Φ
        (fun z hz => ⟨(hΦall z hz).1, (hΦall z hz).2.1⟩) (τe := τe) hτepos
        (by nlinarith [hτe_Tf]) (v := v) hvle (t₀ := t) ht
      have hsp' : (g (cv t)) (velv t) (velv t) = (g x₀) v v := by
        simpa [cv, velv, z, one_div] using hsp
      exact congrArg Real.sqrt hsp'
    have hstay (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : cv t ∈ ball x₀ δa := by
      have hb := flow_curve_stay g hg hinv x₀ (Tf := Tf) hTf Φ (z := z) hz1 hz1'
        (fun z hz => hΦall z hz) (τe := τe) hτepos (by nlinarith [hτe_Tf]) (t₀ := t) ht
      have hb' : ‖(Φ z (τe * t)).1 - x₀‖ ≤ 2 * τe := by simpa using hb
      rw [mem_ball, dist_eq_norm]
      have hc : cv t = (Φ z (τe * t)).1 := rfl
      rw [hc]
      exact lt_of_le_of_lt hb' hτe_δ
    have hcont : ∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 cv O := by
      refine ⟨Ioo (-2) 2, isOpen_Ioo, ?_, ?_⟩
      · intro t ht
        constructor <;> linarith [ht.1, ht.2]
      · have hc := flow_curve_contDiffOn g hg hinv x₀ (Tf := Tf) hTf Φ (z := z) hz1
          (fun z hz => ⟨(hΦall z hz).1, (hΦall z hz).2.1⟩) (τe := τe) hτepos h2τe_Tf
        simpa [cv] using hc
    refine ⟨cv, velv, hcv0, hcv1, ?_, ?_, ?_, hcont⟩
    · intro t ht
      exact hder t ht
    · intro t ht
      exact hspeed t ht
    · intro t ht
      exact hstay t ht
  refine ⟨ρ, hρpos, Φm, hΦmflow, τe, hτepos, ?τle, exp, hExp0, hExpC1ρ, hExpId, hFormula, ?rest⟩
  · dsimp [ρ]
    exact le_rfl
  · refine ⟨⟨U, hU_nhds, V, hV_nhds, hU_open, hV_open, ?_, ?_, ?_, ?_, inv, ?_, ?_, ?_, ?_⟩,
      hGeo⟩
    · exact hMapsTo
    · exact hInj
    · exact hSurj
    · exact hContU
    · intro y hy
      exact hInv1 y hy
    · intro v hv
      exact hInv2 v hv
    · exact hContDiffInv
    · exact hMin




end
end Submission.Model
