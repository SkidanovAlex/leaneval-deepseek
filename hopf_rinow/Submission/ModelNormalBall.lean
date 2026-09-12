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
import Mathlib

/-!
# Genuine normal-ball data at the model level (rigid statement)

Theorem: `Submission.Model.model_normal_ball`.

This module proves the rigid normal-coordinate facts: for a C^3 symmetric positive-definite
invertible metric family `g` on a finite-dimensional normed space `E`, the geodesic-flow
exponential map at `x0` restricts to a C^1 diffeomorphism from a neighbourhood `U` of `0`
onto a neighbourhood `V` of `x0`, with C^1 inverse `inv`; the metric radial coordinate
`F z := sqrt ((g x0) (inv z) (inv z))` has differential bounded by the metric norm
(Gauss bound); and radial geodesics are length-minimising among C^1 curves staying in `V`.
-/

open ContinuousLinearMap
open scoped ContDiff Topology BigOperators
open Set Metric Filter
open MeasureTheory intervalIntegral

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

section PosDef

lemma bilin_pos_sq_nonneg {B : Bilin E} (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (u : E) :
    0 ≤ B u u := by
  by_cases hu : u = 0
  · simp [hu]
  · exact le_of_lt (hpos u hu)

lemma bilin_quad_add_smul {B : Bilin E} (hsym : ∀ u v, B u v = B v u) (u v : E) (t : ℝ) :
    B (u + t • v) (u + t • v) = B u u + 2 * t * B u v + t ^ 2 * B v v := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, pow_two, hsym u v]
  ring

lemma bilin_cauchy_schwarz {B : Bilin E} (hsym : ∀ u v, B u v = B v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (u v : E) :
    |B u v| ≤ Real.sqrt (B u u) * Real.sqrt (B v v) := by
  by_cases hv : v = 0
  · subst v
    simp
  · have hvv : 0 < B v v := hpos v hv
    have huu : 0 ≤ B u u := bilin_pos_sq_nonneg hpos u
    by_cases hu0 : u = 0
    · subst u
      simp
    · have hineq : (B u v) ^ 2 ≤ B u u * B v v := by
        let t : ℝ := -(B u v) / B v v
        by_cases hz : u + t • v = 0
        · have hu : u = -t • v := by
            calc
              u = (u + t • v) - t • v := by abel
              _ = -t • v := by rw [hz]; simp
          have hb : B u v = -t * B v v := by
            calc
              B u v = B (-t • v) v := by rw [hu]
              _ = -t * B v v := by simp
          have hbuu : B u u = t ^ 2 * B v v := by
            calc
              B u u = B (-t • v) (-t • v) := by rw [hu]
              _ = t ^ 2 * B v v := by simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
          have hmain : (B u v) ^ 2 = B u u * B v v := by
            calc
              (B u v) ^ 2 = (-(t * B v v)) ^ 2 := by rw [hb]; ring
              _ = t ^ 2 * (B v v) ^ 2 := by ring
              _ = (t ^ 2 * B v v) * B v v := by ring
              _ = B u u * B v v := by rw [← hbuu]
          exact le_of_eq hmain
        · have hquad : 0 ≤ B (u + t • v) (u + t • v) := le_of_lt (hpos (u + t • v) hz)
          have hq := bilin_quad_add_smul (B := B) hsym u v t
          have hineq0 : 0 ≤ B u u - (B u v) ^ 2 / B v v := by
            rw [hq] at hquad
            have hsub : B u u + 2 * t * B u v + t ^ 2 * B v v = B u u - (B u v) ^ 2 / B v v := by
              dsimp [t]
              field_simp [ne_of_gt hvv]
              ring
            rwa [hsub] at hquad
          have hmul : 0 ≤ (B u u - (B u v) ^ 2 / B v v) * B v v := mul_nonneg hineq0 (le_of_lt hvv)
          have heq : (B u u - (B u v) ^ 2 / B v v) * B v v = B u u * B v v - (B u v) ^ 2 := by
            field_simp [ne_of_gt hvv]
          rw [heq] at hmul
          nlinarith
      have hsq2 : B u u * B v v = (Real.sqrt (B u u) * Real.sqrt (B v v)) ^ 2 := by
        nlinarith [Real.sq_sqrt huu, Real.sq_sqrt (le_of_lt hvv)]
      have hsq : (B u v) ^ 2 ≤ (Real.sqrt (B u u) * Real.sqrt (B v v)) ^ 2 :=
        le_trans hineq (le_of_eq hsq2)
      have habs : |B u v| ≤ |Real.sqrt (B u u) * Real.sqrt (B v v)| := sq_le_sq.mp hsq
      have hnn : 0 ≤ Real.sqrt (B u u) * Real.sqrt (B v v) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rwa [abs_of_nonneg hnn] at habs

lemma bilin_sqrt_pos {B : Bilin E} (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) {v : E} (hv : v ≠ 0) :
    0 < Real.sqrt (B v v) :=
  Real.sqrt_pos.2 (hpos v hv)

lemma bilin_sqrt_eq_zero {B : Bilin E} (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) {v : E}
    (h : Real.sqrt (B v v) = 0) : v = 0 := by
  by_contra hv
  have hpos' : 0 < Real.sqrt (B v v) := bilin_sqrt_pos hpos hv
  linarith

lemma bilin_sqrt_sq {B : Bilin E} (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (v : E) :
    (Real.sqrt (B v v)) ^ 2 = B v v :=
  Real.sq_sqrt (bilin_pos_sq_nonneg hpos v)

end PosDef
/-! ## Inner flow exponential: basic facts -/

section FlowExp

/-- The time-`τ` exponential of a genuine inner flow `Φ` at base point `x₀`. -/
def expOf (x₀ : E) (Φ : E × E → ℝ → E × E) (τ : ℝ) (v : E) : E :=
  (Φ (x₀, τ⁻¹ • v) τ).1

/-- The data point `(x₀, v/τ)` belongs to the radius-1 data ball when `‖v‖ ≤ τ`. -/
lemma slice_data_mem (x₀ : E) (τ : ℝ) (hτ : 0 < τ) {v : E} (hv : ‖v‖ ≤ τ) :
    (x₀, τ⁻¹ • v) ∈ closedBall (x₀, 0) 1 := by
  apply mem_pair_ball x₀ 1 (by norm_num)
  have hposτ : 0 < τ⁻¹ := by positivity
  have hsmul : ‖τ⁻¹ • v‖ = τ⁻¹ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hposτ)]
  have hle : τ⁻¹ * ‖v‖ ≤ τ⁻¹ * τ := mul_le_mul_of_nonneg_left hv (le_of_lt hposτ)
  have hle' : τ⁻¹ * τ = 1 := by field_simp [ne_of_gt hτ]
  calc
    ‖τ⁻¹ • v‖ = τ⁻¹ * ‖v‖ := hsmul
    _ ≤ τ⁻¹ * τ := hle
    _ = 1 := hle'

/-- The radial scaling identity: `exp (s • v) = Φ(x₀, v/τ) (s·τ)` (first component), for the
flow of the geodesic equation with window `±Tf`, whenever the data stay in the radius-1 ball. -/
lemma exp_ray_value (g : E → Bilin E) (hg : ContDiff ℝ 3 g) (hinv : ∀ x, (g x).IsInvertible)
    (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf) (Φ : E × E → ℝ → E × E)
    (hΦ : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    {τ : ℝ} (hτ : 0 < τ) (hτTf : τ < Tf) {v : E} (hv : ‖v‖ ≤ τ) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    expOf x₀ Φ τ (s • v) = (Φ (x₀, τ⁻¹ • v) (s * τ)).1 := by
  by_cases hs0 : s = 0
  · subst s
    have hz : (x₀, τ⁻¹ • v) ∈ closedBall (x₀, 0) 1 := slice_data_mem x₀ τ hτ hv
    have hright : (Φ (x₀, τ⁻¹ • v) 0).1 = x₀ := by
      simpa using congrArg Prod.fst (hΦ (x₀, τ⁻¹ • v) hz |>.1)
    have hτmem : τ ∈ Ioo (-Tf) Tf := by constructor <;> linarith
    have hrest := flow_rest_point g hg hinv hTf (x₀ := x₀) (Φ := Φ) hΦ τ hτmem
    have hleft : (Φ (x₀, 0) τ).1 = x₀ := by simpa using congrArg Prod.fst hrest
    simp [expOf]
    rw [hleft, hright]
  · let w : E := τ⁻¹ • v
    have hw : ‖w‖ ≤ 1 := by
      have hz : (x₀, τ⁻¹ • v) ∈ closedBall (x₀, 0) 1 := slice_data_mem x₀ τ hτ hv
      simpa [w, dist_eq_norm, mem_closedBall] using (mem_closedBall.mp hz)
    have hs0' : s ≠ 0 := hs0
    have ha : |s| ≤ 1 := by rwa [abs_of_nonneg hs]
    have hsc := exp_ray_scaling g hg hinv x₀ hTf Φ hΦ w hw (a := s) ha (by exact hs0') (t := τ)
      (by constructor <;> linarith)
    have harg : τ⁻¹ • (s • v) = s • w := by
      dsimp [w]
      rw [smul_smul, smul_smul]
      congr 1
      ring
    change (Φ (x₀, τ⁻¹ • (s • v)) τ).1 = (Φ (x₀, τ⁻¹ • v) (s * τ)).1
    rw [harg]
    exact hsc

end FlowExp

section ConstDeriv

/-- `x ∈ uIcc 0 t` implies `|x| ≤ |t|`. -/
lemma abs_of_uIcc_zero {t x : ℝ} (hx : x ∈ uIcc (0 : ℝ) t) : |x| ≤ |t| := by
  rcases le_total t 0 with ht0 | ht0
  · have hx' : t ≤ x ∧ x ≤ 0 := by
      rwa [uIcc_of_ge ht0] at hx
    have hle1 : x ≤ |t| := by
      calc x ≤ 0 := hx'.2
           _ ≤ |t| := abs_nonneg t
    have hge : -|t| ≤ x := by
      have : -|t| ≤ t := by
        by_cases ht : 0 ≤ t
        · rw [abs_of_nonneg ht]
          linarith
        · have ht' : t ≤ 0 := le_of_not_ge ht
          rw [abs_of_nonpos ht']
          linarith
      exact le_trans this hx'.1
    exact abs_le.mpr ⟨hge, hle1⟩
  · have hx' : 0 ≤ x ∧ x ≤ t := by
      rwa [uIcc_of_le ht0] at hx
    have hle1 : x ≤ |t| := by
      calc x ≤ t := hx'.2
           _ ≤ |t| := le_abs_self t
    have hge : -|t| ≤ x := by
      calc -|t| ≤ 0 := by linarith [abs_nonneg t]
           _ ≤ x := hx'.1
    exact abs_le.mpr ⟨hge, hle1⟩

/-- If a function has constant derivative `c` on an open interval containing `0` and `t`, then
`f t = f 0 + c * t`. -/
lemma const_deriv_value {f : ℝ → ℝ} {c ε : ℝ} (hε : 0 < ε)
    (hder : ∀ t ∈ Ioo (-ε) ε, HasDerivAt f c t) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    f t = f 0 + c * t := by
  have hmem (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) t) : x ∈ Ioo (-ε) ε := by
    have hxt : |x| < ε := lt_of_le_of_lt (abs_of_uIcc_zero hx) (abs_lt.mpr ht)
    exact ⟨(abs_lt.mp hxt).1, (abs_lt.mp hxt).2⟩
  have hsub : (∫ x in (0 : ℝ)..t, c) = f t - f 0 := by
    have h := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := t) (f := f)
      (f' := fun _ : ℝ => c) (by intro x hx; exact hder x (hmem x hx))
    simpa using h
  have hconst : (∫ x in (0 : ℝ)..t, c) = c * t := by
    rw [intervalIntegral.integral_const]
    simp [mul_comm]
  linarith

/-- Extracting a scalar from the first argument of a bilinear form. -/
lemma bilin_smul_left (B : Bilin E) (a : ℝ) (u v : E) : B (a • u) v = a * B u v := by
  simp [map_smul]

/-- Extracting a scalar from the second argument of a bilinear form. -/
lemma bilin_smul_right (B : Bilin E) (a : ℝ) (u v : E) : B u (a • v) = a * B u v := by
  simpa using map_smul (B u) a v

end ConstDeriv

/-! ## Regularity of the time-`τ` exponential -/

section FlowExpReg

/-- The time-`τ` exponential is `C^1` on a small ball around `0`, given a window of `C^1`-in-data
regularity of the flow map. -/
lemma exp_contDiffOn_ball (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E)
    (Φ : E × E → ℝ → E × E) {τ τc δc : ℝ}
    (hcd : ∀ t ∈ Icc (-τc) τc, ContDiffOn ℝ 1 (fun z => Φ z t) (ball (x₀, 0) δc))
    (hδc0 : 0 < δc) (hτ0 : 0 < τ) (hτc : τ ≤ τc) :
    ContDiffOn ℝ 1 (expOf x₀ Φ τ) (ball 0 (τ * δc / 2)) := by
  have hH : ContDiffOn ℝ 1 (fun z : E × E => (Φ z τ).1) (ball (x₀, 0) δc) :=
    contDiffOn_one_fst_comp (ball (x₀, 0) δc) (hcd τ (by constructor <;> linarith))
  have hAf : ContDiffOn ℝ 1 (fun v : E => (x₀, (1 / τ) • v)) (ball 0 (τ * δc / 2)) :=
    contDiffOn_data_affine x₀ τ (τ * δc / 2)
  have hAfon : ContDiffOn ℝ 1 (fun v : E => (x₀, τ⁻¹ • v)) (ball 0 (τ * δc / 2)) := by
    -- equal to hAf up to 1/τ = τ⁻¹
    have heq : (fun v : E => (x₀, τ⁻¹ • v)) = fun v : E => (x₀, (1 / τ) • v) := by
      funext v
      congr 1
      simp [one_div]
    simpa [heq] using hAf
  have hAfmap : Set.MapsTo (fun v : E => (x₀, τ⁻¹ • v)) (ball 0 (τ * δc / 2))
      (ball (x₀, 0) δc) := by
    intro v hv
    have hlt : ‖v‖ < τ * δc / 2 := by simpa [dist_eq_norm] using (mem_ball.mp hv)
    rw [mem_ball, dist_eq_norm]
    have hnorm : ‖(x₀, τ⁻¹ • v) - (x₀, 0)‖ = ‖τ⁻¹ • v‖ := by simp
    rw [hnorm]
    have hn1 : ‖τ⁻¹ • v‖ ≤ τ⁻¹ * ‖v‖ := by
      rw [norm_smul]
      have hnn : 0 ≤ τ⁻¹ := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hn2 : τ⁻¹ * ‖v‖ < δc := by
      have hle : τ⁻¹ * ‖v‖ ≤ τ⁻¹ * (τ * δc / 2) :=
        mul_le_mul_of_nonneg_left (le_of_lt hlt) (by positivity)
      have hstep : τ⁻¹ * (τ * δc / 2) = δc / 2 := by
        field_simp [hτ0.ne']
      calc
        τ⁻¹ * ‖v‖ ≤ τ⁻¹ * (τ * δc / 2) := hle
        _ = δc / 2 := hstep
        _ < δc := by linarith
    exact lt_of_le_of_lt hn1 hn2
  have hcomp := ContDiffOn.comp hH hAfon hAfmap
  have hconv : (fun z : E × E => (Φ z τ).1) ∘ (fun v : E => (x₀, τ⁻¹ • v))
      = expOf x₀ Φ τ := by
    funext v
    rfl
  simpa [hconv, Function.comp_def] using hcomp

end FlowExpReg

/-! ## The Gauss pairing along flow geodesics -/

section GaussPair

/-- Central Gauss-pairing identity for the time-`τ` exponential along the flow geodesic
`t ↦ Φ (x₀, τ⁻¹ • v) t`: the metric pairing of the variation derivative of `exp` with the
flow velocity equals the model inner product at the base point (up to the flow-time scaling),
and the flow velocity has constant metric speed. -/
lemma gauss_pair (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf) (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hΦall : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       ∀ t : ℝ, Φ z t ∈ closedBall (x₀, 0) 2)
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall (x₀, 0) 1))
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hK : ∀ p ∈ closedBall (x₀, 0) 2, ‖fderiv ℝ (odeField g) p‖ ≤ K0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2)
    {τ : ℝ} (hτ : 0 < τ) (hτTf : 4 * τ ≤ Tf)
    (hUb : ∀ i : Fin (Module.finrank ℝ (E × E)), 4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τ ≤ 1)
    {v W : E} (hvin : (x₀, τ⁻¹ • v) ∈ ball (x₀, 0) δ) :
    DifferentiableAt ℝ (expOf x₀ Φ τ) v ∧
    (g ((Φ (x₀, τ⁻¹ • v) τ).1)) ((fderiv ℝ (expOf x₀ Φ τ)) v W) ((Φ (x₀, τ⁻¹ • v) τ).2)
      = τ⁻¹ * ((g x₀) W) v ∧
    (g ((Φ (x₀, τ⁻¹ • v) τ).1)) ((Φ (x₀, τ⁻¹ • v) τ).2) ((Φ (x₀, τ⁻¹ • v) τ).2)
      = τ⁻¹ ^ 2 * ((g x₀) v) v := by
  classical
  let zbar : E × E := (x₀, τ⁻¹ • v)
  let exp : E → E := expOf x₀ Φ τ
  have hzbar1 : zbar ∈ closedBall (x₀, 0) 1 := by
    have hlt : dist zbar (x₀, 0) < δ := mem_ball.mp hvin
    rw [mem_closedBall]
    exact le_trans (le_of_lt hlt) (by linarith)
  have hUpos : 0 < 2 * τ := by positivity
  have hUTf : 2 * τ ≤ Tf / 2 := by nlinarith [hτTf]
  have hUb2 : ∀ i : Fin (Module.finrank ℝ (E × E)),
      2 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * (2 * τ) ≤ 1 := by
    intro i
    have h := hUb i
    nlinarith
  rcases flow_fderiv_ballpoint g hg hinv (x₀, 0) Tf hTf Lf Φ hΦall hLip hK0 hK
    (δ := δ) hδ0 hδ12 (U := 2 * τ) hUpos hUTf hUb2 zbar hvin τ (by constructor <;> nlinarith [hτ])
    with ⟨J, hJ0, hJd, hJadd, hJsmul, L, hLfd, hLval⟩
  let wdir : E × E := (0, τ⁻¹ • W)
  have hJw0 : J wdir 0 = wdir := hJ0 wdir
  have hJwd : ∀ s ∈ Ioo (-(2 * τ)) (2 * τ),
      HasDerivAt (J wdir) ((fderiv ℝ (odeField g)) (Φ zbar s) (J wdir s)) s := hJd wdir
  have hLv : L wdir = J wdir τ := hLval wdir
  let c : ℝ → E := fun t => (Φ zbar t).1
  let vel : ℝ → E := fun t => (Φ zbar t).2
  have hΦ2 : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    exact ⟨(hΦall z hz).1, (hΦall z hz).2.1⟩
  have hsplit := split_flow_geodesic g hg hinv (x₀, 0) hTf (closedBall (x₀, 0) 1) Φ hΦ2
    (z := zbar) hzbar1
  have hc0 : c 0 = x₀ := by
    dsimp [c]
    have hz0 : Φ zbar 0 = zbar := (hΦall zbar hzbar1).1
    simpa [zbar] using congrArg Prod.fst hz0
  have hvel0 : vel 0 = τ⁻¹ • v := by
    dsimp [vel]
    have hz0 : Φ zbar 0 = zbar := (hΦall zbar hzbar1).1
    simpa [zbar] using congrArg Prod.snd hz0
  have hwin (t : ℝ) (ht : t ∈ Ioo (-(2 * τ)) (2 * τ)) : t ∈ Ioo (-Tf) Tf := by
    constructor <;> linarith [ht.1, ht.2, hτTf, hTf]
  have hcd : ∀ t ∈ Ioo (-(2 * τ)) (2 * τ), HasDerivAt c (vel t) t := by
    intro t ht
    simpa [c, vel] using hsplit.1 t (hwin t ht)
  have hvd : ∀ t ∈ Ioo (-(2 * τ)) (2 * τ),
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t := by
    intro t ht
    simpa [c, vel] using hsplit.2 t (hwin t ht)
  let A₀ : E →L[ℝ] (E × E) :=
    ContinuousLinearMap.prod (0 : E →L[ℝ] E) ((τ⁻¹ : ℝ) • (1 : E →L[ℝ] E))
  have hA₀ : ∀ u : E, A₀ u = (0, τ⁻¹ • u) := by
    intro u
    simp [A₀]
  have hAff : HasFDerivAt (fun u : E => (x₀, τ⁻¹ • u)) A₀ v := by
    have hc1 : HasFDerivAt (fun _ : E => x₀) (0 : E →L[ℝ] E) v := by
      simpa using hasFDerivAt_const x₀ v
    have hl : HasFDerivAt (fun u : E => τ⁻¹ • u) ((τ⁻¹ : ℝ) • (1 : E →L[ℝ] E)) v := by
      exact ((τ⁻¹ : ℝ) • (1 : E →L[ℝ] E)).hasFDerivAt
    have hp := hc1.prodMk hl
    simpa [A₀] using hp
  have hcomp1 : HasFDerivAt (fun u : E => Φ (x₀, τ⁻¹ • u) τ) (L.comp A₀) v := by
    have hc := hLfd.comp v hAff
    simpa [Function.comp_def] using hc
  have hproj : HasFDerivAt (fun u : E => (Φ (x₀, τ⁻¹ • u) τ).1)
      ((ContinuousLinearMap.fst ℝ E E).comp (L.comp A₀)) v := by
    simpa using hcomp1.fst
  have hEqFun : (fun u : E => (Φ (x₀, τ⁻¹ • u) τ).1) = exp := by
    funext u
    rfl
  have hE : HasFDerivAt exp ((ContinuousLinearMap.fst ℝ E E).comp (L.comp A₀)) v := by
    simpa [hEqFun] using hproj
  have hD : DifferentiableAt ℝ exp v := hE.differentiableAt
  have hfdexp : fderiv ℝ exp v = (ContinuousLinearMap.fst ℝ E E).comp (L.comp A₀) := hE.fderiv
  have hfdW : (fderiv ℝ exp v) W = (J wdir τ).1 := by
    calc
      (fderiv ℝ exp v) W = ((ContinuousLinearMap.fst ℝ E E).comp (L.comp A₀)) W := by
        rw [hfdexp]
      _ = (L (A₀ W)).1 := by rfl
      _ = (L wdir).1 := by rw [hA₀ W]
      _ = (J wdir τ).1 := by rw [hLv]
  have hgauss : ∀ t ∈ Ioo (-(2 * τ)) (2 * τ),
      HasDerivAt (fun s => ((g (c s)) ((J wdir s).1)) (vel s))
        ((g x₀) (τ⁻¹ • W) (τ⁻¹ • v)) t := by
    intro t ht
    have hJ' : ∀ s ∈ Ioo (-(2 * τ)) (2 * τ),
        HasDerivAt (J wdir) ((fderiv ℝ (odeField g)) (c s, vel s) (J wdir s)) s := by
      intro s hs
      simpa [c, vel] using hJwd s hs
    have h0 := gauss_identity g hg hinv hsym (ε := 2 * τ) (by positivity)
      (x₀ := x₀) (v₀ := τ⁻¹ • v) (c := c) (vel := vel) (w := τ⁻¹ • W)
      hc0 hvel0 hcd hvd (J := J wdir) hJw0 hJ'
    simpa using h0 t ht
  have hτin : τ ∈ Ioo (-(2 * τ)) (2 * τ) := by constructor <;> linarith [hτ]
  have hval := const_deriv_value (ε := 2 * τ) (by positivity)
    (f := fun s : ℝ => ((g (c s)) ((J wdir s).1)) (vel s))
    (c := (g x₀) (τ⁻¹ • W) (τ⁻¹ • v)) hgauss hτin
  have hval0 : (g (c 0)) ((J wdir 0).1) (vel 0) = 0 := by
    have hj : (J wdir 0).1 = 0 := by simpa [wdir] using congrArg Prod.fst hJw0
    simp [hj]
  have hvalτ : (g (c τ)) ((J wdir τ).1) (vel τ) = τ * ((g x₀) (τ⁻¹ • W) (τ⁻¹ • v)) := by
    rw [hval]
    rw [hval0]
    ring
  have hcτ : c τ = exp v := by
    dsimp [c, exp, expOf, zbar]
  have hspeed : ∀ t ∈ Ioo (-(2 * τ)) (2 * τ),
      HasDerivAt (fun s : ℝ => ((g (c s)) (vel s)) (vel s)) 0 t := by
    intro t ht
    simpa using speed_const g hg hinv hsym (ε := 2 * τ) (by positivity) hcd hvd t ht
  have hspeedval : (g (c τ)) (vel τ) (vel τ) = (g x₀) (τ⁻¹ • v) (τ⁻¹ • v) := by
    have hval2 := const_deriv_value (ε := 2 * τ) (by positivity)
      (f := fun s : ℝ => ((g (c s)) (vel s)) (vel s)) (c := 0) hspeed hτin
    rw [hval2]
    have hc0' : (g (c 0)) (vel 0) (vel 0) = (g x₀) (τ⁻¹ • v) (τ⁻¹ • v) := by
      rw [hc0, hvel0]
    rw [hc0']
    ring
  refine ⟨hD, ?_, ?_⟩
  · calc
      (g ((Φ zbar τ).1)) ((fderiv ℝ exp v) W) ((Φ zbar τ).2)
          = (g (c τ)) ((J wdir τ).1) (vel τ) := by
            rw [hcτ, hfdW]; rfl
      _ = τ * ((g x₀) (τ⁻¹ • W) (τ⁻¹ • v)) := hvalτ
      _ = τ * (τ⁻¹ * (τ⁻¹ * ((g x₀) W) v)) := by
        rw [bilin_smul_left (g x₀) τ⁻¹ W (τ⁻¹ • v)]
        rw [bilin_smul_right (g x₀) τ⁻¹ W v]
      _ = τ⁻¹ * ((g x₀) W) v := by
        field_simp [ne_of_gt hτ]
  · calc
      (g ((Φ zbar τ).1)) ((Φ zbar τ).2) ((Φ zbar τ).2)
          = (g (c τ)) (vel τ) (vel τ) := by rfl
      _ = (g x₀) (τ⁻¹ • v) (τ⁻¹ • v) := hspeedval
      _ = τ⁻¹ ^ 2 * ((g x₀) v) v := by
        rw [bilin_smul_left (g x₀) τ⁻¹ v (τ⁻¹ • v)]
        rw [bilin_smul_right (g x₀) τ⁻¹ v v]
        ring


end GaussPair



/-! ## Radial coordinate derivative -/

section RadialDeriv

/-- The quadratic map `z ↦ (B z) z` has derivative `w ↦ (B w) v + (B v) w` at `v`. -/
lemma bilin_quad_hasFDerivAt (B : Bilin E) (v : E) :
    HasFDerivAt (fun z : E => (B z) z)
      ((B v).comp (1 : E →L[ℝ] E) + B.flip v) v := by
  have hlin : HasFDerivAt (fun z : E => B z) B v := B.hasFDerivAt
  have hid : HasFDerivAt (fun z : E => z) (1 : E →L[ℝ] E) v := (1 : E →L[ℝ] E).hasFDerivAt
  simpa using hlin.clm_apply hid

/-- The value of the derivative of the radial norm `z ↦ sqrt (B z z)` in a direction `W`. -/
lemma radial_fderiv_apply {B : Bilin E} (hsym : ∀ u v, B u v = B v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) {v : E} (hv : v ≠ 0) (W : E) :
    (fderiv ℝ (fun z : E => Real.sqrt (B z z)) v) W = (B v) W / Real.sqrt (B v v) := by
  have hq : HasFDerivAt (fun z : E => (B z) z)
      ((B v).comp (1 : E →L[ℝ] E) + B.flip v) v := bilin_quad_hasFDerivAt B v
  have hqBvv : (fun z : E => (B z) z) v ≠ 0 := by
    change (B v) v ≠ 0
    exact ne_of_gt (hpos v hv)
  have hsq := hq.sqrt hqBvv
  have hsymCLM : ((B v).comp (1 : E →L[ℝ] E) + B.flip v) = 2 • (B v) := by
    ext w
    have hf : (B.flip v) w = B w v := rfl
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply]
    rw [hf, hsym w v]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hD : (1 / (2 * Real.sqrt (B v v))) • ((B v).comp (1 : E →L[ℝ] E) + B.flip v)
      = (1 / Real.sqrt (B v v)) • (B v) := by
    ext w
    have hf : (B.flip v) w = B w v := rfl
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    rw [hf, hsym w v]
    field_simp [Real.sqrt_pos.2 (hpos v hv)]
    ring
  have hsq2 : HasFDerivAt (fun z : E => Real.sqrt (B z z))
      ((1 / Real.sqrt (B v v)) • (B v)) v := by
    rw [hD] at hsq
    simpa using hsq
  have hfd : fderiv ℝ (fun z : E => Real.sqrt (B z z)) v
      = (1 / Real.sqrt (B v v)) • (B v) := hsq2.fderiv
  calc
    (fderiv ℝ (fun z : E => Real.sqrt (B z z)) v) W
        = ((1 / Real.sqrt (B v v)) • (B v)) W := by rw [hfd]
    _ = (1 / Real.sqrt (B v v)) * ((B v) W) := by simp
    _ = (B v) W / Real.sqrt (B v v) := by
      field_simp [Real.sqrt_pos.2 (hpos v hv)]

end RadialDeriv


/-! ## Regularity pack for the flow exponential -/

section ExpRegularity

/-- The time-`τ` exponential has derivative the identity at `0`. -/
lemma expOf_hasFDerivAt_id (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf)
    (Φ : E × E → ℝ → E × E)
    (hΦ2 : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    {τ ρ : ℝ} (hτ : 0 < τ) (hτTf : τ < Tf) (hρ : 0 < ρ)
    (hC : ContDiffOn ℝ 1 (expOf x₀ Φ τ) (ball 0 ρ)) :
    HasFDerivAt (expOf x₀ Φ τ) (ContinuousLinearMap.id ℝ E) 0 := by
  have hτmem : τ ∈ Ioo (-Tf) Tf := by constructor <;> linarith
  have hrest := flow_rest_point g hg hinv hTf (x₀ := x₀) (Φ := Φ) hΦ2 τ hτmem
  have hexp : expOf x₀ Φ τ = fun v : E => (Φ (x₀, (1 / τ) • v) τ).1 := by
    funext v
    simp [expOf, one_div]
  exact exp_fderiv_zero_id g hg hinv x₀ (T0 := Tf) (τ := τ) hTf hτ hτTf Φ hΦ2 hrest
    (ρ := ρ) hρ (expOf x₀ Φ τ) hexp hC

/-- The derivative of `exp` is invertible on a small ball around `0`, given `exp` is C¹ on a
ball and has derivative the identity at `0`. -/
lemma exp_fderiv_invertible_on (x₀ : E) (exp : E → E) {ρE : ℝ} (hρE : 0 < ρE)
    (hC : ContDiffOn ℝ 1 exp (ball 0 ρE))
    (hId : HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0) :
    ∃ ρi > 0, ρi ≤ ρE ∧
      ∀ v ∈ ball 0 ρi, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ exp v := by
  have hDerivCont : ContinuousOn (fun v : E => fderiv ℝ exp v) (ball 0 ρE) :=
    contDiffOn_one_cont_fderiv isOpen_ball hC
  have hfderiv0 : fderiv ℝ exp 0 = ContinuousLinearMap.id ℝ E := hId.fderiv
  have h0b : (0 : E) ∈ ball 0 ρE := by simpa using hρE
  have hCont0 : ContinuousAt (fun v : E => fderiv ℝ exp v) 0 :=
    hDerivCont.continuousAt (by simpa [ball, dist_eq_norm] using (isOpen_ball.mem_nhds h0b))
  rcases Metric.continuousAt_iff.mp hCont0 (1 / 2) (by norm_num) with ⟨ρi', hρi'0, hρi'⟩
  let ρi : ℝ := min ρE (ρi' / 2)
  have hρi0 : 0 < ρi := by dsimp [ρi]; exact lt_min hρE (by positivity)
  refine ⟨ρi, hρi0, ?_, ?_⟩
  · dsimp [ρi]
    exact min_le_left _ _
  · intro v hv
    have hvltρi : ‖v‖ < ρi := by simpa [dist_eq_norm] using (mem_ball.mp hv)
    have hvlt : dist v 0 < ρi' := by
      have hb : ρi ≤ ρi' / 2 := by dsimp [ρi]; exact min_le_right _ _
      rw [dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le hvltρi (by nlinarith)
    have hnear : dist (fderiv ℝ exp v) (fderiv ℝ exp 0) < 1 / 2 := hρi' hvlt
    have hnear' : ‖fderiv ℝ exp v - ContinuousLinearMap.id ℝ E‖ < 1 := by
      have h1 : ‖fderiv ℝ exp v - fderiv ℝ exp 0‖ < 1 / 2 := by
        simpa [dist_eq_norm] using hnear
      have h2 : ‖fderiv ℝ exp v - ContinuousLinearMap.id ℝ E‖ < 1 / 2 := by
        simpa [hfderiv0] using h1
      linarith
    exact clm_invertible_of_near_id (fderiv ℝ exp v) hnear'

end ExpRegularity

/-! ## The radial 1-Lipschitz bound (Gauss estimate) -/

section RadialBound

/-- Gauss estimate for the radial coordinate of the exponential: the differential of
`v ↦ sqrt ((g x₀) v v)` at `v` in direction `W` is bounded by the metric norm of the pushed
tangent vector `(fderiv exp v) W` at `exp v`. -/
lemma radial_bound_main (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf) (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hΦall : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       ∀ t : ℝ, Φ z t ∈ closedBall (x₀, 0) 2)
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall (x₀, 0) 1))
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hK : ∀ p ∈ closedBall (x₀, 0) 2, ‖fderiv ℝ (odeField g) p‖ ≤ K0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2)
    {τ : ℝ} (hτ : 0 < τ) (hτTf : 4 * τ ≤ Tf)
    (hUb : ∀ i : Fin (Module.finrank ℝ (E × E)),
      4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τ ≤ 1)
    {v W : E} (hvin : (x₀, τ⁻¹ • v) ∈ ball (x₀, 0) δ) (hv0 : v ≠ 0) :
    ‖(fderiv ℝ (fun z : E => Real.sqrt ((g x₀) z z)) v) W‖ ≤
      Real.sqrt ((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W)
        ((fderiv ℝ (expOf x₀ Φ τ)) v W)) := by
  classical
  rcases gauss_pair g hg hinv hsym x₀ (Tf := Tf) hTf (Lf := Lf) (Φ := Φ) hΦall hLip
    (K0 := K0) hK0 hK (δ := δ) hδ0 hδ12 (τ := τ) hτ hτTf hUb (v := v) (W := W) hvin with
    ⟨hD, hpair, hspeed⟩
  let r : ℝ := Real.sqrt ((g x₀) v v)
  let e0 : E := (τ / r) • (Φ (x₀, τ⁻¹ • v) τ).2
  have hrpos : 0 < r := bilin_sqrt_pos (hpos x₀) hv0
  have hsqrt : r ^ 2 = ((g x₀) v v) := by
    dsimp [r]
    exact bilin_sqrt_sq (hpos x₀) v
  have hspeedV : (g (expOf x₀ Φ τ v)) ((Φ (x₀, τ⁻¹ • v) τ).2) ((Φ (x₀, τ⁻¹ • v) τ).2)
      = τ⁻¹ ^ 2 * ((g x₀) v v) := by
    simpa [expOf] using hspeed
  have hunit : (g (expOf x₀ Φ τ v)) e0 e0 = 1 := by
    dsimp [e0]
    rw [bilin_smul_left (g (expOf x₀ Φ τ v)) (τ / r) (Φ (x₀, τ⁻¹ • v) τ).2
      ((τ / r) • (Φ (x₀, τ⁻¹ • v) τ).2)]
    rw [bilin_smul_right (g (expOf x₀ Φ τ v)) (τ / r) (Φ (x₀, τ⁻¹ • v) τ).2
      (Φ (x₀, τ⁻¹ • v) τ).2]
    rw [hspeedV]
    calc
      (τ / r) * ((τ / r) * (τ⁻¹ ^ 2 * ((g x₀) v v)))
          = (τ / r) ^ 2 * (τ⁻¹ ^ 2 * ((g x₀) v v)) := by ring
      _ = 1 := by
        rw [← hsqrt]
        field_simp [hrpos.ne', ne_of_gt hτ]
  have hpairX : (g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W)
      ((Φ (x₀, τ⁻¹ • v) τ).2) = τ⁻¹ * (((g x₀) W) v) := by
    simpa [expOf] using hpair
  have hvel : r • e0 = τ • (Φ (x₀, τ⁻¹ • v) τ).2 := by
    dsimp [e0]
    rw [smul_smul]
    congr 1
    field_simp [hrpos.ne']
  have hstep : ((g x₀) W) v =
      ((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W)) (r • e0) := by
    rw [hvel]
    have h2 : ((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W)) (τ • (Φ (x₀, τ⁻¹ • v) τ).2)
        = τ * ((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W)) ((Φ (x₀, τ⁻¹ • v) τ).2) := by
      rw [bilin_smul_right (g (expOf x₀ Φ τ v)) τ ((fderiv ℝ (expOf x₀ Φ τ)) v W)
        (Φ (x₀, τ⁻¹ • v) τ).2]
    rw [h2, hpairX]
    field_simp [ne_of_gt hτ]
  have hB0vW : ((g x₀) W) v =
      r * ((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W) e0) := by
    rw [hstep]
    rw [bilin_smul_right (g (expOf x₀ Φ τ v)) r ((fderiv ℝ (expOf x₀ Φ τ)) v W) e0]
  have hvalR : (fderiv ℝ (fun z : E => Real.sqrt ((g x₀) z z)) v) W = ((g x₀) v) W / r := by
    exact radial_fderiv_apply (B := g x₀) (hsym x₀) (hpos x₀) hv0 W
  have hnorm : ‖(fderiv ℝ (fun z : E => Real.sqrt ((g x₀) z z)) v) W‖
      = ‖((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W) e0)‖ := by
    rw [hvalR]
    have hsym' : ((g x₀) v) W = ((g x₀) W) v := hsym x₀ v W
    calc
      ‖((g x₀) v) W / r‖ = |((g x₀) v) W / r| := rfl
      _ = |((g x₀) W) v / r| := by rw [hsym']
      _ = |((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W) e0)| := by
        congr 1
        rw [hB0vW]
        field_simp [hrpos.ne']
      _ = ‖((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W) e0)‖ := rfl
  have hcs := bilin_cauchy_schwarz (B := g (expOf x₀ Φ τ v)) (hsym (expOf x₀ Φ τ v))
    (hpos (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W) e0
  have hunit' : Real.sqrt ((g (expOf x₀ Φ τ v)) e0 e0) = 1 := by
    rw [hunit]
    norm_num
  calc
    ‖(fderiv ℝ (fun z : E => Real.sqrt ((g x₀) z z)) v) W‖
        = ‖((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W) e0)‖ := hnorm
    _ ≤ Real.sqrt ((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W)
          ((fderiv ℝ (expOf x₀ Φ τ)) v W)) *
        Real.sqrt ((g (expOf x₀ Φ τ v)) e0 e0) := hcs
    _ = Real.sqrt ((g (expOf x₀ Φ τ v)) ((fderiv ℝ (expOf x₀ Φ τ)) v W)
          ((fderiv ℝ (expOf x₀ Φ τ)) v W)) := by
      rw [hunit']
      ring


end RadialBound





/-! ## C^1 diffeomorphism package (open version) -/

section DiffeoOpen

/-- At a point `v` of the ball where `exp` is `C^1` with invertible derivative, the local inverse
`P.symm` produced by the inverse function theorem at `0` is `C^1` at `exp v`. -/
private lemma contDiffAt_symm_of_invDerivOpen {exp : E → E} {ρE : ℝ} {P : OpenPartialHomeomorph E E}
    (hPe : (P : E → E) = exp)
    (hExpC1 : ContDiffOn ℝ 1 exp (ball 0 ρE))
    (hInvDeriv : ∀ v ∈ ball 0 ρE, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ exp v)
    {v : E} (hv : v ∈ ball (0 : E) ρE) (hvs : v ∈ P.source) :
    ContDiffAt ℝ 1 (P.symm) (exp v) := by
  have hcv : ContDiffAt ℝ 1 exp v := hExpC1.contDiffAt (Metric.isOpen_ball.mem_nhds hv)
  rcases hInvDeriv v hv with ⟨e, he⟩
  have hfd : HasFDerivAt exp (fderiv ℝ exp v) v :=
    (hcv.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hfv : HasFDerivAt exp ((e : E →L[ℝ] E)) v := by simpa [he] using hfd
  have hstrict : HasStrictFDerivAt exp ((e : E →L[ℝ] E)) v :=
    hcv.hasStrictFDerivAt' hfv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hns : P.source ∈ 𝓝 v := P.open_source.mem_nhds hvs
  have hp_left : ∀ᶠ x in 𝓝 v, P.symm (exp x) = x := by
    filter_upwards [hns] with x hx
    rw [← hPe]
    exact P.left_inv hx
  have huniq : ∀ᶠ y in 𝓝 (exp v),
      P.symm y = HasStrictFDerivAt.localInverse exp e v hstrict y :=
    HasStrictFDerivAt.localInverse_unique hstrict hp_left
  have hlinv : ContDiffAt ℝ 1 (HasStrictFDerivAt.localInverse exp e v hstrict) (exp v) :=
    ContDiffAt.to_localInverse hcv hfv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  exact hlinv.congr_of_eventuallyEq huniq

/-- C¹ local inverse function theorem package, with openness of `U` and `V` and `V = exp '' U`
made explicit (so that `exp` restricts to a C¹ diffeomorphism of the open `U` onto the open `V`). -/
theorem c1_local_inverse_ball {x₀ : E} (exp : E → E) {ρE : ℝ} (hρE : 0 < ρE)
    (hExpC1 : ContDiffOn ℝ 1 exp (ball 0 ρE))
    (hExp0 : exp 0 = x₀)
    (hFderiv0 : HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0)
    (hInvDeriv : ∀ v ∈ ball 0 ρE, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ exp v) :
    ∃ U : Set E, U ∈ 𝓝 (0 : E) ∧ IsOpen U ∧ U ⊆ ball (0 : E) ρE ∧
      ∃ V : Set E, V ∈ 𝓝 x₀ ∧ IsOpen V ∧ V = exp '' U ∧
        ∃ inv : E → E,
          Set.MapsTo exp U V ∧ Function.Injective (fun v : U => exp v.1) ∧
          Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
          (∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y) ∧
          (∀ v ∈ U, inv (exp v) = v) ∧
          ContDiffOn ℝ 1 inv V := by
  classical
  have hc0 : ContDiffAt ℝ 1 exp (0 : E) := hExpC1.contDiffAt (Metric.ball_mem_nhds (0 : E) hρE)
  have hf0 : HasFDerivAt exp ((ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E)) (0 : E) := by
    simpa using hFderiv0
  let hn0 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  let P : OpenPartialHomeomorph E E := hc0.toOpenPartialHomeomorph exp hf0 hn0
  have hP0 : (0 : E) ∈ P.source := by
    have := ContDiffAt.mem_toOpenPartialHomeomorph_source hc0 hf0 hn0
    simpa [P] using this
  have hPx0 : x₀ ∈ P.target := by
    have := ContDiffAt.image_mem_toOpenPartialHomeomorph_target hc0 hf0 hn0
    simpa [P, hExp0] using this
  have hPe : (P : E → E) = exp := by simp [P]
  have hsrc_nhds : P.source ∩ ball (0 : E) ρE ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (P.open_source.mem_nhds hP0) (Metric.ball_mem_nhds (0 : E) hρE)
  obtain ⟨ρU, hρU_pos, hρU_sub⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : E) ρ ⊆ P.source ∩ ball (0 : E) ρE := by
    rcases (Metric.nhds_basis_ball.mem_iff).mp hsrc_nhds with ⟨r, hr0, hsub⟩
    exact ⟨r, hr0, hsub⟩
  let U : Set E := ball (0 : E) ρU
  let V : Set E := exp '' U
  have hU_open : IsOpen U := isOpen_ball
  have hU_nhds : U ∈ 𝓝 (0 : E) := by
    simpa [U] using (Metric.ball_mem_nhds (0 : E) hρU_pos)
  have hU_source : U ⊆ P.source := by
    intro x hx
    exact (hρU_sub hx).1
  have hU_ballE : U ⊆ ball (0 : E) ρE := by
    intro x hx
    exact (hρU_sub hx).2
  have hU0 : (0 : E) ∈ U := by simpa [U] using hρU_pos
  have hV_open : IsOpen V := by
    have hV_eq : V = P '' U := by
      ext y
      constructor
      · rintro ⟨x, hx, hy⟩
        exact ⟨x, hx, by simpa [P] using hy⟩
      · rintro ⟨x, hx, hy⟩
        exact ⟨x, hx, by simpa [P] using hy⟩
    rw [hV_eq]
    exact P.isOpen_image_of_subset_source hU_open hU_source
  have hV_nhds : V ∈ 𝓝 x₀ := by
    exact hV_open.mem_nhds (by
      refine ⟨(0 : E), hU0, ?_⟩
      exact hExp0)
  have hMapsTo : Set.MapsTo exp U V := by
    intro x hx
    exact mem_image_of_mem exp hx
  have hInj : Function.Injective (fun v : U => exp v.1) := by
    intro a b hab
    apply Subtype.ext
    have ha : a.1 ∈ P.source := hU_source a.2
    have hb : b.1 ∈ P.source := hU_source b.2
    apply P.injOn ha hb
    simpa [P] using hab
  have hSurj : Set.SurjOn exp U V := by
    intro y hy
    simpa [V] using hy
  have hCont : ContinuousOn exp U := hExpC1.continuousOn.mono hU_ballE
  have hInv1 : ∀ y ∈ V, P.symm y ∈ U ∧ exp (P.symm y) = y := by
    intro y hy
    rcases hy with ⟨v, hvU, hyv⟩
    have hvs : v ∈ P.source := hU_source hvU
    have hsy : P.symm y = v := by
      rw [← hyv, ← hPe]
      exact P.left_inv hvs
    constructor
    · rw [hsy]
      exact hvU
    · rw [hsy, hyv]
  have hInv2 : ∀ v ∈ U, P.symm (exp v) = v := by
    intro v hvU
    have hvs : v ∈ P.source := hU_source hvU
    rw [← hPe]
    exact P.left_inv hvs
  have hContDiff : ContDiffOn ℝ 1 (P.symm) V := by
    rw [hV_open.contDiffOn_iff]
    intro y hy
    rcases hy with ⟨v, hvU, hyv⟩
    rw [← hyv]
    exact contDiffAt_symm_of_invDerivOpen (exp := exp) (P := P) hPe hExpC1 hInvDeriv
      (hU_ballE hvU) (hU_source hvU)
  refine ⟨U, hU_nhds, hU_open, hU_ballE, V, hV_nhds, hV_open, ?_, P.symm, hMapsTo, hInj, hSurj,
    hCont, hInv1, hInv2, hContDiff⟩
  rfl

end DiffeoOpen



lemma fderiv_comp_eq_on_open {F : E → ℝ} {R : E → ℝ} {exp : E → E} {U : Set E} {v : E}
    (hU : IsOpen U) (hvU : v ∈ U)
    (hEq : ∀ x ∈ U, F (exp x) = R x)
    (hFy : DifferentiableAt ℝ F (exp v))
    (hExp : DifferentiableAt ℝ exp v)
    (hR : DifferentiableAt ℝ R v) :
    (fderiv ℝ F (exp v)).comp (fderiv ℝ exp v) = fderiv ℝ R v := by
  have hc : HasFDerivAt (fun x : E => F (exp x))
      ((fderiv ℝ F (exp v)).comp (fderiv ℝ exp v)) v := by
    simpa [Function.comp_def] using (hFy.hasFDerivAt.comp v hExp.hasFDerivAt)
  have hev : (fun x : E => F (exp x)) =ᶠ[𝓝 v] R := by
    filter_upwards [hU.mem_nhds hvU] with x hx
    exact hEq x hx
  have hR' : HasFDerivAt (fun x : E => F (exp x)) (fderiv ℝ R v) v :=
    hR.hasFDerivAt.congr_of_eventuallyEq hev
  exact hc.unique hR' 




/-- A vector is the image under `fderiv exp v` of a suitable vector, when the derivative is a
linear equivalence. -/

lemma fderiv_exp_surj {exp : E → E} {ρ : ℝ} (hρ : 0 < ρ) (v : E) (hv : v ∈ ball (0 : E) ρ)
    (hInvD : ∀ w ∈ ball (0 : E) ρ, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ exp w)
    (X : E) : ∃ W : E, (fderiv ℝ exp v) W = X := by
  rcases hInvD v hv with ⟨e, he⟩
  refine ⟨e.symm X, ?_⟩
  have h1 : (fderiv ℝ exp v) (e.symm X) = X := by
    rw [← he]
    simpa using e.apply_symm_apply X
  exact h1

/-- The map `z ↦ sqrt ((B (inv z)) (inv z))` is differentiable at `y` when `inv` is C¹ at `y`
and the value at `y` is positive. -/

lemma radialComp_differentiableAt {B : Bilin E} {inv : E → E} (y : E)
    (hInv : ContDiffAt ℝ 1 inv y) (hpos : 0 < B (inv y) (inv y)) :
    DifferentiableAt ℝ (fun z : E => Real.sqrt (B (inv z) (inv z))) y := by
  let quad : E → ℝ := fun u => B u u
  have hqd : DifferentiableAt ℝ quad (inv y) := by
    have hf := bilin_quad_hasFDerivAt B (inv y)
    exact hf.differentiableAt
  have hid : DifferentiableAt ℝ inv y := hInv.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hq : DifferentiableAt ℝ (fun z : E => quad (inv z)) y := hqd.comp y hid
  have hval : quad (inv y) ≠ 0 := by simpa [quad] using ne_of_gt hpos
  have hs : DifferentiableAt ℝ Real.sqrt (quad (inv y)) := by
    exact (Real.hasDerivAt_sqrt hval).differentiableAt
  have hcomp := hs.comp y hq
  simpa [Function.comp_def, quad] using hcomp

/-- The map `z ↦ sqrt ((B (inv z)) (inv z))` is continuous at `y` when `inv` is continuous at
`y`. -/

lemma radialComp_continuousAt {B : Bilin E} {inv : E → E} (y : E)
    (hInv : ContinuousAt inv y) :
    ContinuousAt (fun z : E => Real.sqrt (B (inv z) (inv z))) y := by
  have hquad : ContinuousAt (fun u : E => B u u) (inv y) := by
    have hf := bilin_quad_hasFDerivAt B (inv y)
    exact hf.differentiableAt.continuousAt
  have hq : ContinuousAt (fun z : E => B (inv z) (inv z)) y := by
    simpa [Function.comp_def] using (hquad.comp hInv)
  exact hq.sqrt

theorem model_normal_ball (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) :
    ∃ ρ > 0, ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
         ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      ∃ exp : E → E, exp 0 = x₀ ∧
        (∀ w : E, (g x₀) w w = 1 → ∀ t ∈ Ioo (-ρ) ρ,
           exp (t • w) = (Φ (x₀, w) t).1) ∧
        HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 ∧
        (∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 x₀,
           Set.MapsTo exp U V ∧ Function.Injective (fun v : U => exp v.1) ∧
           Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
           ∃ inv : E → E,
             (∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y) ∧
             (∀ v ∈ U, inv (exp v) = v) ∧
             ContDiffOn ℝ 1 inv V ∧
             (∀ y ∈ V, y ≠ x₀ → ∀ X : E,
                ‖(fderiv ℝ (fun z => Real.sqrt ((g x₀) (inv z) (inv z))) y) X‖ ≤
                  Real.sqrt ((g y) X X)) ∧
             (∀ v ∈ U, ∀ c : ℝ → E,
                c 0 = x₀ → c 1 = exp v →
                (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
                (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ V) →
                Real.sqrt ((g x₀) v v) ≤ mgLength g c 0 1)) := by
  classical
  let z₀ : E × E := (x₀, 0)
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
  rcases geodesic_flow g hg hinv (x₀, 0) with ⟨Tg, hTg, Cg, hCg0, Φg, hΦgall⟩
  rcases hΦgall with ⟨hΦg2, hΦgtimelip, hΦgtaylor⟩
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
  let ρ : ℝ := min (T / 4) (τ / 8)
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hρT : ρ ≤ T := by
    dsimp [ρ]
    exact le_trans (min_le_left _ _) (by nlinarith [hTpos])
  have hρτ2 : ρ ≤ τ / 2 := by
    dsimp [ρ]
    have h1 : τ / 8 ≤ τ / 2 := by nlinarith [hτpos]
    exact le_trans (min_le_right _ _) h1
  have hΦmflow : ∀ z ∈ closedBall (x₀, 0) 2, Φm z 0 = z ∧
      ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (Φm z) (odeField g (Φm z t)) t := by
    intro z hz
    constructor
    · exact (hΦm2 z hz).1
    · intro t ht
      have ht' : t ∈ Icc (-T) T := by
        constructor <;> linarith [ht.1, ht.2, hρT]
      exact (hΦm2 z hz).2 t ht'
  have hray : ∀ w : E, (g x₀) w w = 1 → ∀ t ∈ Ioo (-ρ) ρ,
      exp (t • w) = (Φm (x₀, w) t).1 := by
    intro w hwunit t ht
    have htρ : |t| < ρ := abs_lt.mpr ht
    by_cases hw2 : ‖w‖ ≤ 2
    · have hrc := ray_agreement_core g hg hinv x₀ τ hτpos Tf hTf (by linarith [hτTf])
        Φ (by intro z hz; exact ⟨(hΦall z hz).1, (hΦall z hz).2.1⟩) T hTpos Φm
        (by intro z hz; exact hΦm2 z hz) hrestτ w hw2 (by
          have h1 : |t| < τ / 2 := lt_of_lt_of_le htρ hρτ2
          have h2 : |t| < T := lt_of_lt_of_le htρ hρT
          exact lt_min h1 h2)
      have hlhs : exp (t • w) = (Φ (x₀, (1 / τ) • (t • w)) τ).1 := by
        dsimp [exp]
        change (Φ (x₀, τ⁻¹ • (t • w)) τ).1 = (Φ (x₀, (1 / τ) • (t • w)) τ).1
        congr 1
        simp [one_div]
      rw [hlhs, hrc]
    · have hn1 : (x₀, w) ∉ closedBall (x₀, 0) 1 := by
        intro hm
        have hd : ‖w‖ ≤ 1 := by
          have hd' : ‖(x₀, w) - (x₀, 0)‖ ≤ 1 := by
            simpa [dist_eq_norm] using (mem_closedBall.mp hm)
          simpa using hd'
        exact hw2 (le_trans hd (by norm_num))
      have hn2 : (x₀, w) ∉ closedBall (x₀, 0) 2 := by
        intro hm
        have hd : ‖w‖ ≤ 2 := by
          have hd' : ‖(x₀, w) - (x₀, 0)‖ ≤ 2 := by
            simpa [dist_eq_norm] using (mem_closedBall.mp hm)
          simpa using hd'
        exact hw2 hd
      dsimp [Φm]
      rw [if_neg hn1, if_neg hn2]
  refine ⟨ρ, hρpos, Φm, hΦmflow, exp, hExp0, hray, hExpId, ?_⟩
  refine ⟨U, hU_nhds, V, hV_nhds, ?_, ?_, ?_, ?_, inv, ?_, ?_, ?_, ?_, ?_⟩
  · exact hMapsTo
  · exact hInj
  · exact hSurj
  · exact hContU
  · intro y hy
    exact hInv1 y hy
  · intro v hv
    exact hInv2 v hv
  · exact hContDiffInv
  · exact hRad
  · exact hMin

end
end Submission.Model
