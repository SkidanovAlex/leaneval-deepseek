import ChallengeDeps
import Submission.Metric
import Submission.ChartNormal
import Submission.ModelNormalBall
import Submission.MChartGeodesicUB
import Submission.NbdGeo
import Mathlib

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

/-!
# Local geodesic extension through a limit point (rigid statement)

Theorem: `Submission.local_extension`.  See the parent brief.  Helper lemmas live below
(and in `Submission/NbdGeo.lean` / `Submission/ModelPkg.lean`).
-/

open scoped Manifold ENNReal ContDiff Topology
open Set Filter Metric
open Bundle
open MeasureTheory

namespace Submission

open LeanEval.Geometry


open ContinuousLinearMap

/-- quadratic form homogeneity under scalar multiplication -/
lemma quad_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a : ℝ) (v : E) :
    B (a • v) (a • v) = a ^ 2 * B v v := by
  have h1 : B (a • v) = a • B v := by
    ext w
    change (B (a • v)) w = (a • B v) w
    simp
  calc
    B (a • v) (a • v) = (a • B v) (a • v) := by rw [h1]
    _ = a * (B v (a • v)) := by simp
    _ = a * (a * B v v) := by
      congr 1
      change (B v) (a • v) = a * (B v v)
      simp
    _ = a ^ 2 * B v v := by ring

/-- square-root homogeneity for nonnegative scalars and nonnegative quadratic values -/
lemma sqrt_quad_smul_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {a : ℝ} (ha : 0 ≤ a) (v : E) (h : 0 ≤ B v v) :
    Real.sqrt (B (a • v) (a • v)) = a * Real.sqrt (B v v) := by
  have hm : (a * Real.sqrt (B v v)) ^ 2 = a ^ 2 * B v v := by
    rw [mul_pow, Real.sq_sqrt h]
  rw [quad_smul B a v]
  rw [← hm]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (mul_nonneg ha (Real.sqrt_nonneg _))





/-- Bundled output of `chart_normal_forward` at `p`: normal coordinates (first package),
model geodesic flow data (second package) and the forward-ray identity, all from ONE
`chart_normal_geo` call (consistent witnesses). -/
structure NormalChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (p : M) where
  ρ0 : ℝ
  hρ00 : 0 < ρ0
  ge : E → E →L[ℝ] E →L[ℝ] ℝ
  hgeC : ContDiff ℝ 3 ge
  hgeSymm : ∀ y u v : E, (ge y) u v = (ge y) v u
  hgePos : ∀ y : E, ∀ v : E, v ≠ 0 → 0 < (ge y) v v
  hgeAgree : ∀ y ∈ ball (extChartAt I p p) ρ0, ∀ u v : E,
    (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
      ((extChartAt I p).symm y)
      ((mfderiv[range I] (extChartAt I p).symm y) u)
      ((mfderiv[range I] (extChartAt I p).symm y) v)
  r : ℝ
  hr0 : 0 < r
  ExpM : E → M
  S : Set M
  invM : M → E
  hExpM0 : ExpM 0 = p
  hSnhds : S ∈ 𝓝 p
  hS_in : ∀ v ∈ ball (0 : E) r, ExpM v ∈ S
  hExpCont : ContinuousOn ExpM (ball (0 : E) r)
  hInj : Function.Injective (fun v : {v : E // v ∈ ball (0 : E) r} => ExpM v.1)
  hSurj : Set.SurjOn ExpM (ball (0 : E) r) S
  hInvS : ∀ y ∈ S, invM y ∈ ball (0 : E) r ∧ ExpM (invM y) = y
  hInvExp : ∀ v ∈ ball (0 : E) r, invM (ExpM v) = v
  hRadial : ∀ v ∈ ball (0 : E) r,
    edist p (ExpM v) = ENNReal.ofReal (Real.sqrt ((ge (extChartAt I p p)) v v))
  ρe : ℝ
  hρe0 : 0 < ρe
  hρele : ρe ≤ r
  τe : ℝ
  hτe0 : 0 < τe
  hρeτe4 : ρe ≤ τe / 4
  Φ : E × E → ℝ → E × E
  exp : E → E
  hExpExpM : ∀ v ∈ ball (0 : E) ρe, ExpM v = (extChartAt I p).symm (exp v)
  hexp0 : exp 0 = extChartAt I p p
  hExpC1 : ContDiffOn ℝ 1 exp (ball (0 : E) ρe)
  hΦODE : ∀ z ∈ closedBall (extChartAt I p p, 0) 2, Φ z 0 = z ∧
    ∀ t ∈ Ioo (-((3 / 2) * τe)) ((3 / 2) * τe),
      HasDerivAt (Φ z) (Submission.Model.odeField ge (Φ z t)) t
  hexpform : ∀ v ∈ ball (0 : E) ρe,
    exp v = (Φ (extChartAt I p p, (1 / τe) • v) τe).1
  hRay : ∀ u : E, ‖u‖ ≤ 1 → Real.sqrt ((ge (extChartAt I p p)) u u) = 1 →
    ∀ t ∈ Ioo (-(τe / 4)) (τe / 4), exp (t • u) = (Φ (extChartAt I p p, u) t).1
  ρT : ℝ
  hρT0 : 0 < ρT
  hρTle : ρT ≤ ρ0
  hρTtgt : ball (extChartAt I p p) ρT ⊆ (extChartAt I p).target
  hcv : ∀ v ∈ ball (0 : E) ρe, ∃ cv velv : ℝ → E,
    cv 0 = extChartAt I p p ∧ cv 1 = exp v ∧
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt cv (velv t) t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
       Real.sqrt ((ge (cv t)) (velv t) (velv t)) =
         Real.sqrt ((ge (extChartAt I p p)) v v)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, cv t ∈ ball (extChartAt I p p) ρT) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
       cv t = (Φ (extChartAt I p p, (1 / τe) • v) (τe * t)).1) ∧
    (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 cv O)
  hFWD : ∀ w : E, ∀ α β : ℝ, 0 ≤ α → α ≤ β → β • w ∈ ball (0 : E) ρe →
    edist (ExpM (α • w)) (ExpM (β • w)) =
      ENNReal.ofReal ((β - α) * Real.sqrt ((ge (extChartAt I p p)) w w))

/-- forward-ray identity (lower + upper) in the normal coordinates at `p` -/
theorem chart_normal_forward {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (p : M) :
    ∃ (ρ0 : ℝ), 0 < ρ0 ∧ ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ,
      ContDiff ℝ 3 ge ∧
      (∀ y u v : E, (ge y) u v = (ge y) v u) ∧
      (∀ y : E, ∀ v : E, v ≠ 0 → 0 < (ge y) v v) ∧
      (∀ y ∈ ball (extChartAt I p p) ρ0, ∀ u v : E,
         (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                       ((extChartAt I p).symm y)
                       ((mfderiv[range I] (extChartAt I p).symm y) u)
                       ((mfderiv[range I] (extChartAt I p).symm y) v)) ∧
      ∃ (r : ℝ), 0 < r ∧ ∃ ExpM : E → M, ∃ S : Set M, ∃ invM : M → E,
        ExpM 0 = p ∧ S ∈ 𝓝 p ∧
        (∀ v ∈ ball (0 : E) r, ExpM v ∈ S) ∧
        ContinuousOn ExpM (ball (0 : E) r) ∧
        Function.Injective (fun v : {v : E // v ∈ ball (0 : E) r} => ExpM v.1) ∧
        Set.SurjOn ExpM (ball (0 : E) r) S ∧
        (∀ y ∈ S, invM y ∈ ball (0 : E) r ∧ ExpM (invM y) = y) ∧
        (∀ v ∈ ball (0 : E) r, invM (ExpM v) = v) ∧
        (∀ v ∈ ball (0 : E) r,
           edist p (ExpM v) = ENNReal.ofReal (Real.sqrt ((ge (extChartAt I p p)) v v))) ∧
        ∃ ρe > 0, ρe ≤ r ∧ ∃ τe : ℝ, 0 < τe ∧ ρe ≤ τe / 4 ∧
          ∃ Φ : E × E → ℝ → E × E, ∃ exp : E → E,
            (∀ v ∈ ball (0 : E) ρe, ExpM v = (extChartAt I p).symm (exp v)) ∧
            exp 0 = extChartAt I p p ∧
            ContDiffOn ℝ 1 exp (ball (0 : E) ρe) ∧
            (∀ z ∈ closedBall (extChartAt I p p, 0) 2, Φ z 0 = z ∧
               ∀ t ∈ Ioo (-((3 / 2) * τe)) ((3 / 2) * τe),
                 HasDerivAt (Φ z) (Submission.Model.odeField ge (Φ z t)) t) ∧
            (∀ v ∈ ball (0 : E) ρe,
               exp v = (Φ (extChartAt I p p, (1 / τe) • v) τe).1) ∧
            (∀ u : E, ‖u‖ ≤ 1 → Real.sqrt ((ge (extChartAt I p p)) u u) = 1 →
               ∀ t ∈ Ioo (-(τe / 4)) (τe / 4),
                 exp (t • u) = (Φ (extChartAt I p p, u) t).1) ∧
            (∃ ρT > 0, ρT ≤ ρ0 ∧
               ball (extChartAt I p p) ρT ⊆ (extChartAt I p).target ∧
               (∀ v ∈ ball (0 : E) ρe, ∃ cv velv : ℝ → E,
                 cv 0 = extChartAt I p p ∧ cv 1 = exp v ∧
                 (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt cv (velv t) t) ∧
                 (∀ t ∈ Icc (0 : ℝ) 1,
                    Real.sqrt ((ge (cv t)) (velv t) (velv t)) =
                      Real.sqrt ((ge (extChartAt I p p)) v v)) ∧
                 (∀ t ∈ Icc (0 : ℝ) 1, cv t ∈ ball (extChartAt I p p) ρT) ∧
                 (∀ t ∈ Icc (0 : ℝ) 1,
                    cv t = (Φ (extChartAt I p p, (1 / τe) • v) (τe * t)).1) ∧
                 (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 cv O))) ∧
          (∀ w : E, ∀ α β : ℝ, 0 ≤ α → α ≤ β → β • w ∈ ball (0 : E) ρe →
             edist (ExpM (α • w)) (ExpM (β • w)) =
               ENNReal.ofReal ((β - α) * Real.sqrt ((ge (extChartAt I p p)) w w))) := by
  rcases chart_normal_geo (I := I) (M := M) p with
    ⟨ρ0, hρ00, ge, hgeC, hgeSymm, hgePos, hgeAgree, hrest⟩
  rcases hrest with ⟨r, hr0, ExpM, S, invM, hExpM0, hSnhds, hS_in, hExpCont, hInj,
    hSurj, hInvS, hInvExp, hRadial, hrest2⟩
  rcases hrest2 with ⟨ρe, hρe0, τe, hτe0, hρele, hρeτe4, Φ, expm,
    hExpExpM, hexp0, hExpC1, hΦODE, hexpform, hRay, hrest3⟩
  rcases hrest3 with ⟨ρT, hρT0, hρTle, hρTtgt, hcv⟩
  let x₀ : E := extChartAt I p p
  have hBnonneg : ∀ v : E, 0 ≤ (ge x₀) v v := by
    intro v
    by_cases hv : v = 0
    · subst v; simp
    · exact le_of_lt (hgePos x₀ v hv)
  refine ⟨ρ0, hρ00, ge, hgeC, hgeSymm, hgePos, hgeAgree, ⟨r, hr0, ExpM, S, invM,
    hExpM0, hSnhds, hS_in, hExpCont, hInj, hSurj, hInvS, hInvExp, hRadial,
    ⟨ρe, hρe0, hρele, τe, hτe0, hρeτe4, Φ, expm,
      ⟨hExpExpM, hexp0, hExpC1, hΦODE, hexpform, hRay,
        ⟨ρT, hρT0, hρTle, hρTtgt, hcv⟩, ?_⟩⟩⟩⟩
  intro w α β hα hαβ hβw
  have hβ : 0 ≤ β := le_trans hα hαβ
  have hαw_r : α • w ∈ ball (0 : E) r := by
    rw [mem_ball, dist_eq_norm]
    have hn : ‖α • w‖ ≤ ‖β • w‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg hα, abs_of_nonneg hβ]
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left hαβ (norm_nonneg w))
    have hlt : ‖β • w‖ < r := by
      have hm := (mem_ball.mp hβw)
      simpa [dist_eq_norm] using (lt_of_lt_of_le hm hρele)
    simpa [sub_zero] using lt_of_le_of_lt (by simpa [sub_zero] using hn) hlt
  have hβw_r : β • w ∈ ball (0 : E) r := by
    have hm := (mem_ball.mp hβw)
    simpa [dist_eq_norm] using (lt_of_lt_of_le hm hρele)
  have hdα : edist p (ExpM (α • w)) = ENNReal.ofReal (α * Real.sqrt ((ge x₀) w w)) := by
    have hd := hRadial (α • w) hαw_r
    calc
      edist p (ExpM (α • w)) = ENNReal.ofReal (Real.sqrt ((ge x₀) (α • w) (α • w))) := by
        simpa [x₀] using hd
      _ = ENNReal.ofReal (α * Real.sqrt ((ge x₀) w w)) := by
        congr 1
        rw [sqrt_quad_smul_nonneg (ge x₀) hα w (hBnonneg w)]
  have hdβ : edist p (ExpM (β • w)) = ENNReal.ofReal (β * Real.sqrt ((ge x₀) w w)) := by
    have hd := hRadial (β • w) hβw_r
    calc
      edist p (ExpM (β • w)) = ENNReal.ofReal (Real.sqrt ((ge x₀) (β • w) (β • w))) := by
        simpa [x₀] using hd
      _ = ENNReal.ofReal (β * Real.sqrt ((ge x₀) w w)) := by
        congr 1
        rw [sqrt_quad_smul_nonneg (ge x₀) hβ w (hBnonneg w)]
  have htri : edist p (ExpM (β • w)) ≤
      edist p (ExpM (α • w)) + edist (ExpM (α • w)) (ExpM (β • w)) :=
    edist_triangle (x := p) (y := ExpM (α • w)) (z := ExpM (β • w))
  have htri' : edist p (ExpM (β • w)) ≤
      edist (ExpM (α • w)) (ExpM (β • w)) + edist p (ExpM (α • w)) := by
    simpa [add_comm] using htri
  have hrev : edist p (ExpM (β • w)) - edist p (ExpM (α • w)) ≤
      edist (ExpM (α • w)) (ExpM (β • w)) := (tsub_le_iff_right).2 htri'
  have hup_lower : ENNReal.ofReal ((β - α) * Real.sqrt ((ge x₀) w w)) ≤
      edist (ExpM (α • w)) (ExpM (β • w)) := by
    have hw0 : 0 ≤ Real.sqrt ((ge x₀) w w) := Real.sqrt_nonneg _
    calc
      ENNReal.ofReal ((β - α) * Real.sqrt ((ge x₀) w w))
          = ENNReal.ofReal (β * Real.sqrt ((ge x₀) w w) - α * Real.sqrt ((ge x₀) w w)) := by
              congr 1
              ring
      _ = ENNReal.ofReal (β * Real.sqrt ((ge x₀) w w)) - ENNReal.ofReal (α * Real.sqrt ((ge x₀) w w)) := by
              rw [ENNReal.ofReal_sub (β * Real.sqrt ((ge x₀) w w)) (mul_nonneg hα hw0)]
      _ = edist p (ExpM (β • w)) - edist p (ExpM (α • w)) := by
              rw [← hdβ, ← hdα]
      _ ≤ edist (ExpM (α • w)) (ExpM (β • w)) := hrev
  -- upper bound
  have hαw_ρe : α • w ∈ ball (0 : E) ρe := by
    rw [mem_ball, dist_eq_norm]
    have hn : ‖α • w‖ ≤ ‖β • w‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg hα, abs_of_nonneg hβ]
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left hαβ (norm_nonneg w))
    have hmem := (mem_ball.mp hβw)
    simpa [sub_zero, dist_eq_norm] using lt_of_le_of_lt (by simpa [sub_zero] using hn) hmem
  have hup_upper : edist (ExpM (α • w)) (ExpM (β • w)) ≤
      ENNReal.ofReal ((β - α) * Real.sqrt ((ge x₀) w w)) := by
    by_cases hβ0 : β = 0
    · subst β
      have hα0 : α = 0 := by linarith
      subst α
      simp [hExpM0]
    · have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      have hpt : expm (α • w) = (Φ (x₀, (1 / τe) • (β • w)) (τe * (α / β))).1 := by
        by_cases hαz : α = 0
        · subst α
          have hz1z : (x₀, (1 / τe) • (β • w)) ∈ closedBall (x₀, 0) 2 := by
            rw [mem_closedBall, dist_eq_norm]
            have hb : ‖(x₀, (1 / τe) • (β • w)) - (x₀, 0)‖ = ‖(1 / τe) • (β • w)‖ := by simp
            rw [hb]
            have hmem := (mem_ball.mp hβw)
            have hpos : 0 < (1 / τe : ℝ) := by positivity
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
            have hmem' : ‖β • w‖ < ρe := by simpa [dist_eq_norm] using hmem
            have hle : (1 / τe) * ‖β • w‖ < (1 / τe) * ρe :=
              mul_lt_mul_of_pos_left hmem' hpos
            have hle2 : (1 / τe) * ρe ≤ 1 / 4 := by
              have hstep : (1 / τe) * (τe / 4) = 1 / 4 := by
                field_simp [ne_of_gt hτe0]
              nlinarith [hρeτe4]
            nlinarith
          have hz0 : (Φ (x₀, (1 / τe) • (β • w)) 0).1 = x₀ :=
            congrArg Prod.fst (hΦODE (x₀, (1 / τe) • (β • w)) hz1z).1
          simpa [x₀, hexp0] using hz0.symm
        · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hαz)
          let z1 : E × E := (x₀, (1 / τe) • (β • w))
          let z2 : E × E := (x₀, (1 / τe) • (α • w))
          have hz1 : z1 ∈ closedBall (x₀, 0) 2 := by
            rw [mem_closedBall, dist_eq_norm]
            have hb : ‖(x₀, (1 / τe) • (β • w)) - (x₀, 0)‖ = ‖(1 / τe) • (β • w)‖ := by simp
            rw [hb]
            have hmem := (mem_ball.mp hβw)
            have hpos : 0 < (1 / τe : ℝ) := by positivity
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
            have hmem' : ‖β • w‖ < ρe := by simpa [dist_eq_norm] using hmem
            have hle : (1 / τe) * ‖β • w‖ < (1 / τe) * ρe :=
              mul_lt_mul_of_pos_left hmem' hpos
            have hle2 : (1 / τe) * ρe ≤ 1 / 4 := by
              have hstep : (1 / τe) * (τe / 4) = 1 / 4 := by
                field_simp [ne_of_gt hτe0]
              nlinarith [hρeτe4]
            nlinarith
          have hz2 : z2 ∈ closedBall (x₀, 0) 2 := by
            rw [mem_closedBall, dist_eq_norm]
            have hb : ‖(x₀, (1 / τe) • (α • w)) - (x₀, 0)‖ = ‖(1 / τe) • (α • w)‖ := by simp
            rw [hb]
            have hmem := (mem_ball.mp hαw_ρe)
            have hpos : 0 < (1 / τe : ℝ) := by positivity
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
            have hmem' : ‖α • w‖ < ρe := by simpa [dist_eq_norm] using hmem
            have hle : (1 / τe) * ‖α • w‖ < (1 / τe) * ρe :=
              mul_lt_mul_of_pos_left hmem' hpos
            have hle2 : (1 / τe) * ρe ≤ 1 / 4 := by
              have hstep : (1 / τe) * (τe / 4) = 1 / 4 := by
                field_simp [ne_of_gt hτe0]
              nlinarith [hρeτe4]
            nlinarith
          let c₁ : ℝ → E := fun t => (Φ z1 t).1
          let vel₁ : ℝ → E := fun t => (Φ z1 t).2
          let c₂ : ℝ → E := fun t => (Φ z2 t).1
          let vel₂ : ℝ → E := fun t => (Φ z2 t).2
          have hε : 0 < (3 / 2) * τe := by positivity
          have hode₁ : ∀ t ∈ Ioo (-((3 / 2) * τe)) ((3 / 2) * τe), HasDerivAt c₁ (vel₁ t) t := by
            intro t ht
            have hf := (hΦODE z1 hz1).2 t ht
            have h1 : HasDerivAt (fun s : ℝ => (Φ z1 s).1) (Submission.Model.odeField ge (Φ z1 t)).1 t := by
              simpa using hf.hasFDerivAt.fst.hasDerivAt
            simpa [c₁, vel₁, Submission.Model.odeField] using h1
          have hvode₁ : ∀ t ∈ Ioo (-((3 / 2) * τe)) ((3 / 2) * τe),
              HasDerivAt vel₁ (Submission.Model.accel (ge (c₁ t)) (fderiv ℝ ge (c₁ t)) (vel₁ t)) t := by
            intro t ht
            have hf := (hΦODE z1 hz1).2 t ht
            have h1 : HasDerivAt (fun s : ℝ => (Φ z1 s).2) (Submission.Model.odeField ge (Φ z1 t)).2 t := by
              simpa using hf.hasFDerivAt.snd.hasDerivAt
            simpa [c₁, vel₁, Submission.Model.odeField, Submission.Model.accel] using h1
          have hode₂ : ∀ t ∈ Ioo (-((3 / 2) * τe)) ((3 / 2) * τe), HasDerivAt c₂ (vel₂ t) t := by
            intro t ht
            have hf := (hΦODE z2 hz2).2 t ht
            have h1 : HasDerivAt (fun s : ℝ => (Φ z2 s).1) (Submission.Model.odeField ge (Φ z2 t)).1 t := by
              simpa using hf.hasFDerivAt.fst.hasDerivAt
            simpa [c₂, vel₂, Submission.Model.odeField] using h1
          have hvode₂ : ∀ t ∈ Ioo (-((3 / 2) * τe)) ((3 / 2) * τe),
              HasDerivAt vel₂ (Submission.Model.accel (ge (c₂ t)) (fderiv ℝ ge (c₂ t)) (vel₂ t)) t := by
            intro t ht
            have hf := (hΦODE z2 hz2).2 t ht
            have h1 : HasDerivAt (fun s : ℝ => (Φ z2 s).2) (Submission.Model.odeField ge (Φ z2 t)).2 t := by
              simpa using hf.hasFDerivAt.snd.hasDerivAt
            simpa [c₂, vel₂, Submission.Model.odeField, Submission.Model.accel] using h1
          have hc₁0 : c₁ 0 = x₀ := by
            dsimp [c₁]
            exact congrArg Prod.fst (hΦODE z1 hz1).1
          have hv₁0 : vel₁ 0 = (1 / τe) • (β • w) := by
            dsimp [vel₁]
            have h0 := congrArg Prod.snd (hΦODE z1 hz1).1
            simpa [z1] using h0
          have hc₂0 : c₂ 0 = x₀ := by
            dsimp [c₂]
            exact congrArg Prod.fst (hΦODE z2 hz2).1
          have hv₂0 : vel₂ 0 = (α / β) • ((1 / τe) • (β • w)) := by
            dsimp [vel₂]
            have h0 := congrArg Prod.snd (hΦODE z2 hz2).1
            have h0' : (Φ z2 0).2 = (1 / τe) • (α • w) := by simpa [z2] using h0
            rw [h0']
            have hscal : (1 / τe) * α = (α / β) * ((1 / τe) * β) := by
              field_simp [ne_of_gt hτe0, ne_of_gt hβpos]
            calc
              (1 / τe) • (α • w) = ((1 / τe) * α) • w := by rw [smul_smul]
              _ = ((α / β) * ((1 / τe) * β)) • w := by rw [hscal]
              _ = (α / β) • ((1 / τe) • (β • w)) := by
                rw [smul_smul, smul_smul]
                congr 1
                ring
          have hs : α / β ≠ 0 := div_ne_zero (ne_of_gt hαpos) (ne_of_gt hβpos)
          have hsc := Submission.Model.flow_scaling (g := ge) (hg := hgeC) (hinv := by
            intro y
            exact bilin_isInvertible_of_pos (ge y) (hgePos y))
            (ε₁ := (3 / 2) * τe) (hε₁ := hε) (ε₂ := (3 / 2) * τe) (hε₂ := hε)
            (c₁ := c₁) (vel₁ := vel₁) (c₂ := c₂) (vel₂ := vel₂)
            (x := x₀) (v := (1 / τe) • (β • w)) (s := α / β) (hs := hs)
            (hc₁ := hc₁0) (hv₁ := hv₁0) (hc₁d := hode₁) (hv₁d := hvode₁)
            (hc₂ := hc₂0) (hv₂ := hv₂0) (hc₂d := hode₂) (hv₂d := hvode₂)
          have hτe_mem : τe ∈ Ioo (-min ((3 / 2) * τe) (((3 / 2) * τe) / |α / β|))
              (min ((3 / 2) * τe) (((3 / 2) * τe) / |α / β|)) := by
            have habs : 0 < |α / β| := abs_pos.mpr hs
            constructor
            · have hminpos : 0 < min ((3 / 2) * τe) (((3 / 2) * τe) / |α / β|) :=
                lt_min (by positivity) (div_pos (by positivity) habs)
              linarith
            · apply lt_min
              · linarith
              · rw [lt_div_iff₀ habs]
                have hαβ' : |α / β| ≤ 1 := by
                  rw [abs_div, abs_of_pos hβpos]
                  rw [div_le_one hβpos]
                  rw [abs_of_nonneg hα]
                  exact hαβ
                calc
                  τe * |α / β| ≤ τe * 1 := mul_le_mul_of_nonneg_left hαβ' (le_of_lt hτe0)
                  _ < (3 / 2) * τe := by nlinarith [hτe0]
          have hmain := hsc τe hτe_mem
          calc
            expm (α • w) = (Φ (x₀, (1 / τe) • (α • w)) τe).1 := by
              simpa [x₀] using (hexpform (α • w) hαw_ρe)
            _ = (Φ z2 τe).1 := rfl
            _ = c₂ τe := rfl
            _ = c₁ ((α / β) * τe) := hmain.1
            _ = c₁ (τe * (α / β)) := by congr 1; ring
            _ = (Φ (x₀, (1 / τe) • (β • w)) (τe * (α / β))).1 := by rfl
      rcases hcv (β • w) hβw with ⟨cv, velv, hcv0, hcv1, hcvd, hcvsp, hcvstay, hcvform, hcvO⟩
      let t0 : ℝ := α / β
      have ht0ge : 0 ≤ t0 := div_nonneg hα (le_of_lt hβpos)
      have ht0le : t0 ≤ 1 := (div_le_one hβpos).mpr hαβ
      have hcv0' : cv t0 = expm (α • w) := by
        have hf := hcvform t0 (by
          constructor
          · exact div_nonneg hα (le_of_lt hβpos)
          · exact (div_le_one hβpos).mpr hαβ)
        rw [hf, hpt]
      let σ : ℝ → M := fun t => (extChartAt I p).symm (cv t)
      have hσ0 : σ t0 = ExpM (α • w) := by
        dsimp [σ]
        rw [hcv0']
        exact (hExpExpM (α • w) hαw_ρe).symm
      have hσ1 : σ 1 = ExpM (β • w) := by
        dsimp [σ]
        rw [hcv1]
        exact (hExpExpM (β • w) hβw).symm
      have hσC : ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (0 : ℝ) 1) := by
        rcases hcvO with ⟨O, hOopen, hOIcc, hcvC1⟩
        have hcvC1I : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 cv (Icc (0 : ℝ) 1) :=
          ((contMDiffOn_iff_contDiffOn).mpr hcvC1).mono hOIcc
        have hsubI : Set.MapsTo cv (Icc (0 : ℝ) 1) (extChartAt I p).target := by
          intro t ht
          exact hρTtgt (hcvstay t ht)
        have hmainC := ContMDiffOn.comp (contMDiffOn_extChartAt_symm (I := I) p) hcvC1I hsubI
        have hσeq : Set.EqOn σ ((extChartAt I p).symm ∘ cv) (Icc (0 : ℝ) 1) := by
          intro t ht
          rfl
        exact hmainC.congr hσeq
      have hspeed : ∀ t ∈ Icc t0 1, ‖mfderiv% σ t 1‖ₑ =
          ENNReal.ofReal (Real.sqrt ((ge x₀) (β • w) (β • w))) := by
        intro t ht
        have hmem : t ∈ Icc (0 : ℝ) 1 := by
          constructor
          · exact le_trans ht0ge ht.1
          · exact ht.2
        have hcvball : cv t ∈ ball (extChartAt I p p) ρT := hcvstay t hmem
        have hγeq : ∀ s : ℝ, σ s = (extChartAt I p).symm (cv s) := by intro s; rfl
        have hspd := chart_speed_core (I := I) (M := M) (E := E) p
          (ρ := ρT) (ge := ge)
          (by intro y hy u v; exact hgeAgree y (ball_subset_ball hρTle hy) u v)
          (by simpa [x₀] using hρTtgt)
          (hγeq := hγeq) (hcball := hcvball) (hu := hcvd t hmem)
        have hsq : Real.sqrt ((ge (cv t)) (velv t) (velv t)) = Real.sqrt ((ge x₀) (β • w) (β • w)) := by
          simpa [x₀] using (hcvsp t hmem)
        calc
          ‖mfderiv% σ t 1‖ₑ = ENNReal.ofReal (Real.sqrt ((ge (cv t)) (velv t) (velv t))) := hspd
          _ = ENNReal.ofReal (Real.sqrt ((ge x₀) (β • w) (β • w))) := by rw [hsq]
      have hpath : Manifold.pathELength I σ t0 1 ≤
          ENNReal.ofReal ((1 - t0) * Real.sqrt ((ge x₀) (β • w) (β • w))) := by
        rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
        calc
          (∫⁻ t in Icc t0 1, ‖mfderiv% σ t 1‖ₑ)
              = ∫⁻ t in Icc t0 1, ENNReal.ofReal (Real.sqrt ((ge x₀) (β • w) (β • w))) :=
                  MeasureTheory.setLIntegral_congr_fun measurableSet_Icc hspeed
          _ = ENNReal.ofReal (Real.sqrt ((ge x₀) (β • w) (β • w))) * volume (Icc t0 1) := by
              rw [MeasureTheory.setLIntegral_const]
          _ ≤ ENNReal.ofReal ((1 - t0) * Real.sqrt ((ge x₀) (β • w) (β • w))) := by
              rw [Real.volume_Icc]
              have hd0 : 0 ≤ 1 - t0 := by linarith
              rw [mul_comm, ← ENNReal.ofReal_mul hd0]
      have hdst : Manifold.riemannianEDist I (ExpM (α • w)) (ExpM (β • w)) ≤
          Manifold.pathELength I σ t0 1 := by
        exact Manifold.riemannianEDist_le_pathELength (I := I) (hσC.mono (by
          intro t ht
          constructor
          · exact le_trans ht0ge ht.1
          · exact ht.2)) hσ0 hσ1 ht0le
      have hdst' : edist (ExpM (α • w)) (ExpM (β • w)) ≤ Manifold.pathELength I σ t0 1 := by
        simpa [IsRiemannianManifold.out (I := I) (ExpM (α • w)) (ExpM (β • w))] using hdst
      have hfin : (1 - t0) * Real.sqrt ((ge x₀) (β • w) (β • w)) = (β - α) * Real.sqrt ((ge x₀) w w) := by
        have hsqβ : Real.sqrt ((ge x₀) (β • w) (β • w)) = β * Real.sqrt ((ge x₀) w w) := by
          rw [sqrt_quad_smul_nonneg (ge x₀) hβ w (hBnonneg w)]
        dsimp [t0]
        rw [hsqβ]
        field_simp [ne_of_gt hβpos]
      calc
        edist (ExpM (α • w)) (ExpM (β • w)) ≤ Manifold.pathELength I σ t0 1 := hdst'
        _ ≤ ENNReal.ofReal ((1 - t0) * Real.sqrt ((ge x₀) (β • w) (β • w))) := hpath
        _ = ENNReal.ofReal ((β - α) * Real.sqrt ((ge x₀) w w)) := by rw [hfin]
  exact le_antisymm hup_upper hup_lower


open ContinuousLinearMap

/-- bilinear expansion of `B (u + t v) (u + t v)` -/
lemma bilin_quad_add_smul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) (t : ℝ) :
    B (u + t • v) (u + t • v) =
      B u u + t * B u v + t * B v u + t * t * B v v := by
  have hL1 : (B u) (u + t • v) = B u u + t • (B u) v := by simp
  have hL2 : (B v) (u + t • v) = B v u + t • (B v) v := by simp
  have hB : B (u + t • v) = B u + t • B v := by
    ext w
    change (B (u + t • v)) w = (B u + t • B v) w
    simp [map_add, map_smul]
  calc
    B (u + t • v) (u + t • v) = (B u + t • B v) (u + t • v) := by rw [hB]
    _ = (B u) (u + t • v) + (t • B v) (u + t • v) := by simp
    _ = (B u u + t • (B u) v) + t • (B v) (u + t • v) := by rw [hL1]; simp
    _ = (B u u + t • (B u) v) + t • (B v u + t • (B v) v) := by rw [hL2]
    _ = B u u + t * B u v + t * B v u + t * t * B v v := by simp; ring

/-- bilinear expansion of `B (u - t v) (u - t v)` (symmetric case) -/
lemma bilin_quad_sub_smul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ u v : E, B u v = B v u)
    (u v : E) (t : ℝ) :
    B (u - t • v) (u - t • v) =
      B u u - 2 * t * B u v + t * t * B v v := by
  have hx := bilin_quad_add_smul' B u v (-t)
  have hs0 : B v u = B u v := hsym v u
  rw [hs0] at hx
  have hneg : u + (-t) • v = u - t • v := by
    rw [sub_eq_add_neg, neg_smul]
  rw [hneg] at hx
  -- hx : B (u - t•v)(u - t•v) = Buu + (-t)Buv + (-t)Buv + (-t)(-t)Bvv
  convert hx using 1
  ring

/-- equality case of Cauchy-Schwarz for a positive definite symmetric bilinear form -/
lemma bilin_cs_eq_colinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ u v : E, B u v = B v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u)
    {u v : E} (hne : v ≠ 0) (hu : u ≠ 0)
    (heq : B u v * B u v = B u u * B v v) :
    ∃ t : ℝ, u = t • v := by
  have hc : B v v ≠ 0 := by
    intro h0
    have : (0 : ℝ) < B v v := hpos v hne
    linarith
  let t0 : ℝ := B u v / B v v
  have hsqeq (t : ℝ) : B v v * B (u - t • v) (u - t • v) =
      (t * B v v - B u v) ^ 2 + (B u u * B v v - B u v * B u v) := by
    have hx := bilin_quad_sub_smul' B hsym u v t
    rw [hx]
    ring
  have hX : B (u - t0 • v) (u - t0 • v) = 0 := by
    have hbig : B v v * B (u - t0 • v) (u - t0 • v) = 0 := by
      rw [hsqeq t0]
      have hz0 : B u u * B v v - B u v * B u v = 0 := by
        rw [← heq]
        ring
      rw [hz0, add_zero]
      have hlin : ((t0 * B v v - B u v) ^ 2) = 0 := by
        dsimp [t0]
        have hmm : (B u v / B v v) * B v v - B u v = 0 := by
          rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hc, mul_one]
          ring
        rw [hmm]
        ring
      exact hlin
    rcases mul_eq_zero.mp hbig with hvv | hX
    · exact False.elim (hc hvv)
    · exact hX
  by_cases hw : u - t0 • v = 0
  · exact ⟨t0, eq_of_sub_eq_zero hw⟩
  · have hp : (0 : ℝ) < B (u - t0 • v) (u - t0 • v) := hpos (u - t0 • v) hw
    linarith

/-- A c-locally-linear curve on `(a,b)` with limit `q` at `b⁻` satisfies
`edist q (γ t) ≤ c * (b - t)` for all `t ∈ (a,b)` (Lipschitz + limit). -/
lemma lin_tendsto_q_edist_le {M : Type*} [PseudoEMetricSpace M]
    {a b : ℝ} (hab : a < b) {c : NNReal} {γ : ℝ → M} {q : M}
    (hγ : Metric.IsLocLinear a b c γ) (hlim : Tendsto γ (𝓝[Iio b] b) (𝓝 q)) :
    ∀ t ∈ Ioo a b, edist q (γ t) ≤ (c : ℝ≥0∞) * ENNReal.ofReal (b - t) := by
  intro t ht
  have hbt : 0 < b - t := sub_pos.mpr ht.2
  have hc0 : 0 ≤ (c : ℝ) := c.2
  have hcont : Continuous (fun x : M => edist x (γ t)) := by
    continuity
  let s : ℕ → ℝ := fun n => b - (b - t) / ((n : ℝ) + 2)
  have hn0 (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hs_gt_t (n : ℕ) : t < s n := by
    dsimp [s]
    have hd : 1 < (n : ℝ) + 2 := by nlinarith [hn0 n]
    have hdiv : (b - t) / ((n : ℝ) + 2) < b - t := div_lt_self hbt hd
    linarith
  have hs_lt_b (n : ℕ) : s n < b := by
    dsimp [s]
    have hpos : 0 < (b - t) / ((n : ℝ) + 2) := by positivity
    linarith
  have hs_ab (n : ℕ) : s n ∈ Ioo a b := ⟨lt_trans ht.1 (hs_gt_t n), hs_lt_b n⟩
  have hfrac0 : Tendsto (fun n : ℕ => (b - t) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have htop : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => (((n : ℝ) + 2))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp htop
    have hmul : Tendsto (fun n : ℕ => (b - t) * (((n : ℝ) + 2))⁻¹) atTop (𝓝 ((b - t) * 0)) :=
      tendsto_const_nhds.mul hinv
    simpa [div_eq_mul_inv] using hmul
  have hsn_tend : Tendsto s atTop (𝓝[Iio b] b) := by
    intro V hV
    have hV' : ∃ l ∈ Ico t b, Ioo l b ⊆ V :=
      (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset (a := b) (l' := t) (s := V) ht.2).mp hV
    rcases hV' with ⟨l, hl, hsub⟩
    have hbl : 0 < b - l := sub_pos.mpr hl.2
    have hfrac_lt : ∀ᶠ n : ℕ in (atTop : Filter ℕ), (b - t) / ((n : ℝ) + 2) < b - l := by
      have hmem0 : {r : ℝ | r < b - l} ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds hbl
      exact (Filter.Tendsto.eventually hfrac0 hmem0)
    have hev_mem : ∀ᶠ n : ℕ in (atTop : Filter ℕ), s n ∈ Ioo l b := by
      filter_upwards [hfrac_lt] with n hn
      constructor
      · dsimp [s]
        linarith
      · exact hs_lt_b n
    exact hev_mem.mono (fun n hn => hsub hn)
  have hsγ_tend : Tendsto (fun n : ℕ => γ (s n)) atTop (𝓝 q) := by
    simpa [Function.comp_def] using hlim.comp hsn_tend
  have hTend1 : Tendsto (fun n : ℕ => edist (γ (s n)) (γ t)) atTop (𝓝 (edist q (γ t))) := by
    simpa [Function.comp_def] using hcont.continuousAt.tendsto.comp hsγ_tend
  have hbound_tend : Tendsto (fun n : ℕ => ENNReal.ofReal ((c : ℝ) * (s n - t)))
      atTop (𝓝 (ENNReal.ofReal ((c : ℝ) * (b - t)))) := by
    have hdiff : Tendsto (fun n : ℕ => s n - t) atTop (𝓝 (b - t)) := by
      have hb : Tendsto s atTop (𝓝 b) := hsn_tend.mono_right nhdsWithin_le_nhds
      exact hb.sub_const t
    have hcm : Tendsto (fun n : ℕ => (c : ℝ) * (s n - t)) atTop (𝓝 ((c : ℝ) * (b - t))) := by
      simpa using tendsto_const_nhds.mul hdiff
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hcm
  have hpoint (n : ℕ) : edist (γ (s n)) (γ t) ≤
      ENNReal.ofReal ((c : ℝ) * (s n - t)) := by
    have hst : t ≤ s n := le_of_lt (hs_gt_t n)
    have hle := Metric.IsLocLinear.edist_le_of_le hγ ht (hs_ab n) hst
    have hmain : edist (γ (s n)) (γ t) ≤ (c : ℝ≥0∞) * ENNReal.ofReal (s n - t) := by
      simpa [edist_comm] using hle
    calc
      edist (γ (s n)) (γ t) ≤ (c : ℝ≥0∞) * ENNReal.ofReal (s n - t) := hmain
      _ = ENNReal.ofReal (c : ℝ) * ENNReal.ofReal (s n - t) := by
        rw [ENNReal.ofReal_coe_nnreal]
      _ = ENNReal.ofReal ((c : ℝ) * (s n - t)) := by
        rw [← ENNReal.ofReal_mul hc0]
  have hfin : ∀ᶠ n : ℕ in (atTop : Filter ℕ), edist (γ (s n)) (γ t) ≤
      ENNReal.ofReal ((c : ℝ) * (s n - t)) := by
    exact (Filter.eventually_atTop.mpr ⟨0, fun n hn => hpoint n⟩)
  have hineq : edist q (γ t) ≤ ENNReal.ofReal ((c : ℝ) * (b - t)) :=
    le_of_tendsto_of_tendsto hTend1 hbound_tend hfin
  calc
    edist q (γ t) ≤ ENNReal.ofReal ((c : ℝ) * (b - t)) := hineq
    _ = ENNReal.ofReal (c : ℝ) * ENNReal.ofReal (b - t) := by
      rw [ENNReal.ofReal_mul hc0]
    _ = (c : ℝ≥0∞) * ENNReal.ofReal (b - t) := by
      rw [ENNReal.ofReal_coe_nnreal]


/-- A positive definite quadratic form on a finite-dimensional space is bounded below by a
positive multiple of the square of the norm. -/
lemma quad_ellipsoid_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ u : E, u ≠ 0 → 0 < Q u u) :
    ∃ m : ℝ, 0 < m ∧ ∀ u : E, m * ‖u‖ ^ 2 ≤ Q u u := by
  have hfcont : Continuous (fun u : E => Q u u) := by
    have hQ : Continuous (fun u : E => Q u) := ContinuousLinearMap.continuous Q
    exact Continuous.clm_apply hQ continuous_id
  by_cases hE : ∃ u : E, u ≠ 0
  · rcases hE with ⟨w, hw⟩
    let u₀ : E := (‖w‖⁻¹) • w
    have hu₀ : ‖u₀‖ = 1 := by
      dsimp [u₀]
      rw [norm_smul]
      have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hwinv : 0 ≤ ‖w‖⁻¹ := inv_nonneg.mpr (le_of_lt hw0)
      rw [Real.norm_eq_abs, abs_of_nonneg hwinv]
      field_simp [ne_of_gt hw0]
    have hS : IsCompact (sphere (0 : E) 1) := isCompact_sphere (0 : E) 1
    have hSne : (sphere (0 : E) 1).Nonempty := ⟨u₀, by simpa [dist_eq_norm] using hu₀⟩
    rcases hS.exists_isMinOn hSne hfcont.continuousOn with ⟨v, hvS, hvmin⟩
    have hv1 : ‖v‖ = 1 := by simpa [dist_eq_norm] using hvS
    have hvne : v ≠ 0 := by
      intro hv
      have : ‖v‖ = 0 := by simp [hv]
      linarith
    refine ⟨Q v v, hpos v hvne, ?_⟩
    intro u
    by_cases hu : u = 0
    · subst u
      simp
    · have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
      let u' : E := (‖u‖⁻¹) • u
      have hu'S : u' ∈ sphere (0 : E) 1 := by
        simp only [dist_eq_norm, mem_sphere]
        dsimp [u']
        rw [sub_zero]
        rw [norm_smul]
        have huinv : 0 ≤ ‖u‖⁻¹ := inv_nonneg.mpr (le_of_lt hu0)
        rw [Real.norm_eq_abs, abs_of_nonneg huinv]
        field_simp [ne_of_gt hu0]
      have hmin' : Q v v ≤ Q u' u' := hvmin hu'S
      have hsc : Q u' u' = ‖u‖⁻¹ ^ 2 * Q u u := by
        dsimp [u']
        rw [quad_smul Q (‖u‖⁻¹) u]
      rw [hsc] at hmin'
      have hrel : (Q v v) * ‖u‖ ^ 2 ≤ Q u u := by
        have hmul := mul_le_mul_of_nonneg_right hmin' (sq_nonneg (‖u‖) )
        -- hmin' : Q v v ≤ ‖u‖⁻¹^2 * Q u u ; multiply both sides by ‖u‖^2:
        have h1 : (Q v v) * ‖u‖ ^ 2 ≤ (‖u‖⁻¹ ^ 2 * Q u u) * ‖u‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right hmin' (sq_nonneg ‖u‖)
        have hinv : ‖u‖⁻¹ ^ 2 * ‖u‖ ^ 2 = 1 := by
          rw [← mul_pow]
          field_simp [ne_of_gt hu0]
        have hstep : (‖u‖⁻¹ ^ 2 * (Q u u)) * ‖u‖ ^ 2 = (Q u u) := by
          calc
            (‖u‖⁻¹ ^ 2 * (Q u u)) * ‖u‖ ^ 2 = (Q u u) * (‖u‖⁻¹ ^ 2 * ‖u‖ ^ 2) := by ring
            _ = (Q u u) := by rw [hinv, mul_one]
        rwa [hstep] at h1
      calc
        (Q v v) * ‖u‖ ^ 2 ≤ Q u u := hrel
        _ = Q u u := rfl
  · have hzero : ∀ u : E, u = 0 := by
      intro u
      by_contra hu
      exact hE ⟨u, hu⟩
    refine ⟨1, by norm_num, ?_⟩
    intro u
    have hu : u = 0 := hzero u
    subst u
    simp

/-- Directions with bounded quadratic speed have bounded norm (uniformly). -/
lemma norm_bound_of_quad_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ u : E, u ≠ 0 → 0 < Q u u)
    (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ V : E, Real.sqrt (Q V V) ≤ c → ‖V‖ ≤ K := by
  rcases quad_ellipsoid_bound Q hpos with ⟨m, hm0, hmb⟩
  let K : ℝ := c / Real.sqrt m + 1
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    have h1 : 0 ≤ c / Real.sqrt m := div_nonneg (le_of_lt hc) (le_of_lt hsm)
    exact le_trans h1 (le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℝ)))
  refine ⟨K, ?hKpos, ?_⟩
  · dsimp [K]
    have h1 : 0 ≤ c / Real.sqrt m := div_nonneg (le_of_lt hc) (le_of_lt hsm)
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_add_of_nonneg_left h1)
  intro V hV
  by_cases hV0 : V = 0
  · subst V
    simpa using hKnonneg
  · have hmb' : m * ‖V‖ ^ 2 ≤ Q V V := hmb V
    have hq0 : 0 ≤ Q V V := le_of_lt (hpos V hV0)
    have hsqrt : Real.sqrt (m * ‖V‖ ^ 2) ≤ Real.sqrt (Q V V) :=
      Real.sqrt_le_sqrt hmb'
    have hsq : Real.sqrt (m * ‖V‖ ^ 2) = Real.sqrt m * ‖V‖ := by
      rw [Real.sqrt_mul (le_of_lt hm0) (‖V‖ ^ 2)]
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (norm_nonneg V)]
    have hmul : Real.sqrt m * ‖V‖ ≤ c := by
      calc
        Real.sqrt m * ‖V‖ = Real.sqrt (m * ‖V‖ ^ 2) := hsq.symm
        _ ≤ Real.sqrt (Q V V) := hsqrt
        _ ≤ c := hV
    have hsqrtm0 : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
    have hle : ‖V‖ ≤ c / Real.sqrt m := (le_div_iff₀ hsqrtm0).2 (by simpa [mul_comm] using hmul)
    dsimp [K]
    linarith



/-- Local linearity only depends on the values of the curve on the open interval. -/
lemma isLocLinear_congr {M : Type*} [PseudoEMetricSpace M]
    {a b : ℝ} {c : NNReal} {γ γR : ℝ → M}
    (hγ : Metric.IsLocLinear a b c γ) (hEq : ∀ t ∈ Ioo a b, γR t = γ t) :
    Metric.IsLocLinear a b c γR := by
  intro t₀ ht₀
  rcases hγ t₀ ht₀ with ⟨δ, hδ, hwin⟩
  refine ⟨δ, hδ, ?_⟩
  intro s t hs ht
  have hsab : s ∈ Ioo a b := by
    constructor
    · exact lt_of_le_of_lt (le_max_left a (t₀ - δ)) hs.1
    · exact lt_of_lt_of_le hs.2 (min_le_left b (t₀ + δ))
  have htab : t ∈ Ioo a b := by
    constructor
    · exact lt_of_le_of_lt (le_max_left a (t₀ - δ)) ht.1
    · exact lt_of_lt_of_le ht.2 (min_le_left b (t₀ + δ))
  rw [hEq s hsab, hEq t htab]
  exact hwin s t hs ht

/-- A curve that is locally linear on `(a,b)` is locally linear on any subinterval. -/
lemma isLocLinear_restrict' {M : Type*} [PseudoEMetricSpace M]
    {a b a' b' : ℝ} {c : NNReal} {γ : ℝ → M}
    (hγ : Metric.IsLocLinear a b c γ) (ha : a ≤ a') (hb : b' ≤ b) :
    Metric.IsLocLinear a' b' c γ :=
  Metric.IsLocLinear.restrict hγ ha hb



/-- In a normal ball where the radial identity holds, the norm of the coordinate `invM X` is
controlled by the metric distance from the centre: `‖invM X‖ * √m ≤ edist C X` for a uniform
`m > 0` (the lower eigenvalue bound of the quadratic form). -/
lemma coord_bound_of_edist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {M : Type*} [PseudoEMetricSpace M] (C : M)
    (ExpM : E → M) (invM : M → E) (S : Set M) (r : ℝ)
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (hQpos : ∀ u : E, u ≠ 0 → 0 < Q u u)
    (hInvS : ∀ X ∈ S, invM X ∈ ball (0 : E) r ∧ ExpM (invM X) = X)
    (hRad : ∀ v ∈ ball (0 : E) r,
       edist C (ExpM v) = ENNReal.ofReal (Real.sqrt (Q v v))) :
    ∃ m : ℝ, 0 < m ∧ ∀ X ∈ S, ‖invM X‖ * Real.sqrt m ≤ ENNReal.toReal (edist C X) := by
  rcases quad_ellipsoid_bound Q hQpos with ⟨m, hm0, hmb⟩
  refine ⟨m, hm0, ?_⟩
  intro X hXS
  rcases hInvS X hXS with ⟨hw, hEq⟩
  have hR : edist C X = ENNReal.ofReal (Real.sqrt (Q (invM X) (invM X))) := by
    have h := hRad (invM X) hw
    rw [hEq] at h
    exact h
  have htoReal : ENNReal.toReal (edist C X) = Real.sqrt (Q (invM X) (invM X)) := by
    rw [hR]
    exact ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
  have hmb' : m * ‖invM X‖ ^ 2 ≤ Q (invM X) (invM X) := hmb (invM X)
  have hsq : Real.sqrt (m * ‖invM X‖ ^ 2) ≤ Real.sqrt (Q (invM X) (invM X)) :=
    Real.sqrt_le_sqrt hmb'
  have hid : Real.sqrt (m * ‖invM X‖ ^ 2) = Real.sqrt m * ‖invM X‖ := by
    rw [Real.sqrt_mul (le_of_lt hm0) (‖invM X‖ ^ 2)]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (norm_nonneg (invM X))]
  have h1 : Real.sqrt m * ‖invM X‖ ≤ Real.sqrt (Q (invM X) (invM X)) := by
    simpa [hid] using hsq
  rw [htoReal]
  simpa [mul_comm] using h1



/-- A radial curve `t ↦ ExpM ((t-b) • W)` for `t ∈ (b, b+η)` is locally linear with speed `c`,
provided the forward-ray distance formula holds (for pairs along `W`) and the images stay in the
ball of radius `ρe`. -/
lemma radial_ray_locLinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [PseudoEMetricSpace M] (ExpM : E → M)
    {ρe η b : ℝ} {W : E} {c : NNReal}
    (hη : 0 < η) (hρe : 0 < ρe)
    (hFW : ∀ ⦃α β : ℝ⦄, 0 ≤ α → α ≤ β → β • W ∈ ball (0 : E) ρe →
       edist (ExpM (α • W)) (ExpM (β • W)) = (c : ℝ≥0∞) * ENNReal.ofReal (β - α))
    (hV : ∀ t ∈ Ioo b (b + η), (t - b) • W ∈ ball (0 : E) ρe) :
    Metric.IsLocLinear b (b + η) c (fun t => ExpM ((t - b) • W)) := by
  intro t₀ ht₀
  let δ : ℝ := min ((t₀ - b) / 2) ((b + η - t₀) / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos (sub_pos.mpr ht₀.1)) (half_pos (sub_pos.mpr ht₀.2))
  refine ⟨δ, hδpos, ?_⟩
  intro s t hs ht
  have hs_b : b < s := by
    have h1 : s > max b (t₀ - δ) := hs.1
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left b (t₀ - δ)) h1) (le_refl s)
  have ht_b : b < t := by
    have h1 : t > max b (t₀ - δ) := ht.1
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left b (t₀ - δ)) h1) (le_refl t)
  have hs_e : s < b + η := lt_of_lt_of_le hs.2 (min_le_left (b + η) (t₀ + δ))
  have ht_e : t < b + η := lt_of_lt_of_le ht.2 (min_le_left (b + η) (t₀ + δ))
  have hsη : s ∈ Ioo b (b + η) := ⟨hs_b, hs_e⟩
  have htη : t ∈ Ioo b (b + η) := ⟨ht_b, ht_e⟩
  by_cases hst : s ≤ t
  · have hs_b' : 0 ≤ s - b := sub_nonneg.mpr (le_of_lt hs_b)
    have hαβ' : s - b ≤ t - b := by linarith
    have hd := hFW (α := s - b) (β := t - b) hs_b' hαβ' (hV t htη)
    calc
      edist (ExpM ((s - b) • W)) (ExpM ((t - b) • W))
          = (c : ℝ≥0∞) * ENNReal.ofReal ((t - b) - (s - b)) := hd
      _ = (c : ℝ≥0∞) * ENNReal.ofReal (t - s) := by
        congr 2
        ring
      _ = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
        congr 2
        rw [abs_of_nonneg (sub_nonneg.mpr hst)]
  · have ht_b' : 0 ≤ t - b := sub_nonneg.mpr (le_of_lt ht_b)
    have hαβ' : t - b ≤ s - b := by linarith
    have hd := hFW (α := t - b) (β := s - b) ht_b' hαβ' (hV s hsη)
    calc
      edist (ExpM ((s - b) • W)) (ExpM ((t - b) • W))
          = edist (ExpM ((t - b) • W)) (ExpM ((s - b) • W)) := edist_comm _ _
      _ = (c : ℝ≥0∞) * ENNReal.ofReal ((s - b) - (t - b)) := hd
      _ = (c : ℝ≥0∞) * ENNReal.ofReal (s - t) := by
        congr 2
        ring
      _ = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
        congr 2
        rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hst))]
        ring

/-- Two points `ExpM (α•W)` and `ExpM (β•W)` on the same ray have exact distance given by the
forward-ray formula, with absolute value (order-free version). -/
lemma fwd_pair_abs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [PseudoEMetricSpace M] (ExpM : E → M) {ρe : ℝ}
    {W : E} {c : NNReal}
    (hFW : ∀ ⦃α β : ℝ⦄, 0 ≤ α → α ≤ β → β • W ∈ ball (0 : E) ρe →
       edist (ExpM (α • W)) (ExpM (β • W)) = (c : ℝ≥0∞) * ENNReal.ofReal (β - α))
    {s t : ℝ} (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hmem : max s t • W ∈ ball (0 : E) ρe) :
    edist (ExpM (s • W)) (ExpM (t • W)) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
  by_cases hst : s ≤ t
  · have hd := hFW (α := s) (β := t) hs0 hst (by simpa [max_eq_right hst] using hmem)
    calc
      edist (ExpM (s • W)) (ExpM (t • W)) = (c : ℝ≥0∞) * ENNReal.ofReal (t - s) := hd
      _ = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
        congr 2
        rw [abs_of_nonneg (sub_nonneg.mpr hst)]
  · have hts : t ≤ s := le_of_not_ge hst
    have hd := hFW (α := t) (β := s) ht0 hts (by simpa [max_eq_left hts] using hmem)
    calc
      edist (ExpM (s • W)) (ExpM (t • W)) = edist (ExpM (t • W)) (ExpM (s • W)) := edist_comm _ _
      _ = (c : ℝ≥0∞) * ENNReal.ofReal (s - t) := hd
      _ = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
        congr 2
        rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hst))]
        ring



end Submission
