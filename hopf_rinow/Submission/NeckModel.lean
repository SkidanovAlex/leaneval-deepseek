import ChallengeDeps
import Submission.Metric
import Submission.ChartArc
import Submission.Rigidity
import Submission.ChartNormal
import Submission.LocalExt
import Submission.TinyStrict
import Submission.ModelNormalBall
import Submission.ArcModel
import Submission.ModelArc
import Submission.ArcNB
import Submission.ModelExpDiffeo2
import Submission.ExpLocalDiffeo
import Submission.MinimalityWrap
import Mathlib

/-!
# Model-level engine for the neck lemma (per-base normal ball with exports)

Extends the verified `Submission.Model.uniform_normal_ball_aux` with the surjectivity /
inverse / radial-bound exports that the manifold transfer needs, by copying its proof and
emitting the per-base package.
-/

open scoped Manifold ENNReal ContDiff Topology
open Set Metric
open Bundle

namespace Submission.NeckModel

open Submission.Model

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem uniform_normal_ball_full (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) (ρu τf : ℝ) (hρu : 0 < ρu) (hτf : 0 < τf)
    (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hPerBase : ∀ b ∈ ball x₀ ρu, ∀ z ∈ closedBall (b, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (b, 0) 2))
    (hLip : ∀ t ∈ Icc (-τf) τf, ∀ b ∈ ball x₀ ρu,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, 0) 1)) :
    ∃ ρB δu τu ρE : ℝ, 0 < ρB ∧ 0 < δu ∧ 0 < τu ∧ 0 < ρE ∧ ρB ≤ ρu ∧
      δu ≤ τu ∧ δu ≤ ρE ∧ ρE ≤ τu ∧ 2 * τu ≤ τf ∧
      ∀ b ∈ ball x₀ ρB,
        ∃ expb invb : E → E,
          expb 0 = b ∧
          (∀ v : E, expb v = expOf b Φ τu v) ∧
          ContDiffOn ℝ 1 expb (ball (0 : E) ρE) ∧
          (ball b δu ⊆ expb '' ball (0 : E) ρE) ∧
          (∀ y ∈ ball b δu, invb y ∈ ball (0 : E) ρE ∧ expb (invb y) = y) ∧
          (∀ v ∈ ball (0 : E) ρE, invb (expb v) = v) ∧
          (∀ u v : E, u ∈ ball (0 : E) ρE → v ∈ ball (0 : E) ρE → expb u = expb v → u = v) ∧
          (∀ v ∈ ball (0 : E) ρE, ∀ c : ℝ → E,
             c 0 = b → c 1 = expb v →
             (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
             (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ ball b δu) →
             Real.sqrt ((g b) v v) ≤ mgLength g c 0 1) ∧
          (∀ y ∈ ball b δu, y ≠ b → ∀ X : E,
             ‖(fderiv ℝ (fun z : E => Real.sqrt ((g b) (invb z) (invb z)))) y X‖ ≤
               Real.sqrt ((g y) X X)) := by
  classical
  -- ------------ global constants (uniform over all bases) ------------
  rcases field_fderiv_bound g hg hinv (x₀, (0 : E)) (ρu + 2) (by linarith) with ⟨K0, hK0, hKbig⟩
  have hKbig' : ∀ p ∈ closedBall (x₀, (0 : E)) (ρu + 2), ‖fderiv ℝ (odeField g) p‖ ≤ K0 := hKbig
  rcases field_lipschitzOn_r g hg hinv (x₀, (0 : E)) (ρu + 2) (by linarith) with ⟨Kf, hKfBig⟩
  rcases uniform_flow_c1 g hg hinv x₀ ρu τf hρu hτf Lf Φ hPerBase hLip hK0 hKbig' with
    ⟨τc, hτc0, hτcτf8, δc, hδc0, hδc8, hcd⟩
  let S : ℝ := Finset.univ.sum (fun i : Fin (Module.finrank ℝ (E × E)) =>
    (‖Module.finBasis ℝ (E × E) i‖ + 1))
  have hS0 : 0 ≤ S := Finset.sum_nonneg (by intro i hi; positivity)
  let M : ℝ := S + 1
  have hMpos : 0 < M := by dsimp [M]; linarith
  have hK0p : 0 < K0 + 1 := by linarith
  have hKf0 : 0 ≤ (Kf : ℝ) := by exact_mod_cast (Kf : NNReal).2
  have hLf0 : 0 ≤ (Lf : ℝ) := by exact_mod_cast (Lf : NNReal).2
  have hKf1 : 0 < (Kf : ℝ) + 1 := by linarith
  have hLf1 : 0 < (Lf : ℝ) + 1 := by linarith
  let τu : ℝ := min τc (min (τf / 8) (min (1 / (8 * (K0 + 1) * M))
    (1 / (4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1)))))
  have hτu0 : 0 < τu := by
    dsimp [τu]
    positivity
  have hτuτc : τu ≤ τc := by
    dsimp [τu]
    exact min_le_left _ _
  have hτuτf8 : τu ≤ τf / 8 := by
    dsimp [τu]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hτuDen1 : τu ≤ 1 / (8 * (K0 + 1) * M) := by
    dsimp [τu]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hτuDen2 : τu ≤ 1 / (4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1)) := by
    dsimp [τu]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have h2τuτf : 2 * τu ≤ τf := by nlinarith [hτuτf8]
  have hτuτf : τu < τf := by nlinarith [hτuτf8, hτf]
  have h4τuτf : 4 * τu ≤ τf := by nlinarith [hτuτf8]
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
  have hUb : ∀ i : Fin (Module.finrank ℝ (E × E)),
      4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τu ≤ 1 := by
    intro i
    have hnonneg : 0 ≤ 4 * (K0 + 1) * M := by positivity
    have hpos2 : 0 ≤ τu := le_of_lt hτu0
    have hBMi : ‖Module.finBasis ℝ (E × E) i‖ + 1 ≤ M := hBM i
    have hm1 : 4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) ≤ 4 * (K0 + 1) * M := by
      exact mul_le_mul_of_nonneg_left hBMi (by positivity)
    have hm : 4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τu
        ≤ 4 * (K0 + 1) * M * τu := by
      exact mul_le_mul_of_nonneg_right hm1 hpos2
    have hm2 : 4 * (K0 + 1) * M * τu ≤ 1 := by
      calc
        4 * (K0 + 1) * M * τu ≤ 4 * (K0 + 1) * M * (1 / (8 * (K0 + 1) * M)) :=
          mul_le_mul_of_nonneg_left hτuDen1 hnonneg
        _ = 1 / 2 := by
          field_simp [hK0p.ne', hMpos.ne']
          ring
        _ ≤ 1 := by norm_num
    exact le_trans hm hm2
  have hκ0 : 0 ≤ (Kf : ℝ) * (Lf : ℝ) * τu := by positivity
  have hκ14 : (Kf : ℝ) * (Lf : ℝ) * τu ≤ 1 / 4 := by
    have hle : (Kf : ℝ) * (Lf : ℝ) ≤ ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1) := by nlinarith
    have hdenpos : 0 < 4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1) := by positivity
    have hpos3 : 0 ≤ (Kf : ℝ) * (Lf : ℝ) := mul_nonneg hKf0 hLf0
    have hc0 : 0 ≤ 1 / (4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1)) := by positivity
    calc
      (Kf : ℝ) * (Lf : ℝ) * τu
          ≤ (Kf : ℝ) * (Lf : ℝ) * (1 / (4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1))) := by
            exact mul_le_mul_of_nonneg_left hτuDen2 hpos3
      _ ≤ ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1) * (1 / (4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1))) := by
            exact mul_le_mul_of_nonneg_right hle hc0
      _ = 1 / 4 := by
            field_simp [hdenpos.ne']
  have hκ1 : (Kf : ℝ) * (Lf : ℝ) * τu < 1 := by nlinarith [hκ14]
  let ρE : ℝ := τu * δc / 2
  have hρE : 0 < ρE := by dsimp [ρE]; positivity
  have hρEτu : ρE ≤ τu := by
    dsimp [ρE]
    have h1 : δc / 2 ≤ 1 := by
      have hδc2 : δc ≤ 2 := by linarith [hδc8]
      nlinarith
    nlinarith [h1, hτu0]
  let ρB : ℝ := ρu
  have hρB : 0 < ρB := by dsimp [ρB]; exact hρu
  have hρBρu : ρB ≤ ρu := le_rfl
  let δu : ℝ := ρE / 4
  have hδu : 0 < δu := by dsimp [δu]; positivity
  have hδuτu : δu ≤ τu := by
    dsimp [δu]
    have h1 : ρE ≤ 4 * τu := by
      dsimp [ρE]
      have hδc8' : δc / 2 ≤ 8 := by nlinarith [hδc8]
      nlinarith [hδc8', hτu0]
    nlinarith
  have hδuρE : δu ≤ ρE := by dsimp [δu]; linarith
  have hδuκρE : δu ≤ (1 - (Kf : ℝ) * (Lf : ℝ) * τu) * ρE := by
    dsimp [δu]
    have h : (3 / 4 : ℝ) * ρE ≤ (1 - (Kf : ℝ) * (Lf : ℝ) * τu) * ρE := by
      have hκ' : (Kf : ℝ) * (Lf : ℝ) * τu ≤ 1 / 4 := hκ14
      nlinarith [hρE]
    have h2 : ρE / 4 ≤ (3 / 4 : ℝ) * ρE := by nlinarith [hρE]
    exact le_trans h2 h
  have hρEτu_le2 : (2 : ℝ) * τu ≤ τf := h2τuτf
  -- ------------- witnesses -------------
  refine ⟨ρB, δu, τu, ρE, hρB, hδu, hτu0, hρE, hρBρu, hδuτu, hδuρE, hρEτu, h2τuτf, ?_⟩
  intro b hb
  -- per-base instantiation of the flow hypotheses
  have hPerB : ∀ z ∈ closedBall (b, (0 : E)) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (b, (0 : E)) 2) := by
    intro z hz
    exact hPerBase b hb z hz
  have hLipB : ∀ t ∈ Icc (-τf) τf,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, (0 : E)) 1) := by
    intro t ht
    exact hLip t ht b hb
  have hKb : ∀ p ∈ closedBall (b, (0 : E)) 2, ‖fderiv ℝ (odeField g) p‖ ≤ K0 := by
    intro p hp
    exact hKbig p (closedBall_b0_subset x₀ hρu hb hp)
  have hKfb : LipschitzOnWith Kf (odeField g) (closedBall (b, (0 : E)) 2) := by
    exact hKfBig.mono (closedBall_b0_subset x₀ hρu hb)
  let expb : E → E := expOf b Φ τu
  have hcdb : ∀ t ∈ Icc (-τc) τc, ContDiffOn ℝ 1 (fun z : E × E => Φ z t) (ball (b, (0 : E)) δc) := by
    intro t ht
    exact (hcd b hb t ht).1
  have hExpC1 : ContDiffOn ℝ 1 expb (ball (0 : E) ρE) := by
    dsimp [expb, ρE]
    exact exp_contDiffOn_ball g hg hinv b Φ (τ := τu) (τc := τc) (δc := δc) hcdb hδc0 hτu0 hτuτc
  have hΦ2b : ∀ z ∈ closedBall (b, (0 : E)) 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    exact ⟨(hPerB z hz).1, (hPerB z hz).2.1⟩
  have hExp0 : expb (0 : E) = b := by
    dsimp [expb]
    have hτmem : τu ∈ Ioo (-τf) τf := by
      constructor
      · linarith [hτu0, hτf]
      · exact hτuτf
    have hrest := flow_rest_point g hg hinv hτf (x₀ := b) (Φ := Φ) hΦ2b τu hτmem
    simpa [expOf] using congrArg Prod.fst hrest
  have hExpId : HasFDerivAt expb (ContinuousLinearMap.id ℝ E) (0 : E) := by
    dsimp [expb]
    exact expOf_hasFDerivAt_id g hg hinv b (Tf := τf) hτf Φ hΦ2b (τ := τu) hτu0 hτuτf
      (ρ := ρE) hρE (by simpa [expb] using hExpC1)
  -- two-point expansion bound of `expb` (uniform data of the flow)
  have hΦtu : ∀ z ∈ closedBall (b, (0 : E)) 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-τu) τu, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    constructor
    · exact (hPerB z hz).1
    · intro t ht
      have ht' : t ∈ Icc (-τf) τf := by
        constructor <;> linarith [ht.1, ht.2, hτuτf]
      exact (hPerB z hz).2.1 t ht'
  have hContb : ∀ z ∈ closedBall (b, (0 : E)) 1, ∀ t ∈ Icc (0 : ℝ) τu,
      Φ z t ∈ closedBall (b, (0 : E)) 2 := by
    intro z hz t ht
    exact (hPerB z hz).2.2 t
  have hLipb : ∀ t ∈ Icc (-τu) τu,
      LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, (0 : E)) 1) := by
    intro t ht
    have ht' : t ∈ Icc (-τf) τf := by
      constructor <;> linarith [ht.1, ht.2, hτuτf]
    exact hLipB t ht'
  have hexpf (u : E) : expb u = (Φ (b, (1 / τu) • u) τu).1 := by
    have hs : (τu⁻¹ : ℝ) • u = (1 / τu) • u := by rw [inv_eq_one_div]
    dsimp [expb]
    rw [expOf, hs]
  have htp : ∀ u v : E, u ∈ closedBall (0 : E) τu → v ∈ closedBall (0 : E) τu →
      ‖(expb u - expb v) - (u - v)‖ ≤ (Kf : ℝ) * (Lf : ℝ) * τu * ‖u - v‖ := by
    intro u v hu hv
    have hh := exp_two_point_bound g hg hinv b (ρ := τu) hτu0 Lf Kf Φ hΦtu hContb hLipb hKfb u v hu hv
    simpa [hexpf, mul_assoc] using hh
  -- the estimate on the small velocity ball
  have hclE : closedBall (0 : E) ρE ⊆ closedBall (0 : E) τu := closedBall_subset_closedBall hρEτu
  have hest : ∀ ⦃u v : E⦄, u ∈ closedBall (0 : E) ρE → v ∈ closedBall (0 : E) ρE →
      ‖(expb u - expb v) - (u - v)‖ ≤ (Kf : ℝ) * (Lf : ℝ) * τu * ‖u - v‖ := by
    intro u v hu hv
    exact htp u v (hclE hu) (hclE hv)
  rcases exp_est_local_diffeomorphism_ball expb b ρE ((Kf : ℝ) * (Lf : ℝ) * τu) hρE hκ0 hκ1 hExp0 hest
    with ⟨invb, hInv2b, hInv1b, hInjb, hCoverb⟩
  -- derivative of expb is near the identity on ball 0 ρE
  have hfdNear (v : E) (hv : v ∈ ball (0 : E) ρE) :
      ‖fderiv ℝ expb v - ContinuousLinearMap.id ℝ E‖ ≤ (Kf : ℝ) * (Lf : ℝ) * τu := by
    let G : E → E := expb - (fun z : E => z)
    have hde : DifferentiableAt ℝ expb v := by
      exact (hExpC1.contDiffAt (isOpen_ball.mem_nhds hv)).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have hdid : HasFDerivAt (fun z : E => z) (ContinuousLinearMap.id ℝ E) v := hasFDerivAt_id v
    have hdG : HasFDerivAt G (fderiv ℝ expb v - ContinuousLinearMap.id ℝ E) v := by
      change HasFDerivAt (expb - (fun z : E => z)) (fderiv ℝ expb v - ContinuousLinearMap.id ℝ E) v
      exact hde.hasFDerivAt.sub hdid
    have hvτ : v ∈ ball (0 : E) τu := by
      exact ball_subset_ball hρEτu hv
    have hlip' : ∀ᶠ x in 𝓝 v, ‖G x - G v‖ ≤ (Kf : ℝ) * (Lf : ℝ) * τu * ‖x - v‖ := by
      filter_upwards [isOpen_ball.mem_nhds hvτ] with x hx
      have hxτ : x ∈ ball (0 : E) τu := hx
      have hxτ' : x ∈ closedBall (0 : E) τu := ball_subset_closedBall hxτ
      have hvτ' : v ∈ closedBall (0 : E) τu := ball_subset_closedBall hvτ
      have hb' := htp x v hxτ' hvτ'
      have heq : expb x - x - (expb v - v) = (expb x - expb v) - (x - v) := by abel
      simpa [G, heq] using hb'
    have hfdG : ‖fderiv ℝ expb v - ContinuousLinearMap.id ℝ E‖ ≤ (Kf : ℝ) * (Lf : ℝ) * τu :=
      hdG.le_of_lip' hκ0 hlip'
    exact hfdG
  have hInvDb : ∀ v ∈ ball (0 : E) ρE, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ expb v := by
    intro v hv
    have hlt : ‖fderiv ℝ expb v - ContinuousLinearMap.id ℝ E‖ < 1 := by
      have hle := hfdNear v hv
      linarith [hκ14]
    exact clm_invertible_of_near_id (fderiv ℝ expb v) hlt

  -- domain of staying curves and C¹-ness of the inverse on it
  have hVcov : ball b δu ⊆ expb '' ball (0 : E) ρE := by
    exact Subset.trans (ball_subset_ball hδuκρE) hCoverb
  have hContAtInv (y : E) (hyV : y ∈ ball b δu) : ContDiffAt ℝ 1 invb y := by
    exact contDiffAt_inv_of_twoPoint expb hρE hExpC1 hInvDb hInv2b hInv1b (hVcov hyV)
  let V : Set E := ball b δu
  let F : E → ℝ := fun z : E => Real.sqrt ((g b) (invb z) (invb z))
  have hFcont : ContinuousOn F V := by
    intro y hyV
    have hc1 : ContDiffAt ℝ 1 invb y := hContAtInv y hyV
    have hc : ContinuousAt (fun z : E => Real.sqrt ((g b) (invb z) (invb z))) y :=
      radialComp_continuousAt (B := g b) (inv := invb) y hc1.continuousAt
    have hc' : ContinuousAt F y := by simpa [F] using hc
    exact hc'.continuousWithinAt
  have hFdiff : ∀ y ∈ V, y ≠ b → DifferentiableAt ℝ F y := by
    intro y hyV hyne
    have hc1 : ContDiffAt ℝ 1 invb y := hContAtInv y hyV
    have hinv0 : invb y ≠ 0 := by
      intro hz
      apply hyne
      have hy' : expb (invb y) = y := (hInv1b y (hVcov hyV)).2
      rw [← hy', hz, hExp0]
    have hposval : 0 < ((g b) (invb y)) (invb y) := hpos b (invb y) hinv0
    have hd := radialComp_differentiableAt (B := g b) (inv := invb) y hc1 hposval
    simpa [F] using hd
  -- radial (Gauss) bound, with the uniform constants
  have hFb : ∀ y ∈ V, y ≠ b → ∀ X : E, ‖(fderiv ℝ F y) X‖ ≤ mgSpeed g y X := by
    intro y hyV hyne X
    have hyExp : y ∈ expb '' ball (0 : E) ρE := hVcov hyV
    have hvU : invb y ∈ ball (0 : E) ρE := (hInv1b y hyExp).1
    have hvexp : expb (invb y) = y := (hInv1b y hyExp).2
    let v : E := invb y
    have hvb : v ∈ ball (0 : E) ρE := hvU
    have hvexp' : expb v = y := by simpa [v] using hvexp
    have hvne : v ≠ 0 := by
      intro hz
      apply hyne
      rw [← hvexp', hz]
      exact hExp0
    have hvE : ‖v‖ < ρE := by
      have hd : dist v 0 < ρE := mem_ball.mp hvb
      simpa [dist_eq_norm] using hd
    have hvin : (b, τu⁻¹ • v) ∈ ball (b, (0 : E)) (1 / 4) := by
      have hρ4 : ρE < τu / 4 := by
        dsimp [ρE]
        have hδ : δc / 2 < 1 / 4 := by
          have hδc4 : δc ≤ 1 / 4 := by linarith [hδc8]
          nlinarith [hδc4, hδc0]
        nlinarith [hδ, hτu0]
      have hvlt : ‖v‖ < τu / 4 := lt_of_lt_of_le hvE (le_of_lt hρ4)
      rw [mem_ball, dist_eq_norm]
      have hnorm : ‖(b, τu⁻¹ • v) - (b, (0 : E))‖ = ‖τu⁻¹ • v‖ := by simp
      rw [hnorm]
      have hposτ : 0 < τu⁻¹ := by positivity
      have hsmul : ‖τu⁻¹ • v‖ ≤ τu⁻¹ * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hposτ)]
      have h2 : τu⁻¹ * ‖v‖ < 1 / 4 := by
        have hle : τu⁻¹ * ‖v‖ < τu⁻¹ * (τu / 4) :=
          mul_lt_mul_of_pos_left hvlt hposτ
        have hstep : τu⁻¹ * (τu / 4) = 1 / 4 := by
          field_simp [ne_of_gt hτu0]
        rw [hstep] at hle
        exact hle
      exact lt_of_le_of_lt hsmul h2
    rcases fderiv_exp_surj (ρ := ρE) hρE v hvb hInvDb X with ⟨W, hXW⟩
    let R : E → ℝ := fun z : E => Real.sqrt ((g b) z z)
    have hFR : ∀ x ∈ ball (0 : E) ρE, F (expb x) = R x := by
      intro x hxU
      dsimp [F, R]
      rw [hInv2b x hxU]
    have hFyD : DifferentiableAt ℝ F (expb v) := by
      have hyE : expb v ≠ b := by rw [hvexp']; exact hyne
      have hmem : expb v ∈ V := by rw [hvexp']; exact hyV
      exact hFdiff (expb v) hmem hyE
    have hExpD : DifferentiableAt ℝ expb v := by
      have hcv : ContDiffAt ℝ 1 expb v := hExpC1.contDiffAt (isOpen_ball.mem_nhds hvb)
      exact hcv.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have hRD : DifferentiableAt ℝ R v := by
      have hd := radialComp_differentiableAt (B := g b) (inv := fun z : E => z) v
        (by
          have hcv : ContDiffAt ℝ 1 (fun z : E => z) v :=
            (contDiff_id : ContDiff ℝ 1 (fun z : E => z)).contDiffAt
          exact hcv) (by simpa using hpos b v hvne)
      simpa [R] using hd
    have hdcomp := fderiv_comp_eq_on_open (F := F) (R := R) (exp := expb) (U := ball (0 : E) ρE)
      isOpen_ball hvb hFR hFyD hExpD hRD
    have hval : (fderiv ℝ F y) X = (fderiv ℝ R v) W := by
      calc
        (fderiv ℝ F y) X = (fderiv ℝ F (expb v)) ((fderiv ℝ expb v) W) := by rw [← hvexp', hXW]
        _ = ((fderiv ℝ F (expb v)).comp (fderiv ℝ expb v)) W := rfl
        _ = (fderiv ℝ R v) W := by rw [hdcomp]
    have hb := radial_bound_main g hg hinv hsym hpos b (Tf := τf) hτf (Lf := Lf) (Φ := Φ)
      hPerB hLipB (K0 := K0) hK0 hKb (δ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      (τ := τu) hτu0 h4τuτf hUb (v := v) (W := W) hvin hvne
    have hbX : ‖(fderiv ℝ R v) W‖ ≤ Real.sqrt ((g y) X X) := by
      have h1 : ‖(fderiv ℝ R v) W‖ ≤
          Real.sqrt ((g (expOf b Φ τu v)) ((fderiv ℝ (expOf b Φ τu)) v W)
            ((fderiv ℝ (expOf b Φ τu)) v W)) := by
        simpa [R] using hb
      have hXeq : (fderiv ℝ (expOf b Φ τu)) v W = X := by
        simpa [expb] using hXW
      have hyeq : expOf b Φ τu v = y := by
        simpa [expb] using hvexp'
      rw [hXeq] at h1
      rw [hyeq] at h1
      simpa using h1
    have hmain : ‖(fderiv ℝ F y) X‖ ≤ Real.sqrt ((g y) X X) := by
      rw [hval]
      exact hbX
    simpa [mgSpeed] using hmain
  -- staying minimality from the generic wrapper
  have hU0 : (0 : E) ∈ ball (0 : E) ρE := by simpa using hρE
  have hVb : b ∈ V := by
    dsimp [V]
    simpa using hδu
  have hinj0 : ∀ v ∈ ball (0 : E) ρE, expb v = b → v = 0 := by
    intro v hv hx0
    have h0U' : (0 : E) ∈ ball (0 : E) ρE := hU0
    have heq : expb v = expb (0 : E) := by simpa [hExp0] using hx0
    exact hInjb v (0 : E) hv h0U' heq
  have hFeq : (radialCoord g b invb) = F := by
    funext z
    simp [F, radialCoord]
  have hFRC_cont : ContinuousOn (radialCoord g b invb) V := by
    simpa [hFeq] using hFcont
  have hFRC_diff : ∀ y ∈ V, y ≠ b → DifferentiableAt ℝ (radialCoord g b invb) y := by
    intro y hy hne
    have hd := hFdiff y hy hne
    simpa [hFeq] using hd
  have hFRC_b : ∀ y ∈ V, y ≠ b → ∀ X : E,
      ‖(fderiv ℝ (radialCoord g b invb) y) X‖ ≤ mgSpeed g y X := by
    intro y hy hne X
    have hd := hFb y hy hne X
    simpa [hFeq] using hd
  have hMinb : ∀ v ∈ ball (0 : E) ρE, ∀ c : ℝ → E,
      c 0 = b → c 1 = expb v →
      (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
      (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ V) →
      Real.sqrt ((g b) v v) ≤ mgLength g c 0 1 := by
    intro v hv c hc0 hc1 hcO hcV
    exact radial_minimality g hg hinv hsym hpos b (exp := expb) (inv := invb)
      (U := ball (0 : E) ρE) (V := V) hExp0 hU0 hInv2b hinj0 hVb hFRC_cont hFRC_diff hFRC_b
      v hv c hc0 hc1 hcO hcV
  -- assemble the per-base package
  refine ⟨expb, invb, hExp0, ?_, hExpC1, hVcov, ?_, hInv2b, hInjb, ?_, ?_⟩
  · intro v
    rfl
  · intro y hy
    exact hInv1b y (hVcov hy)
  · intro v hv c hc0 hc1 hcO hcV
    exact hMinb v hv c hc0 hc1 hcO hcV
  · intro y hy hyne X
    have hd := hFb y hy hyne X
    simpa [F, mgSpeed] using hd

end NeckModel
end Submission

namespace Submission.NeckModel

open Submission.Model

section PairEngine

open scoped ENNReal Topology
open Set Filter Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


end PairEngine

end Submission.NeckModel
