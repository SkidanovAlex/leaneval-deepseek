import ChallengeDeps
import Submission.ModelArc
import Submission.ArcNB
import Submission.ModelNormalBall
import Submission.ModelExpDiffeo2
import Submission.ModelExpC1
import Submission.MinimalityWrap
import Submission.LocalExt
import Mathlib

/-!
# Model-level: equality case of staying minimality (flow exponential), uniform over bases
-/

open scoped ENNReal ContDiff Topology
open Set Metric
open Bundle
open MeasureTheory intervalIntegral
open Filter

namespace Submission
namespace NeckEq

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

open Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## A drop lemma: radial coordinate growth is bounded by length, along slices -/

/-- Radial-coordinate drop along a constant-speed staying slice: if `c` has model speed `r`
on `(0,1)`, avoids the base `b` on `(p,q)`, and stays in the ball where the radial bound holds,
then `F (c q) - F (c p) ≤ (q - p) * r`. -/
lemma radial_drop_le (g : E → Bilin E) (b : E) (invb : E → E)
    {δu : ℝ} (hδu0 : 0 < δu)
    (hFcont : ContinuousOn (radialCoord g b invb) (ball b δu))
    (hFdiff : ∀ y ∈ ball b δu, y ≠ b → DifferentiableAt ℝ (radialCoord g b invb) y)
    (hFb : ∀ y ∈ ball b δu, y ≠ b → ∀ X : E,
       ‖(fderiv ℝ (radialCoord g b invb) y) X‖ ≤ mgSpeed g y X)
    {c : ℝ → E}
    (hcO : ∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O)
    (hcV : ∀ s ∈ Icc (0 : ℝ) 1, c s ∈ ball b δu)
    {r : ℝ} (hr : ∀ s ∈ Ioo (0 : ℝ) 1, mgSpeed g (c s) (deriv c s) = r)
    {p q : ℝ} (hpq : p ≤ q) (hp0 : 0 ≤ p) (hq1 : q ≤ 1)
    (hcne : ∀ s ∈ Ioo p q, c s ≠ b) :
    radialCoord g b invb (c q) - radialCoord g b invb (c p) ≤ (q - p) * r := by
  let F : E → ℝ := radialCoord g b invb
  let G : ℝ → ℝ := fun t => F (c t) - r * t
  rcases hcO with ⟨O, hOopen, hOIcc, hcC1⟩
  have hcContO : ContinuousOn c O := hcC1.continuousOn
  have hcdiffAt (t : ℝ) (ht : t ∈ O) : DifferentiableAt ℝ c t := by
    exact (hcC1.contDiffAt (hOopen.mem_nhds ht)).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hI01 (t : ℝ) (ht : t ∈ Icc p q) : t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact le_trans hp0 ht.1
    · exact le_trans ht.2 hq1
  have hV (t : ℝ) (ht : t ∈ Icc p q) : c t ∈ ball b δu := hcV t (hI01 t ht)
  have hmemO (t : ℝ) (ht : t ∈ Icc p q) : t ∈ O := hOIcc (hI01 t ht)
  -- G continuous on Icc p q
  have hFcCont : ContinuousOn (fun t => F (c t)) (Icc p q) := by
    refine hFcont.comp (hcContO.mono ?_) ?_
    · intro t ht
      exact hmemO t ht
    · intro t ht
      exact hV t ht
  have hlinCont : ContinuousOn (fun t : ℝ => r * t) (Icc p q) :=
    (continuous_const.mul continuous_id).continuousOn
  have hGcont : ContinuousOn G (Icc p q) := by
    have hsub := hFcCont.sub hlinCont
    refine hsub.congr ?_
    intro t ht
    rfl
  -- differentiability on the interior
  have hGdiff : DifferentiableOn ℝ G (interior (Icc p q)) := by
    rw [interior_Icc]
    intro t ht
    have ht' : t ∈ Icc p q := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hmemV : c t ∈ ball b δu := hV t ht'
    have htne : c t ≠ b := hcne t ht
    have hFdiffAt : DifferentiableAt ℝ F (c t) := hFdiff (c t) hmemV htne
    have hcd : DifferentiableAt ℝ c t := hcdiffAt t (hmemO t ht')
    have hcomp : DifferentiableAt ℝ (fun x => F (c x)) t := hFdiffAt.comp t hcd
    have hid : DifferentiableAt ℝ (fun x : ℝ => r * x) t := by
      simpa using ((hasDerivAt_id t).const_mul r).differentiableAt
    have hdiffG : DifferentiableAt ℝ (fun x : ℝ => F (c x) - r * x) t := hcomp.sub hid
    simpa [G] using hdiffG.differentiableWithinAt
  -- derivative bound
  have hGle : ∀ x ∈ interior (Icc p q), deriv G x ≤ 0 := by
    intro t ht
    have ht' : t ∈ Ioo p q := by simpa [interior_Icc] using ht
    have htI : t ∈ Icc p q := ⟨le_of_lt ht'.1, le_of_lt ht'.2⟩
    have hmemV : c t ∈ ball b δu := hV t htI
    have htne : c t ≠ b := hcne t ht'
    have hFdiffAt : DifferentiableAt ℝ F (c t) := hFdiff (c t) hmemV htne
    have hcd : DifferentiableAt ℝ c t := hcdiffAt t (hmemO t htI)
    have hderF : HasDerivAt (fun x => F (c x)) ((fderiv ℝ F (c t)) (deriv c t)) t := by
      exact hFdiffAt.hasFDerivAt.comp_hasDerivAt t hcd.hasDerivAt
    have hderlin : HasDerivAt (fun x : ℝ => r * x) r t := by
      simpa using (hasDerivAt_id t).const_mul r
    have hderG : HasDerivAt G ((fderiv ℝ F (c t)) (deriv c t) - r) t := by
      change HasDerivAt (fun x : ℝ => F (c x) - r * x)
        ((fderiv ℝ F (c t)) (deriv c t) - r) t
      exact hderF.sub hderlin
    have hmem01 : t ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact lt_of_le_of_lt hp0 ht'.1
      · exact lt_of_lt_of_le ht'.2 hq1
    have hφ : mgSpeed g (c t) (deriv c t) = r := hr t hmem01
    have hb := hFb (c t) hmemV htne (deriv c t)
    have hb' : ‖(fderiv ℝ (radialCoord g b invb) (c t)) (deriv c t)‖ ≤ r := by
      simpa [hφ] using hb
    have hle1 : (fderiv ℝ F (c t)) (deriv c t) ≤ r := by
      have hn : ‖(fderiv ℝ F (c t)) (deriv c t)‖ = |(fderiv ℝ F (c t)) (deriv c t)| := rfl
      have htmp : ‖(fderiv ℝ F (c t)) (deriv c t)‖ ≤ r := by
        simpa [F] using hb'
      exact le_trans (le_abs_self _) htmp
    have hGle' : (fderiv ℝ F (c t)) (deriv c t) - r ≤ 0 := by linarith
    have hderv : deriv G t = (fderiv ℝ F (c t)) (deriv c t) - r := hderG.deriv
    rwa [hderv]
  have hanti : AntitoneOn G (Icc p q) :=
    antitoneOn_of_deriv_nonpos (convex_Icc p q) hGcont hGdiff hGle
  have hGfinal : G q ≤ G p := hanti (left_mem_Icc.mpr hpq) (right_mem_Icc.mpr hpq) hpq
  dsimp [G] at hGfinal
  change radialCoord g b invb (c q) - radialCoord g b invb (c p) ≤ (q - p) * r
  nlinarith

/-! ## Per-base normal-ball data package -/

/-- Per-base normal-ball data (exp, inverse, radial coordinate) with all the exports needed
for the equality case of radial minimality. -/
structure NeckData (g : E → Bilin E) (b : E) (Φ : E × E → ℝ → E × E) (τu δu ρE : ℝ) where
  expb : E → E
  invb : E → E
  exp0 : expb 0 = b
  expform : ∀ v : E, expb v = expOf b Φ τu v
  exp_c1 : ContDiffOn ℝ 1 expb (ball (0 : E) ρE)
  cover : ball b δu ⊆ expb '' ball (0 : E) ρE
  inv_right : ∀ y ∈ ball b δu, invb y ∈ ball (0 : E) ρE ∧ expb (invb y) = y
  inv_left : ∀ v ∈ ball (0 : E) ρE, invb (expb v) = v
  inj : ∀ u v : E, u ∈ ball (0 : E) ρE → v ∈ ball (0 : E) ρE → expb u = expb v → u = v
  fderiv_inv : ∀ v ∈ ball (0 : E) ρE, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ expb v
  inv_c1 : ∀ y ∈ ball b δu, ContDiffAt ℝ 1 invb y
  F_cont : ContinuousOn (radialCoord g b invb) (ball b δu)
  F_diff : ∀ y ∈ ball b δu, y ≠ b → DifferentiableAt ℝ (radialCoord g b invb) y
  F_bound : ∀ y ∈ ball b δu, y ≠ b → ∀ X : E,
      ‖(fderiv ℝ (radialCoord g b invb) y) X‖ ≤ mgSpeed g y X

/-- Uniform (over bases in a ball) per-base normal-ball data with explicit radii. -/
theorem neck_package (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) (ρu τf : ℝ) (hρu : 0 < ρu) (hτf : 0 < τf)
    (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hPerBase : ∀ b ∈ ball x₀ ρu, ∀ z ∈ closedBall (b, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (b, 0) 2))
    (hLip : ∀ t ∈ Icc (-τf) τf, ∀ b ∈ ball x₀ ρu,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, 0) 1)) :
    ∃ ρB δu τu ρE K0 : ℝ, 0 < ρB ∧ 0 < δu ∧ 0 < τu ∧ 0 < ρE ∧ 0 ≤ K0 ∧ ρB ≤ ρu ∧ δu ≤ ρE ∧
      4 * ρE ≤ τu ∧ 8 * τu ≤ τf ∧
      (∀ p ∈ closedBall (x₀, (0 : E)) (ρu + 2), ‖fderiv ℝ (odeField g) p‖ ≤ K0) ∧
      (∀ i : Fin (Module.finrank ℝ (E × E)),
         4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τu ≤ 1) ∧
      ∀ b ∈ ball x₀ ρB, Nonempty (NeckData g b Φ τu δu ρE) := by
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
  have h4ρEτu : 4 * ρE ≤ τu := by
    dsimp [ρE]
    have hδ0le : 0 ≤ δc := le_of_lt hδc0
    have hm : τu * δc ≤ τu * (1 / 8) := mul_le_mul_of_nonneg_left hδc8 (le_of_lt hτu0)
    nlinarith [hm, hτu0]
  have h8τuτf : 8 * τu ≤ τf := by nlinarith [hτuτf8]
  -- ------------- witnesses -------------
  refine ⟨ρB, δu, τu, ρE, K0, hρB, hδu, hτu0, hρE, hK0, hρBρu, hδuρE, h4ρEτu, h8τuτf, hKbig', hUb, ?_⟩
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
  apply Nonempty.intro
  refine ⟨expb, invb, hExp0, ?_, hExpC1, hVcov, ?_, hInv2b, hInjb, hInvDb, ?_, ?_, ?_, ?_⟩
  · intro v
    rfl
  · intro y hy
    exact hInv1b y (hVcov hy)
  · intro y hy
    exact hContAtInv y hy
  · simpa [V] using hFRC_cont
  · simpa [V] using hFRC_diff
  · intro y hy hyne X
    have hd := hFRC_b y hy hyne X
    simpa [V] using hd
/-! ## Two-sided flow scaling and the diagonal derivative of the exponential -/

/-- Flow scaling along a ray, valid for scales `a` beyond `1` as long as the scaled data
stays in the radius-1 data ball and the scaled time stays in the flow window. -/
lemma exp_ray_scaling' (g : E → Bilin E) (hg : ContDiff ℝ 3 g) (hinv : ∀ x, (g x).IsInvertible)
    (x₀ : E) {T : ℝ} (hT : 0 < T) (Φc : E × E → ℝ → E × E)
    (hΦc : ∀ z ∈ closedBall (x₀, (0 : E)) 1, Φc z 0 = z ∧
       ∀ s ∈ Icc (-T) T, HasDerivAt (Φc z) (odeField g (Φc z s)) s)
    (w : E) (hw : ‖w‖ ≤ 1) {a : ℝ} (ha0 : a ≠ 0) (hwscale : ‖a • w‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo (-T) T) (htscale : |t| * |a| < T) :
    (Φc (x₀, a • w) t).1 = (Φc (x₀, w) (a * t)).1 := by
  have hz1 : (x₀, w) ∈ closedBall (x₀, 0) 1 := mem_data_ball x₀ w hw
  have hz2 : (x₀, a • w) ∈ closedBall (x₀, 0) 1 := mem_data_ball x₀ (a • w) hwscale
  have hsplit1 := split_flow_geodesic g hg hinv (x₀, 0) hT (closedBall (x₀, 0) 1) Φc
    (fun z hz => ⟨(hΦc z hz).1, (hΦc z hz).2⟩) (z := (x₀, w)) hz1
  have hsplit2 := split_flow_geodesic g hg hinv (x₀, 0) hT (closedBall (x₀, 0) 1) Φc
    (fun z hz => ⟨(hΦc z hz).1, (hΦc z hz).2⟩) (z := (x₀, a • w)) hz2
  let c₁ : ℝ → E := fun u => (Φc (x₀, w) u).1
  let vel₁ : ℝ → E := fun u => (Φc (x₀, w) u).2
  let c₂ : ℝ → E := fun u => (Φc (x₀, a • w) u).1
  let vel₂ : ℝ → E := fun u => (Φc (x₀, a • w) u).2
  have hc₁ (s : ℝ) (hs : s ∈ Ioo (-T) T) : HasDerivAt c₁ (vel₁ s) s := by
    simpa [c₁, vel₁] using hsplit1.1 s hs
  have hv₁ (s : ℝ) (hs : s ∈ Ioo (-T) T) :
      HasDerivAt vel₁ (accel (g (c₁ s)) (fderiv ℝ g (c₁ s)) (vel₁ s)) s := by
    simpa [c₁, vel₁] using hsplit1.2 s hs
  have hc₂ (s : ℝ) (hs : s ∈ Ioo (-T) T) : HasDerivAt c₂ (vel₂ s) s := by
    simpa [c₂, vel₂] using hsplit2.1 s hs
  have hv₂ (s : ℝ) (hs : s ∈ Ioo (-T) T) :
      HasDerivAt vel₂ (accel (g (c₂ s)) (fderiv ℝ g (c₂ s)) (vel₂ s)) s := by
    simpa [c₂, vel₂] using hsplit2.2 s hs
  have hc₁0 : c₁ 0 = x₀ := by
    simpa [c₁] using (congrArg Prod.fst (hΦc (x₀, w) hz1).1)
  have hv₁0 : vel₁ 0 = w := by
    simpa [vel₁] using (congrArg Prod.snd (hΦc (x₀, w) hz1).1)
  have hc₂0 : c₂ 0 = x₀ := by
    simpa [c₂] using (congrArg Prod.fst (hΦc (x₀, a • w) hz2).1)
  have hv₂0 : vel₂ 0 = a • w := by
    simpa [vel₂] using (congrArg Prod.snd (hΦc (x₀, a • w) hz2).1)
  have hscaling := flow_scaling (g := g) (hg := hg) (hinv := hinv) (ε₁ := T) (ε₂ := T)
    (hε₁ := hT) (hε₂ := hT) (c₁ := c₁) (vel₁ := vel₁) (c₂ := c₂) (vel₂ := vel₂)
    (x := x₀) (v := w) (s := a) (hs := ha0)
    (hc₁ := hc₁0) (hv₁ := hv₁0) (hc₂ := hc₂0) (hv₂ := hv₂0)
    (hc₁d := hc₁) (hv₁d := hv₁) (hc₂d := hc₂) (hv₂d := hv₂)
  have hAbs : 0 < |a| := abs_pos.mpr ha0
  have ht1 : |t| < T := by
    have hmem : t ∈ Ioo (-T) T := ht
    rw [abs_lt]
    exact ⟨hmem.1, hmem.2⟩
  have ht2 : |t| < T / |a| := by
    rw [lt_div_iff₀ hAbs]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htscale
  have hmin : |t| < min T (T / |a|) := lt_min ht1 ht2
  have hmem2 := abs_lt.mp hmin
  have ht' : t ∈ Ioo (-min T (T / |a|)) (min T (T / |a|)) := ⟨hmem2.1, hmem2.2⟩
  have hsc := hscaling t ht'
  have hmain : c₂ t = c₁ (a * t) := hsc.1
  calc
    (Φc (x₀, a • w) t).1 = c₂ t := by rfl
    _ = c₁ (a * t) := hmain
    _ = (Φc (x₀, w) (a * t)).1 := by rfl

/-- The diagonal derivative of the exponential along the radial direction: the derivative of
`exp` at `u` applied to the vector `u` is `τ` times the flow velocity at the endpoint, i.e.
the tangent vector of the radial curve `s ↦ exp (s • u)` at `s = 1`. -/
lemma exp_fderiv_diag (g : E → Bilin E) (hg : ContDiff ℝ 3 g) (hinv : ∀ x, (g x).IsInvertible)
    (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf) (Φ : E × E → ℝ → E × E)
    (hΦall : ∀ z ∈ closedBall (x₀, (0 : E)) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       ∀ t : ℝ, Φ z t ∈ closedBall (x₀, (0 : E)) 2)
    {τ ρE : ℝ} (hτ : 0 < τ) (h2τTf : 2 * τ < Tf) (hρE : 0 < ρE) (hρEτ : ρE ≤ τ)
    (hC : ContDiffOn ℝ 1 (expOf x₀ Φ τ) (ball (0 : E) ρE))
    {u : E} (hu : u ∈ ball (0 : E) ρE) :
    (fderiv ℝ (expOf x₀ Φ τ) u) u = τ • (Φ (x₀, τ⁻¹ • u) τ).2 := by
  have hΦ2 : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
      ∀ s ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z s)) s := by
    intro z hz
    exact ⟨(hΦall z hz).1, (hΦall z hz).2.1⟩
  have huE : ‖u‖ < ρE := by
    have hd : dist u 0 < ρE := mem_ball.mp hu
    simpa [dist_eq_norm] using hd
  have huτ : ‖u‖ < τ := lt_of_lt_of_le huE hρEτ
  have hτin : τ ∈ Ioo (-Tf) Tf := by
    constructor <;> nlinarith [h2τTf, hTf]
  have hτmem : τ ∈ Icc (-Tf) Tf := ⟨le_of_lt hτin.1, le_of_lt hτin.2⟩
  let w : E := τ⁻¹ • u
  have hτinv0 : 0 < τ⁻¹ := by positivity
  have hwlt : ‖w‖ < 1 := by
    dsimp [w]
    calc
      ‖τ⁻¹ • u‖ = ‖(τ⁻¹ : ℝ)‖ * ‖u‖ := by rw [norm_smul]
      _ = τ⁻¹ * ‖u‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hτinv0)]
      _ < τ⁻¹ * τ := mul_lt_mul_of_pos_left huτ hτinv0
      _ = 1 := by field_simp [ne_of_gt hτ]
  have hw1 : ‖w‖ ≤ 1 := le_of_lt hwlt
  let κ : ℝ := ‖w‖
  have hκ0 : 0 ≤ κ := norm_nonneg w
  have hκ1 : κ < 1 := by simpa [κ] using hwlt
  let f : ℝ → E := fun a => expOf x₀ Φ τ (a • u)
  let gg : ℝ → E := fun a => (Φ (x₀, τ⁻¹ • u) (a * τ)).1
  -- a small two-sided neighbourhood of 1 where the ray scaling holds
  let δ : ℝ := min (1 / 2) (min ((1 - κ) / 2) ((Tf / τ - 1) / 2))
  have hδ12 : δ ≤ 1 / 2 := by dsimp [δ]; exact min_le_left _ _
  have hδ1 : δ ≤ (1 - κ) / 2 := by dsimp [δ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ2 : δ ≤ (Tf / τ - 1) / 2 := by dsimp [δ]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    have h1 : 0 < (1 - κ) / 2 := by linarith [hκ1]
    have h2 : 0 < (Tf / τ - 1) / 2 := by
      have htfτ : 1 < Tf / τ := by
        rw [lt_div_iff₀ hτ]
        linarith [h2τTf]
      linarith
    exact lt_min (by norm_num) (lt_min h1 h2)
  have hfeq (a : ℝ) (ha : |a - 1| < δ) : f a = gg a := by
    have ha1 : |a| ≤ 1 + δ := by
      have htri : |a| ≤ |a - 1| + 1 := by
        calc
          |a| = |(a - 1) + 1| := by congr 1; ring
          _ ≤ |a - 1| + |(1 : ℝ)| := abs_add_le (a - 1) (1 : ℝ)
          _ = |a - 1| + 1 := by norm_num
      linarith [ha]
    have haκ : ‖a • w‖ ≤ 1 := by
      have hκa : |a| * κ ≤ (1 + δ) * κ := mul_le_mul_of_nonneg_right ha1 hκ0
      have hκb : (1 + δ) * κ ≤ 1 := by
        have hκm : (1 + (1 - κ) / 2) * κ ≤ 1 := by
          nlinarith [hκ1, hκ0]
        nlinarith [hκm, hδ1]
      have hnorm : ‖a • w‖ = |a| * κ := by
        rw [norm_smul]
        rw [Real.norm_eq_abs]
      rw [hnorm]
      exact le_trans hκa hκb
    have hat : |a| * τ < Tf := by
      have hb : (1 + (Tf / τ - 1) / 2) * τ < Tf := by
        field_simp [ne_of_gt hτ]
        nlinarith [h2τTf]
      nlinarith [ha1, hδ2, hb]
    have ha0 : a ≠ 0 := by
      by_contra hz
      have hle : |a - 1| = 1 := by simp [hz]
      have hδ1' : δ ≤ 1 / 2 := hδ12
      linarith
    have hsmul : τ⁻¹ • (a • u) = a • (τ⁻¹ • u) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    have htsc : |τ| * |a| < Tf := by
      rw [abs_of_pos hτ]
      simpa [mul_comm] using hat
    have hsc := exp_ray_scaling' g hg hinv x₀ hTf Φ hΦ2 (w := w) hw1 (a := a) ha0 haκ
      (t := τ) hτin htsc
    dsimp [f, gg]
    change (Φ (x₀, τ⁻¹ • (a • u)) τ).1 = (Φ (x₀, τ⁻¹ • u) (a * τ)).1
    rw [hsmul]
    simpa [w] using hsc
  -- derivative of g at 1
  let z : E × E := (x₀, τ⁻¹ • u)
  have hz1 : z ∈ closedBall (x₀, 0) 1 := mem_data_ball x₀ w hw1
  have hderΦ : HasDerivAt (Φ z) (odeField g (Φ z τ)) τ := (hΦ2 z hz1).2 τ hτmem
  have hsplit := split_flow_geodesic g hg hinv (x₀, (0 : E)) hTf (closedBall (x₀, 0) 1) Φ hΦ2
    (z := z) hz1
  have hderfst : HasDerivAt (fun t : ℝ => (Φ z t).1) (Φ z τ).2 τ := by
    have h := hsplit.1 τ hτin
    simpa using h
  have hlin1 : HasDerivAt (fun a : ℝ => a * τ) τ (1 : ℝ) := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const τ
  have hderfst' : HasFDerivAt (fun t : ℝ => (Φ z t).1)
      (ContinuousLinearMap.toSpanSingleton ℝ ((Φ z τ).2)) (1 * τ) := by
    simpa [one_mul] using hderfst.hasFDerivAt
  have hgderz : HasDerivAt (fun a : ℝ => (Φ z (a * τ)).1) (τ • (Φ z τ).2) (1 : ℝ) := by
    have hc := hderfst'.comp_hasDerivAt (1 : ℝ) hlin1
    simpa [Function.comp_def] using hc
  have hgder : HasDerivAt gg (τ • (Φ z τ).2) (1 : ℝ) := by
    simpa [gg, z] using hgderz
  -- f agrees with g near 1, so f has the same derivative
  have hfeq_near : ∀ᶠ a in 𝓝 (1 : ℝ), f a = gg a := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (1 : ℝ) hδ0) ?_
    intro a ha
    exact hfeq a (by simpa [dist_eq_norm] using ha)
  have hfder : HasDerivAt f (τ • (Φ z τ).2) (1 : ℝ) := hgder.congr_of_eventuallyEq hfeq_near
  -- chain rule for f
  have hExpDiff : DifferentiableAt ℝ (expOf x₀ Φ τ) u := by
    exact (hC.contDiffAt (isOpen_ball.mem_nhds hu)).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hmem1u : ((1 : ℝ) • u) ∈ ball (0 : E) ρE := by
    rw [one_smul]
    exact hu
  have hExpDiff1 : DifferentiableAt ℝ (expOf x₀ Φ τ) ((1 : ℝ) • u) := by
    exact (hC.contDiffAt (isOpen_ball.mem_nhds hmem1u)).differentiableAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hlinu : HasDerivAt (fun a : ℝ => a • u) u (1 : ℝ) := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const u
  have hc1 := hExpDiff1.hasFDerivAt.comp_hasDerivAt (1 : ℝ) hlinu
  have hchain : HasDerivAt f ((fderiv ℝ (expOf x₀ Φ τ) u) u) (1 : ℝ) := by
    simpa [f, Function.comp_def] using hc1
  have hval : (fderiv ℝ (expOf x₀ Φ τ) u) u = τ • (Φ z τ).2 := hchain.unique hfder
  simpa [z] using hval

/-- Equality case of the radial (Gauss) bound in exponential coordinates: if the radial
coordinate derivative `(fderiv R u) A` equals the model speed of the pushed tangent vector
`(fderiv exp u) A`, then the coordinate vector `A` is collinear with `u`. -/
lemma collinear_of_radial_eq (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) {Tf : ℝ} (hTf : 0 < Tf) (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hΦall : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       ∀ t : ℝ, Φ z t ∈ closedBall (x₀, 0) 2)
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall (x₀, 0) 1))
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hK : ∀ p ∈ closedBall (x₀, 0) 2, ‖fderiv ℝ (odeField g) p‖ ≤ K0)
    {τ ρE : ℝ} (hτ : 0 < τ) (h4τTf : 4 * τ ≤ Tf) (hρE : 0 < ρE) (h4ρEτ : 4 * ρE ≤ τ)
    (hUb : ∀ i : Fin (Module.finrank ℝ (E × E)),
       4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τ ≤ 1)
    (hC : ContDiffOn ℝ 1 (expOf x₀ Φ τ) (ball (0 : E) ρE))
    {u : E} (hu : u ∈ ball (0 : E) ρE) (hu0 : u ≠ 0)
    (hInjD : ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ (expOf x₀ Φ τ) u)
    {A : E}
    (heq : (fderiv ℝ (fun z : E => √(((g x₀) z) z)) u) A =
      √(((g (expOf x₀ Φ τ u)) ((fderiv ℝ (expOf x₀ Φ τ) u) A)) ((fderiv ℝ (expOf x₀ Φ τ) u) A))) :
    ∃ t : ℝ, A = t • u := by
  classical
  let exp : E → E := expOf x₀ Φ τ
  let y : E := exp u
  let Z : E := (Φ (x₀, τ⁻¹ • u) τ).2
  let Y : E := (fderiv ℝ exp u) A
  let rr : ℝ := √(((g x₀) u) u)
  have hrr : 0 < rr := bilin_sqrt_pos (hpos x₀) hu0
  have hτinv0 : 0 < τ⁻¹ := by positivity
  have h2τTf : 2 * τ < Tf := by nlinarith [h4τTf, hTf]
  have huE : ‖u‖ < ρE := by
    have hd : dist u 0 < ρE := mem_ball.mp hu
    simpa [dist_eq_norm] using hd
  have hvin : (x₀, τ⁻¹ • u) ∈ ball (x₀, 0) (1 / 2) := by
    rw [mem_ball, dist_eq_norm]
    have hnorm : ‖(x₀, τ⁻¹ • u) - (x₀, 0)‖ = ‖τ⁻¹ • u‖ := by simp
    rw [hnorm]
    have hτinv : 0 < τ⁻¹ := by positivity
    have hsmul : ‖τ⁻¹ • u‖ ≤ τ⁻¹ * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hτinv)]
    have hρ4 : ρE ≤ τ / 4 := by nlinarith [h4ρEτ]
    have hule : ‖u‖ < τ / 4 := lt_of_lt_of_le huE hρ4
    have hlt : τ⁻¹ * ‖u‖ < τ⁻¹ * (τ / 4) := mul_lt_mul_of_pos_left hule hτinv
    have hstep : τ⁻¹ * (τ / 4) = 1 / 4 := by
      field_simp [ne_of_gt hτ]
    have h2 : τ⁻¹ * ‖u‖ < 1 / 2 := by
      rw [hstep] at hlt
      linarith
    exact lt_of_le_of_lt hsmul h2

  rcases gauss_pair g hg hinv hsym x₀ (Tf := Tf) hTf (Lf := Lf) (Φ := Φ) hΦall hLip
    (K0 := K0) hK0 hK (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (τ := τ) hτ h4τTf hUb
    (v := u) (W := A) hvin with ⟨hD, hpair, hspeed⟩
  -- gauss identities
  have hpair' : ((g y) Y) Z = τ⁻¹ * ((g x₀) A) u := by
    simpa [y, Z, Y, exp, expOf] using hpair
  have hspeed' : ((g y) Z) Z = τ⁻¹ ^ 2 * ((g x₀) u) u := by
    simpa [y, Z, exp, expOf] using hspeed
  -- the radial derivative formula and equality
  have hvalR : (fderiv ℝ (fun z : E => √(((g x₀) z) z)) u) A = ((g x₀) u) A / rr := by
    simpa [rr] using radial_fderiv_apply (B := g x₀) (hsym x₀) (hpos x₀) hu0 A
  have heq2 : ((g x₀) u) A / rr = √(((g y) Y) Y) := by
    simpa [y, Y, exp, hvalR] using heq
  by_cases hA0 : A = 0
  · subst A
    exact ⟨0, by simp⟩
  · have hY0 : Y ≠ 0 := by
      intro hz
      apply hA0
      rcases hInjD with ⟨e, he⟩
      have hinj : Function.Injective (fderiv ℝ exp u) := by
        intro a b h
        have h' : (e : E →L[ℝ] E) a = (e : E →L[ℝ] E) b := by simpa [exp, he] using h
        simpa [exp, he] using e.injective h'
      exact hinj (by simpa [Y] using hz)
    have hZ0 : Z ≠ 0 := by
      intro hz
      have hz' : ((g y) Z) Z = 0 := by simp [hz]
      have hposZ : 0 < ((g y) Z) Z := by
        rw [hspeed']
        exact mul_pos (sq_pos_of_ne_zero (ne_of_gt hτinv0)) (hpos x₀ u hu0)
      rw [hz'] at hposZ
      exact (lt_irrefl _) hposZ
    have hnonneg : 0 ≤ τ⁻¹ * rr := le_of_lt (mul_pos hτinv0 hrr)
    have hZsqrt : √(((g y) Z) Z) = τ⁻¹ * rr := by
      have h1 : ((g y) Z) Z = (τ⁻¹ * rr) ^ 2 := by
        rw [hspeed']
        have hsq : ((g x₀) u) u = rr ^ 2 := by
          dsimp [rr]
          exact (bilin_sqrt_sq (hpos x₀) u).symm
        rw [hsq]
        ring
      rw [h1]
      rw [Real.sqrt_sq hnonneg]
    have hpair2 : ((g y) Y) Z = √(((g y) Y) Y) * √(((g y) Z) Z) := by
      have hmain : ((g x₀) u) A = rr * √(((g y) Y) Y) := by
        have hden : rr ≠ 0 := ne_of_gt hrr
        rw [← heq2]
        field_simp [hden]
      rw [hpair', hsym x₀ A u, hmain, hZsqrt]
      ring
    have hsq : ((g y) Y) Z * ((g y) Y) Z = ((g y) Y) Y * ((g y) Z) Z := by
      have hpair3 := hpair2
      have hnonY : 0 ≤ ((g y) Y) Y := le_of_lt (hpos y Y hY0)
      have hnonZ : 0 ≤ ((g y) Z) Z := le_of_lt (hpos y Z hZ0)
      rw [hpair3]
      have hsqY : (√(((g y) Y) Y)) ^ 2 = ((g y) Y) Y := Real.sq_sqrt hnonY
      have hsqZ : (√(((g y) Z) Z)) ^ 2 = ((g y) Z) Z := Real.sq_sqrt hnonZ
      nlinarith [hsqY, hsqZ]
    rcases bilin_cs_eq_colinear (B := g y) (hsym y) (hpos y) (u := Y) (v := Z) hZ0 hY0 hsq with ⟨t, hYZ⟩
    -- L2: diagonal derivative
    have hL2 : (fderiv ℝ exp u) u = τ • Z := by
      have hdiag := exp_fderiv_diag g hg hinv x₀ (Tf := Tf) hTf Φ hΦall (τ := τ) hτ h2τTf
        (ρE := ρE) hρE (by nlinarith [h4ρEτ]) hC hu
      simpa [exp, Z] using hdiag
    have hZeq : Z = τ⁻¹ • ((fderiv ℝ exp u) u) := by
      rw [hL2]
      rw [smul_smul]
      have hmul : τ⁻¹ * τ = 1 := by field_simp [ne_of_gt hτ]
      rw [hmul, one_smul]
    have hYZ2 : (fderiv ℝ exp u) A = (t * τ⁻¹) • ((fderiv ℝ exp u) u) := by
      have htmp : Y = t • Z := hYZ
      change Y = (t * τ⁻¹) • ((fderiv ℝ exp u) u)
      rw [htmp, hZeq]
      rw [smul_smul]
    -- injectivity of the derivative gives A collinear with u
    rcases hInjD with ⟨e, he⟩
    have hinj : Function.Injective (fderiv ℝ exp u) := by
      intro a b h
      have h' : (e : E →L[ℝ] E) a = (e : E →L[ℝ] E) b := by simpa [exp, he] using h
      simpa [exp, he] using e.injective h'
    have hdiff : (fderiv ℝ exp u) A = (fderiv ℝ exp u) ((t * τ⁻¹) • u) := by
      rw [hYZ2]
      simp
    exact ⟨t * τ⁻¹, hinj hdiff⟩

/-- Direction-constancy engine: if a curve `w` is differentiable on `(0,1)`, its derivative is
always collinear with its position, its `(g b)`-squared norm is `(s r)^2`, and `w 1 = v`, then
`w s = s • v` on `(0,1)`. -/
lemma neck_direction (g : E → Bilin E) (b : E)
    (hsymB : ∀ u w : E, ((g b) u) w = ((g b) w) u)
    {r : ℝ} (hr : 0 < r) {v : E} {wF : ℝ → E}
    (hwFcont : ContinuousAt wF 1)
    (hwFdiff : ∀ s ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ wF s)
    (hq : ∀ s ∈ Ioo (0 : ℝ) 1, ((g b) (wF s)) (wF s) = (s * r) ^ 2)
    (hcoll : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ t : ℝ, deriv wF s = t • (wF s))
    (hw1 : wF 1 = v) :
    ∀ s ∈ Ioo (0 : ℝ) 1, wF s = s • v := by
  have hwd (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : HasDerivAt wF (deriv wF s) s :=
    (hwFdiff s hs).hasDerivAt
  -- (g b)-value of the derivative
  have hqval (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : ((g b) (wF s)) (deriv wF s) = s * r ^ 2 := by
    have hquad := bilin_quad_hasFDerivAt (B := g b) (wF s)
    have hcomp := hquad.comp_hasDerivAt s (hwd s hs)
    have hsym2 : ((g b) (deriv wF s)) (wF s) = ((g b) (wF s)) (deriv wF s) := hsymB (deriv wF s) (wF s)
    have hlin : (((g b) (wF s)).comp (1 : E →L[ℝ] E) + (g b).flip (wF s)) (deriv wF s)
        = 2 * (((g b) (wF s)) (deriv wF s)) := by
      simp [hsym2]
      ring
    have hfeqfun : (fun z : E => ((g b) z) z) ∘ wF = fun t : ℝ => ((g b) (wF t)) (wF t) := by
      funext t
      rfl
    have hqder : HasDerivAt (fun t : ℝ => ((g b) (wF t)) (wF t))
        (2 * (((g b) (wF s)) (deriv wF s))) s := by
      rw [hfeqfun] at hcomp
      rw [hlin] at hcomp
      exact hcomp

    have hsame' : (fun t : ℝ => (t * r) ^ 2) =ᶠ[𝓝 s]
        (fun u : ℝ => ((g b) (wF u)) (wF u)) := by
      refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) ?_
      intro t ht
      exact (hq t ht).symm
    have hlin2 : HasDerivAt (fun t : ℝ => t * r) r s := by
      simpa using (hasDerivAt_id s).mul_const r
    have hpow := hlin2.pow 2
    have hvalp : ↑2 * (s * r) ^ (2 - 1) * r = 2 * s * r ^ 2 := by
      rw [show (2 - 1) = 1 by norm_num, pow_one]
      ring
    have hmul2 := hlin2.mul hlin2
    have hfun' : (fun t : ℝ => (t * r) ^ 2) = (fun t : ℝ => t * r) * (fun t : ℝ => t * r) := by
      funext t
      simp [pow_two]
    have hvald : r * (s * r) + (s * r) * r = 2 * s * r ^ 2 := by ring
    have hrhs : HasDerivAt (fun t : ℝ => (t * r) ^ 2) (2 * s * r ^ 2) s := by
      simpa [hfun', hvald] using hmul2
    have huniq := (hqder.congr_of_eventuallyEq hsame').unique hrhs
    have h2 : 2 * (((g b) (wF s)) (deriv wF s)) = 2 * s * r ^ 2 := huniq
    nlinarith
  -- explicit scalar factor of the derivative
  have hscalar (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : deriv wF s = (s⁻¹ : ℝ) • (wF s) := by
    rcases hcoll s hs with ⟨t, ht⟩
    have hsr2 : (s * r) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (mul_ne_zero (ne_of_gt hs.1) (ne_of_gt hr))
    have htval : t * (((g b) (wF s)) (wF s)) = s * r ^ 2 := by
      have hb : ((g b) (wF s)) (deriv wF s) = ((g b) (wF s)) (t • (wF s)) := by rw [ht]
      have hbl : ((g b) (wF s)) (t • (wF s)) = t * (((g b) (wF s)) (wF s)) := bilin_smul_right (g b) t (wF s) (wF s)
      rw [hbl] at hb
      exact hb.symm.trans (hqval s hs)
    have ht' : t = s⁻¹ := by
      rw [hq s hs] at htval
      have hneX : s * r ^ 2 ≠ 0 := by
        exact mul_ne_zero (ne_of_gt hs.1) (pow_ne_zero 2 (ne_of_gt hr))
      have h1' : (t * s) * (s * r ^ 2) = s * r ^ 2 := by
        calc
          (t * s) * (s * r ^ 2) = t * (s * r) ^ 2 := by ring
          _ = s * r ^ 2 := htval
      have hmul : t * s = 1 := (mul_left_cancel₀ hneX) (by simpa [mul_comm, mul_left_comm, mul_assoc] using h1')
      field_simp [ne_of_gt hs.1]
      exact hmul
    calc
      deriv wF s = t • (wF s) := ht
      _ = (s⁻¹ : ℝ) • (wF s) := by rw [ht']
  -- the normalized curve e is constant
  let e : ℝ → E := (fun t : ℝ => t⁻¹) • wF
  have hederiv (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : HasDerivAt e 0 s := by
    have hsne : s ≠ 0 := ne_of_gt hs.1
    have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-(s ^ 2)⁻¹) s := hasDerivAt_inv hsne
    have hsmul := hinv.smul (hwd s hs)
    have hval0 : s⁻¹ • (deriv wF s) + -((s ^ 2)⁻¹ • (wF s)) = 0 := by
      rw [hscalar s hs]
      rw [smul_smul]
      have hm : s⁻¹ * s⁻¹ = (s ^ 2)⁻¹ := by
        field_simp [pow_two, hsne]
      rw [hm]
      abel
    simpa [e, hval0] using hsmul
  have hdiffOn : DifferentiableOn ℝ e (Ioo (0 : ℝ) 1) := by
    intro x hx
    exact (hederiv x hx).differentiableAt.differentiableWithinAt
  have hderiv0 : EqOn (deriv e) 0 (Ioo (0 : ℝ) 1) := by
    intro x hx
    exact (hederiv x hx).deriv
  rcases IsOpen.exists_is_const_of_deriv_eq_zero (𝕜 := ℝ) (G := E) (s := Ioo (0 : ℝ) 1)
    isOpen_Ioo isPreconnected_Ioo hdiffOn hderiv0 with ⟨c, hc⟩
  have hwsc (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : wF s = s • c := by
    have hsne : s ≠ 0 := ne_of_gt hs.1
    have hec : (s⁻¹ : ℝ) • wF s = c := by
      have hh := hc s hs
      simpa [e] using hh
    calc
      wF s = s • ((s⁻¹ : ℝ) • wF s) := by
        rw [smul_smul]
        have hm : s * s⁻¹ = 1 := by field_simp [hsne]
        rw [hm, one_smul]
      _ = s • c := by rw [hec]
  -- identify c with v by the endpoint value
  have hcv : c = v := by
    let g : ℝ → E := fun s => s • c
    have hgcont : ContinuousAt g 1 := by
      exact (continuousAt_id.smul continuousAt_const)
    have hmem : Set.Ioo (1 / 2 : ℝ) 1 ∈ 𝓝[Iio (1 : ℝ)] 1 := by
      rw [nhdsWithin]
      rw [Filter.mem_inf_principal]
      refine Filter.mem_of_superset (isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Ioi (1 / 2))) ?_
      intro x hx xlt
      exact ⟨hx, xlt⟩
    have heq' : g =ᶠ[𝓝[Iio (1 : ℝ)] 1] wF := by
      refine Filter.mem_of_superset hmem ?_
      intro s hs
      have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
      have hsc : wF s = s • c := hwsc s hs01
      simpa [g] using hsc.symm
    have hwlim : Tendsto wF (𝓝[Iio (1 : ℝ)] 1) (𝓝 v) := by
      have hwv : Tendsto wF (𝓝 (1 : ℝ)) (𝓝 (wF 1)) := hwFcont.tendsto
      simpa [hw1] using hwv.mono_left nhdsWithin_le_nhds
    have hglim : Tendsto g (𝓝[Iio (1 : ℝ)] 1) (𝓝 c) := by
      simpa [g] using hgcont.tendsto.mono_left nhdsWithin_le_nhds
    have hwlim' : Tendsto wF (𝓝[Iio (1 : ℝ)] 1) (𝓝 c) := hglim.congr' heq'
    exact (tendsto_nhds_unique hwlim hwlim').symm
  intro s hs
  rw [hwsc s hs, hcv]

theorem neck_eq_per_base (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (b : E) {τf : ℝ} (hτf : 0 < τf) (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hPerB : ∀ z ∈ closedBall (b, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (b, 0) 2))
    (hLipB : ∀ t ∈ Icc (-τf) τf,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, 0) 1))
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hKb : ∀ p ∈ closedBall (b, 0) 2, ‖fderiv ℝ (odeField g) p‖ ≤ K0)
    {τu δu ρE : ℝ} (hτu0 : 0 < τu) (hδu0 : 0 < δu) (hρE0 : 0 < ρE)
    (h8τuτf : 8 * τu ≤ τf) (h4ρEτu : 4 * ρE ≤ τu) (hδuρE : δu ≤ ρE)
    (hUb : ∀ i : Fin (Module.finrank ℝ (E × E)),
       4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τu ≤ 1)
    (D : NeckData g b Φ τu δu ρE)
    {v : E} (hv : v ∈ ball (0 : E) δu) {c : ℝ → E}
    (hc0 : c 0 = b) (hc1 : c 1 = D.expb v)
    (hcO : ∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O)
    (hcStay : ∀ s ∈ Icc (0 : ℝ) 1, c s ∈ ball b δu)
    (hSpeed : ∀ s ∈ Ioo (0 : ℝ) 1, mgSpeed g (c s) (deriv c s) = √((g b) v v)) :
    ∀ s ∈ Icc (0 : ℝ) 1, c s = D.expb (s • v) := by
  let r : ℝ := √((g b) v v)
  let inv : E → E := D.invb
  let F : E → ℝ := radialCoord g b inv
  let R : E → ℝ := fun z : E => √(((g b) z) z)
  have hfe : D.expb = expOf b Φ τu := funext (fun z => D.expform z)
  have hFval (u : E) (hu : u ∈ ball (0 : E) ρE) : F (D.expb u) = R u := by
    dsimp [F, inv, R, radialCoord]
    rw [D.inv_left u hu]
  have hFb0 : F b = 0 := by
    dsimp [F, inv, radialCoord]
    have h0mem : (0 : E) ∈ ball (0 : E) ρE := by simpa using hρE0
    have hb0 : D.invb b = 0 := by
      exact (congrArg D.invb D.exp0).symm.trans (D.inv_left (0 : E) h0mem)
    rw [hb0]
    simp
  rcases hcO with ⟨O, hOopen, hOIcc, hcC1⟩
  have hcdiffAt (t : ℝ) (ht : t ∈ O) : DifferentiableAt ℝ c t := by
    exact (hcC1.contDiffAt (hOopen.mem_nhds ht)).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hcontAt (t : ℝ) (ht : t ∈ O) : ContinuousAt c t :=
    (hcC1.contDiffAt (hOopen.mem_nhds ht)).continuousAt
  have hmemO (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t ∈ O := hOIcc ht
  by_cases hv0 : v = 0
  · subst v
    -- constant speed 0 forces c to be constant
    have hzeroDeriv (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : deriv c s = 0 := by
      have hφ0 : mgSpeed g (c s) (deriv c s) = 0 := by
        have hg0 : √(((g b) 0) 0) = 0 := by simp
        simpa [hg0] using hSpeed s hs
      have hnn : 0 ≤ ((g (c s)) (deriv c s)) (deriv c s) :=
        bilin_pos_sq_nonneg (hpos (c s)) (deriv c s)
      have hsq : √(((g (c s)) (deriv c s)) (deriv c s)) = 0 := by
        simpa [mgSpeed] using hφ0
      have hd0 : ((g (c s)) (deriv c s)) (deriv c s) = 0 :=
        (Real.sqrt_eq_zero hnn).mp hsq
      by_contra hne
      exact (ne_of_gt (hpos (c s) (deriv c s) hne)) hd0
    intro s hs
    by_cases hs0 : s = 0
    · rw [hs0]
      simp [hc0, D.exp0]
    · have hs0le : 0 ≤ s := hs.1
      have hs1 : s ≤ 1 := hs.2
      have hdiff0 : ∀ x ∈ Ioo (0 : ℝ) s, HasDerivAt c 0 x := by
        intro x hx
        have hx1 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_lt_of_le hx.2 hs1⟩
        have hxO : x ∈ O := hmemO x ⟨le_of_lt hx1.1, le_of_lt hx1.2⟩
        have hd : HasDerivAt c (deriv c x) x := (hcdiffAt x hxO).hasDerivAt
        simpa [hzeroDeriv x hx1] using hd
      have hcont0 : ContinuousOn c (Icc (0 : ℝ) s) := by
        refine hcC1.continuousOn.mono ?_
        intro t ht
        exact hmemO t ⟨ht.1, le_trans ht.2 hs1⟩
      have hint : IntervalIntegrable (fun _ : ℝ => (0 : E)) volume (0 : ℝ) s := by
        simpa using (intervalIntegral.integrableOn_const :
          MeasureTheory.IntegrableOn (fun _ : ℝ => (0 : E)) (Set.Icc (0 : ℝ) s) volume)
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (a := (0 : ℝ)) (b := s) hs0le hcont0 hdiff0 hint
      have hint0 : (∫ x in (0 : ℝ)..s, (0 : E)) = 0 := by simp
      have hcs : c s = c 0 := by
        have hsub : c s - c 0 = 0 := by
          rw [← hFTC]
          exact hint0
        exact sub_eq_zero.mp hsub
      rw [hcs, hc0]
      simp [D.exp0]
  · -- main case: v ≠ 0
    have hr : 0 < r := by
      dsimp [r]
      exact bilin_sqrt_pos (hpos b) hv0
    have hφ (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : mgSpeed g (c s) (deriv c s) = r := by
      simpa [r] using hSpeed s hs
    have hvU : v ∈ ball (0 : E) ρE := by exact ball_subset_ball hδuρE hv
    have h0U : (0 : E) ∈ ball (0 : E) ρE := by simpa using hρE0
    have hc1ne : c 1 ≠ b := by
      intro heq
      apply hv0
      have hE : D.expb v = D.expb (0 : E) := by
        rw [← hc1, heq, D.exp0]
      exact D.inj v (0 : E) hvU h0U hE
    have hcAt01 (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ContinuousAt c s := by
      exact hcontAt s (hmemO s hs)
    let Z : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ c s = b}
    have hZnonempty : Z.Nonempty := ⟨0, by simp [Z, hc0]⟩
    have hZclosed : IsClosed Z := by
      refine ⟨?_⟩
      rw [isOpen_iff_mem_nhds]
      intro s hs
      by_cases hs01 : s ∈ Icc (0 : ℝ) 1
      · have hcne : c s ≠ b := by
          intro heq
          exact hs ⟨hs01, heq⟩
        have hnhds : c ⁻¹' ({b}ᶜ) ∈ 𝓝 s := by
          exact (hcAt01 s hs01).preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hcne)
        refine Filter.mem_of_superset hnhds ?_
        intro t ht tZ
        exact ht tZ.2
      · have hmem : s ∈ (Icc (0 : ℝ) 1)ᶜ := by simpa using hs01
        have hnhds : (Icc (0 : ℝ) 1)ᶜ ∈ 𝓝 s := isClosed_Icc.isOpen_compl.mem_nhds hmem
        refine Filter.mem_of_superset hnhds ?_
        intro t ht tZ
        exact ht tZ.1
    have hZbd : BddAbove Z := ⟨1, by intro s hs; exact hs.1.2⟩
    let a : ℝ := sSup Z
    have haZ : a ∈ Z := IsClosed.csSup_mem hZclosed hZnonempty hZbd
    have ha0 : 0 ≤ a := haZ.1.1
    have ha1 : a ≤ 1 := haZ.1.2
    have hca : c a = b := haZ.2
    have h1notZ : (1 : ℝ) ∉ Z := by
      intro h1Z
      exact hc1ne h1Z.2
    have ha1lt : a < 1 := lt_of_le_of_ne ha1 (by
      intro haeq1
      exact h1notZ (by simpa [haeq1] using haZ))
    have hne_gt (x : ℝ) (hx : x ∈ Ioo a 1) : c x ≠ b := by
      intro heq
      have hx01 : x ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [ha0, hx.1, hx.2]
      have hxZ : x ∈ Z := ⟨hx01, heq⟩
      have hxle : x ≤ a := le_csSup hZbd hxZ
      exact (not_lt_of_ge hxle) hx.1
    have hFc1 : F (c 1) = r := by
      dsimp [F, inv, radialCoord, r]
      rw [hc1]
      rw [D.inv_left v hvU]
    have hFcA : F (c a) = 0 := by
      rw [hca]
      exact hFb0
    have hFc0 : F (c 0) = 0 := by
      rw [hc0]
      exact hFb0
    -- radial drop over [a,1]: r ≤ (1-a) r, so a = 0
    have hdropA_raw := radial_drop_le g b inv hδu0 D.F_cont D.F_diff D.F_bound ⟨O, hOopen, hOIcc, hcC1⟩
      hcStay (r := r) hφ (p := a) (q := 1) (le_of_lt ha1lt) ha0 (le_refl (1 : ℝ))
      (by intro x hx; exact hne_gt x hx)
    have hdropA : F (c 1) - F (c a) ≤ (1 - a) * r := by
      simpa [F, inv] using hdropA_raw
    have hdropA' : r ≤ (1 - a) * r := by
      rw [hFc1, hFcA] at hdropA
      simpa using hdropA
    have ha0' : a ≤ 0 := by nlinarith [hdropA', hr]
    have haeq0 : a = 0 := le_antisymm ha0' ha0
    have hne0 (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : c x ≠ b := by
      exact hne_gt x (by simpa [haeq0] using hx)
    -- monotonicity of the radial coordinate: F(c s) = s r
    have hFs (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : F (c s) = s * r := by
      have hdrop1_raw := radial_drop_le g b inv hδu0 D.F_cont D.F_diff D.F_bound ⟨O, hOopen, hOIcc, hcC1⟩
        hcStay (r := r) hφ (p := 0) (q := s) (le_of_lt hs.1) (le_refl (0 : ℝ)) (le_of_lt hs.2)
        (by intro x hx; exact hne0 x ⟨hx.1, lt_trans hx.2 hs.2⟩)
      have hdrop1 : F (c s) - F (c 0) ≤ (s - 0) * r := by
        simpa [F, inv] using hdrop1_raw
      have hup : F (c s) ≤ s * r := by
        rw [hFc0] at hdrop1
        nlinarith [hdrop1]
      have hdrop2_raw := radial_drop_le g b inv hδu0 D.F_cont D.F_diff D.F_bound ⟨O, hOopen, hOIcc, hcC1⟩
        hcStay (r := r) hφ (p := s) (q := 1) (le_of_lt hs.2) (le_of_lt hs.1) (le_refl (1 : ℝ))
        (by intro x hx; exact hne0 x ⟨lt_trans hs.1 hx.1, hx.2⟩)
      have hdrop2 : F (c 1) - F (c s) ≤ (1 - s) * r := by
        simpa [F, inv] using hdrop2_raw
      have hlo : s * r ≤ F (c s) := by
        rw [hFc1] at hdrop2
        nlinarith [hdrop2]
      exact le_antisymm hup hlo
    -- the derivative of F along c is r on (0,1)
    have hFcDer (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : HasDerivAt (fun t => F (c t)) r s := by
      have heq : ∀ᶠ t in 𝓝 s, (fun x : ℝ => F (c x)) t = t * r := by
        refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) ?_
        intro t ht
        exact hFs t ht
      have hlin : HasDerivAt (fun t : ℝ => t * r) r s := by
        simpa using (hasDerivAt_id s).mul_const r
      exact hlin.congr_of_eventuallyEq heq
    have hFcDerChain (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
        HasDerivAt (fun t => F (c t)) ((fderiv ℝ F (c s)) (deriv c s)) s := by
      have hmemV : c s ∈ ball b δu := hcStay s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      have htne : c s ≠ b := hne0 s hs
      have hFdiffAt : DifferentiableAt ℝ F (c s) := D.F_diff (c s) hmemV htne
      have hcd : DifferentiableAt ℝ c s := hcdiffAt s (hmemO s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
      have hd := hFdiffAt.hasFDerivAt.comp_hasDerivAt s hcd.hasDerivAt
      simpa [Function.comp_def] using hd
    have hvalF (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : (fderiv ℝ F (c s)) (deriv c s) = r := by
      exact (hFcDerChain s hs).unique (hFcDer s hs)
    -- equal speed value on (0,1)
    have hRadEq (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
        (fderiv ℝ F (c s)) (deriv c s) = √(((g (c s)) (deriv c s)) (deriv c s)) := by
      have hsp : √(((g (c s)) (deriv c s)) (deriv c s)) = r := by
        simpa [mgSpeed] using hφ s hs
      rw [hvalF s hs, hsp]
    have hCexp : ContDiffOn ℝ 1 (expOf b Φ τu) (ball (0 : E) ρE) := by
      rw [← hfe]
      exact D.exp_c1
    -- the coordinate inverse curve w
    let wF : ℝ → E := fun t => D.invb (c t)
    have hFval' (u : E) (hu : u ∈ ball (0 : E) ρE) : F (expOf b Φ τu u) = R u := by
      dsimp [F, inv, R, radialCoord]
      have hiv : D.invb (D.expb u) = u := D.inv_left u hu
      have harg : D.invb (expOf b Φ τu u) = u := by
        calc
          D.invb (expOf b Φ τu u) = D.invb (D.expb u) := by rw [hfe]
          _ = u := hiv
      rw [harg]
    have hwDiff (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : DifferentiableAt ℝ wF s := by
      have hmemV : c s ∈ ball b δu := hcStay s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      have hci : ContDiffAt ℝ 1 D.invb (c s) := D.inv_c1 (c s) hmemV
      have hd1 : DifferentiableAt ℝ D.invb (c s) :=
        hci.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
      have hd2 : DifferentiableAt ℝ c s := hcdiffAt s (hmemO s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
      have hd := hd1.comp s hd2
      simpa [wF, Function.comp_def] using hd
    have hwmem (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : wF s ∈ ball (0 : E) ρE := by
      have hmemV : c s ∈ ball b δu := hcStay s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      exact (D.inv_right (c s) hmemV).1
    have hwexp (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : expOf b Φ τu (wF s) = c s := by
      have hmemV : c s ∈ ball b δu := hcStay s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      have he1 := (D.inv_right (c s) hmemV).2
      calc
        expOf b Φ τu (wF s) = D.expb (wF s) := by rw [← hfe]
        _ = c s := by simpa [wF] using he1
    have hwne (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : wF s ≠ 0 := by
      intro hz
      apply hne0 s hs
      rw [← hwexp s hs, hz]
      rw [← hfe]
      exact D.exp0
    have hFbAt (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
        ‖(fderiv ℝ F (c s)) (deriv c s)‖ ≤ mgSpeed g (c s) (deriv c s) := by
      have hmemV : c s ∈ ball b δu := hcStay s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      exact D.F_bound (c s) hmemV (hne0 s hs) (deriv c s)
    -- velocity is collinear with the coordinate position
    have hwcol (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : ∃ t : ℝ, deriv wF s = t • (wF s) := by
      have hmemV : c s ∈ ball b δu := hcStay s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      let u : E := wF s
      have huU : u ∈ ball (0 : E) ρE := by simpa [u] using hwmem s hs
      have hu0 : u ≠ 0 := by simpa [u] using hwne s hs
      have hU : expOf b Φ τu u = c s := by simpa [u] using hwexp s hs
      -- injectivity of the derivative of exp at u
      rcases D.fderiv_inv u huU with ⟨e, he⟩
      have hInjD : ∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = fderiv ℝ (expOf b Φ τu) u := by
        refine ⟨e, ?_⟩
        -- fderiv D.expb u = fderiv expOf u (same function)
        have hfeq : fderiv ℝ D.expb u = fderiv ℝ (expOf b Φ τu) u := by
          exact congrArg (fun f : E → E => fderiv ℝ f u) hfe
        simpa [hfeq] using he
      -- chain rule for c = exp ∘ w
      have hcd2 : HasDerivAt c (deriv c s) s := (hcdiffAt s (hmemO s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)).hasDerivAt
      have hwd2 : HasDerivAt wF (deriv wF s) s := (hwDiff s hs).hasDerivAt
      have hexpDiff : DifferentiableAt ℝ (expOf b Φ τu) u := by
        exact (hCexp.contDiffAt (isOpen_ball.mem_nhds huU)).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
      have hcompd : HasDerivAt (fun t => expOf b Φ τu (wF t)) ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s)) s := by
        have hc := hexpDiff.hasFDerivAt.comp_hasDerivAt s hwd2
        simpa [Function.comp_def, u] using hc
      have hceq : ∀ᶠ t in 𝓝 s, c t = expOf b Φ τu (wF t) := by
        refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) ?_
        intro t ht
        exact (hwexp t ht).symm
      have hchain : deriv c s = (fderiv ℝ (expOf b Φ τu) u) (deriv wF s) := by
        have hc' : HasDerivAt c ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s)) s :=
          hcompd.congr_of_eventuallyEq hceq
        exact (hc'.unique hcd2).symm
      -- the domain-level radial equality
      have hFR (x : E) (hx : x ∈ ball (0 : E) ρE) : F (expOf b Φ τu x) = R x := hFval' x hx
      have hFRd : DifferentiableAt ℝ F (expOf b Φ τu u) := by
        have hyV : expOf b Φ τu u ∈ ball b δu := by rw [hU]; exact hmemV
        have hyne : expOf b Φ τu u ≠ b := by rw [hU]; exact hne0 s hs
        exact D.F_diff (expOf b Φ τu u) hyV hyne
      have hExpd : DifferentiableAt ℝ (expOf b Φ τu) u := hexpDiff
      have hRd : DifferentiableAt ℝ R u := by
        exact radialComp_differentiableAt (B := g b) (inv := fun z : E => z) u
          (by
            have hc' : ContDiffAt ℝ 1 (fun z : E => z) u := (contDiff_id : ContDiff ℝ 1 (fun z : E => z)).contDiffAt
            exact hc') (by simpa using hpos b u hu0)
      have hdcomp := fderiv_comp_eq_on_open (F := F) (R := R) (exp := expOf b Φ τu) (U := ball (0 : E) ρE)
        isOpen_ball huU hFR hFRd hExpd hRd
      have hval2 : (fderiv ℝ F (expOf b Φ τu u)) ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s)) =
          (fderiv ℝ R u) (deriv wF s) := by
        have hcomp := congrArg (fun L : E →L[ℝ] ℝ => L (deriv wF s)) hdcomp
        simpa [Function.comp_def] using hcomp
      have htmp0 := hRadEq s hs
      have htmp1 : (fderiv ℝ F (c s)) ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s)) =
          √(((g (c s)) ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s)))
            ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s))) := by
        rw [hchain] at htmp0
        simpa using htmp0
      have htmp2 : (fderiv ℝ F (expOf b Φ τu u)) ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s)) =
          √(((g (expOf b Φ τu u)) ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s)))
            ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s))) := by
        rw [← hU] at htmp1
        simpa using htmp1
      have hheq : (fderiv ℝ (fun z : E => √(((g b) z) z)) u) (deriv wF s) =
          √(((g (expOf b Φ τu u)) ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s)))
            ((fderiv ℝ (expOf b Φ τu) u) (deriv wF s))) := by
        rw [hval2] at htmp2
        simpa [R] using htmp2
      rcases collinear_of_radial_eq g hg hinv hsym hpos b (Tf := τf) hτf Lf Φ hPerB hLipB
        (K0 := K0) hK0 hKb (τ := τu) hτu0 (by nlinarith [h8τuτf]) (ρE := ρE) hρE0 h4ρEτu hUb
        hCexp (u := u) huU hu0 hInjD (A := deriv wF s) hheq with ⟨t, htcol⟩
      exact ⟨t, by simpa [u] using htcol⟩
    -- the (g b)-squared norm of w is (s r)^2
    have hFw (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : √(((g b) (wF s)) (wF s)) = s * r := by
      have h1 : F (c s) = s * r := hFs s hs
      have h2 : F (c s) = √(((g b) (wF s)) (wF s)) := by
        dsimp [F, inv, wF, radialCoord]
      exact h2.symm.trans h1
    have hq (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : ((g b) (wF s)) (wF s) = (s * r) ^ 2 := by
      have hnn : 0 ≤ ((g b) (wF s)) (wF s) := bilin_pos_sq_nonneg (hpos b) (wF s)
      have hsquared : ((g b) (wF s)) (wF s) = (√(((g b) (wF s)) (wF s))) ^ 2 :=
        (Real.sq_sqrt hnn).symm
      rw [hsquared, hFw s hs]
    have hwFcont : ContinuousAt wF 1 := by
      have hmemV : c 1 ∈ ball b δu := hcStay 1 (by norm_num)
      have hci : ContinuousAt D.invb (c 1) := (D.inv_c1 (c 1) hmemV).continuousAt
      have hcc : ContinuousAt c 1 := hcontAt 1 (hmemO 1 (by norm_num))
      have hcomp := hci.comp hcc
      simpa [wF, Function.comp_def] using hcomp
    have hw1 : wF 1 = v := by
      dsimp [wF]
      rw [hc1, D.inv_left v hvU]
    have hdir := neck_direction g b (hsym b) (r := r) hr (v := v) (wF := wF) hwFcont
      (by intro s hs; exact hwDiff s hs) (by intro s hs; exact hq s hs)
      (by intro s hs; exact hwcol s hs) hw1
    have hfinal (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : c s = D.expb (s • v) := by
      have hws : wF s = s • v := hdir s hs
      calc
        c s = expOf b Φ τu (wF s) := (hwexp s hs).symm
        _ = expOf b Φ τu (s • v) := by rw [hws]
        _ = D.expb (s • v) := by rw [← hfe]
    intro s hs
    by_cases hs0' : s = 0
    · subst s
      simp [hc0, D.exp0]
    · by_cases hs1' : s = 1
      · subst s
        simp [one_smul, hc1]
      · have hs01 : s ∈ Ioo (0 : ℝ) 1 :=
          ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0'), lt_of_le_of_ne hs.2 hs1'⟩
        exact hfinal s hs01


/-! ## The uniform equality case -/

/-- Uniform over bases: a staying curve of constant model speed from `b` to the exponential of
`v` is the radial exponential curve. -/
theorem neck_eq_case {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x0 : E) (ρu τf : ℝ) (hρu : 0 < ρu) (hτf : 0 < τf)
    (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hPerBase : ∀ b ∈ ball x0 ρu, ∀ z ∈ closedBall (b, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (b, 0) 2))
    (hLip : ∀ t ∈ Icc (-τf) τf, ∀ b ∈ ball x0 ρu,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, 0) 1)) :
    ∃ ρB δu τu : ℝ, 0 < ρB ∧ 0 < δu ∧ 0 < τu ∧ ρB ≤ ρu ∧ 2 * τu ≤ τf ∧
      ∀ b ∈ ball x0 ρB,
        ∀ v ∈ ball (0 : E) δu,
          ∀ c : ℝ → E,
            c 0 = b → c 1 = expOf b Φ τu v →
            (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
            (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ ball b δu) →
            (∀ s ∈ Ioo (0 : ℝ) 1,
               Real.sqrt ((g (c s)) (deriv c s) (deriv c s)) = Real.sqrt ((g b) v v)) →
            ∀ s ∈ Icc (0 : ℝ) 1, c s = expOf b Φ τu (s • v) := by
  classical
  rcases neck_package g hg hinv hsym hpos x0 ρu τf hρu hτf Lf Φ hPerBase hLip with
    ⟨ρB, δu, τu, ρE, K0, hρB, hδu, hτu, hρE0, hK0, hρBρu, hδuρE, h4ρEτu, h8τuτf, hKbig, hUb,
      hpkg⟩
  refine ⟨ρB, δu, τu, hρB, hδu, hτu, hρBρu, ?_, ?_⟩
  · nlinarith [h8τuτf]
  · intro b hb v hv c hc0 hc1 hcO hcStay hSpeed
    have hb' : b ∈ ball x0 ρu := by exact ball_subset_ball hρBρu hb
    have hPerB : ∀ z ∈ closedBall (b, 0) 1, Φ z 0 = z ∧
        (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
        (∀ t : ℝ, Φ z t ∈ closedBall (b, 0) 2) := by
      intro z hz
      exact hPerBase b hb' z hz
    have hLipB : ∀ t ∈ Icc (-τf) τf,
        LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, 0) 1) := by
      intro t ht
      exact hLip t ht b hb'
    have hKb : ∀ p ∈ closedBall (b, 0) 2, ‖fderiv ℝ (odeField g) p‖ ≤ K0 := by
      intro p hp
      exact hKbig p (closedBall_b0_subset x0 hρu hb' hp)
    rcases hpkg b hb with ⟨D⟩
    have hc1' : c 1 = D.expb v := by
      rw [hc1]
      exact (D.expform v).symm
    have hmain := neck_eq_per_base g hg hinv hsym hpos b (τf := τf) hτf Lf Φ hPerB hLipB
      (K0 := K0) hK0 hKb (τu := τu) hτu hδu hρE0 h8τuτf h4ρEτu hδuρE hUb
      D hv hc0 hc1' hcO hcStay hSpeed
    intro s hs01
    have hcs := hmain s hs01
    rw [D.expform (s • v)] at hcs
    exact hcs
