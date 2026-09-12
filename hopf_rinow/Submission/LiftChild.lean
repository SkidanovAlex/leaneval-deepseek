import ChallengeDeps
import Submission.Metric
import Submission.NeckEq
import Submission.NeckSmooth
import Mathlib

/-!
# Lifted model-flow-curve path length bound (child task)

Model+chart.  `ge` is C3 symmetric positive definite, agreeing with the Riemannian bundle
metric of the chart `(extChartAt I q)` on the ball `ball (extChartAt I q q) ρT` (which lies in
the chart target).  At the model point `p` (inside `ball x0 (ρT/2)`) the flow `Φr` satisfies
per-base flow clauses over `closedBall (p,0) 1` for times `Icc (-τf) τf`, with the map
`z ↦ Φr z t` Lf-Lipschitz on `closedBall (p,0) 1`; `τu < τf`; `‖v‖ ≤ τu`; and
`(Lf:ℝ) * ‖v‖ / τu < ρT/2`.

Define σ(u) := expOf p Φr τu (u • v)  (the model geodesic from p with "initial" vector v).
CONCLUSION: the lifted chart curve Γ := (extChartAt I q).symm ∘ σ is C¹ on `Icc (0,1)` and
`Manifold.pathELength I Γ 0 1 ≤ ENNReal.ofReal (Real.sqrt ((ge p) v v))`.

Proof route:
1. `exp_ray_value` (ModelNormalBall / ModelPkg): σ u = (Φr (p, τu⁻¹•v) (u•τu)).1 for u∈[0,1].
2. derivative of σ: `flow_reparam_hasDerivAt` (ModelPkg) gives HasDerivAt of u↦(Φr z (τu•u)).1
   with value vel(u) := τu • (Φr z (τu•u)).2  (z := (p, τu⁻¹•v)); use HasDerivAt congr on a
   neighbourhood (valid on Ioo (0,1)).
3. squared speed: `flow_curve_speed` (ModelPkg): (ge (σ u)) (vel u) (vel u) = (ge p) v v.
4. staying in the chart ball: by the Lipschitz property, ‖σ u − p‖ ≤ (Lf:ℝ)·‖τu⁻¹v‖ ≤ (Lf:ℝ)‖v‖/τu
   (using `flow_rest_point` for the equilibrium (p,0)); with p∈ball x0 (ρT/2) and the smallness
   bound this gives σ u ∈ ball x0 ρT (⊆ target), so `chart_speed_core` gives the pointwise
   manifold speed ‖(mfderiv% Γ u) 1‖ₑ = ofReal √((ge p) v v) on Ioo (0,1).
5. pathELength is the lintegral of the pointwise speed over Ioo (use
   `Manifold.pathELength_eq_lintegral_mfderiv_Ioo`), which equals ofReal √((ge p) v v) (the
   length of the unit interval).
6. C¹ of Γ on Icc (0,1): compose the smooth σ with the chart inverse (ContMDiffOn ∞ on the
   target), using the per-point derivative/continuity; or prove via ContDiffOn of the
   reparametrization on an open set containing [0,1] and `.mono`.

All lemmas cited exist in the imported modules (check them).  No gaps remain in the file.
-/

open scoped Manifold ENNReal ContDiff Topology
open Set Filter Metric
open Bundle
open MeasureTheory

namespace Submission
namespace LiftChild

open Submission.Model

set_option synthInstance.maxHeartbeats 10000000
set_option maxHeartbeats 32000000

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem lift_length {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (q : M) (ge : E → E →L[ℝ] E →L[ℝ] ℝ) (hgeC : ContDiff ℝ 3 ge)
    (hinv : ∀ x, (ge x).IsInvertible) (hsym : ∀ x u v, (ge x) u v = (ge x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (ge x) u u)
    {ρT : ℝ} (hρT0 : 0 < ρT) (hρTtgt : ball (extChartAt I q q) ρT ⊆ (extChartAt I q).target)
    (hagree : ∀ y ∈ ball (extChartAt I q q) ρT, ∀ u v : E,
      (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
        ((extChartAt I q).symm y)
        ((mfderiv[range I] (extChartAt I q).symm y) u)
        ((mfderiv[range I] (extChartAt I q).symm y) v))
    (p : E) (hpT2 : p ∈ ball (extChartAt I q q) (ρT / 2))
    {τf : ℝ} (hτf : 0 < τf) (Lf : NNReal)
    (Φr : E × E → ℝ → E × E)
    (hPerB : ∀ z ∈ closedBall (p, 0) 1, Φr z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φr z) (odeField ge (Φr z t)) t) ∧
       (∀ t : ℝ, Φr z t ∈ closedBall (p, 0) 2))
    (hLipB : ∀ t ∈ Icc (-τf) τf,
       LipschitzOnWith Lf (fun z => Φr z t) (closedBall (p, 0) 1))
    {τu : ℝ} (hτu0 : 0 < τu) (hτuTf : τu < τf)
    {v : E} (hv : ‖v‖ ≤ τu) (hsmall : (Lf : ℝ) * ‖v‖ / τu < ρT / 2) :
    let σ : ℝ → E := fun u => expOf p Φr τu (u • v)
    let Γ : ℝ → M := fun u => (extChartAt I q).symm (σ u)
    ContMDiffOn 𝓘(ℝ,ℝ) I 1 Γ (Icc (0 : ℝ) 1) ∧
    Manifold.pathELength I Γ 0 1 ≤ ENNReal.ofReal (Real.sqrt ((ge p) v v)) := by
  classical
  let x0 : E := extChartAt I q q
  let σ : ℝ → E := fun u => expOf p Φr τu (u • v)
  let Γ : ℝ → M := fun u => (extChartAt I q).symm (σ u)
  change ContMDiffOn 𝓘(ℝ,ℝ) I 1 Γ (Icc (0 : ℝ) 1) ∧
    Manifold.pathELength I Γ 0 1 ≤ ENNReal.ofReal (Real.sqrt ((ge p) v v))
  -- the flow data in the two-conjunct form used by the model lemmas
  have hΦ2 : ∀ z ∈ closedBall (p, 0) 1, Φr z 0 = z ∧
       ∀ t ∈ Icc (-τf) τf, HasDerivAt (Φr z) (odeField ge (Φr z t)) t := by
    intro z hz
    exact ⟨(hPerB z hz).1, (hPerB z hz).2.1⟩
  have hz : (p, τu⁻¹ • v) ∈ closedBall (p, 0) 1 := by
    simpa using slice_data_mem p τu hτu0 (v := v) hv
  let c : ℝ → E := fun u => (Φr (p, τu⁻¹ • v) (τu * u)).1
  let vel : ℝ → E := fun u => τu • (Φr (p, τu⁻¹ • v) (τu * u)).2
  -- σ equals the reparametrized flow curve on [0,1]
  have hσc : ∀ u ∈ Icc (0 : ℝ) 1, σ u = c u := by
    intro u hu
    have hray := exp_ray_value (g := ge) (hg := hgeC) (hinv := hinv) p (Tf := τf) hτf Φr hΦ2
      (τ := τu) hτu0 hτuTf (v := v) hv (s := u) hu.1 hu.2
    dsimp [σ, c]
    rw [hray]
    ring_nf
  -- time membership facts for u ∈ [0,1]
  have hwin0 (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : τu * u ∈ Icc (-τf) τf := by
    constructor
    · have hneg : -τf ≤ (0 : ℝ) := by linarith
      exact le_trans hneg (mul_nonneg (le_of_lt hτu0) hu.1)
    · have hm : τu * u ≤ τu * 1 := mul_le_mul_of_nonneg_left hu.2 (le_of_lt hτu0)
      linarith
  have hwin0oo (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : τu * u ∈ Ioo (-τf) τf := by
    have hge : -τf < τu * u := by
      have hpos : 0 ≤ τu * u := mul_nonneg (le_of_lt hτu0) hu.1
      linarith
    have hlt : τu * u < τf := by
      have hm : τu * u ≤ τu * 1 := mul_le_mul_of_nonneg_left hu.2 (le_of_lt hτu0)
      linarith
    exact ⟨hge, hlt⟩
  -- ============================================================
  -- C^1 of σ on Icc (0,1)
  -- ============================================================
  have hcC1 : ContDiffOn ℝ 1 σ (Icc (0 : ℝ) 1) := by
    let R : ℝ := τf / τu
    have hR0 : 0 < R := div_pos hτf hτu0
    have hR1 : 1 < R := by
      dsimp [R]
      rwa [one_lt_div hτu0]
    have hOI : Icc (0 : ℝ) 1 ⊆ Ioo (-R) R := by
      intro t ht
      constructor
      · linarith [hR0, ht.1]
      · linarith [hR1, ht.2]
    have hwinO (t : ℝ) (ht : t ∈ Ioo (-R) R) : τu * t ∈ Icc (-τf) τf := by
      have h1 : |t| < R := abs_lt.mpr ht
      have h2 : |τu * t| = τu * |t| := by rw [abs_mul, abs_of_pos hτu0]
      have h3 : τu * |t| < τu * R := mul_lt_mul_of_pos_left h1 hτu0
      have h4 : τu * R = τf := by dsimp [R]; field_simp [ne_of_gt hτu0]
      have h5 : |τu * t| < τf := by
        calc
          |τu * t| = τu * |t| := h2
          _ < τu * R := h3
          _ = τf := h4
      exact abs_le.mp (le_of_lt h5)
    have hdiffO (t : ℝ) (ht : t ∈ Ioo (-R) R) : DifferentiableAt ℝ c t := by
      have hd := flow_reparam_hasDerivAt (g := ge) (hg := hgeC) (hinv := hinv) p (Tf := τf) hτf Φr
        (z := (p, τu⁻¹ • v)) hz hΦ2 (τe := τu) (t := t) (hwinO t ht)
      simpa [c] using hd.differentiableAt
    have hflowContO (t : ℝ) (ht : t ∈ Ioo (-R) R) :
        ContinuousAt (fun u : ℝ => Φr (p, τu⁻¹ • v) (τu * u)) t := by
      have hc1 : ContinuousAt (fun u : ℝ => τu * u) t :=
        ((hasDerivAt_id (𝕜 := ℝ) t).const_mul τu).continuousAt
      have hd : HasDerivAt (Φr (p, τu⁻¹ • v)) (odeField ge (Φr (p, τu⁻¹ • v) (τu * t))) (τu * t) :=
        (hPerB (p, τu⁻¹ • v) hz).2.1 (τu * t) (hwinO t ht)
      exact hd.continuousAt.comp hc1
    have hvelContO (t : ℝ) (ht : t ∈ Ioo (-R) R) : ContinuousAt vel t := by
      have hc2 : ContinuousAt (fun u : ℝ => (Φr (p, τu⁻¹ • v) (τu * u)).2) t :=
        (hflowContO t ht).snd
      have hsmul : ContinuousAt (fun u : ℝ => τu • (Φr (p, τu⁻¹ • v) (τu * u)).2) t :=
        hc2.const_smul τu
      simpa [vel] using hsmul
    have hvelContOn : ContinuousOn vel (Ioo (-R) R) := by
      intro t ht
      exact (hvelContO t ht).continuousWithinAt
    have hdv (t : ℝ) (ht : t ∈ Ioo (-R) R) : derivWithin c (Ioo (-R) R) t = vel t := by
      have hd := flow_reparam_hasDerivAt (g := ge) (hg := hgeC) (hinv := hinv) p (Tf := τf) hτf Φr
        (z := (p, τu⁻¹ • v)) hz hΦ2 (τe := τu) (t := t) (hwinO t ht)
      have hd' : deriv c t = vel t := by simpa [c, vel] using hd.deriv
      rw [derivWithin_of_isOpen isOpen_Ioo ht]
      exact hd'
    have hcontDeriv : ContinuousOn (fun t => derivWithin c (Ioo (-R) R) t) (Ioo (-R) R) := by
      apply ContinuousOn.congr hvelContOn
      intro t ht
      exact hdv t ht
    have hcCont : ContDiffOn ℝ 1 c (Ioo (-R) R) := by
      have hdiffOn : DifferentiableOn ℝ c (Ioo (-R) R) := by
        intro t ht
        exact (hdiffO t ht).differentiableWithinAt
      exact (contDiffOn_one_iff_derivWithin (isOpen_Ioo.uniqueDiffOn (s := Ioo (-R) R))).2
        ⟨hdiffOn, hcontDeriv⟩
    have hcContIcc : ContDiffOn ℝ 1 c (Icc (0 : ℝ) 1) := hcCont.mono hOI
    exact hcContIcc.congr (fun u hu => hσc u hu)
  -- ============================================================
  -- staying inside the agreement ball
  -- ============================================================
  have hnormv : ‖τu⁻¹ • v‖ = ‖v‖ / τu := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hτu0))]
    field_simp [ne_of_gt hτu0]
  have hbound (s : ℝ) (hs : s ∈ Ioo (-τf) τf) :
      ‖(Φr (p, τu⁻¹ • v) s).1 - p‖ ≤ (Lf : ℝ) * (‖v‖ / τu) := by
    have hsI : s ∈ Icc (-τf) τf := Ioo_subset_Icc_self hs
    have hrest : Φr (p, 0) s = (p, 0) := by
      exact flow_rest_point ge hgeC hinv hτf (x₀ := p) (Φ := Φr) hΦ2 s hs
    have hlip : LipschitzOnWith Lf (fun z => Φr z s) (closedBall (p, 0) 1) := hLipB s hsI
    have hb := (lipschitzOnWith_iff_dist_le_mul.mp hlip) (p, τu⁻¹ • v) hz (p, (0 : E))
      (by simp)
    have hdst : dist (p, τu⁻¹ • v) (p, (0 : E)) = ‖τu⁻¹ • v‖ := by
      simp [dist_eq_norm]
    have hb' : dist (Φr (p, τu⁻¹ • v) s) (Φr (p, 0) s) ≤ (Lf : ℝ) * ‖τu⁻¹ • v‖ := by
      simpa [hdst] using hb
    have hmain : ‖(Φr (p, τu⁻¹ • v) s) - (Φr (p, 0) s)‖ ≤ (Lf : ℝ) * ‖τu⁻¹ • v‖ := by
      simpa [dist_eq_norm] using hb'
    calc
      ‖(Φr (p, τu⁻¹ • v) s).1 - p‖
          = ‖((Φr (p, τu⁻¹ • v) s) - (p, (0 : E))).1‖ := by simp
      _ = ‖((Φr (p, τu⁻¹ • v) s) - (Φr (p, 0) s)).1‖ := by
          rw [hrest]
      _ ≤ ‖(Φr (p, τu⁻¹ • v) s) - (Φr (p, 0) s)‖ := norm_fst_le _
      _ ≤ (Lf : ℝ) * ‖τu⁻¹ • v‖ := hmain
      _ ≤ (Lf : ℝ) * (‖v‖ / τu) := by
          rw [hnormv]
  have hσmem (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : σ u ∈ ball x0 ρT := by
    rw [mem_ball, dist_eq_norm]
    have hc : σ u = c u := hσc u hu
    have h1 : ‖σ u - p‖ < ρT / 2 := by
      rw [hc]
      have hb := hbound (τu * u) (hwin0oo u hu)
      have h2 : (Lf : ℝ) * (‖v‖ / τu) < ρT / 2 := by
        have : (Lf : ℝ) * (‖v‖ / τu) = (Lf : ℝ) * ‖v‖ / τu := by ring
        rwa [this]
      exact lt_of_le_of_lt hb h2
    have hp : ‖p - x0‖ < ρT / 2 := by
      have := mem_ball.mp hpT2
      simpa [x0, dist_eq_norm] using this
    have htri : ‖σ u - x0‖ ≤ ‖σ u - p‖ + ‖p - x0‖ := by
      rw [show σ u - x0 = (σ u - p) + (p - x0) by abel]
      exact norm_add_le (σ u - p) (p - x0)
    have hlt : ‖σ u - x0‖ < ρT / 2 + ρT / 2 := lt_of_le_of_lt htri (add_lt_add h1 hp)
    have hlt' : ‖σ u - x0‖ < ρT := by linarith
    simpa [x0, dist_eq_norm] using hlt'
  -- ============================================================
  -- pointwise manifold speed on Ioo (0,1)
  -- ============================================================
  let c0 : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt ((ge p) v v))
  have hptwspeed (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : ‖(mfderiv% Γ t) 1‖ₑ = c0 := by
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hder : HasDerivAt σ (vel t) t := by
      have hflowder : HasDerivAt c (vel t) t := by
        have hd := flow_reparam_hasDerivAt (g := ge) (hg := hgeC) (hinv := hinv) p (Tf := τf) hτf Φr
          (z := (p, τu⁻¹ • v)) hz hΦ2 (τe := τu) (t := t) (hwin0 t htcc)
        simpa [c, vel] using hd
      have ht_nhds : Ioo (0 : ℝ) 1 ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
      have heq : σ =ᶠ[𝓝 t] c := by
        filter_upwards [ht_nhds] with u hu
        exact hσc u ⟨le_of_lt hu.1, le_of_lt hu.2⟩
      exact hflowder.congr_of_eventuallyEq heq
    have hspd := chart_speed_core (I := I) (M := M) q (ρ := ρT) (ge := ge) hagree hρTtgt
      (γ := Γ) (c := σ) (t := t) (u := vel t) (by intro s; rfl) (hσmem t htcc) hder
    have hsp := flow_curve_speed (g := ge) (hg := hgeC) (hinv := hinv) (hsym := hsym) p
      (Tf := τf) hτf Φr hΦ2 (τe := τu) hτu0 hτuTf (v := v) hv (t₀ := t) htcc
    have hsp' : (ge (σ t)) (vel t) (vel t) = (ge p) v v := by
      rw [hσc t htcc]
      simpa [c, vel] using hsp
    rw [hspd]
    rw [hsp']
  -- ============================================================
  -- the pathELength computation
  -- ============================================================
  have hEq : Manifold.pathELength I Γ 0 1 = c0 := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    calc
      (∫⁻ (t : ℝ) in Ioo (0 : ℝ) 1, ‖(mfderiv% Γ t) 1‖ₑ)
          = ∫⁻ (t : ℝ) in Ioo (0 : ℝ) 1, c0 := by
              exact setLIntegral_congr_fun measurableSet_Ioo (fun t ht => hptwspeed t ht)
      _ = c0 * (volume : Measure ℝ) (Ioo (0 : ℝ) 1) := MeasureTheory.setLIntegral_const (Ioo (0 : ℝ) 1) c0
      _ = c0 := by
          rw [Real.volume_Ioo]
          norm_num
  -- ============================================================
  -- assembly
  -- ============================================================
  have hΓC : ContMDiffOn 𝓘(ℝ,ℝ) I 1 Γ (Icc (0 : ℝ) 1) := by
    have hσM : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 σ (Icc (0 : ℝ) 1) := hcC1.contMDiffOn
    have hσtgt : Set.MapsTo σ (Icc (0 : ℝ) 1) (extChartAt I q).target := by
      intro u hu
      exact hρTtgt (by simpa [x0] using hσmem u hu)
    have hcomp : ContMDiffOn 𝓘(ℝ,ℝ) I 1 ((extChartAt I q).symm ∘ σ) (Icc (0 : ℝ) 1) :=
      ContMDiffOn.comp (contMDiffOn_extChartAt_symm (I := I) (x := q)) hσM hσtgt
    refine ContMDiffOn.congr hcomp ?_
    intro u hu
    rfl
  have hlen : Manifold.pathELength I Γ 0 1 ≤ ENNReal.ofReal (Real.sqrt ((ge p) v v)) := by
    rw [hEq]
  exact ⟨hΓC, hlen⟩

end
end LiftChild
end Submission
