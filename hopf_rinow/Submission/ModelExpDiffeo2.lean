import Submission.Model
import Submission.ModelCore
import Submission.ModelFlowCont
import Submission.ModelVarFrechet
import Submission.ModelScale
import Submission.ModelExp
import Submission.ModelAlg
import Submission.ModelUniq
import Submission.ModelVarConv
import Submission.ModelDerivId
import Submission.ExpCore
import Mathlib

/-!
# The geodesic-flow exponential map is a local diffeomorphism near zero (rigid statement)

Theorem: `Submission.Model.flow_exp_local_diffeomorphism`.

For a `C³` metric family `g : E → Bilin E` (symmetric, invertible at every point), a fixed base
point `x₀`, there is a positive `ρ` and a local flow `Φ` of the geodesic field on
`closedBall (x₀, 0) 2` (times in `Ioo (-ρ) ρ`), and an exponential map `exp` such that:

* `exp 0 = x₀`;
* on every unit-metric ray (`(g x₀) w w = 1`) the ray `t ↦ exp (t • w)` is the geodesic with
  initial data `(x₀, w)`: `exp (t • w) = (Φ (x₀, w) t).1`;
* `HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0`;
* `exp` is a local diffeomorphism at `0` (injective on a neighbourhood `U` of `0`, image `V` a
  neighbourhood of `x₀`, continuous, with a local inverse).

## Proof structure

1. The core analytic theorem (`Submission.ExpCore.flow_exp_core`, proved separately) provides a
   small `ρ₀ > 0` and a flow `Φ₀` of the geodesic field on `closedBall (x₀, 0) 1` (window
   `Icc (-(2ρ₀)) (2ρ₀)`, uniformly Lipschitz in the initial data) such that the map
   `exp₀ v := (Φ₀ (x₀, v/ρ₀) ρ₀).1` fixes `0`, has derivative the identity at `0` and is a
   local diffeomorphism at `0`.
2. The exponential map is `exp := exp₀`.  A flow on the full radius-2 data ball is obtained by
   gluing `Φ₀` (inside radius 1) with the geodesic flow `Φg` of `Submission.ModelExp.geodesic_flow`
   (between radii 1 and 2); beyond radius 2 the first component tracks `exp`.
3. The ray agreement `exp (t • w) = (Φ (x₀, w) t).1` for metric-unit `w` follows from the
   time-rescaling property of geodesics (`Submission.ModelFlowScale.flow_scaling`) for `‖w‖ ≤ 2`
   (where `Φ (x₀,w)` is a genuine flow value), and by definition of the tracking branch for
   `‖w‖ > 2`.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedSectionVars false

/-- Splitting of an arbitrary flow into position/velocity geodesic equations. -/
lemma split_flow_geodesic (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) {T : ℝ} (hT : 0 < T)
    (S : Set (E × E)) (Φ : E × E → ℝ → E × E)
    (hΦ : ∀ z ∈ S, Φ z 0 = z ∧
       ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    {z : E × E} (hz : z ∈ S) :
    (∀ t ∈ Ioo (-T) T, HasDerivAt (fun s => (Φ z s).1) ((Φ z t).2) t) ∧
    (∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun s => (Φ z s).2)
        (accel (g ((Φ z t).1)) (fderiv ℝ g ((Φ z t).1)) ((Φ z t).2)) t) := by
  constructor
  · intro t ht
    have hαt := (hΦ z hz).2 t (Ioo_subset_Icc_self ht)
    have h1 : HasDerivAt (fun s => (Φ z s).1) (odeField g (Φ z t)).1 t := by
      have hf := hαt.hasFDerivAt.fst.hasDerivAt
      simpa using hf
    simpa [odeField] using h1
  · intro t ht
    have hαt := (hΦ z hz).2 t (Ioo_subset_Icc_self ht)
    have h2 : HasDerivAt (fun s => (Φ z s).2) (odeField g (Φ z t)).2 t := by
      have hf := hαt.hasFDerivAt.snd.hasDerivAt
      simpa using hf
    simpa [odeField] using h2

/-- Membership of `(x₀, (t/ρ₀) • w)` in the radius-1 data ball, for small `t`. -/
lemma mem_data_slice (x₀ : E) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (w : E) {t : ℝ}
    (ht : |t| < ρ₀ / 2) (hw : ‖w‖ ≤ 2) : (x₀, (t / ρ₀) • w) ∈ closedBall (x₀, 0) 1 := by
  apply mem_pair_ball x₀ 1 (by norm_num)
  have hpos : 0 ≤ |t| / ρ₀ := div_nonneg (abs_nonneg t) (le_of_lt hρ₀)
  have h1 : (|t| / ρ₀) * ‖w‖ ≤ (|t| / ρ₀) * 2 := mul_le_mul_of_nonneg_left hw hpos
  have h2 : (|t| / ρ₀) * 2 < 1 := by
    rw [div_mul_eq_mul_div]
    rw [div_lt_one (by positivity : 0 < ρ₀)]
    nlinarith [ht]
  have hnormlt : ‖(t / ρ₀) • w‖ < 1 := by
    calc
      ‖(t / ρ₀) • w‖ = ‖t / ρ₀‖ * ‖w‖ := by rw [norm_smul]
      _ = (|t| / ρ₀) * ‖w‖ := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hρ₀]
      _ ≤ (|t| / ρ₀) * 2 := h1
      _ < 1 := h2
  exact le_of_lt hnormlt

/-- Ray agreement for a unit-time slice of the flow: `exp(t • w) = flow₂(x₀, w)(t)`, where the
two flows may differ as long as both produce genuine geodesics on their windows. -/
lemma ray_agreement_core (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (ε₁ : ℝ) (hε₁ : 0 < ε₁) (hρε₁ : ρ₀ < ε₁)
    (Φ₀ : E × E → ℝ → E × E)
    (hΦ₀ : ∀ z ∈ closedBall (x₀, 0) 1, Φ₀ z 0 = z ∧
       ∀ t ∈ Icc (-ε₁) ε₁, HasDerivAt (Φ₀ z) (odeField g (Φ₀ z t)) t)
    (ε₂ : ℝ) (hε₂ : 0 < ε₂)
    (Φ₂ : E × E → ℝ → E × E)
    (hΦ₂ : ∀ z ∈ closedBall (x₀, 0) 2, Φ₂ z 0 = z ∧
       ∀ t ∈ Icc (-ε₂) ε₂, HasDerivAt (Φ₂ z) (odeField g (Φ₂ z t)) t)
    (hrest : Φ₀ (x₀, 0) ρ₀ = (x₀, 0))
    (w : E) (hw : ‖w‖ ≤ 2) {t : ℝ} (ht : |t| < min (ρ₀ / 2) ε₂) :
    (Φ₀ (x₀, (1 / ρ₀) • (t • w)) ρ₀).1 = (Φ₂ (x₀, w) t).1 := by
  have htρ : |t| < ρ₀ / 2 := lt_of_lt_of_le ht (min_le_left _ _)
  have htε₂ : |t| < ε₂ := lt_of_lt_of_le ht (min_le_right _ _)
  by_cases ht0 : t = 0
  · subst t
    have hz₀₂ : (x₀, w) ∈ closedBall (x₀, 0) 2 := mem_pair_ball x₀ 2 (by norm_num) w hw
    have hleft : (Φ₀ (x₀, 0) ρ₀).1 = x₀ := by
      simpa using congrArg Prod.fst hrest
    have hright : (Φ₂ (x₀, w) 0).1 = x₀ := by
      simpa using congrArg Prod.fst (hΦ₂ (x₀, w) hz₀₂).1
    simp [smul_zero, hleft, hright]
  · let a : E := (t / ρ₀) • w
    have ha : a = (1 / ρ₀) • (t • w) := by
      simp [a, smul_smul]
      ring_nf
    let c₁ : ℝ → E := fun s => (Φ₀ (x₀, a) s).1
    let vel₁ : ℝ → E := fun s => (Φ₀ (x₀, a) s).2
    let c₂ : ℝ → E := fun s => (Φ₂ (x₀, w) s).1
    let vel₂ : ℝ → E := fun s => (Φ₂ (x₀, w) s).2
    have hza : (x₀, a) ∈ closedBall (x₀, 0) 1 := by
      simpa [a] using mem_data_slice x₀ ρ₀ hρ₀ w htρ hw
    have hzw : (x₀, w) ∈ closedBall (x₀, 0) 2 := mem_pair_ball x₀ 2 (by norm_num) w hw
    have hsplit₁ := split_flow_geodesic g hg hinv (x₀,0) hε₁ (closedBall (x₀,0) 1) Φ₀ hΦ₀ hza
    have hsplit₂ := split_flow_geodesic g hg hinv (x₀,0) hε₂ (closedBall (x₀,0) 2) Φ₂ hΦ₂ hzw
    let s : ℝ := ρ₀ / t
    have hs : s ≠ 0 := div_ne_zero (ne_of_gt hρ₀) ht0
    have hsa : s • a = w := by
      dsimp [s, a]
      rw [smul_smul]
      have hmul : (ρ₀ / t) * (t / ρ₀) = 1 := by
        field_simp [ht0, ne_of_gt hρ₀]
      rw [hmul, one_smul]
    have hc10 : c₁ 0 = x₀ := by
      simpa [c₁] using (congrArg Prod.fst (hΦ₀ (x₀,a) hza).1)
    have hv10 : vel₁ 0 = a := by
      simpa [vel₁] using (congrArg Prod.snd (hΦ₀ (x₀,a) hza).1)
    have hc20 : c₂ 0 = x₀ := by
      simpa [c₂] using (congrArg Prod.fst (hΦ₂ (x₀,w) hzw).1)
    have hv20 : vel₂ 0 = s • a := by
      have hsnd : (Φ₂ (x₀, w) 0).2 = w := congrArg Prod.snd (hΦ₂ (x₀,w) hzw).1
      rw [hsa]
      simpa [vel₂, hsnd]
    have hc₁d : ∀ u ∈ Ioo (-ε₁) ε₁, HasDerivAt c₁ (vel₁ u) u := by
      intro u hu
      simpa [c₁, vel₁] using hsplit₁.1 u hu
    have hv₁d : ∀ u ∈ Ioo (-ε₁) ε₁,
        HasDerivAt vel₁ (accel (g (c₁ u)) (fderiv ℝ g (c₁ u)) (vel₁ u)) u := by
      intro u hu
      simpa [c₁, vel₁] using hsplit₁.2 u hu
    have hc₂d : ∀ u ∈ Ioo (-ε₂) ε₂, HasDerivAt c₂ (vel₂ u) u := by
      intro u hu
      simpa [c₂, vel₂] using hsplit₂.1 u hu
    have hv₂d : ∀ u ∈ Ioo (-ε₂) ε₂,
        HasDerivAt vel₂ (accel (g (c₂ u)) (fderiv ℝ g (c₂ u)) (vel₂ u)) u := by
      intro u hu
      simpa [c₂, vel₂] using hsplit₂.2 u hu
    have hscaling := flow_scaling (g := g) (hg := hg) (hinv := hinv)
      (ε₁ := ε₁) (hε₁ := hε₁) (ε₂ := ε₂) (hε₂ := hε₂)
      (c₁ := c₁) (vel₁ := vel₁) (c₂ := c₂) (vel₂ := vel₂) (x := x₀) (v := a) (s := s) (hs := hs)
      (hc₁ := hc10) (hv₁ := hv10) (hc₂ := hc20) (hv₂ := hv20)
      (hc₁d := hc₁d) (hv₁d := hv₁d) (hc₂d := hc₂d) (hv₂d := hv₂d)
    have hst : s * t = ρ₀ := by
      dsimp [s]
      field_simp [ht0, ne_of_gt hρ₀]
    have hmm : |t| < min ε₂ (ε₁ / |s|) := by
      have hltε₂ : |t| < ε₂ := htε₂
      have hs0 : 0 < |s| := abs_pos.mpr hs
      have hstabs : |s| * |t| < ε₁ := by
        have h1 : |s * t| = ρ₀ := by rw [hst, abs_of_pos hρ₀]
        have h2 : |s| * |t| = |s * t| := by rw [abs_mul]
        rw [h1] at h2
        rw [h2]
        exact hρε₁
      have hlt2s : |t| < ε₁ / |s| := by
        apply (lt_div_iff₀ hs0).mpr
        simpa [mul_comm] using hstabs
      exact lt_min hltε₂ hlt2s
    have htI : t ∈ Ioo (-min ε₂ (ε₁ / |s|)) (min ε₂ (ε₁ / |s|)) := by
      rcases abs_lt.mp hmm with ⟨h1, h2⟩
      exact ⟨h1, h2⟩
    have hconcl := hscaling t htI
    have hmain : c₂ t = c₁ (s * t) := hconcl.1
    have hgoal : c₁ ρ₀ = (Φ₀ (x₀, (1 / ρ₀) • (t • w)) ρ₀).1 := by
      dsimp [c₁]
      rw [← ha]
    have hc2 : c₂ t = (Φ₂ (x₀, w) t).1 := rfl
    calc
      (Φ₀ (x₀, (1 / ρ₀) • (t • w)) ρ₀).1 = c₁ ρ₀ := hgoal.symm
      _ = c₁ (s * t) := by rw [hst]
      _ = c₂ t := hmain.symm
      _ = (Φ₂ (x₀, w) t).1 := hc2

/-- The geodesic-flow exponential map (rigid statement): the flow exponential map near a base
point is a local diffeomorphism at zero and agrees with the genuine geodesic flow on all
unit-metric rays. -/
theorem flow_exp_local_diffeomorphism (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (x₀ : E) :
    ∃ ρ > 0, ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
         ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      (∃ exp : E → E, exp 0 = x₀ ∧
        (∀ w : E, (g x₀) w w = 1 → ∀ t ∈ Ioo (-ρ) ρ, exp (t • w) = (Φ (x₀, w) t).1) ∧
        HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 ∧
        (∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 x₀,
           Set.MapsTo exp U V ∧ Function.Injective (fun v : U => exp v.1) ∧
           Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
           ∃ inv : E → E, ∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y ∧
             ∀ v ∈ U, inv (exp v) = v)) := by
  classical
  rcases Submission.ExpCore.flow_exp_core g hg hinv x₀ with ⟨ρ₀, hρ₀pos, Φ₀, L₀, hΦ₀, hLip₀, hrest, hcore⟩
  let exp₀ : E → E := fun v => (Φ₀ (x₀, (1 / ρ₀) • v) ρ₀).1
  rcases hcore with ⟨hE0, hEder, hD⟩
  rcases geodesic_flow g hg hinv (x₀, 0) with ⟨Tg, hTgpos, Cg, hCg0, Φg, hΦgall⟩
  rcases hΦgall with ⟨hΦg, hΦgtimelip, hΦgtaylor⟩
  let ρ : ℝ := min (ρ₀ / 4) (Tg / 4)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (by positivity)
  have hρρ₀ : ρ ≤ ρ₀ / 2 := by
    dsimp [ρ]
    exact le_trans (min_le_left _ _) (by linarith)
  have hρTg : ρ ≤ Tg := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (by linarith)
  have hρ2ρ₀ : ρ ≤ 2 * ρ₀ := by linarith [hρρ₀]
  let T_c : ℝ := min (2 * ρ₀) Tg
  have hT_c_pos : 0 < T_c := by
    dsimp [T_c]
    exact lt_min (by positivity) (by positivity)
  have hT_c_le_2ρ₀ : T_c ≤ 2 * ρ₀ := by
    dsimp [T_c]
    exact min_le_left _ _
  have hT_c_le_Tg : T_c ≤ Tg := by
    dsimp [T_c]
    exact min_le_right _ _
  -- the merged flow: inner part from the core flow, outer part (radius ≤ 2) from the global
  -- geodesic flow, and beyond that it tracks the exponential map in the first component.
  let Φ : E × E → ℝ → E × E := fun z t =>
    if hz1 : z ∈ closedBall (x₀, 0) 1 then Φ₀ z t
    else if hz2 : z ∈ closedBall (x₀, 0) 2 then Φg z t
    else (exp₀ (t • z.2), (0 : E))
  have hΦ2 : ∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
      ∀ t ∈ Icc (-T_c) T_c, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    by_cases hz1 : z ∈ closedBall (x₀, 0) 1
    · have hfun : Φ z = Φ₀ z := by
        funext s
        dsimp [Φ]
        rw [if_pos hz1]
      constructor
      · rw [hfun]
        exact (hΦ₀ z hz1).1
      · intro t ht
        have ht' : t ∈ Icc (-(2 * ρ₀)) (2 * ρ₀) := by
          constructor
          · exact le_trans (neg_le_neg hT_c_le_2ρ₀) ht.1
          · exact le_trans ht.2 hT_c_le_2ρ₀
        rw [hfun]
        exact (hΦ₀ z hz1).2 t ht'
    · have hfun : Φ z = Φg z := by
        funext s
        dsimp [Φ]
        rw [if_neg hz1]
        have hz2 : z ∈ closedBall (x₀, 0) 2 := hz
        rw [if_pos hz2]
      constructor
      · rw [hfun]
        exact (hΦg z hz).1
      · intro t ht
        have ht' : t ∈ Icc (-Tg) Tg := by
          constructor
          · exact le_trans (neg_le_neg hT_c_le_Tg) ht.1
          · exact le_trans ht.2 hT_c_le_Tg
        rw [hfun]
        exact (hΦg z hz).2 t ht'
  have hρT_c : ρ ≤ T_c := by
    dsimp [T_c]
    exact le_min hρ2ρ₀ hρTg
  refine ⟨ρ, hρ, Φ, ?_, exp₀, ?_, ?_, ?_, ?_⟩
  · -- (A): the flow property on the full closed ball of radius 2, times in Ioo (-ρ) ρ
    intro z hz
    constructor
    · exact (hΦ2 z hz).1
    · intro t ht
      have htIcc : t ∈ Icc (-T_c) T_c := by
        constructor <;> linarith [ht.1, ht.2, hρT_c]
      exact (hΦ2 z hz).2 t htIcc
  · -- exp 0 = x₀
    simpa [exp₀] using hE0
  · -- ray agreement with the merged flow
    intro w hwunit t ht
    by_cases hw2 : ‖w‖ ≤ 2
    · have htabs : |t| < min (ρ₀ / 2) T_c := by
        have h1 : |t| < ρ := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        exact lt_min (lt_of_lt_of_le h1 hρρ₀) (lt_of_lt_of_le h1 hρT_c)
      have hray := ray_agreement_core g hg hinv x₀ ρ₀ (by positivity) (2 * ρ₀)
        (by positivity) (by linarith) Φ₀ hΦ₀ T_c hT_c_pos Φ hΦ2 hrest w hw2 htabs
      simpa [exp₀] using hray
    · have hnm1 : (x₀, w) ∉ closedBall (x₀, 0) 1 := by
        intro hm
        exact hw2 (by
          have hd : ‖(x₀, w) - (x₀, 0)‖ ≤ 2 := by
            have hmem2 : (x₀, w) ∈ closedBall (x₀, 0) 2 :=
              closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hm
            rw [← dist_eq_norm]
            exact mem_closedBall.mp hmem2
          simpa using hd)
      have hnm2 : (x₀, w) ∉ closedBall (x₀, 0) 2 := by
        intro hm
        exact hw2 (by
          have hd : ‖(x₀, w) - (x₀, 0)‖ ≤ 2 := by
            rw [← dist_eq_norm]
            exact mem_closedBall.mp hm
          simpa using hd)
      dsimp [exp₀]
      dsimp [Φ]
      rw [if_neg hnm1, if_neg hnm2]
  · -- HasFDerivAt exp₀ id 0
    simpa [exp₀] using hEder
  · -- local diffeomorphism clause: reuse the core's clause (definitionally the same map)
    dsimp [exp₀]
    exact hD

end
end Submission.Model
