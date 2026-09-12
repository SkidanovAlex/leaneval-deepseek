import Submission.Model
import Submission.ModelCore
import Submission.ModelFlowCont
import Submission.ModelAlg
import Submission.ModelUniq
import Submission.ModelFlowScale
import Mathlib

/-!
# The model exponential map at a base point

Task: prove the final theorem `exp_deriv_identity` (replace its placeholder).

## Goal

For a fixed base point `x₀ : E` and the smooth invertible metric family `g`, produce a local
exponential map `exp : E → E` defined near `0` such that

* `exp 0 = x₀`;
* on every unit direction `w` (`‖w‖ = 1`), the ray `t ↦ exp (t • w)` is the geodesic from
  `(x₀, w)` (i.e. `exp (t • w) = (Φ (x₀, w) t).1` where `Φ` is a local flow around `(x₀, 0)`);
* `exp` is differentiable at `0` with derivative the identity map.

## Proof route

1. Obtain a local flow `Φ : E × E → ℝ → E × E` around `(x₀, 0)` from
   `Submission.ModelFlowCont.flow_lipschitz g hg hinv x₀ 0`.  Its ball contains all
   `(x₀, w)` with `‖w‖ = 1` (enlarge the ball to radius 2 by choosing `z ∈ closedBall (x₀,0) 2`
   and shrinking the time interval if needed — or simply use `flow_lipschitz`'s ball and note
   the unit sphere is compact, hence contained in a finite union of its balls; simplest is to
   restate the flow property for `closedBall (x₀,0) 2` with a possibly smaller time `ρ > 0`,
   which you may obtain by a compactness/covering argument over the unit sphere, or by invoking
   `flow_lipschitz` at finitely many points — actually easiest: `flow_lipschitz` is already
   centred at `(x₀,0)`; scale the velocities: for any unit `w` the data point `(x₀, w)` has
   `‖(x₀,w) - (x₀,0)‖ = 1`, so if the flow's ball radius `r ≥ 1` we are done; if `r < 1`, shrink
   `w`-velocities is impossible — instead re-run `flow_lipschitz` at `(x₀, 0)` with the *same*
   base but ask the agent to verify that a common time exists for all unit velocities by a
   compactness argument over the unit sphere (finite subcover of the spheres of data-balls), or
   allow `ρ` to depend on nothing else — the theorem's `Φ` clause lets the agent choose `Φ`
   itself; so the agent may construct `Φ` directly as the flow from `flow_lipschitz` and then
   prove the required property holds for unit `w` after shrinking `ρ`).

2. Define `exp v` for `‖v‖` small: if `v = 0` then `exp 0 := x₀`; else
   `exp v := (Φ (x₀, v / ‖v‖) ‖v‖).1` (position after time `‖v‖` along the unit-velocity
   geodesic in direction `v/‖v‖`).  Then for `w` unit and `t ≥ 0` small:
   `exp (t • w) = (Φ (x₀, w) t).1` by definition (since `(t•w)/‖t•w‖ = w` and `‖t•w‖ = t`).

3. `exp 0 = x₀` — by definition.

4. **Derivative at 0 is the identity.**  For a unit `w`, `t ↦ exp (t • w) = (Φ (x₀, w) t).1`
   is the position component of a geodesic starting at `(x₀, w)`; its derivative at `t = 0` is
   `w` (initial velocity: from the flow property `HasDerivAt (Φ (x₀,w)) (odeField g (Φ (x₀,w) t)) t`
   at `t = 0`, the derivative of the position component is the second component of
   `odeField g (x₀, w) = (w, accel ...)`, namely `w`).  Hence along every unit ray the
   directional derivative of `exp` at `0` is the identity; conclude `HasFDerivAt exp id 0`
   (e.g. by a standard criterion: if all directional derivatives exist, are linear, and the map
   is sufficiently nice — for this concrete map you can directly prove the little-o estimate
   `exp v - x₀ - v = o(‖v‖)` using the geodesic's `HasDerivAt` at 0, the definition of `exp`,
   and `ModelScale.geodesic_rescale` if needed).

## Concrete statement to prove (keep the signature)

    theorem exp_deriv_identity (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
        (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) :
        ∃ ρ > 0, ∃ (exp : E → E) (Φ : E × E → ℝ → E × E),
          (∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
             ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
          exp 0 = x₀ ∧
          (∀ w : E, ‖w‖ = 1 → ∀ t ∈ Ioo (-ρ) ρ, exp (t • w) = (Φ (x₀, w) t).1) ∧
          HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0

Do NOT change the statement of `exp_deriv_identity`.  You may add helper definitions/lemmas
(including a definition `modelExp`).  No placeholder/`axiom` may remain.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section


/-- A `C¹` vector field that agrees with the geodesic field on `closedBall z₀ 3`, vanishes
outside `closedBall z₀ 4`, and is globally bounded and globally Lipschitz. -/
lemma smooth_truncation (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) :
    ∃ F : (E × E) → (E × E), ∃ L K : ℝ, 0 ≤ L ∧ 0 ≤ K ∧
      ContDiff ℝ 1 F ∧
      (∀ x, ‖F x‖ ≤ L) ∧
      (∀ x y, ‖F y - F x‖ ≤ K * ‖y - x‖) ∧
      (∀ x ∈ closedBall z₀ 3, F x = odeField g x) ∧
      (∀ x, 4 ≤ ‖x - z₀‖ → F x = 0) := by
  let X := E × E
  let V : X → X := odeField g
  have hV1 : ContDiff ℝ 1 V := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases p with ⟨x, v⟩
    simpa [V] using odeField_contDiffAt g hg hinv x v
  let φ : ContDiffBump z₀ := ⟨3, 4, by norm_num, by norm_num⟩
  let ψ : X → ℝ := (φ : X → ℝ)
  have hψ1 (x : X) (hx : x ∈ closedBall z₀ 3) : ψ x = 1 := by
    simpa [ψ] using φ.one_of_mem_closedBall hx
  have hψ0 (x : X) (hx : 4 ≤ ‖x - z₀‖) : ψ x = 0 := by
    have hd : 4 ≤ dist x z₀ := by
      calc
        4 ≤ ‖x - z₀‖ := hx
        _ = dist x z₀ := (dist_eq_norm x z₀).symm
    simpa [ψ] using (φ.zero_of_le_dist hd : (φ : X → ℝ) x = 0)
  have hψnonneg (x : X) : 0 ≤ ψ x := by
    simpa [ψ] using (φ.nonneg : 0 ≤ (φ : X → ℝ) x)
  have hψle1 (x : X) : ψ x ≤ 1 := by
    simpa [ψ] using (φ.le_one : (φ : X → ℝ) x ≤ 1)
  have hφs : ContDiff ℝ 1 ψ := by
    exact ContDiffBump.contDiff (f := φ)
  let F : X → X := fun x => ψ x • V x
  have hF1 : ContDiff ℝ 1 F := by
    have hs := hφs.smul hV1
    convert hs using 1
    funext x
    rfl
  have hFdiff : Differentiable ℝ F := by
    exact hF1.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hfdCont : Continuous (fderiv ℝ F) :=
    hF1.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have mem4_iff (x : X) : x ∈ closedBall z₀ 4 ↔ ‖x - z₀‖ ≤ 4 := by
    rw [mem_closedBall, dist_eq_norm]
  -- L bound: sup of ‖V‖ on the compact ball radius 4
  have hB4 : IsCompact (closedBall z₀ 4) := isCompact_closedBall z₀ 4
  have hB4ne : (closedBall z₀ 4).Nonempty := ⟨z₀, by simp⟩
  have hVcont : Continuous V := hV1.continuous
  have hVnrm : ContinuousOn (fun x : X => ‖V x‖) (closedBall z₀ 4) := hVcont.norm.continuousOn
  rcases hB4.exists_isMaxOn hB4ne hVnrm with ⟨xM, hxM, hmaxV⟩
  let L : ℝ := ‖V xM‖
  have hL0 : 0 ≤ L := by dsimp [L]; exact norm_nonneg _
  have hLb (x : X) : ‖F x‖ ≤ L := by
    dsimp [F]
    by_cases hxin : ‖x - z₀‖ ≤ 4
    · have hx : x ∈ closedBall z₀ 4 := (mem4_iff x).mpr hxin
      have hψle : ‖ψ x‖ ≤ 1 := by
        have hnn : 0 ≤ ψ x := hψnonneg x
        calc
          ‖ψ x‖ = ψ x := by rw [Real.norm_eq_abs, abs_of_nonneg hnn]
          _ ≤ 1 := hψle1 x
      calc
        ‖ψ x • V x‖ = ‖ψ x‖ * ‖V x‖ := by rw [norm_smul]
        _ ≤ 1 * ‖V x‖ := by
          exact mul_le_mul_of_nonneg_right hψle (norm_nonneg _)
        _ = ‖V x‖ := by simp
        _ ≤ L := by
          have : ‖V x‖ ≤ ‖V xM‖ := hmaxV hx
          simpa [L] using this
    · have hxout : 4 ≤ ‖x - z₀‖ := by linarith
      have hψ0x : ψ x = 0 := hψ0 x hxout
      rw [hψ0x]
      simp [hL0]
  -- K bound: sup of ‖fderiv F‖ on closedBall z₀ 4, and zero outside
  have hfnrm : ContinuousOn (fun x : X => ‖fderiv ℝ F x‖) (closedBall z₀ 4) :=
    hfdCont.norm.continuousOn
  rcases hB4.exists_isMaxOn hB4ne hfnrm with ⟨xK, hxK, hmaxFd⟩
  let K : ℝ := ‖fderiv ℝ F xK‖
  have hK0 : 0 ≤ K := by dsimp [K]; exact norm_nonneg _
  have hfd0 (x : X) (hx : x ∉ closedBall z₀ 4) : fderiv ℝ F x = 0 := by
    have hxout : 4 < ‖x - z₀‖ := by
      have hle : ¬ ‖x - z₀‖ ≤ 4 := by
        intro h
        exact hx ((mem4_iff x).mpr h)
      linarith
    let r0 : ℝ := (‖x - z₀‖ - 4) / 2
    have hr0 : 0 < r0 := by dsimp [r0]; positivity
    have hF0ev : F =ᶠ[𝓝 x] (fun _ : X => (0 : X)) := by
      refine Filter.mem_of_superset (Metric.ball_mem_nhds x hr0) ?_
      intro y hy
      have hxy : ‖y - x‖ < r0 := by
        have hd : dist y x < r0 := mem_ball.mp hy
        rw [dist_eq_norm] at hd
        exact hd
      have hxy' : ‖x - y‖ ≤ r0 := by
        have : ‖x - y‖ = ‖y - x‖ := by rw [norm_sub_rev]
        rw [this]
        exact le_of_lt hxy
      have htri : ‖x - z₀‖ ≤ ‖x - y‖ + ‖y - z₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub x y z₀
      have hmid : 4 < ‖x - z₀‖ - r0 := by
        dsimp [r0]
        nlinarith [hxout]
      have hyz : 4 ≤ ‖y - z₀‖ := by
        nlinarith [htri, hxy', hmid]
      have hypsi : ψ y = 0 := hψ0 y hyz
      dsimp [F]
      rw [hypsi]
      simp
    have hder0 : HasFDerivAt F (0 : X →L[ℝ] X) x := by
      exact (hasFDerivAt_const (0 : X) x).congr_of_eventuallyEq hF0ev
    exact (hFdiff.differentiableAt).hasFDerivAt.unique hder0
  have hKbnd (x : X) : ‖fderiv ℝ F x‖ ≤ K := by
    by_cases hx : x ∈ closedBall z₀ 4
    · have : ‖fderiv ℝ F x‖ ≤ ‖fderiv ℝ F xK‖ := hmaxFd hx
      simpa [K] using this
    · have hz : fderiv ℝ F x = 0 := hfd0 x hx
      rw [hz]
      simpa using hK0
  have hKlip (x y : X) : ‖F y - F x‖ ≤ K * ‖y - x‖ := by
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := F) (s := Set.univ)
      (fun q _ => hFdiff.differentiableAt) (fun q _ => hKbnd q) convex_univ trivial trivial
  -- agree with V on radius 3
  have hagree (x : X) (hx : x ∈ closedBall z₀ 3) : F x = V x := by
    have hp : ψ x = 1 := hψ1 x hx
    simp [F, V, hp]
  refine ⟨F, L, K, hL0, hK0, ?_, ?_, ?_, ?_, ?_⟩
  · exact hF1
  · intro x
    exact hLb x
  · intro x y
    exact hKlip x y
  · intro x hx
    exact hagree x hx
  · intro x hx
    have hp : ψ x = 0 := hψ0 x hx
    dsimp [F]
    rw [hp]
    simp




/-- A local geodesic flow valid on the closed data ball `closedBall z₀ 2`, on a symmetric time
interval `Icc (-T) T`, together with uniform Lipschitz-in-time and uniform first-order Taylor
estimates. -/
lemma geodesic_flow (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) :
    ∃ T > 0, ∃ C : ℝ, 0 ≤ C ∧ ∃ Φ : (E × E) → ℝ → (E × E),
      (∀ z ∈ closedBall z₀ 2, Φ z 0 = z ∧
         ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      (∀ z ∈ closedBall z₀ 2, ∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T,
        ‖Φ z s - Φ z t‖ ≤ C * |s - t|) ∧
      (∀ z ∈ closedBall z₀ 2, ∀ t ∈ Icc (-T) T,
        ‖Φ z t - z - t • odeField g z‖ ≤ C * t ^ 2) := by
  let X := E × E
  let V : X → X := odeField g
  have norm_of_mem (a : X) (r : ℝ) (x : X) (hx : x ∈ closedBall a r) : ‖x - a‖ ≤ r := by
    rw [← dist_eq_norm]
    exact mem_closedBall.mp hx
  have mem_of_norm (a : X) (r : ℝ) (x : X) (hx : ‖x - a‖ ≤ r) : x ∈ closedBall a r := by
    exact mem_closedBall.mpr (by simpa [dist_eq_norm] using hx)
  rcases smooth_truncation g hg hinv z₀ with ⟨F, L, K, hL0, hK0, hF1, hFbnd, hFlip, hFagree, hF0⟩
  let Ln : NNReal := ⟨L, hL0⟩
  let Kn : NNReal := ⟨K, hK0⟩
  have hKn : (Kn : ℝ) = K := rfl
  have hLn : (Ln : ℝ) = L := rfl
  have hLipB : LipschitzOnWith Kn F (closedBall z₀ 3) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [hKn]
    have h := hFlip x y
    simpa [dist_eq_norm, norm_sub_rev] using h
  let τ : ℝ := 1 / (2 * (L + 1))
  have hτpos : 0 < τ := by positivity
  have hle1 : L * τ ≤ 1 := by
    dsimp [τ]
    have hpos : 0 < 2 * (L + 1) := by positivity
    calc
      L * (1 / (2 * (L + 1))) = L / (2 * (L + 1)) := by ring
      _ ≤ 1 := by
        rw [div_le_iff₀ hpos]
        nlinarith [hL0]
  have hmem0 : (0 : ℝ) ∈ Icc (-τ) τ := by constructor <;> linarith
  have hpl : IsPicardLindelof (fun _ => F) (tmin := -τ) (tmax := τ) ⟨0, hmem0⟩ z₀
      (3 : NNReal) 2 Ln Kn := by
    refine IsPicardLindelof.mk ?lipschitzOnWith ?continuousOn ?norm_le ?mul_max_le
    · intro t ht
      exact hLipB
    · intro x hx
      exact continuousOn_const
    · intro t ht x hx
      exact hFbnd x
    · rw [hLn]
      norm_num
      exact hle1
  rcases hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith with
    ⟨α, hα, L', hLip⟩
  let T : ℝ := τ / 2
  have hT : 0 < T := by dsimp [T]; linarith
  have hTlt : T < τ := by dsimp [T]; linarith
  have h0T : (0 : ℝ) ∈ Icc (-T) T := by constructor <;> linarith
  let Φ : X → ℝ → X := α
  have hz0 (z : X) (hz : z ∈ closedBall z₀ 2) : Φ z 0 = z := by
    simpa [Φ] using (hα z hz).1
  have hΦF (z : X) (hz : z ∈ closedBall z₀ 2) (t : ℝ) (ht : t ∈ Icc (-T) T) :
      HasDerivAt (Φ z) (F (Φ z t)) t := by
    have htlo : -τ < t := lt_of_lt_of_le (neg_lt_neg hTlt) ht.1
    have hthi : t < τ := lt_of_le_of_lt ht.2 hTlt
    have htIcc : t ∈ Icc (-τ) τ := by constructor <;> linarith
    have hder : HasDerivWithinAt (α z) (F (α z t)) (Icc (-τ) τ) t := (hα z hz).2 t htIcc
    simpa [Φ] using hder.hasDerivAt (Icc_mem_nhds htlo hthi)
  have hDisp (z : X) (hz : z ∈ closedBall z₀ 2) (s t : ℝ)
      (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) : ‖Φ z s - Φ z t‖ ≤ L * |s - t| := by
    by_cases hle : s ≤ t
    · have hseg (u : ℝ) (hu : u ∈ Icc s t) : HasDerivAt (Φ z) (F (Φ z u)) u := by
        exact hΦF z hz u ⟨le_trans hs.1 hu.1, le_trans hu.2 ht.2⟩
      have hf' : ∀ u ∈ Icc s t,
          HasDerivWithinAt (fun u : ℝ => Φ z u) (F (Φ z u)) (Icc s t) u := by
        intro u hu
        exact (hseg u hu).hasDerivWithinAt
      have hb' : ∀ u ∈ Ico s t, ‖F (Φ z u)‖ ≤ L := by
        intro u hu
        exact hFbnd (Φ z u)
      have hmain : ‖Φ z t - Φ z s‖ ≤ L * (t - s) :=
        norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ => Φ z u)
          (f' := fun u => F (Φ z u)) hf' hb' t (right_mem_Icc.mpr hle)
      have habs : |s - t| = t - s := by
        rw [abs_of_nonpos (by linarith : s - t ≤ 0)]
        ring
      have hnorm : ‖Φ z s - Φ z t‖ ≤ L * (t - s) := by
        simpa [norm_sub_rev] using hmain
      simpa [habs] using hnorm
    · have hgt : t < s := lt_of_not_ge hle
      have hseg (u : ℝ) (hu : u ∈ Icc t s) : HasDerivAt (Φ z) (F (Φ z u)) u := by
        exact hΦF z hz u ⟨le_trans ht.1 hu.1, le_trans hu.2 hs.2⟩
      have hf' : ∀ u ∈ Icc t s,
          HasDerivWithinAt (fun u : ℝ => Φ z u) (F (Φ z u)) (Icc t s) u := by
        intro u hu
        exact (hseg u hu).hasDerivWithinAt
      have hb' : ∀ u ∈ Ico t s, ‖F (Φ z u)‖ ≤ L := by
        intro u hu
        exact hFbnd (Φ z u)
      have hmain : ‖Φ z s - Φ z t‖ ≤ L * (s - t) :=
        norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ => Φ z u)
          (f' := fun u => F (Φ z u)) hf' hb' s (right_mem_Icc.mpr (le_of_lt hgt))
      have habs : |s - t| = s - t := by
        rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
      simpa [habs] using hmain
  -- trajectory containment inside the radius-3 ball on the time window
  have hCont (z : X) (hz : z ∈ closedBall z₀ 2) (t : ℝ) (ht : t ∈ Icc (-T) T) :
      ‖Φ z t - z₀‖ ≤ 3 := by
    have hz2 : ‖z - z₀‖ ≤ 2 := norm_of_mem z₀ 2 z hz
    have hd : ‖Φ z t - z‖ ≤ L * |t| := by
      simpa [hz0 z hz] using hDisp z hz t 0 ht h0T
    have htle : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmain : L * T ≤ 1 := by
      calc
        L * T = L * (τ / 2) := by rfl
        _ ≤ L * τ := by
          exact mul_le_mul_of_nonneg_left (by linarith : τ / 2 ≤ τ) hL0
        _ ≤ 1 := hle1
    have hb : L * |t| ≤ 1 := by
      calc
        L * |t| ≤ L * T := mul_le_mul_of_nonneg_left htle hL0
        _ ≤ 1 := hmain
    have htri : ‖Φ z t - z₀‖ ≤ ‖Φ z t - z‖ + ‖z - z₀‖ := by
      simpa [norm_sub_rev] using (norm_sub_le_norm_sub_add_norm_sub (Φ z t) z z₀)
    nlinarith
  -- hence Φ z is a geodesic of the original vector field on the window
  have hΦ (z : X) (hz : z ∈ closedBall z₀ 2) (t : ℝ) (ht : t ∈ Icc (-T) T) :
      HasDerivAt (Φ z) (V (Φ z t)) t := by
    have hder := hΦF z hz t ht
    have hmem3 : Φ z t ∈ closedBall z₀ 3 := mem_of_norm z₀ 3 (Φ z t) (hCont z hz t ht)
    have hag : F (Φ z t) = V (Φ z t) := hFagree (Φ z t) hmem3
    simpa [V] using hder.congr_deriv hag
  let C : ℝ := K * L + L
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hTaylor (z : X) (hz : z ∈ closedBall z₀ 2) (t : ℝ) (ht : t ∈ Icc (-T) T) :
      ‖Φ z t - z - t • V z‖ ≤ (K * L) * t ^ 2 := by
    have hz3 : z ∈ closedBall z₀ 3 := mem_of_norm z₀ 3 z (by
      have hz2 : ‖z - z₀‖ ≤ 2 := norm_of_mem z₀ 2 z hz
      nlinarith)
    have hFz : F z = V z := hFagree z hz3
    have he (u : ℝ) (hu : u ∈ Icc (-T) T) :
        HasDerivAt (fun s : ℝ => Φ z s - z - s • (F z)) (F (Φ z u) - F z) u := by
      have h1 := hΦF z hz u hu
      have hlin : HasDerivAt (fun s : ℝ => s • (F z)) (F z) u := by
        have hlin0 := (hasDerivAt_id u).smul_const (F z)
        simpa using hlin0
      have hcz : HasDerivAt (fun _ : ℝ => z) (0 : X) u := by
        apply hasDerivAt_const
      have hd : HasDerivAt (fun s : ℝ => Φ z s - z - s • (F z)) (F (Φ z u) - 0 - F z) u :=
        ((h1.sub hcz).sub hlin)
      simpa using hd.congr_deriv (by simp)
    by_cases ht0 : 0 ≤ t
    · have hmemT (u : ℝ) (hu0 : 0 ≤ u) (hut : u ≤ t) : u ∈ Icc (-T) T := by
        constructor
        · exact le_trans (by linarith : -T ≤ 0) hu0
        · exact le_trans hut ht.2
      have hbnd (u : ℝ) (hu : u ∈ Ico 0 t) : ‖F (Φ z u) - F z‖ ≤ (K * L) * u := by
        have hu0 : 0 ≤ u := hu.1
        have huI : u ∈ Icc (-T) T := hmemT u hu.1 (le_of_lt hu.2)
        have hd : ‖Φ z u - z‖ ≤ L * u := by
          simpa [hz0 z hz, abs_of_nonneg hu0] using hDisp z hz u 0 huI h0T
        calc
          ‖F (Φ z u) - F z‖ ≤ K * ‖Φ z u - z‖ := hFlip z (Φ z u)
          _ ≤ K * (L * u) := mul_le_mul_of_nonneg_left hd hK0
          _ = (K * L) * u := by ring
      have hf' : ∀ u ∈ Icc 0 t,
          HasDerivWithinAt (fun s : ℝ => Φ z s - z - s • (F z)) (F (Φ z u) - F z) (Icc 0 t) u := by
        intro u hu
        exact (he u (hmemT u hu.1 hu.2)).hasDerivWithinAt
      have hb' : ∀ u ∈ Ico 0 t, ‖F (Φ z u) - F z‖ ≤ (K * L) * t := by
        intro u hu
        have hut : u ≤ t := le_of_lt hu.2
        calc
          ‖F (Φ z u) - F z‖ ≤ (K * L) * u := hbnd u hu
          _ ≤ (K * L) * t := mul_le_mul_of_nonneg_left hut (by positivity)
      have hmain : ‖(Φ z t - z - t • (F z)) - (Φ z 0 - z - 0 • (F z))‖ ≤ ((K * L) * t) * t := by
        simpa using (norm_image_sub_le_of_norm_deriv_le_segment'
          (f := fun s : ℝ => Φ z s - z - s • (F z)) (f' := fun u => F (Φ z u) - F z)
          hf' hb' t (right_mem_Icc.mpr ht0))
      have hm : ‖Φ z t - z - t • (F z)‖ ≤ (K * L) * t ^ 2 := by
        have hconv : ((K * L) * t) * t = (K * L) * t ^ 2 := by ring
        rw [← hconv]
        simpa [hz0 z hz] using hmain
      rw [← hFz]
      exact hm
    · have ht0' : t ≤ 0 := le_of_not_ge ht0
      have hmemT (u : ℝ) (hut : t ≤ u) (hu0 : u ≤ 0) : u ∈ Icc (-T) T := by
        constructor
        · exact le_trans ht.1 hut
        · exact le_trans hu0 (by linarith : 0 ≤ T)
      let At : ℝ := |t|
      have hbnd (u : ℝ) (hu : u ∈ Ico t 0) : ‖F (Φ z u) - F z‖ ≤ (K * L) * At := by
        have huI : u ∈ Icc (-T) T := hmemT u hu.1 (le_of_lt hu.2)
        have hd : ‖Φ z u - z‖ ≤ L * |u| := by
          simpa [hz0 z hz] using hDisp z hz u 0 huI h0T
        have habsu : |u| ≤ At := by
          dsimp [At]
          have hu_neg : |u| = -u := abs_of_nonpos (le_of_lt hu.2)
          have ht_neg : |t| = -t := abs_of_nonpos ht0'
          rw [hu_neg, ht_neg]
          linarith [hu.1]
        calc
          ‖F (Φ z u) - F z‖ ≤ K * ‖Φ z u - z‖ := hFlip z (Φ z u)
          _ ≤ K * (L * |u|) := mul_le_mul_of_nonneg_left hd hK0
          _ = (K * L) * |u| := by ring
          _ ≤ (K * L) * At := mul_le_mul_of_nonneg_left habsu (by positivity)
      have hf' : ∀ u ∈ Icc t 0,
          HasDerivWithinAt (fun s : ℝ => Φ z s - z - s • (F z)) (F (Φ z u) - F z) (Icc t 0) u := by
        intro u hu
        exact (he u (hmemT u hu.1 hu.2)).hasDerivWithinAt
      have hmain : ‖(Φ z 0 - z - 0 • (F z)) - (Φ z t - z - t • (F z))‖ ≤
          ((K * L) * At) * (0 - t) := by
        simpa using (norm_image_sub_le_of_norm_deriv_le_segment'
          (f := fun s : ℝ => Φ z s - z - s • (F z)) (f' := fun u => F (Φ z u) - F z)
          hf' hbnd (0 : ℝ) (right_mem_Icc.mpr ht0'))
      have hmain0 : ‖0 - (Φ z t - z - t • (F z))‖ ≤ ((K * L) * At) * (0 - t) := by
        have h1 : ‖(Φ z 0 - z - 0 • (F z)) - (Φ z t - z - t • (F z))‖ =
            ‖0 - (Φ z t - z - t • (F z))‖ := by
          have hz00 : Φ z 0 = z := hz0 z hz
          simp [hz00]
        rw [← h1]
        exact hmain
      have hAt : ((K * L) * At) * (0 - t) = (K * L) * t ^ 2 := by
        dsimp [At]
        rw [abs_of_nonpos ht0']
        ring
      have hm : ‖Φ z t - z - t • (F z)‖ ≤ (K * L) * t ^ 2 := by
        have hneg : -(Φ z t - z - t • (F z)) = 0 - (Φ z t - z - t • (F z)) := by simp
        calc
          ‖Φ z t - z - t • (F z)‖ = ‖-(Φ z t - z - t • (F z))‖ := (norm_neg _).symm
          _ = ‖0 - (Φ z t - z - t • (F z))‖ := by rw [hneg]
          _ ≤ ((K * L) * At) * (0 - t) := hmain0
          _ = (K * L) * t ^ 2 := hAt
      rw [← hFz]
      exact hm
  refine ⟨T, hT, C, hC0, Φ, ?_, ?_, ?_⟩
  · intro z hz
    constructor
    · exact hz0 z hz
    · intro t ht
      exact hΦ z hz t ht
  · intro z hz s hs t ht
    have h1 : ‖Φ z s - Φ z t‖ ≤ L * |s - t| := hDisp z hz s t hs ht
    have h2 : L * |s - t| ≤ C * |s - t| := by
      dsimp [C]
      have hnn : 0 ≤ |s - t| := abs_nonneg _
      have hLle : L ≤ K * L + L := by nlinarith
      exact mul_le_mul_of_nonneg_right hLle hnn
    exact le_trans h1 h2
  · intro z hz t ht
    have h1 := hTaylor z hz t ht
    have h2 : (K * L) * t ^ 2 ≤ C * t ^ 2 := by
      dsimp [C]
      have hnn : 0 ≤ t ^ 2 := sq_nonneg t
      have hKLle : K * L ≤ K * L + L := by nlinarith
      exact mul_le_mul_of_nonneg_right hKLle hnn
    exact le_trans h1 h2



/-- Membership of a pair with fixed position in the flow's data ball: `(x₀, u)` lies in
`closedBall (x₀, 0) r` whenever `‖u‖ ≤ r`. -/
lemma mem_pair_ball (x₀ : E) (r : ℝ) (hr : 0 ≤ r) (u : E) (hu : ‖u‖ ≤ r) :
    (x₀, u) ∈ closedBall (x₀, 0) r := by
  rw [← closedBall_prod_same]
  constructor
  · exact mem_closedBall.mpr (by simpa using hr)
  · have hdist : dist u 0 ≤ r := by
      simpa [dist_eq_norm] using hu
    exact mem_closedBall.mpr hdist

/-- A pair-flow solution splits into position and velocity geodesic equations. -/
lemma flow_geodesic_pair (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {T : ℝ} (hT : 0 < T)
    (Φ : (E × E) → ℝ → (E × E))
    (hΦ : ∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
       ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    {z : E × E} (hz : z ∈ closedBall (x₀, 0) 2) :
    ((Φ z 0).1 = z.1 ∧ (Φ z 0).2 = z.2) ∧
    (∀ t ∈ Ioo (-T) T, HasDerivAt (fun s => (Φ z s).1) ((Φ z t).2) t) ∧
    (∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun s => (Φ z s).2)
        (accel (g ((Φ z t).1)) (fderiv ℝ g ((Φ z t).1)) ((Φ z t).2)) t) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rw [(hΦ z hz).1]
    · rw [(hΦ z hz).1]
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

/-- Running the geodesic backwards: the flow from `(x₀, -w)` at time `t` is the flow from
`(x₀, w)` at time `-t`. -/
lemma flow_reversal (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {T : ℝ} (hT : 0 < T)
    (Φ : (E × E) → ℝ → (E × E))
    (hΦ : ∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
       ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    (w : E) (hw : ‖w‖ ≤ 2) :
    ∀ t ∈ Ioo (-T) T, (Φ (x₀, -w) t).1 = (Φ (x₀, w) (-t)).1 := by
  let z1 : E × E := (x₀, w)
  let z2 : E × E := (x₀, -w)
  have hz1 : z1 ∈ closedBall (x₀, 0) 2 := by
    dsimp [z1]
    exact mem_pair_ball x₀ 2 (by norm_num) w hw
  have hz2 : z2 ∈ closedBall (x₀, 0) 2 := by
    dsimp [z2]
    have h : ‖-w‖ ≤ 2 := by simpa using hw
    exact mem_pair_ball x₀ 2 (by norm_num) (-w) h
  have hpair1 := flow_geodesic_pair g hg hinv x₀ hT Φ hΦ hz1
  have hpair2 := flow_geodesic_pair g hg hinv x₀ hT Φ hΦ hz2
  have hfs := flow_scaling (g := g) (hg := hg) (hinv := hinv) (ε₁ := T) (ε₂ := T)
    (hε₁ := hT) (hε₂ := hT)
    (c₁ := fun t : ℝ => (Φ z1 t).1) (vel₁ := fun t : ℝ => (Φ z1 t).2)
    (c₂ := fun t : ℝ => (Φ z2 t).1) (vel₂ := fun t : ℝ => (Φ z2 t).2)
    (x := x₀) (v := w) (s := -1) (by norm_num : (-1 : ℝ) ≠ 0)
    (hc₁ := by simpa [z1] using hpair1.1.1)
    (hv₁ := by simpa [z1] using hpair1.1.2)
    (hc₁d := by simpa [z1] using hpair1.2.1)
    (hv₁d := by simpa [z1] using hpair1.2.2)
    (hc₂ := by simpa [z2] using hpair2.1.1)
    (hv₂ := by
      simpa [z2, neg_one_smul] using hpair2.1.2)
    (hc₂d := by simpa [z2] using hpair2.2.1)
    (hv₂d := by simpa [z2] using hpair2.2.2)
  intro t ht
  have ht' : t ∈ Ioo (-min T (T / |(-1 : ℝ)|)) (min T (T / |(-1 : ℝ)|)) := by
    simpa using ht
  have hconcl := hfs t ht'
  simpa [z1, z2] using hconcl.1



-- scalar/vector algebra helpers --------------------------------------------------------------

lemma norm_smul_unit (v : E) (hv : v ≠ 0) : ‖(1 / ‖v‖) • v‖ = 1 := by
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [norm_smul]
  have hpos : 0 < 1 / ‖v‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  field_simp [ne_of_gt hv0]

lemma norm_smul_unit_id (v : E) (hv : v ≠ 0) : ‖v‖ • ((1 / ‖v‖) • v) = v := by
  rw [smul_smul]
  have hne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have h : ‖v‖ * (1 / ‖v‖) = 1 := by field_simp [hne]
  rw [h, one_smul]

lemma ray_norm_pos {t : ℝ} (ht : 0 < t) (w : E) (hw : ‖w‖ = 1) : ‖t • w‖ = t := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht)]
  rw [hw]
  ring

lemma ray_norm_neg {t : ℝ} (ht : t < 0) (w : E) (hw : ‖w‖ = 1) : ‖t • w‖ = -t := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (le_of_lt ht)]
  rw [hw]
  ring

lemma ray_unit_pos {t : ℝ} (ht : 0 < t) (w : E) (hw : ‖w‖ = 1) :
    (1 / ‖t • w‖) • (t • w) = w := by
  have hnorm : ‖t • w‖ = t := ray_norm_pos ht w hw
  rw [hnorm]
  rw [smul_smul]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have h : (1 / t) * t = 1 := by field_simp [ht0]
  rw [h, one_smul]

lemma ray_unit_neg {t : ℝ} (ht : t < 0) (w : E) (hw : ‖w‖ = 1) :
    (1 / ‖t • w‖) • (t • w) = -w := by
  have hnorm : ‖t • w‖ = -t := ray_norm_neg ht w hw
  rw [hnorm]
  rw [smul_smul]
  have ht0 : t ≠ 0 := ne_of_lt ht
  have h : (1 / -t) * t = -1 := by
    field_simp [ht0]
  rw [h]
  simp

/-- A nonzero multiple of a unit vector is nonzero. -/
lemma smul_ne_zero_of_pos {t : ℝ} (ht : t ≠ 0) (w : E) (hw : w ≠ 0) : t • w ≠ 0 := by
  exact smul_ne_zero ht hw


/-- The exponential map at a base point is defined near zero, equals the geodesic flow on unit
rays, and has derivative the identity at zero. -/
theorem exp_deriv_identity (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) :
    ∃ ρ > 0, ∃ (exp : E → E) (Φ : E × E → ℝ → E × E),
      (∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
         ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      exp 0 = x₀ ∧
      (∀ w : E, ‖w‖ = 1 → ∀ t ∈ Ioo (-ρ) ρ, exp (t • w) = (Φ (x₀, w) t).1) ∧
      HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 := by
  classical
  rcases geodesic_flow g hg hinv (x₀, 0) with ⟨T, hT, C, hC0, Φ, hΦ, hDisp, hTaylor⟩
  let ρ : ℝ := T
  have hρ : 0 < ρ := hT
  let exp : E → E := fun v => if v = 0 then x₀ else (Φ (x₀, (1 / ‖v‖) • v) ‖v‖).1
  have hB : exp 0 = x₀ := by
    simp [exp]
  have hbd (v : E) (hv : v ≠ 0) (hvt : ‖v‖ < T) :
      ‖exp v - x₀ - v‖ ≤ C * ‖v‖ * ‖v‖ := by
    let u : E := (1 / ‖v‖) • v
    have hun : ‖u‖ = 1 := by
      simpa [u] using norm_smul_unit v hv
    have hmemu : (x₀, u) ∈ closedBall (x₀, 0) 2 := by
      exact mem_pair_ball x₀ 2 (by norm_num) u (by rw [hun]; norm_num)
    have htIn : ‖v‖ ∈ Icc (-T) T := by
      constructor
      · exact le_trans (by linarith) (norm_nonneg v)
      · exact le_of_lt hvt
    have htay := hTaylor (x₀, u) hmemu ‖v‖ htIn
    have hV1 : (odeField g (x₀, u)).1 = u := by
      simp [odeField]
    have hproj : ‖(Φ (x₀, u) ‖v‖).1 - x₀ - ‖v‖ • u‖ ≤ C * (‖v‖ ^ 2) := by
      have hfstle : ‖((Φ (x₀, u) ‖v‖ - (x₀, u) - ‖v‖ • odeField g (x₀, u)).1)‖ ≤
          ‖Φ (x₀, u) ‖v‖ - (x₀, u) - ‖v‖ • odeField g (x₀, u)‖ := by
        exact norm_fst_le _
      have heq : (Φ (x₀, u) ‖v‖ - (x₀, u) - ‖v‖ • odeField g (x₀, u)).1 =
          (Φ (x₀, u) ‖v‖).1 - x₀ - ‖v‖ • u := by
        simp [hV1]
      exact le_trans (by simpa [heq] using hfstle) htay
    have hvid : ‖v‖ • u = v := by
      simpa [u] using norm_smul_unit_id v hv
    have heval : exp v = (Φ (x₀, u) ‖v‖).1 := by
      change (if v = 0 then x₀ else (Φ (x₀, (1 / ‖v‖) • v) ‖v‖).1) = (Φ (x₀, u) ‖v‖).1
      rw [if_neg hv]
    have hproj' : ‖(Φ (x₀, u) ‖v‖).1 - x₀ - v‖ ≤ C * (‖v‖ ^ 2) := by
      rw [hvid] at hproj
      exact hproj
    calc
      ‖exp v - x₀ - v‖ = ‖(Φ (x₀, u) ‖v‖).1 - x₀ - v‖ := by rw [heval]
      _ ≤ C * (‖v‖ ^ 2) := hproj'
      _ = C * ‖v‖ * ‖v‖ := by
        rw [pow_two]
        ring
  have hLittle : (fun h : E => exp h - x₀ - h) =o[𝓝 (0 : E)] (fun h : E => h) := by
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    let δ : ℝ := min T (c / (C + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min hT (by positivity)
    filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hmem
    have hlt : ‖h‖ < δ := by
      simpa [Real.dist_eq] using (mem_ball.mp hmem)
    have hltT : ‖h‖ < T := lt_of_lt_of_le hlt (min_le_left T (c / (C + 1)))
    have hltc : ‖h‖ ≤ c / (C + 1) :=
      le_of_lt (lt_of_lt_of_le hlt (min_le_right T (c / (C + 1))))
    by_cases h0 : h = 0
    · subst h
      simp [exp]
    · have hbdh := hbd h h0 hltT
      have hposC : 0 < C + 1 := by positivity
      have h2 : C * (c / (C + 1)) ≤ c := by
        field_simp [ne_of_gt hposC]
        nlinarith [hc, hC0]
      have hCbd : C * ‖h‖ ≤ c :=
        le_trans (mul_le_mul_of_nonneg_left hltc hC0) h2
      have hmain : C * ‖h‖ * ‖h‖ ≤ c * ‖h‖ := by
        exact mul_le_mul_of_nonneg_right hCbd (norm_nonneg h)
      calc
        ‖exp h - x₀ - h‖ ≤ C * ‖h‖ * ‖h‖ := hbdh
        _ ≤ c * ‖h‖ := hmain
  refine ⟨ρ, hρ, exp, Φ, ?_, ?_, ?_, ?_⟩
  · intro z hz
    constructor
    · exact (hΦ z hz).1
    · intro t ht
      have ht' : t ∈ Icc (-T) T := by
        constructor <;> linarith [ht.1, ht.2, hρ]
      exact (hΦ z hz).2 t ht'
  · exact hB
  · intro w hw t ht
    have hw0 : w ≠ 0 := by
      intro h
      rw [h] at hw
      norm_num at hw
    have hwle : ‖w‖ ≤ 2 := by
      rw [hw]
      norm_num
    have hmemw : (x₀, w) ∈ closedBall (x₀, 0) 2 := mem_pair_ball x₀ 2 (by norm_num) w hwle
    have hmemw' : (x₀, -w) ∈ closedBall (x₀, 0) 2 := by
      have h : ‖-w‖ ≤ 2 := by simpa using hwle
      exact mem_pair_ball x₀ 2 (by norm_num) (-w) h
    rcases (lt_trichotomy t 0) with htneg | ht0 | htpos
    · have htw : t • w ≠ 0 := smul_ne_zero (ne_of_lt htneg) hw0
      have hrev := flow_reversal g hg hinv x₀ hT Φ hΦ w hwle
      have h1 : exp (t • w) = (Φ (x₀, -w) (-t)).1 := by
        change (if t • w = 0 then x₀ else (Φ (x₀, (1 / ‖t • w‖) • (t • w)) ‖t • w‖).1) =
          (Φ (x₀, -w) (-t)).1
        rw [if_neg htw]
        rw [ray_unit_neg htneg w hw]
        rw [ray_norm_neg htneg w hw]
      have h2 : (Φ (x₀, -w) (-t)).1 = (Φ (x₀, w) t).1 := by
        have hmemneg : -t ∈ Ioo (-T) T := by
          constructor <;> linarith [ht.1, ht.2]
        simpa using (hrev (-t) hmemneg)
      exact h1.trans h2
    · subst t
      simp [exp, (hΦ (x₀, w) hmemw).1]
    · have htw : t • w ≠ 0 := smul_ne_zero (ne_of_gt htpos) hw0
      change (if t • w = 0 then x₀ else (Φ (x₀, (1 / ‖t • w‖) • (t • w)) ‖t • w‖).1) =
        (Φ (x₀, w) t).1
      rw [if_neg htw]
      rw [ray_unit_pos htpos w hw]
      rw [ray_norm_pos htpos w hw]
  · rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    simpa [exp] using hLittle

