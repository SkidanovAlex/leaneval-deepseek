import Submission.ModelNormalBall
import Submission.ModelExpC1
import Submission.ModelPkg
import Mathlib

/-!
# Model-level two-sided minimality of short exponential arcs

This module builds the uniform-in-base machinery needed to prove that short geodesic
arcs through a point are length-minimizing among staying curves (model level).
-/

open ContinuousLinearMap
open scoped ContDiff Topology BigOperators
open Set Metric Filter
open MeasureTheory intervalIntegral
open ODE

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-- Smooth truncation of the geodesic field, agreeing with `odeField` on a ball of radius `a`
around `z₀` and vanishing far away (parameterized version of `smooth_truncation`). -/
lemma smooth_truncation_rad (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (a : ℝ) (ha : 0 < a) :
    ∃ F : (E × E) → (E × E), ∃ L K : ℝ, 0 ≤ L ∧ 0 ≤ K ∧
      ContDiff ℝ 1 F ∧
      (∀ x, ‖F x‖ ≤ L) ∧
      (∀ x y, ‖F y - F x‖ ≤ K * ‖y - x‖) ∧
      (∀ x ∈ closedBall z₀ a, F x = odeField g x) ∧
      (∀ x, a + 1 ≤ ‖x - z₀‖ → F x = 0) := by
  let X := E × E
  let V : X → X := odeField g
  have hV1 : ContDiff ℝ 1 V := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases p with ⟨x, v⟩
    simpa [V] using odeField_contDiffAt g hg hinv x v
  let φ : ContDiffBump z₀ := ⟨a, a + 1, ha, by linarith⟩
  let ψ : X → ℝ := (φ : X → ℝ)
  have hψ1 (x : X) (hx : x ∈ closedBall z₀ a) : ψ x = 1 := by
    simpa [ψ] using φ.one_of_mem_closedBall hx
  have hψ0 (x : X) (hx : a + 1 ≤ ‖x - z₀‖) : ψ x = 0 := by
    have hd : a + 1 ≤ dist x z₀ := by
      calc
        a + 1 ≤ ‖x - z₀‖ := hx
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
  have memR_iff (x : X) : x ∈ closedBall z₀ (a + 1) ↔ ‖x - z₀‖ ≤ a + 1 := by
    rw [mem_closedBall, dist_eq_norm]
  -- L bound: sup of ‖V‖ on the compact ball radius a+1
  have hBR : IsCompact (closedBall z₀ (a + 1)) := isCompact_closedBall z₀ (a + 1)
  have hBRne : (closedBall z₀ (a + 1)).Nonempty := by
    refine ⟨z₀, ?_⟩
    rw [mem_closedBall, dist_self]
    exact by positivity
  have hVcont : Continuous V := hV1.continuous
  have hVnrm : ContinuousOn (fun x : X => ‖V x‖) (closedBall z₀ (a + 1)) := hVcont.norm.continuousOn
  rcases hBR.exists_isMaxOn hBRne hVnrm with ⟨xM, hxM, hmaxV⟩
  let L : ℝ := ‖V xM‖
  have hL0 : 0 ≤ L := by dsimp [L]; exact norm_nonneg _
  have hLb (x : X) : ‖F x‖ ≤ L := by
    dsimp [F]
    by_cases hxin : ‖x - z₀‖ ≤ a + 1
    · have hx : x ∈ closedBall z₀ (a + 1) := (memR_iff x).mpr hxin
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
    · have hxout : a + 1 ≤ ‖x - z₀‖ := by linarith
      have hψ0x : ψ x = 0 := hψ0 x hxout
      rw [hψ0x]
      simp [hL0]
  -- K bound: sup of ‖fderiv F‖ on closedBall z₀ (a+1), zero outside
  have hfnrm : ContinuousOn (fun x : X => ‖fderiv ℝ F x‖) (closedBall z₀ (a + 1)) :=
    hfdCont.norm.continuousOn
  rcases hBR.exists_isMaxOn hBRne hfnrm with ⟨xK, hxK, hmaxFd⟩
  let K : ℝ := ‖fderiv ℝ F xK‖
  have hK0 : 0 ≤ K := by dsimp [K]; exact norm_nonneg _
  have hfd0 (x : X) (hx : x ∉ closedBall z₀ (a + 1)) : fderiv ℝ F x = 0 := by
    have hxout : a + 1 < ‖x - z₀‖ := by
      have hle : ¬ ‖x - z₀‖ ≤ a + 1 := by
        intro h
        exact hx ((memR_iff x).mpr h)
      linarith
    let r0 : ℝ := (‖x - z₀‖ - (a + 1)) / 2
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
      have hmid : a + 1 < ‖x - z₀‖ - r0 := by
        dsimp [r0]
        nlinarith [hxout]
      have hyz : a + 1 ≤ ‖y - z₀‖ := by
        nlinarith [htri, hxy', hmid]
      have hypsi : ψ y = 0 := hψ0 y hyz
      dsimp [F]
      rw [hypsi]
      simp
    have hder0 : HasFDerivAt F (0 : X →L[ℝ] X) x := by
      exact (hasFDerivAt_const (0 : X) x).congr_of_eventuallyEq hF0ev
    exact (hFdiff.differentiableAt).hasFDerivAt.unique hder0
  have hKbnd (x : X) : ‖fderiv ℝ F x‖ ≤ K := by
    by_cases hx : x ∈ closedBall z₀ (a + 1)
    · have : ‖fderiv ℝ F x‖ ≤ ‖fderiv ℝ F xK‖ := hmaxFd hx
      simpa [K] using this
    · have hz : fderiv ℝ F x = 0 := hfd0 x hx
      rw [hz]
      simpa using hK0
  have hKlip (x y : X) : ‖F y - F x‖ ≤ K * ‖y - x‖ := by
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := F) (s := Set.univ)
      (fun q _ => hFdiff.differentiableAt) (fun q _ => hKbnd q) convex_univ trivial trivial
  refine ⟨F, L, K, hL0, hK0, ?_, ?_, ?_, ?_, ?_⟩
  · exact hF1
  · intro x
    exact hLb x
  · intro x y
    exact hKlip x y
  · intro x hx
    have hp : ψ x = 1 := hψ1 x hx
    simp [F, V, hp]
  · intro x hx
    have hp : ψ x = 0 := hψ0 x hx
    dsimp [F]
    rw [hp]
    simp

/-- A flow of the geodesic field valid on the closed ball `closedBall z₀ R` of initial data,
uniform in time over `Icc (-T) T`, with data-Lipschitz regularity.  Parameterized version of
`ExpCore.flow_unit_ball_cont` (initial radius `R`, stay radius `R+1`). -/
lemma flow_ball_cont (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (R : NNReal) :
    ∃ T > 0, ∃ L : NNReal, ∃ Φ : (E × E) → ℝ → (E × E),
      (∀ z ∈ closedBall z₀ (R : ℝ), Φ z 0 = z ∧
         (∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
         (∀ t : ℝ, Φ z t ∈ closedBall z₀ ((R + 1) : ℝ))) ∧
      (∀ t ∈ Icc (-T) T, LipschitzOnWith L (fun z => Φ z t) (closedBall z₀ (R : ℝ))) := by
  classical
  let V : (E × E) → (E × E) := odeField g
  have hV1 : ContDiff ℝ 1 V := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases p with ⟨x, v⟩
    simpa [V] using odeField_contDiffAt g hg hinv x v
  have hfcont : Continuous (fderiv ℝ V) := hV1.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hVcont : Continuous V := hV1.continuous
  let S : Set (E × E) := closedBall z₀ ((R + 1 : NNReal) : ℝ)
  have hScomp : IsCompact S := by simpa [S] using (isCompact_closedBall z₀ (((R + 1 : NNReal) : ℝ)))
  have hSne : S.Nonempty := ⟨z₀, by
    simp [S]
    exact add_nonneg R.2 zero_le_one⟩
  have hnormOn : ContinuousOn (fun x => ‖fderiv ℝ V x‖) S := hfcont.norm.continuousOn
  rcases hScomp.exists_isMaxOn hSne hnormOn with ⟨xm, hxm, hmax⟩
  have hVnormOn : ContinuousOn (fun x => ‖V x‖) S := hVcont.norm.continuousOn
  rcases hScomp.exists_isMaxOn hSne hVnormOn with ⟨xL, hxL, hLmax⟩
  let K : NNReal := ⟨‖fderiv ℝ V xm‖, norm_nonneg _⟩
  let Lb : NNReal := ⟨‖V xL‖, norm_nonneg _⟩
  have hKbnd : ∀ x ∈ S, ‖fderiv ℝ V x‖ ≤ (K : ℝ) := by
    intro x hx
    calc
      ‖fderiv ℝ V x‖ ≤ ‖fderiv ℝ V xm‖ := hmax hx
      _ = (K : ℝ) := rfl
  have hLbnd : ∀ x ∈ S, ‖V x‖ ≤ (Lb : ℝ) := by
    intro x hx
    calc
      ‖V x‖ ≤ ‖V xL‖ := hLmax hx
      _ = (Lb : ℝ) := rfl
  have hKbd (x : E × E) (hx : x ∈ S) (y : E × E) (hy : y ∈ S) : ‖V y - V x‖ ≤ (K : ℝ) * ‖y - x‖ := by
    have hdiff : ∀ q ∈ S, DifferentiableAt ℝ V q := fun q _ =>
      (hV1.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
    have hsub := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := V) hdiff hKbnd
      (convex_closedBall z₀ (((R + 1 : NNReal) : ℝ))) hx hy
    simpa [V, S] using hsub
  have hKbdnn : LipschitzOnWith K V S := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have := hKbd x hx y hy
    simpa [dist_eq_norm, norm_sub_rev] using this
  let τ : ℝ := 1 / (2 * ((Lb : ℝ) + 1))
  have hτpos : 0 < τ := by positivity
  have hmem0 : (0 : ℝ) ∈ Icc (-τ) τ := by constructor <;> linarith
  let r1 : NNReal := R
  let r2 : NNReal := R + 1
  have hpl : IsPicardLindelof (fun _ => V) (tmin := -τ) (tmax := τ) ⟨0, hmem0⟩ z₀
      r2 r1 Lb K := by
    refine IsPicardLindelof.mk ?lipschitzOnWith ?continuousOn ?norm_le ?mul_max_le
    · intro t ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      have hb := hKbd x hx y hy
      simpa [V, dist_eq_norm, norm_sub_rev] using hb
    · intro x hx
      exact continuousOn_const
    · intro t ht x hx
      simpa using hLbnd x hx
    · dsimp
      rw [show max (τ - 0) (0 - -τ) = τ by simp]
      have hle : (Lb : ℝ) * τ ≤ 1 := by
        dsimp [τ]
        have hpos : 0 < 2 * ((Lb : ℝ) + 1) := by positivity
        calc
          (Lb : ℝ) * (1 / (2 * ((Lb : ℝ) + 1))) = (Lb : ℝ) / (2 * ((Lb : ℝ) + 1)) := by ring
          _ ≤ 1 := by
            rw [div_le_iff₀ hpos]
            nlinarith [Lb.2]
      change (Lb : ℝ) * τ ≤ ((R + 1 : NNReal) : ℝ) - (R : ℝ)
      norm_num
      exact hle
  have hex (x : E × E) (hx : x ∈ closedBall z₀ r1) :
      ∃ β : FunSpace (tmin := -τ) (tmax := τ) ⟨0, hmem0⟩ z₀ r1 Lb,
        Function.IsFixedPt (FunSpace.next hpl hx) β := by
    exact FunSpace.exists_isFixedPt_next hpl hx
  choose α hα using hex
  let Φ : (E × E) → ℝ → (E × E) := fun x t => if hx : x ∈ closedBall z₀ r1 then
    α x hx |>.compProj t else 0
  have hmemCurve (x : E × E) (hx : x ∈ closedBall z₀ r1) (t : ℝ) :
      (α x hx).compProj t ∈ closedBall z₀ r2 :=
    FunSpace.compProj_mem_closedBall (α x hx) hpl.mul_max_le
  obtain ⟨L', h⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hpl
  let T : ℝ := τ / 2
  have hTpos : 0 < T := by dsimp [T]; positivity
  refine ⟨T, hTpos, L', Φ, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ closedBall z₀ r1 := hz
    constructor
    · have hmain : (α z hz').compProj (0 : ℝ) = z := by
        rw [FunSpace.compProj_apply, projIcc_of_mem (hx := hmem0)]
        rw [← hα z hz', FunSpace.next_apply₀]
      calc
        Φ z 0 = (α z hz').compProj (0 : ℝ) := by
          dsimp only [Φ]
          rw [dif_pos hz']
        _ = z := hmain
    · constructor
      · intro t ht
        have h1 : -T ≤ t := (mem_Icc.mp ht).1
        have h2 : t ≤ T := (mem_Icc.mp ht).2
        have htlo : -τ < t := by dsimp [T] at *; linarith
        have hthi : t < τ := by dsimp [T] at *; linarith
        have htIcc : t ∈ Icc (-τ) τ := by constructor <;> linarith
        have hΦeq : (fun s : ℝ => Φ z s) = (α z hz').compProj := by
          funext s
          dsimp [Φ]
          rw [dif_pos hz']
        have hderα : HasDerivWithinAt ((α z hz').compProj) (V ((α z hz').compProj t))
              (Icc (-τ) τ) t := by
          apply hasDerivWithinAt_picard_Icc hmem0 hpl.continuousOn_uncurry
              (α z hz' |>.continuous_compProj.continuousOn)
              (fun _ ht' => (α z hz').compProj_mem_closedBall hpl.mul_max_le) z htIcc
              |>.congr_of_mem _ htIcc
          intro t' ht'
          nth_rw 1 [← hα z hz']
          rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
        have hderαAt : HasDerivAt ((α z hz').compProj) (V ((α z hz').compProj t)) t :=
          hderα.hasDerivAt (Icc_mem_nhds htlo hthi)
        have hfuneq : (fun s : ℝ => Φ z s) =ᶠ[𝓝 t] (α z hz').compProj := by
          filter_upwards with s
          exact congr_fun hΦeq s
        have hderΦ1 : HasDerivAt (fun s : ℝ => Φ z s) (V ((α z hz').compProj t)) t :=
          hderαAt.congr_of_eventuallyEq hfuneq
        have hval : V ((α z hz').compProj t) = V (Φ z t) := by
          congr 1
          exact (congr_fun hΦeq t).symm
        have hderAt : HasDerivAt (fun s : ℝ => Φ z s) (V (Φ z t)) t :=
          hderΦ1.congr_deriv hval
        have hder : HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
          simpa [V] using hderAt
        exact hder
      · intro t
        dsimp only [Φ]
        rw [dif_pos hz']
        have hmem : (α z hz').compProj t ∈ closedBall z₀ r2 := hmemCurve z hz' t
        simpa [r2] using hmem
  · -- per-time Lipschitz of the flow in the initial data
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hx' : x ∈ closedBall z₀ r1 := hx
    have hy' : y ∈ closedBall z₀ r1 := hy
    dsimp only [Φ]
    rw [dif_pos hx', dif_pos hy', FunSpace.compProj_apply, FunSpace.compProj_apply,
      ← FunSpace.toContinuousMap_apply_eq_apply, ← FunSpace.toContinuousMap_apply_eq_apply]
    have hnon : Nonempty (Icc (-τ) τ) := ⟨⟨0, hmem0⟩⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx' hy' (α x hx') (α y hy') (hα x hx') (hα y hy')




/-- Trajectories of a flow with field bounded by `M` stay within distance `M * |t|` of their
start, for small times. -/
lemma flow_displacement_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : X → X} {T : ℝ} (hT : 0 < T) {z : X} {Φ : ℝ → X} {M : ℝ} (hM0 : 0 ≤ M)
    (hder : ∀ t ∈ Ioo (-T) T, HasDerivAt Φ (V (Φ t)) t)
    (hbound : ∀ t ∈ Ico (0 : ℝ) T, ‖V (Φ t)‖ ≤ M) :
    ∀ t ∈ Ico (0 : ℝ) T, ‖Φ t - Φ 0‖ ≤ M * t := by
  intro t ht
  have hseg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : HasDerivAt Φ (V (Φ s)) s := by
    have hltT : -T < s := lt_of_lt_of_le (neg_neg_of_pos hT) hs.1
    exact hder s ⟨hltT, lt_of_le_of_lt hs.2 ht.2⟩
  have hb' : ∀ s ∈ Ico (0 : ℝ) t, ‖V (Φ s)‖ ≤ M := by
    intro s hs
    exact hbound s ⟨hs.1, lt_trans hs.2 ht.2⟩
  have hmain : ‖Φ t - Φ 0‖ ≤ M * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := Φ) (f' := fun s => V (Φ s))
      (fun s hs => (hseg s hs).hasDerivWithinAt) hb' t (by constructor <;> linarith [ht.1, ht.2])
  simpa using hmain



/-- Region flow with a short uniform window `[-Tc,Tc]`, clipped outside the window so that
per-base containment in `closedBall (b,0) 2` holds for *all* times, uniformly for bases
`b` in a ball around `x₀`. -/
lemma region_flow_pkg (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) (R0 : NNReal) (hR02 : (2 : ℝ) ≤ (R0 : ℝ)) :
    ∃ Tf > 0, ∃ ρu > 0, ∃ L : NNReal, ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall (x₀, 0) (R0 : ℝ), Φ z 0 = z ∧
         (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
         (∀ t : ℝ, Φ z t ∈ closedBall (x₀, 0) ((R0 : ℝ) + 1))) ∧
      (∀ z ∈ closedBall (x₀, 0) 1, ∀ t : ℝ, Φ z t ∈ closedBall (x₀, 0) 2) ∧
      (∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith L (fun z => Φ z t) (closedBall (x₀, 0) 1)) ∧
      (∀ t ∈ Icc (-Tf) Tf, ∀ b ∈ ball x₀ ρu,
         LipschitzOnWith L (fun z => Φ z t) (closedBall (b, 0) 1)) ∧
      (∀ b ∈ ball x₀ ρu, ∀ z ∈ closedBall (b, 0) 1,
        Φ z 0 = z ∧
        (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
        (∀ t : ℝ, Φ z t ∈ closedBall (b, 0) 2)) := by
  classical
  rcases flow_ball_cont g hg hinv (x₀, 0) R0 with ⟨Tf0, hTf0, Lf0, Ψ, hΨp, hLip⟩
  have hcon : ∀ z ∈ closedBall (x₀, 0) (R0 : ℝ), ∀ t : ℝ,
      Ψ z t ∈ closedBall (x₀, 0) ((R0 : ℝ) + 1) := by
    intro z hz t
    have hc := (hΨp z hz).2.2 t
    simpa using hc
  rcases field_value_bound g hg hinv (x₀, 0) ((R0 : ℝ) + 1) (by positivity) with ⟨M0, hM0, hMbd⟩
  let Tc : ℝ := min (Tf0 / 2) (1 / (2 * (M0 + 1)))
  have hTc : 0 < Tc := by
    dsimp [Tc]
    exact lt_min (half_pos hTf0) (by positivity)
  have hTcTf0 : Tc ≤ Tf0 / 2 := by dsimp [Tc]; exact min_le_left _ _
  have hM0Tc : M0 * Tc ≤ 1 / 2 := by
    have h2' : Tc ≤ 1 / (2 * (M0 + 1)) := by dsimp [Tc]; exact min_le_right _ _
    calc
      M0 * Tc ≤ M0 * (1 / (2 * (M0 + 1))) := mul_le_mul_of_nonneg_left h2' hM0
      _ = M0 / (2 * (M0 + 1)) := by ring
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity : 0 < 2 * (M0 + 1))]
        nlinarith [hM0]
  have hbndAll (z : E × E) (hz : z ∈ closedBall (x₀, 0) (R0 : ℝ)) (s : ℝ) :
      ‖odeField g (Ψ z s)‖ ≤ M0 := by
    exact hMbd (Ψ z s) (hcon z hz s)
  have hderv (z : E × E) (hz : z ∈ closedBall (x₀, 0) (R0 : ℝ)) (s : ℝ)
      (hs : s ∈ Icc (-Tf0) Tf0) : HasDerivAt (Ψ z) (odeField g (Ψ z s)) s := by
    exact (hΨp z hz).2.1 s hs
  have hdispl (z : E × E) (hz : z ∈ closedBall (x₀, 0) (R0 : ℝ))
      {t : ℝ} (ht : |t| ≤ Tc) : ‖Ψ z t - z‖ ≤ 1 / 2 := by
    have hz0 : Ψ z 0 = z := (hΨp z hz).1
    by_cases ht0 : 0 ≤ t
    · have htTf : t < Tf0 := by
        have : t ≤ Tc := by rwa [abs_of_nonneg ht0] at ht
        linarith
      have hseg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : HasDerivAt (Ψ z) (odeField g (Ψ z s)) s :=
        hderv z hz s ⟨by linarith [hs.1], by linarith [hs.2, htTf]⟩
      have hb' : ∀ s ∈ Ico (0 : ℝ) t, ‖odeField g (Ψ z s)‖ ≤ M0 := by
        intro s hs
        exact hbndAll z hz s
      have hmain : ‖Ψ z t - Ψ z 0‖ ≤ M0 * (t - 0) :=
        norm_image_sub_le_of_norm_deriv_le_segment' (f := Ψ z) (f' := fun s => odeField g (Ψ z s))
          (fun s hs => (hseg s hs).hasDerivWithinAt) hb' t (by constructor <;> linarith)
      have hle2 : M0 * t ≤ 1 / 2 := by
        have : t ≤ Tc := by rwa [abs_of_nonneg ht0] at ht
        calc M0 * t ≤ M0 * Tc := mul_le_mul_of_nonneg_left this hM0
          _ ≤ 1 / 2 := hM0Tc
      rw [abs_of_nonneg ht0] at ht
      rw [hz0] at hmain
      linarith
    · have hneg : t ≤ 0 := le_of_not_ge ht0
      have hntTf : -t < Tf0 := by
        have : -t ≤ Tc := by rwa [abs_of_nonpos hneg] at ht
        linarith
      have hseg (s : ℝ) (hs : s ∈ Icc t 0) : HasDerivAt (Ψ z) (odeField g (Ψ z s)) s :=
        hderv z hz s ⟨by linarith [hs.1, hntTf], by linarith [hs.2, hTf0]⟩
      have hb' : ∀ s ∈ Ico t 0, ‖odeField g (Ψ z s)‖ ≤ M0 := by
        intro s hs
        exact hbndAll z hz s
      have hmain : ‖Ψ z 0 - Ψ z t‖ ≤ M0 * (0 - t) :=
        norm_image_sub_le_of_norm_deriv_le_segment' (f := Ψ z) (f' := fun s => odeField g (Ψ z s))
          (fun s hs => (hseg s hs).hasDerivWithinAt) hb' 0 (right_mem_Icc.mpr hneg)
      have hle2 : M0 * (-t) ≤ 1 / 2 := by
        have : -t ≤ Tc := by rwa [abs_of_nonpos hneg] at ht
        calc M0 * (-t) ≤ M0 * Tc := mul_le_mul_of_nonneg_left this hM0
          _ ≤ 1 / 2 := hM0Tc
      have hmain' : ‖Ψ z t - z‖ ≤ M0 * (-t) := by
        simpa [hz0, norm_sub_rev] using hmain
      linarith
  let Φ : E × E → ℝ → E × E := fun z t => if h : |t| ≤ Tc then Ψ z t else z
  let Tf : ℝ := Tc / 2
  have hTf : 0 < Tf := by dsimp [Tf]; positivity
  have hTfle : Tf ≤ Tc := by dsimp [Tf]; linarith
  have hder (z : E × E) (hz : z ∈ closedBall (x₀, 0) (R0 : ℝ)) (t : ℝ)
      (ht : t ∈ Icc (-Tf) Tf) : HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    have ht' : t ∈ Icc (-(Tc / 2)) (Tc / 2) := by
      change t ∈ Icc (-Tf) Tf at ht
      simpa using ht
    have h1 : -Tc ≤ t := by
      exact le_trans (by linarith) ht'.1
    have h2 : t ≤ Tc := by
      exact le_trans ht'.2 (by linarith)
    have hle_t : |t| ≤ Tc := abs_le.mpr ⟨h1, h2⟩
    have ht0 : t ∈ Icc (-Tf0) Tf0 := by
      constructor
      · exact le_trans (by linarith) (abs_le.mp hle_t).1
      · exact le_trans (abs_le.mp hle_t).2 (by linarith)
    have hd : HasDerivAt (Ψ z) (odeField g (Ψ z t)) t := (hΨp z hz).2.1 t ht0
    have hfunEq : (fun s : ℝ => Φ z s) =ᶠ[𝓝 t] (fun s : ℝ => Ψ z s) := by
      refine Filter.mem_of_superset (Ioo_mem_nhds (show -Tc < t by nlinarith [hTc, ht'.1]) (show t < Tc by nlinarith [hTc, ht'.2])) ?_
      intro s hs
      dsimp [Φ]
      rw [if_pos (le_of_lt (abs_lt.mpr ⟨hs.1, hs.2⟩))]
    have hdΦ : HasDerivAt (fun s : ℝ => Φ z s) (odeField g (Ψ z t)) t :=
      hd.congr_of_eventuallyEq hfunEq
    have hval : (fun s : ℝ => Φ z s) t = Ψ z t := by
      dsimp [Φ]
      rw [if_pos hle_t]
    have hdΦ' : HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
      simpa [hval] using hdΦ
    exact hdΦ'
  let ρu : ℝ := 1 / 2
  have hρu : 0 < ρu := by norm_num
  have hLipC : ∀ t ∈ Icc (-Tf) Tf, ∀ b ∈ ball x₀ ρu,
      LipschitzOnWith Lf0 (fun z => Φ z t) (closedBall (b, (0 : E)) 1) := by
    intro t ht b hb
    have ht0 : t ∈ Icc (-Tf0) Tf0 := by constructor <;> linarith [ht.1, ht.2, hTfle, hTcTf0, hTf0]
    have h' := hLip t ht0
    have hsub : closedBall (b, (0 : E)) 1 ⊆ closedBall (x₀, (0 : E)) (R0 : ℝ) := by
      intro x hx
      rw [mem_closedBall]
      have hx1 : dist x (b, (0 : E)) ≤ 1 := mem_closedBall.mp hx
      have hle : dist x (x₀, (0 : E)) ≤ dist x (b, (0 : E)) + dist (b, (0 : E)) (x₀, (0 : E)) :=
        dist_triangle x (b, (0 : E)) (x₀, (0 : E))
      have hb0' : dist (b, (0 : E)) (x₀, (0 : E)) ≤ 1 / 2 := by
        have hnorm : ‖b - x₀‖ < 1 / 2 := by
          have hd : dist b x₀ < 1 / 2 := mem_ball.mp hb
          simpa [dist_eq_norm] using hd
        simpa [dist_eq_norm] using (le_of_lt hnorm)
      calc
        dist x (x₀, (0 : E)) ≤ dist x (b, (0 : E)) + dist (b, (0 : E)) (x₀, (0 : E)) := hle
        _ ≤ 1 + 1 / 2 := by linarith
        _ ≤ (R0 : ℝ) := by linarith
    have hm : LipschitzOnWith Lf0 (fun z : E × E => Ψ z t) (closedBall (b, (0 : E)) 1) := h'.mono hsub
    have hsame : (fun z : E × E => Φ z t) = fun z : E × E => Ψ z t := by
      funext x
      dsimp [Φ]
      have hxt : |t| ≤ Tc := by
        have h1 : -Tc ≤ t := by linarith [ht.1, hTfle]
        have h2 : t ≤ Tc := by linarith [ht.2, hTfle]
        exact abs_le.mpr ⟨h1, h2⟩
      rw [if_pos hxt]
    rwa [hsame]

  have hfam2 : ∀ z ∈ closedBall (x₀, (0 : E)) 1, ∀ t : ℝ, Φ z t ∈ closedBall (x₀, (0 : E)) 2 := by
    intro z hz t
    by_cases hw : |t| ≤ Tc
    · have hd : ‖Ψ z t - z‖ ≤ 1 / 2 := hdispl z (by
        exact closedBall_subset_closedBall (by linarith) hz) hw
      have hz1 : dist z (x₀, 0) ≤ 1 := mem_closedBall.mp hz
      have hsame : Φ z t = Ψ z t := by dsimp [Φ]; rw [if_pos hw]
      rw [mem_closedBall, dist_eq_norm, hsame]
      have h1 : ‖Ψ z t - (x₀, 0)‖ ≤ ‖Ψ z t - z‖ + ‖z - (x₀, 0)‖ :=
        norm_sub_le_norm_sub_add_norm_sub (Ψ z t) z (x₀, 0)
      have hd2 : ‖Ψ z t - z‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hd
      have hz2 : ‖z - (x₀, 0)‖ ≤ 1 := by simpa [dist_eq_norm] using hz1
      have hle2 : ‖Ψ z t - z‖ + ‖z - (x₀, 0)‖ ≤ 2 := by linarith
      exact le_trans h1 hle2
    · have hsame : Φ z t = z := by dsimp [Φ]; rw [if_neg hw]
      rw [hsame]
      have hz1 : dist z (x₀, 0) ≤ 1 := mem_closedBall.mp hz
      have hle : (1 : ℝ) ≤ 2 := by norm_num
      rw [mem_closedBall, dist_eq_norm]
      exact le_trans (by simpa [dist_eq_norm] using hz1) hle
  have hLipFam : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf0 (fun z => Φ z t) (closedBall (x₀, (0 : E)) 1) := by
    intro t ht
    have ht0 : t ∈ Icc (-Tf0) Tf0 := by constructor <;> linarith [ht.1, ht.2, hTfle, hTcTf0, hTf0]
    have h' := hLip t ht0
    have hsub : closedBall (x₀, (0 : E)) 1 ⊆ closedBall (x₀, (0 : E)) (R0 : ℝ) := by
      exact closedBall_subset_closedBall (by linarith)
    have hm : LipschitzOnWith Lf0 (fun z : E × E => Ψ z t) (closedBall (x₀, (0 : E)) 1) := h'.mono hsub
    have hsame : (fun z : E × E => Φ z t) = fun z : E × E => Ψ z t := by
      funext x
      dsimp [Φ]
      have hxt : |t| ≤ Tc := by
        have h1 : -Tc ≤ t := by linarith [ht.1, hTfle]
        have h2 : t ≤ Tc := by linarith [ht.2, hTfle]
        exact abs_le.mpr ⟨h1, h2⟩
      rw [if_pos hxt]
    rwa [hsame]
  refine ⟨Tf, hTf, ρu, hρu, Lf0, Φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    constructor
    · dsimp [Φ]
      simp [hΨp z hz |>.1]
    · constructor
      · intro t ht
        exact hder z hz t ht
      · intro t
        by_cases hw : |t| ≤ Tc
        · have hsame : Φ z t = Ψ z t := by dsimp [Φ]; rw [if_pos hw]
          rw [hsame]
          exact hcon z hz t
        · have hsame : Φ z t = z := by dsimp [Φ]; rw [if_neg hw]
          rw [hsame]
          have hzmem : dist z (x₀, 0) ≤ (R0 : ℝ) := mem_closedBall.mp hz
          have hle : (R0 : ℝ) ≤ (R0 : ℝ) + 1 := by linarith
          rw [mem_closedBall, dist_eq_norm]
          exact le_trans (by simpa [dist_eq_norm] using hzmem) hle
  · exact hfam2
  · exact hLipFam
  · exact hLipC
  · intro b hb z hz
    have hzR : z ∈ closedBall (x₀, 0) (R0 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      have h1 : ‖z - (x₀, 0)‖ ≤ ‖z - (b, (0 : E))‖ + ‖(b, (0 : E)) - (x₀, (0 : E))‖ :=
        norm_sub_le_norm_sub_add_norm_sub z (b, (0 : E)) (x₀, (0 : E))
      have h2 : ‖z - (b, (0 : E))‖ ≤ 1 := by
        have hd : dist z (b, (0 : E)) ≤ 1 := mem_closedBall.mp hz
        simpa [dist_eq_norm] using hd
      have hb0 : ‖(b, (0 : E)) - (x₀, (0 : E))‖ ≤ 1 / 2 := by
        have hnorm : ‖b - x₀‖ < 1 / 2 := by
          have hd : dist b x₀ < 1 / 2 := mem_ball.mp hb
          simpa [dist_eq_norm] using hd
        have hpair : ‖(b, (0 : E)) - (x₀, (0 : E))‖ = ‖b - x₀‖ := by simp
        rw [hpair]
        exact le_of_lt hnorm
      have h3 : ‖z - (b, (0 : E))‖ + ‖(b, (0 : E)) - (x₀, (0 : E))‖ ≤ (R0 : ℝ) := by
        calc
          ‖z - (b, (0 : E))‖ + ‖(b, (0 : E)) - (x₀, (0 : E))‖ ≤ 1 + 1 / 2 := by linarith
          _ ≤ (R0 : ℝ) := by linarith
      exact le_trans h1 h3
    constructor
    · dsimp [Φ]
      simp [hΨp z hzR |>.1]
    · constructor
      · intro t ht
        exact hder z hzR t ht
      · intro t
        have hz2 : ‖z - (b, (0 : E))‖ ≤ 1 := by
          have hd : dist z (b, (0 : E)) ≤ 1 := mem_closedBall.mp hz
          simpa [dist_eq_norm] using hd
        by_cases hw : |t| ≤ Tc
        · have hd : ‖Ψ z t - z‖ ≤ 1 / 2 := hdispl z hzR hw
          have hsame : Φ z t = Ψ z t := by dsimp [Φ]; rw [if_pos hw]
          rw [mem_closedBall, dist_eq_norm, hsame]
          have h1 : ‖Ψ z t - (b, (0 : E))‖ ≤ ‖Ψ z t - z‖ + ‖z - (b, (0 : E))‖ :=
            norm_sub_le_norm_sub_add_norm_sub (Ψ z t) z (b, (0 : E))
          have hle2 : ‖Ψ z t - z‖ + ‖z - (b, (0 : E))‖ ≤ 2 := by linarith
          exact le_trans h1 hle2
        · have hsame : Φ z t = z := by dsimp [Φ]; rw [if_neg hw]
          rw [mem_closedBall, dist_eq_norm, hsame]
          have hzle : ‖z - (b, (0 : E))‖ ≤ 2 := by linarith
          exact hzle

theorem exp_ray_geodesic (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) (Rvel : NNReal) :
    ∃ T > 0, ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall (x₀, 0) ((Rvel : ℝ) + 2), Φ z 0 = z ∧
         ∀ t ∈ Ioo (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      (∀ W : E, ‖W‖ ≤ (Rvel : ℝ) →
        (∀ tt ∈ Ioo (-T) T,
          HasDerivAt (fun ss => (Φ (x₀, W) ss).1) ((Φ (x₀, W) tt).2) tt ∧
             Real.sqrt ((g ((Φ (x₀, W) tt).1)) ((Φ (x₀, W) tt).2) ((Φ (x₀, W) tt).2)) =
               Real.sqrt ((g x₀) W W))) := by
  classical
  let R0 : NNReal := ⟨(Rvel : ℝ) + 2, by positivity⟩
  have hR0 : (R0 : ℝ) = (Rvel : ℝ) + 2 := rfl
  rcases flow_ball_cont g hg hinv (x₀, 0) R0 with ⟨T, hT, L, Φ, hΦp, hLip⟩
  refine ⟨T, hT, Φ, ?_, ?_⟩
  · intro z hz
    have hz0 : z ∈ closedBall (x₀, 0) (R0 : ℝ) := by simpa [hR0] using hz
    constructor
    · exact (hΦp z hz0).1
    · intro t ht
      have htIcc : t ∈ Icc (-T) T := by constructor <;> linarith [ht.1, ht.2]
      exact (hΦp z hz0).2.1 t htIcc
  · intro W hW tt htt
    have hz : (x₀, W) ∈ closedBall (x₀, 0) (R0 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      have hnorm : ‖(x₀, W) - (x₀, 0)‖ = ‖W‖ := by simp
      rw [hnorm]
      have hle : ‖W‖ ≤ (Rvel : ℝ) + 2 := by linarith
      simpa [hR0] using hle
    let S : Set (E × E) := closedBall (x₀, 0) (R0 : ℝ)
    have hΦS : ∀ z ∈ S, Φ z 0 = z ∧
        ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
      intro z hzS
      exact ⟨(hΦp z hzS).1, (hΦp z hzS).2.1⟩
    have hsplit := split_flow_geodesic g hg hinv (x₀, 0) hT S Φ hΦS (z := (x₀, W)) hz
    have hc : ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun ss => (Φ (x₀, W) ss).1) ((Φ (x₀, W) t).2) t := by
      intro t ht
      simpa using hsplit.1 t ht
    have hv : ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun ss => (Φ (x₀, W) ss).2)
          (accel (g ((Φ (x₀, W) t).1)) (fderiv ℝ g ((Φ (x₀, W) t).1)) ((Φ (x₀, W) t).2)) t := by
      intro t ht
      simpa using hsplit.2 t ht
    have hspeed := speed_const g hg hinv hsym (ε := T) hT (c := fun ss => (Φ (x₀, W) ss).1)
      (v := fun ss => (Φ (x₀, W) ss).2) hc hv
    have hf0 : (g ((Φ (x₀, W) 0).1)) ((Φ (x₀, W) 0).2) ((Φ (x₀, W) 0).2) = (g x₀) W W := by
      have hz0 : Φ (x₀, W) 0 = (x₀, W) := (hΦp (x₀, W) hz).1
      simp [hz0]
    have hval : (g ((Φ (x₀, W) tt).1)) ((Φ (x₀, W) tt).2) ((Φ (x₀, W) tt).2) = (g x₀) W W := by
      let f : ℝ → ℝ := fun ss => (g ((Φ (x₀, W) ss).1)) ((Φ (x₀, W) ss).2) ((Φ (x₀, W) ss).2)
      have hcst : ∀ t ∈ Ioo (-T) T, HasDerivAt f 0 t := by
        intro t ht
        simpa [f] using hspeed t ht
      have hmain := const_deriv_value (f := f) (c := 0) (ε := T) hT hcst (t := tt) htt
      have hf0' : f 0 = (g x₀) W W := by
        simpa [f] using hf0
      calc
        (g ((Φ (x₀, W) tt).1)) ((Φ (x₀, W) tt).2) ((Φ (x₀, W) tt).2)
            = f tt := by simp [f]
        _ = f 0 + 0 * tt := hmain
        _ = f 0 := by ring
        _ = (g x₀) W W := hf0'
    constructor
    · exact hc tt htt
    · rw [hval]


