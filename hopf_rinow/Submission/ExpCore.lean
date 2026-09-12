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
import Submission.ExpLocalDiffeo
import Submission.ExpFieldLip
import Submission.ExpTwoPoint
import Submission.ExpFderivRest
import Mathlib

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedSectionVars false

/-! ## Basic lemmas -/

/-- The Euler–Lagrange right-hand covector at zero velocity is zero. -/
lemma rhsCovector_zero (T : E →L[ℝ] Bilin E) : rhsCovector T 0 = 0 := by
  unfold rhsCovector evalAtV
  ext w
  simp

/-- The acceleration vanishes at zero velocity. -/
lemma accel_zero (gx : Bilin E) (T : E →L[ℝ] Bilin E) : accel gx T 0 = 0 := by
  unfold accel
  rw [rhsCovector_zero]
  simp

/-- The geodesic field vanishes at any point with zero velocity: `(x, 0)` is a rest point. -/
lemma odeField_zero_snd (g : E → Bilin E) (x : E) : odeField g (x, 0) = (0 : E × E) := by
  unfold odeField
  rw [accel_zero]
  simp

open ODE

/-- A local flow of the geodesic field on the unit ball around `z₀`, with trajectory containment
inside the radius-2 ball and per-time Lipschitz continuity in the initial data. -/
lemma flow_unit_ball_cont (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) :
    ∃ T > 0, ∃ L : NNReal, ∃ Φ : (E × E) → ℝ → (E × E),
      (∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
         (∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
         (∀ t : ℝ, Φ z t ∈ closedBall z₀ 2)) ∧
      (∀ t ∈ Icc (-T) T, LipschitzOnWith L (fun z => Φ z t) (closedBall z₀ 1)) := by
  classical
  let V : (E × E) → (E × E) := odeField g
  have hV1 : ContDiff ℝ 1 V := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases p with ⟨x, v⟩
    simpa [V] using odeField_contDiffAt g hg hinv x v
  have hfcont : Continuous (fderiv ℝ V) := hV1.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hVcont : Continuous V := hV1.continuous
  let S : Set (E × E) := closedBall z₀ (2 : ℝ)
  have hScomp : IsCompact S := by simpa [S] using (isCompact_closedBall z₀ (2 : ℝ))
  have hSne : S.Nonempty := ⟨z₀, by simp [S]⟩
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
  have hKbd (x : E × E) (hx : x ∈ closedBall z₀ (2 : ℝ)) (y : E × E)
      (hy : y ∈ closedBall z₀ (2 : ℝ)) : ‖V y - V x‖ ≤ (K : ℝ) * ‖y - x‖ := by
    have hdiff : ∀ q ∈ S, DifferentiableAt ℝ V q := fun q _ =>
      (hV1.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
    have hsub := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := V) hdiff hKbnd
      (convex_closedBall z₀ (2 : ℝ)) hx hy
    simpa [V, S] using hsub
  have hKbdnn : LipschitzOnWith K V (closedBall z₀ (2 : ℝ)) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have := hKbd x hx y hy
    simpa [dist_eq_norm, norm_sub_rev] using this
  let τ : ℝ := 1 / (2 * ((Lb : ℝ) + 1))
  have hτpos : 0 < τ := by positivity
  have hmem0 : (0 : ℝ) ∈ Icc (-τ) τ := by constructor <;> linarith
  let r1 : NNReal := ⟨1, by norm_num⟩
  let r2 : NNReal := ⟨2, by norm_num⟩
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
      change (Lb : ℝ) * τ ≤ (2 : ℝ) - (1 : ℝ)
      norm_num
      exact hle
  -- build the flow by hand so that we can export trajectory containment
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
    · -- Φ z 0 = z
      have hmain : (α z hz').compProj (0 : ℝ) = z := by
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
        exact hmemCurve z hz' t
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

/-- The flow trajectory through the rest point `(x₀, 0)` stays at the rest point. -/
lemma flow_rest_point (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {T : ℝ} (hT : 0 < T) {Φ : (E × E) → ℝ → (E × E)}
    (x₀ : E)
    (hΦ₀ : ∀ z ∈ closedBall (x₀, 0) (1 : ℝ), Φ z 0 = z ∧
       ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) :
    ∀ t ∈ Ioo (-T) T, Φ (x₀, 0) t = (x₀, 0) := by
  let z₀ : E × E := (x₀, 0)
  have hz₀mem : z₀ ∈ closedBall (x₀, 0) (1 : ℝ) := by
    simp [z₀, closedBall, dist_eq_norm]
  have hcur (s : ℝ) (hs : s ∈ Ioo (-T) T) :
      HasDerivAt (fun u : ℝ => Φ z₀ u) (odeField g (Φ z₀ s)) s := by
    exact (hΦ₀ z₀ hz₀mem).2 s (Ioo_subset_Icc_self hs)
  intro t ht
  -- (c,vel) splitting of the trajectory
  let c₂ : ℝ → E := fun s => (Φ z₀ s).1
  let vel₂ : ℝ → E := fun s => (Φ z₀ s).2
  have hc₂ (s : ℝ) (hs : s ∈ Ioo (-T) T) : HasDerivAt c₂ (vel₂ s) s := by
    have h1 : HasDerivAt (fun u => (Φ z₀ u).1) (odeField g (Φ z₀ s)).1 s := by
      have hf := (hcur s hs).hasFDerivAt.fst.hasDerivAt
      simpa using hf
    simpa [c₂, vel₂, odeField] using h1
  have hv₂ (s : ℝ) (hs : s ∈ Ioo (-T) T) :
      HasDerivAt vel₂ (accel (g (c₂ s)) (fderiv ℝ g (c₂ s)) (vel₂ s)) s := by
    have h2 : HasDerivAt (fun u => (Φ z₀ u).2) (odeField g (Φ z₀ s)).2 s := by
      have hf := (hcur s hs).hasFDerivAt.snd.hasDerivAt
      simpa using hf
    simpa [c₂, vel₂, odeField] using h2
  let c₁ : ℝ → E := fun _ => x₀
  let vel₁ : ℝ → E := fun _ => 0
  have hc₁ (s : ℝ) (hs : s ∈ Ioo (-T) T) : HasDerivAt c₁ (vel₁ s) s := by
    simpa [c₁, vel₁] using (hasDerivAt_const s x₀)
  have hv₁ (s : ℝ) (hs : s ∈ Ioo (-T) T) :
      HasDerivAt vel₁ (accel (g (c₁ s)) (fderiv ℝ g (c₁ s)) (vel₁ s)) s := by
    simp [c₁, vel₁]
    rw [accel_zero]
    exact hasDerivAt_const s (0 : E)
  have hc0 : c₁ 0 = c₂ 0 := by
    simp [c₁, c₂]
    have h := congrArg Prod.fst (hΦ₀ z₀ hz₀mem).1
    simpa [z₀] using h.symm
  have hv0 : vel₁ 0 = vel₂ 0 := by
    simp [vel₁, vel₂]
    have h := congrArg Prod.snd (hΦ₀ z₀ hz₀mem).1
    simpa [z₀] using h.symm
  rcases unique_geodesic g hg hinv hT (c₁ := c₁) (vel₁ := vel₁) (c₂ := c₂) (vel₂ := vel₂)
      hc₁ hv₁ hc₂ hv₂ hc0 hv0 with ⟨heq₁, heq₂⟩
  change (Φ z₀ t) = z₀
  apply Prod.ext
  · simpa [z₀] using (heq₁ t ht).symm
  · simpa [z₀] using (heq₂ t ht).symm




/-- Along the constant rest trajectory the linearized (Jacobi) solutions are affine:
`Jc w t = (w.1 + t • w.2, w.2)`. -/
lemma jacobi_eq_affine_rest (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {ε : ℝ} (hε : 0 < ε)
    {Φ : (E × E) → ℝ → (E × E)}
    (hΦ₀ : ∀ z ∈ closedBall (x₀, (0 : E)) (1 : ℝ), Φ z 0 = z ∧
       ∀ t ∈ Icc (-ε) ε, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    (hrest : ∀ t ∈ Ioo (-ε) ε, Φ (x₀, (0 : E)) t = (x₀, (0 : E)))
    {Jc : (E × E) → ℝ → (E × E)}
    (hJc0 : ∀ w : E × E, Jc w 0 = w)
    (hJcOde : ∀ w : E × E, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (Jc w) ((fderiv ℝ (odeField g)) (Φ (x₀, 0) t) (Jc w t)) t) :
    ∀ (w : E × E) (t : ℝ), t ∈ Ioo (-ε) ε → Jc w t = (w.1 + t • w.2, w.2) := by
  intro w t ht
  have hz₀mem : (x₀, (0 : E)) ∈ closedBall (x₀, (0 : E)) (1 : ℝ) := by simp [closedBall, dist_eq_norm]
  have hz (s : ℝ) (hs : s ∈ Ioo (-ε) ε) :
      HasDerivAt (fun u : ℝ => Φ (x₀, 0) u) (odeField g (Φ (x₀, 0) s)) s := by
    exact (hΦ₀ (x₀, 0) hz₀mem).2 s (Ioo_subset_Icc_self hs)
  let J₂ : ℝ → E × E := fun s => (w.1 + s • w.2, w.2)
  have hJ₂0 : J₂ 0 = w := by simp [J₂]
  have hJ₂d (s : ℝ) (hs : s ∈ Ioo (-ε) ε) :
      HasDerivAt J₂ ((fderiv ℝ (odeField g)) (Φ (x₀, 0) s) (J₂ s)) s := by
    have hsm : HasDerivAt (fun u : ℝ => u • w.2) w.2 s := by
      simpa using ((hasDerivAt_id s).smul_const w.2)
    have hc1 : HasDerivAt (fun u : ℝ => w.1 + u • w.2) w.2 s := by
      have hadd : HasDerivAt (fun u : ℝ => w.1 + u • w.2) ((0 : E) + w.2) s :=
        (hasDerivAt_const s w.1).add hsm
      simpa using hadd
    have hc2 : HasDerivAt (fun _ : ℝ => w.2) (0 : E) s := hasDerivAt_const s w.2
    have hder : HasDerivAt (fun u : ℝ => (w.1 + u • w.2, w.2)) (w.2, (0 : E)) s :=
      hc1.prodMk hc2
    have hval : (fderiv ℝ (odeField g)) (Φ (x₀, 0) s) (J₂ s) = (w.2, (0 : E)) := by
      rw [hrest s hs]
      have hfd := fderiv_odeField_rest g hg hinv x₀ (w.1 + s • w.2, w.2)
      simpa [J₂] using hfd
    exact hder.congr_deriv hval.symm
  have hJ₁ : Jc w 0 = w ∧ ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt (Jc w) ((fderiv ℝ (odeField g)) (Φ (x₀, 0) s) (Jc w s)) s :=
    ⟨hJc0 w, hJcOde w⟩
  have hJ₂ : J₂ 0 = w ∧ ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt J₂ ((fderiv ℝ (odeField g)) (Φ (x₀, 0) s) (J₂ s)) s :=
    ⟨hJ₂0, hJ₂d⟩
  have huniq := jacobi_unique_along_flow g hg hinv hε (z := fun u : ℝ => Φ (x₀, 0) u)
    (hz := hz) (J₁ := Jc w) (J₂ := J₂) (w := w) hJ₁ hJ₂
  have heq := huniq t ht
  simpa [J₂] using heq




/-- The slice-flow exponential map has derivative the identity at `0`, given the Fréchet
derivative of the flow at the rest point is `w ↦ (w.1 + ρ • w.2, w.2)`. -/
lemma exp_hasFDerivAt_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ : E) (ρ : ℝ) (hρ : 0 < ρ) {Φ : (E × E) → ℝ → (E × E)}
    (hFD : ∃ L0 : (E × E) →L[ℝ] (E × E),
      HasFDerivAt (fun z : E × E => Φ z ρ) L0 (x₀, (0 : E)) ∧
        ∀ w : E × E, L0 w = (w.1 + ρ • w.2, w.2)) :
    HasFDerivAt (fun v : E => (Φ (x₀, (1 / ρ) • v) ρ).1)
      (ContinuousLinearMap.id ℝ E) (0 : E) := by
  rcases hFD with ⟨L0, hFL0, hL0val⟩
  let L1 : (E × E) →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp L0
  let hlin : E →L[ℝ] (E × E) :=
    (0 : E →L[ℝ] E).prod ((1 / ρ : ℝ) • (ContinuousLinearMap.id ℝ E))
  have hder_h : HasFDerivAt (fun u : E => (x₀, (1 / ρ) • u)) hlin (0 : E) := by
    have hL : HasFDerivAt (fun u : E => hlin u) hlin (0 : E) := by
      exact hlin.hasFDerivAt
    have hc : HasFDerivAt (fun u : E => hlin u + (x₀, (0 : E))) hlin (0 : E) :=
      hL.add_const (x₀, (0 : E))
    have hfun : (fun u : E => (x₀, (1 / ρ) • u)) =ᶠ[𝓝 (0 : E)]
        (fun u : E => hlin u + (x₀, (0 : E))) := by
      filter_upwards with u
      ext <;> simp [hlin]
    exact hc.congr_of_eventuallyEq hfun
  have hFL1 : HasFDerivAt (fun z : E × E => (Φ z ρ).1)
      ((ContinuousLinearMap.fst ℝ E E).comp L0) (x₀, (0 : E)) := by
    simpa using hFL0.fst
  have hFL1' : HasFDerivAt (fun z : E × E => (Φ z ρ).1)
      ((ContinuousLinearMap.fst ℝ E E).comp L0) (x₀, (1 / ρ) • (0 : E)) := by
    simpa using hFL1
  have hcomp : HasFDerivAt (fun v : E => (Φ (x₀, (1 / ρ) • v) ρ).1)
      (L1.comp hlin) (0 : E) := by
    have hc := HasFDerivAt.comp (x := (0 : E)) hFL1' hder_h
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards with v
    rfl
  have hid : L1.comp hlin = ContinuousLinearMap.id ℝ E := by
    ext v
    change (L0 ((0 : E), (1 / ρ) • v)).1 = v
    rw [hL0val ((0 : E), (1 / ρ) • v)]
    have hsmul : ρ • ((1 / ρ) • v) = v := by
      rw [smul_smul]
      have hm : (ρ * (1 / ρ) : ℝ) = 1 := by field_simp [ne_of_gt hρ]
      rw [hm]
      simp
    simpa using hsmul
  exact hcomp.congr_fderiv hid

end

end Submission.Model

open Submission.Model

namespace Submission.ExpCore

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
set_option linter.unusedSectionVars false

/-- The time-`ρ` flow map from the slice `{x₀} × E` near the rest point `(x₀, 0)` of the geodesic
field is a local diffeomorphism at `0`, with derivative the identity at `0`. -/
theorem flow_exp_core (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) :
    ∃ ρ > 0, ∃ Φ : E × E → ℝ → E × E, ∃ L : NNReal,
      (∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
         ∀ t ∈ Icc (-(2 * ρ)) (2 * ρ), HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      (∀ t ∈ Icc (-(2 * ρ)) (2 * ρ), LipschitzOnWith L (fun z => Φ z t) (closedBall (x₀, 0) 1)) ∧
      (Φ (x₀, 0) ρ = (x₀, 0)) ∧
      (let exp : E → E := fun v => (Φ (x₀, (1 / ρ) • v) ρ).1; exp 0 = x₀ ∧
       HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 ∧
       (∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 x₀,
         Set.MapsTo exp U V ∧ Function.Injective (fun v : U => exp v.1) ∧
         Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
         ∃ inv : E → E, ∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y ∧
           ∀ v ∈ U, inv (exp v) = v)) := by
  classical
  let z₀ : E × E := (x₀, 0)
  rcases flow_unit_ball_cont g hg hinv z₀ with ⟨T, hT, Lf, Φ, hΦAll, hLipF⟩
  have hΦ₀can (z : E × E) (hz : z ∈ closedBall z₀ (1 : ℝ)) :
      Φ z 0 = z ∧ ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t :=
    ⟨(hΦAll z hz).1, (hΦAll z hz).2.1⟩
  have hContAll (z : E × E) (hz : z ∈ closedBall z₀ (1 : ℝ)) (t : ℝ) :
      Φ z t ∈ closedBall z₀ (2 : ℝ) := (hΦAll z hz).2.2 t
  rcases canonical_solutions g hg hinv z₀ T hT Φ hΦ₀can with
    ⟨Tj, hTj, hTjT, Jc, hJc0, hJcOde, hJcadd, hJcsmul⟩
  rcases flow_fderiv_canonical g hg hinv z₀ T hT Lf Φ hΦ₀can hLipF Tj hTj hTjT
      Jc hJc0 hJcOde hJcadd hJcsmul with ⟨Tc, hTc, hTcT, hFD⟩
  have hRestAll : ∀ t ∈ Ioo (-T) T, Φ z₀ t = z₀ := by
    have hfr := flow_rest_point g hg hinv hT (x₀ := x₀) (Φ := Φ) hΦ₀can
    simpa [z₀] using hfr
  rcases field_lipschitzOn g hg hinv z₀ with ⟨K, hVLip⟩
  let ρ : ℝ := (1 / 2) * min T (min Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1))))
  have hposM : 0 < min T (min Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1)))) := by
    refine lt_min hT (lt_min hTj (lt_min hTc ?_))
    have hden : 0 < ((Lf : ℝ) * (K : ℝ)) + 1 := by positivity
    exact one_div_pos.mpr hden
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact mul_pos (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)) hposM
  have hρT : ρ < T := by
    dsimp [ρ]
    have hm : 0 < min T (min Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1)))) := hposM
    have hle : min T (min Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1)))) ≤ T := min_le_left _ _
    nlinarith
  have hρTj : ρ < Tj := by
    dsimp [ρ]
    have hm : 0 < min T (min Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1)))) := hposM
    have hle : min T (min Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1)))) ≤ Tj :=
      le_trans (min_le_right T _) (min_le_left Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1))))
    nlinarith
  have hρTc : ρ < Tc := by
    dsimp [ρ]
    have hm : 0 < min T (min Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1)))) := hposM
    have hle : min T (min Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1)))) ≤ Tc :=
      le_trans (min_le_right T _)
        (le_trans (min_le_right Tj _) (min_le_left Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1))))
    nlinarith
  have hκlt1 : (K : ℝ) * (Lf : ℝ) * ρ < 1 := by
    have hle2 : min T (min Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1)))) ≤
        1 / (((Lf : ℝ) * (K : ℝ)) + 1) :=
      le_trans (min_le_right T _)
        (le_trans (min_le_right Tj _) (min_le_right Tc _))
    have hρle : ρ ≤ (1 / 2) * (1 / (((Lf : ℝ) * (K : ℝ)) + 1)) := by
      dsimp [ρ]
      exact mul_le_mul_of_nonneg_left hle2 (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
    have hden : 0 < (Lf : ℝ) * (K : ℝ) + 1 := by positivity
    have hmain : (K : ℝ) * (Lf : ℝ) * ((1 / 2) * (1 / ((Lf : ℝ) * (K : ℝ) + 1))) < 1 := by
      field_simp [hden.ne']
      nlinarith [show 0 ≤ (Lf : ℝ) * (K : ℝ) by positivity]
    calc
      (K : ℝ) * (Lf : ℝ) * ρ ≤ (K : ℝ) * (Lf : ℝ) *
          ((1 / 2) * (1 / (((Lf : ℝ) * (K : ℝ)) + 1))) := by
        gcongr
      _ < 1 := hmain
  -- derivative data at the rest point, assembled for exp
  have hJaff : ∀ (w : E × E) (t : ℝ), t ∈ Ioo (-Tj) Tj → Jc w t = (w.1 + t • w.2, w.2) := by
    have hΦ₀Tj (z : E × E) (hz : z ∈ closedBall (x₀, (0 : E)) (1 : ℝ)) :
        Φ z 0 = z ∧ ∀ t ∈ Icc (-Tj) Tj, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
      constructor
      · exact (hΦ₀can z (by simpa [z₀] using hz)).1
      · intro t ht
        exact (hΦ₀can z (by simpa [z₀] using hz)).2 t (by
          constructor
          · exact le_trans (neg_le_neg (le_of_lt hTjT)) ht.1
          · exact le_trans ht.2 (le_of_lt hTjT))
    have hrestTj : ∀ t ∈ Ioo (-Tj) Tj, Φ (x₀, (0 : E)) t = (x₀, (0 : E)) := by
      intro t ht
      have ht' : t ∈ Ioo (-T) T := by
        constructor
        · exact lt_trans (neg_lt_neg hTjT) ht.1
        · exact lt_trans ht.2 hTjT
      simpa [z₀] using hRestAll t ht'
    exact jacobi_eq_affine_rest g hg hinv x₀ hTj hΦ₀Tj hrestTj hJc0 hJcOde
  have hρIooTj : ρ ∈ Ioo (-Tj) Tj := by constructor <;> linarith [hρ, hTj, hρTj]
  have hρIccTc : ρ ∈ Icc (-Tc) Tc := by constructor <;> linarith [hρ, hTc, hρTc]
  rcases hFD ρ hρIccTc with ⟨L0, hFL0, hL0val⟩
  have hL0aff (w : E × E) : L0 w = (w.1 + ρ • w.2, w.2) := by
    have hjj := hJaff w ρ hρIooTj
    calc
      L0 w = Jc w ρ := hL0val w
      _ = (w.1 + ρ • w.2, w.2) := hjj
  let exp : E → E := fun v => (Φ (x₀, (1 / ρ) • v) ρ).1
  have hexp0 : exp 0 = x₀ := by
    have hres : Φ (x₀, (0 : E)) ρ = (x₀, (0 : E)) := by
      have ht' : ρ ∈ Ioo (-T) T := by constructor <;> linarith [hρ, hT, hρT]
      simpa [z₀] using hRestAll ρ ht'
    simp [exp, hres]
  have hfderiv : HasFDerivAt exp (ContinuousLinearMap.id ℝ E) (0 : E) := by
    refine exp_hasFDerivAt_id x₀ ρ hρ (Φ := Φ) ?_
    exact ⟨L0, hFL0, hL0aff⟩
  -- window-ρ flow facts, rest point and Lipschitz for the estimate
  have hΦ₀ρ (z : E × E) (hz : z ∈ closedBall z₀ (1 : ℝ)) :
      Φ z 0 = z ∧ ∀ t ∈ Icc (-ρ) ρ, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    constructor
    · exact (hΦ₀can z hz).1
    · intro t ht
      exact (hΦ₀can z hz).2 t (by
        constructor
        · exact le_trans (neg_le_neg (le_of_lt hρT)) ht.1
        · exact le_trans ht.2 (le_of_lt hρT))
  have hLipρ (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) :
      LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ (1 : ℝ)) := by
    exact hLipF t (by
      constructor
      · exact le_trans (neg_le_neg (le_of_lt hρT)) ht.1
      · exact le_trans ht.2 (le_of_lt hρT))
  have h2ρ_le_T : 2 * ρ ≤ T := by
    dsimp [ρ]
    have hle : min T (min Tj (min Tc (1 / (((Lf : ℝ) * (K : ℝ)) + 1)))) ≤ T := min_le_left _ _
    nlinarith
  have hContρ (z : E × E) (hz : z ∈ closedBall z₀ (1 : ℝ)) (t : ℝ) (ht : t ∈ Icc 0 ρ) :
      Φ z t ∈ closedBall z₀ (2 : ℝ) := hContAll z hz t
  have hΦ₀w (z : E × E) (hz : z ∈ closedBall z₀ (1 : ℝ)) :
      Φ z 0 = z ∧ ∀ t ∈ Icc (-(2 * ρ)) (2 * ρ), HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    constructor
    · exact (hΦ₀can z hz).1
    · intro t ht
      exact (hΦ₀can z hz).2 t (by
        constructor
        · exact le_trans (neg_le_neg h2ρ_le_T) ht.1
        · exact le_trans ht.2 h2ρ_le_T)
  have hLipw (t : ℝ) (ht : t ∈ Icc (-(2 * ρ)) (2 * ρ)) :
      LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ (1 : ℝ)) := by
    exact hLipF t (by
      constructor
      · exact le_trans (neg_le_neg h2ρ_le_T) ht.1
      · exact le_trans ht.2 h2ρ_le_T)
  have htwo : ∀ u v : E, u ∈ closedBall (0 : E) ρ → v ∈ closedBall (0 : E) ρ →
      ‖((Φ (x₀, (1 / ρ) • u) ρ).1 - (Φ (x₀, (1 / ρ) • v) ρ).1) - (u - v)‖ ≤
        ((K : ℝ) * (Lf : ℝ) * ρ) * ‖u - v‖ := by
    intro u v hu hv
    have hΦ0x (z : E × E) (hz : z ∈ closedBall (x₀, (0 : E)) (1 : ℝ)) :
        Φ z 0 = z ∧ ∀ t ∈ Icc (-ρ) ρ, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
      simpa [z₀] using hΦ₀ρ z hz
    have hCx (z : E × E) (hz : z ∈ closedBall (x₀, (0 : E)) (1 : ℝ)) (t : ℝ) (ht : t ∈ Icc 0 ρ) :
        Φ z t ∈ closedBall (x₀, (0 : E)) (2 : ℝ) := by
      simpa [z₀] using hContρ z hz t ht
    have hLx (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) :
        LipschitzOnWith Lf (fun z => Φ z t) (closedBall (x₀, (0 : E)) (1 : ℝ)) := by
      simpa [z₀] using hLipρ t ht
    have hKx : LipschitzOnWith K (odeField g) (closedBall (x₀, (0 : E)) (2 : ℝ)) := by
      simpa [z₀] using hVLip
    exact exp_two_point_bound g hg hinv x₀ ρ hρ Lf K Φ hΦ0x hCx hLx hKx u v hu hv
  have hκ0 : 0 ≤ (K : ℝ) * (Lf : ℝ) * ρ := by positivity
  have hresρ : Φ (x₀, (0 : E)) ρ = (x₀, (0 : E)) := by
    have ht' : ρ ∈ Ioo (-T) T := by constructor <;> linarith [hρ, hT, hρT]
    simpa [z₀] using hRestAll ρ ht'
  have hld : ∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 x₀,
      Set.MapsTo exp U V ∧ Function.Injective (fun v : U => exp v.1) ∧
      Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
      ∃ inv : E → E, ∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y ∧
        ∀ v ∈ U, inv (exp v) = v := by
    refine Submission.ExpLocalDiffeo.exp_local_diffeomorphism_of_estimates exp x₀ ρ
      ((K : ℝ) * (Lf : ℝ) * ρ) hρ hκ0 hκlt1 hexp0 ?_
    exact fun u v hu hv => by simpa [exp] using htwo u v hu hv
  refine ⟨ρ, hρ, Φ, Lf, ?_, ?_, ?_, ?_⟩
  · -- flow on the window Icc (-(2*ρ)) (2*ρ)
    intro z hz
    simpa [z₀] using hΦ₀w z hz
  · -- per-time Lipschitz with constant Lf
    intro t ht
    simpa [z₀] using hLipw t ht
  · -- the rest point stays fixed at time ρ
    simpa [z₀] using hresρ
  · -- the exponential map part
    change exp 0 = x₀ ∧ HasFDerivAt exp (ContinuousLinearMap.id ℝ E) (0 : E) ∧
      (∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 x₀,
        Set.MapsTo exp U V ∧ Function.Injective (fun v : U => exp v.1) ∧
        Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
        ∃ inv : E → E, ∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y ∧
          ∀ v ∈ U, inv (exp v) = v)
    constructor
    · exact hexp0
    · constructor
      · exact hfderiv
      · exact hld
