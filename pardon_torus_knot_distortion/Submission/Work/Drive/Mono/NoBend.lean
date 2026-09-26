import Mathlib
import Submission.Work.Drive.Mono.ae_exists_goodV

/-!
# The "no-bend" genericity of the knot at its vertical crossings

Fix a unit direction `e` (in the application `e = shiftVσ σ 1`, so that `⟪e, y⟫ = y (σ 2)`).  Write

* `vertVel K e t = perpProj e (deriv K.curve t)` for the component of the velocity of `K`
  orthogonal to `e` (the knot is *vertical* at `t` when this vanishes);
* `vertAcc K e t = perpProj e (deriv (deriv K.curve) t)` for the corresponding component of the
  acceleration (the knot *bends* at `t` when this does not vanish).

`Work.Drive.Mono.ae_noBendCrossing` says that for almost every level `u` of the flat height
`(·) (σ 2)`, every vertical crossing of the knot with the level inside the closed box is
**bend-free**.  The reason is one-dimensional: the set of *bending* vertical parameters is discrete
(the orthogonal velocity has a simple zero there), hence countable, and its image under the flat
height is null.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-! ## The orthogonal projection -/

/-- Orthogonal projection of `x` onto the orthogonal complement of `e`. -/
def perpProj (e x : R3) : R3 := x - inner ℝ e x • e

/-- The orthogonal projection onto `e^⊥` as a continuous linear map. -/
def perpProjCLM (e : R3) : R3 →L[ℝ] R3 :=
  ContinuousLinearMap.id ℝ R3 - (innerSL ℝ e).smulRight e

theorem perpProjCLM_apply (e x : R3) : perpProjCLM e x = perpProj e x := by
  simp [perpProjCLM, perpProj, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem eq_smul_of_perpProj_eq_zero {e x : R3} (h : perpProj e x = 0) :
    x = inner ℝ e x • e := sub_eq_zero.mp h

@[simp] theorem perpProj_zero (e : R3) : perpProj e (0 : R3) = 0 := by simp [perpProj]

theorem perpProj_eq_self_of_inner_eq_zero {e x : R3} (h : inner ℝ e x = 0) :
    perpProj e x = x := by
  rw [perpProj, h, zero_smul, sub_zero]

theorem inner_perpProj_eq_zero (e x : R3) (he : ‖e‖ = 1) : inner ℝ (perpProj e x) e = 0 := by
  rw [perpProj, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he,
    real_inner_comm e x]
  ring

theorem perpProj_eq_zero_iff {e x : R3} (he : ‖e‖ = 1) :
    perpProj e x = 0 ↔ ∃ a : ℝ, x = a • e := by
  constructor
  · intro h
    exact ⟨inner ℝ e x, eq_smul_of_perpProj_eq_zero h⟩
  · rintro ⟨a, rfl⟩
    rw [perpProj, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    simp

theorem norm_perpProj_le {e x : R3} (he : ‖e‖ = 1) : ‖perpProj e x‖ ≤ ‖x‖ := by
  have horth : inner ℝ (perpProj e x) (inner ℝ e x • e) = 0 := by
    rw [real_inner_smul_right, inner_perpProj_eq_zero e x he, mul_zero]
  have hx : x = perpProj e x + inner ℝ e x • e := by rw [perpProj]; abel
  have hpy : ‖x‖ * ‖x‖ =
      ‖perpProj e x‖ * ‖perpProj e x‖ + ‖inner ℝ e x • e‖ * ‖inner ℝ e x • e‖ := by
    conv_lhs => rw [hx]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hle : ‖perpProj e x‖ * ‖perpProj e x‖ ≤ ‖x‖ * ‖x‖ := by
    rw [hpy]; exact le_add_of_nonneg_right (mul_self_nonneg _)
  nlinarith [norm_nonneg (perpProj e x), norm_nonneg x]

/-! ## The velocity and acceleration orthogonal to `e` -/

/-- The component of the velocity of `K` orthogonal to `e`. -/
def vertVel (K : Knot) (e : R3) (t : ℝ) : R3 := perpProj e (deriv K.curve t)

/-- The component of the acceleration of `K` orthogonal to `e`. -/
def vertAcc (K : Knot) (e : R3) (t : ℝ) : R3 := perpProj e (deriv (deriv K.curve) t)

/-- The velocity of the knot, as a `C^∞` map. -/
theorem contDiff_deriv_curve (K : Knot) : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => deriv K.curve t) :=
  ContDiff.iterate_deriv 1 K.smooth

/-- The acceleration of the knot, as a `C^∞` map. -/
theorem contDiff_deriv2_curve (K : Knot) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => deriv (deriv K.curve) t) :=
  ContDiff.iterate_deriv 2 K.smooth

theorem contDiff_perpProj (e : R3) : ContDiff ℝ (⊤ : ℕ∞) (perpProj e) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (perpProjCLM e) := (perpProjCLM e).contDiff (n := (⊤ : ℕ∞))
  have hfun : (perpProjCLM e : R3 → R3) = perpProj e := by
    funext x; rw [perpProjCLM_apply]
  rwa [hfun] at h

theorem contDiff_vertVel (K : Knot) (e : R3) : ContDiff ℝ (⊤ : ℕ∞) (vertVel K e) := by
  have h := (contDiff_perpProj e).comp (contDiff_deriv_curve K)
  exact h

theorem contDiff_vertAcc (K : Knot) (e : R3) : ContDiff ℝ (⊤ : ℕ∞) (vertAcc K e) := by
  have h := (contDiff_perpProj e).comp (contDiff_deriv2_curve K)
  exact h

theorem continuous_vertVel (K : Knot) (e : R3) : Continuous (vertVel K e) :=
  (contDiff_vertVel K e).continuous

theorem continuous_vertAcc (K : Knot) (e : R3) : Continuous (vertAcc K e) :=
  (contDiff_vertAcc K e).continuous

/-- The derivative of `vertVel` is `vertAcc`. -/
theorem deriv_vertVel (K : Knot) (e : R3) (t : ℝ) :
    deriv (vertVel K e) t = vertAcc K e t := by
  have hd : HasDerivAt (fun r : ℝ => deriv K.curve r) (deriv (deriv K.curve) t) t :=
    ((contDiff_deriv_curve K).differentiable (by simp)).differentiableAt.hasDerivAt
  have hconst : HasDerivAt (fun _ : ℝ => e) 0 t := hasDerivAt_const t e
  have hin : HasDerivAt (fun r : ℝ => inner ℝ e (deriv K.curve r))
      (inner ℝ e (deriv (deriv K.curve) t)) t := by
    have h := hconst.inner (𝕜 := ℝ) hd
    simpa using h
  have hsm : HasDerivAt (fun r : ℝ => inner ℝ e (deriv K.curve r) • e)
      (inner ℝ e (deriv (deriv K.curve) t) • e) t := hin.smul_const e
  have hsub := hd.sub hsm
  have hfun : vertVel K e = fun r : ℝ =>
      deriv K.curve r - inner ℝ e (deriv K.curve r) • e := rfl
  have hkey : deriv (fun r : ℝ => deriv K.curve r - inner ℝ e (deriv K.curve r) • e) t
      = deriv (deriv K.curve) t - inner ℝ e (deriv (deriv K.curve) t) • e := by
    have hfun2 : (fun r : ℝ => deriv K.curve r - inner ℝ e (deriv K.curve r) • e)
        = (fun r : ℝ => deriv K.curve r) -
          (fun r : ℝ => inner ℝ e (deriv K.curve r) • e) := by
      funext r; rfl
    rw [hfun2]
    exact hsub.deriv
  rw [hfun, hkey, vertAcc, perpProj]

/-- The derivative of the scalar function `t ↦ ⟪vertVel K e t, u⟫` is `⟪vertAcc K e t, u⟫`. -/
theorem deriv_vertVel_inner (K : Knot) (e u : R3) (t : ℝ) :
    deriv (fun r : ℝ => inner ℝ (vertVel K e r) u) t = inner ℝ (vertAcc K e t) u := by
  have hd : HasDerivAt (vertVel K e) (deriv (vertVel K e) t) t :=
    ((contDiff_vertVel K e).differentiable (by simp)).differentiableAt.hasDerivAt
  have hd' : HasDerivAt (vertVel K e) (vertAcc K e t) t := by
    rwa [deriv_vertVel] at hd
  have hconst : HasDerivAt (fun _ : ℝ => u) 0 t := hasDerivAt_const t u
  have h := hd'.inner (𝕜 := ℝ) hconst
  have hderiv := h.deriv
  rw [hderiv]
  simp

/-! ## Countability from isolated points -/

/-- A set of reals in which every point is isolated is countable. -/
theorem countable_of_isolated {S : Set ℝ}
    (h : ∀ t ∈ S, ∃ ε > 0, ∀ t' ∈ S, |t' - t| < ε → t' = t) : S.Countable := by
  classical
  have key : ∀ t : ℝ, ∃ p : ℚ × ℚ, t ∈ S → ((p.1 : ℝ) < t ∧ t < (p.2 : ℝ) ∧
      ∀ t' ∈ S, (p.1 : ℝ) < t' → t' < (p.2 : ℝ) → t' = t) := by
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨ε, hε, hiso⟩ := h t ht
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t - ε < t by linarith)
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show t < t + ε by linarith)
      refine ⟨(q, r), fun _ => ⟨hq2, hr1, fun t' ht' h1 h2 => hiso t' ht' ?_⟩⟩
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    · exact ⟨(0, 0), fun hcon => absurd hcon ht⟩
  set p : ℝ → ℚ × ℚ := fun t => Classical.choose (key t) with hp
  have hspec : ∀ t (ht : t ∈ S), (p t).1 < t ∧ t < (p t).2 ∧
      ∀ t' ∈ S, (p t).1 < t' → t' < (p t).2 → t' = t :=
    fun t ht => Classical.choose_spec (key t) ht
  refine MapsTo.countable_of_injOn (f := p) (s := S) (t := (Set.univ : Set (ℚ × ℚ)))
    (fun x _ => Set.mem_univ _) ?_ (Set.countable_univ)
  intro t ht t' ht' heq
  have h1 : (p t).1 = (p t').1 := by rw [heq]
  have h2 : (p t).2 = (p t').2 := by rw [heq]
  have hlt1 : (p t).1 < t' := by rw [h1]; exact (hspec t' ht').1
  have hlt2 : t' < (p t).2 := by rw [h2]; exact (hspec t' ht').2.1
  exact ((hspec t ht).2.2 t' ht' hlt1 hlt2).symm

/-- The set of parameters at which the knot is *vertical* (velocity along `e`) and *bends* (the
orthogonal part of the acceleration is nonzero). -/
def bendSet (K : Knot) (e : R3) : Set ℝ := {t | vertVel K e t = 0 ∧ vertAcc K e t ≠ 0}

/-- At a bending vertical parameter the orthogonal velocity has a simple zero. -/
theorem exists_isolating_of_bend (K : Knot) (e : R3) {t : ℝ} (h0 : vertVel K e t = 0)
    (h1 : vertAcc K e t ≠ 0) :
    ∃ δ > 0, ∀ t', |t' - t| < δ → t' ≠ t → vertVel K e t' ≠ 0 := by
  set v : R3 := vertAcc K e t with hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr h1
  set g : ℝ → ℝ := fun s => inner ℝ (vertVel K e s) (‖v‖⁻¹ • v) with hgdef
  have hgval : g t = 0 := by simp [hgdef, h0]
  have hgder : ∀ s, deriv g s = inner ℝ (vertAcc K e s) (‖v‖⁻¹ • v) := by
    intro s
    have h := deriv_vertVel_inner K e (‖v‖⁻¹ • v) s
    simpa [hgdef] using h
  have hgcont : Continuous g := by
    rw [hgdef]
    exact (continuous_vertVel K e).inner continuous_const
  have hgdiff : Differentiable ℝ g := by
    rw [hgdef]
    exact ((contDiff_vertVel K e).differentiable (by simp)).inner ℝ (differentiable_const _)
  have hf_cont : Continuous (fun s : ℝ => inner ℝ (vertAcc K e s) (‖v‖⁻¹ • v)) :=
    (continuous_vertAcc K e).inner continuous_const
  have hval : inner ℝ (vertAcc K e t) (‖v‖⁻¹ • v) = ‖v‖ := by
    rw [hv, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hcontAt : ContinuousAt (fun s : ℝ => deriv g s) t := by
    have heq : (fun s : ℝ => deriv g s) = fun s => inner ℝ (vertAcc K e s) (‖v‖⁻¹ • v) := by
      funext s; exact hgder s
    rw [heq]
    exact hf_cont.continuousAt
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hcontAt (‖v‖ / 2) (by positivity)
  have hδ' : ∀ x : ℝ, |x - t| < δ → ‖v‖ / 2 < deriv g x := by
    intro x hx
    have h1' := hδ (x := x) (by rw [Real.dist_eq]; exact hx)
    rw [Real.dist_eq, hgder x, hgder t, hval, abs_lt] at h1'
    rw [hgder x]
    linarith [h1'.1]
  refine ⟨δ, hδ0, fun t' hlt hne hzero => ?_⟩
  have hgval' : g t' = 0 := by simp [hgdef, hzero]
  rcases lt_or_gt_of_ne hne with hgt | hlt'
  · obtain ⟨c, hcIoo, hcder⟩ :=
      exists_deriv_eq_slope g hgt hgcont.continuousOn hgdiff.differentiableOn
    have hslope : deriv g c = 0 := by rw [hcder, hgval, hgval', sub_self, zero_div]
    have hclose : |c - t| < δ := by
      have hcomp : |c - t| < |t' - t| := by
        have hct : c - t < 0 := by linarith [hcIoo.2]
        have htt : t' - t < 0 := by linarith [hgt]
        rw [abs_of_neg hct, abs_of_neg htt]
        linarith [hcIoo.1]
      linarith [hlt]
    have := hδ' c hclose
    rw [hslope] at this
    linarith
  · obtain ⟨c, hcIoo, hcder⟩ :=
      exists_deriv_eq_slope g hlt' hgcont.continuousOn hgdiff.differentiableOn
    have hslope : deriv g c = 0 := by rw [hcder, hgval, hgval', sub_self, zero_div]
    have hclose : |c - t| < δ := by
      have hcomp : |c - t| < |t' - t| := by
        have hct : 0 < c - t := by linarith [hcIoo.1]
        have htt : 0 < t' - t := by linarith [hlt']
        rw [abs_of_pos hct, abs_of_pos htt]
        linarith [hcIoo.2]
      linarith [hlt]
    have := hδ' c hclose
    rw [hslope] at this
    linarith

/-- The set of parameters at which the knot is *vertical* (velocity along `e`) and *bends* (the
orthogonal part of the acceleration is nonzero). -/
theorem countable_bendSet (K : Knot) (e : R3) : (bendSet K e).Countable := by
  classical
  refine countable_of_isolated (S := bendSet K e) (fun t ht => ?_)
  obtain ⟨h0, h1⟩ := ht
  obtain ⟨δ, hδ0, hiso⟩ := exists_isolating_of_bend K e h0 h1
  exact ⟨δ, hδ0, fun t' ht' hlt => by
    by_contra hne
    exact hiso t' hlt hne ht'.1⟩

/-! ## The a.e. no-bend statement -/

/-- **Almost every level of the flat height is bend-free at its vertical crossings inside the closed
box.** -/
theorem ae_noBendCrossing (K : Knot) (e : R3) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ t : ℝ, K.curve t ∈ closure (Submission.PBox s c σ) →
        (K.curve t) (σ 2) = c (σ 2) + u → vertVel K e t = 0 → vertAcc K e t = 0 := by
  classical
  set S : Set ℝ := {t : ℝ | bendSet K e t ∧ K.curve t ∈ closure (Submission.PBox s c σ)} with hS
  have hSc : S.Countable := (countable_bendSet K e).mono (fun t ht => ht.1)
  set ph : ℝ → ℝ := fun t => (K.curve t) (σ 2) - c (σ 2) with hph
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure ℝ) (ph '' S) = 0 :=
    (hSc.image ph).measure_zero _
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hnull
  intro u hu
  rw [Set.mem_ofPred_eq] at hu
  push Not at hu
  obtain ⟨t, ht1, ht2, hv, ha⟩ := hu
  exact ⟨t, ⟨⟨hv, ha⟩, ht1⟩, by simp only [hph]; linarith⟩

end

end Work.Drive.Mono
