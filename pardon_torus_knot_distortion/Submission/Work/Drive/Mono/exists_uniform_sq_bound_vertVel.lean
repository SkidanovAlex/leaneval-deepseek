import Mathlib
import Submission.Work.Drive.Mono.NoBend

/-!
# The orthogonal velocity is quadratic at a bend-free vertical parameter, uniformly

Fix a unit direction `e` and write

* `vertVel K e t = perpProj e (deriv K.curve t)` for the component of the velocity of `K`
  orthogonal to `e` (the knot is *vertical* at `t` when this vanishes), and
* `vertAcc K e t = perpProj e (deriv (deriv K.curve) t)` for the corresponding component of the
  acceleration (the knot *bends* at `t` when this does not vanish),

as in `Submission/Work/Drive/Mono/NoBend.lean`.

At a parameter `t₀` which is both vertical and bend-free, the function `w = vertVel K e` satisfies
`w t₀ = 0` and `w' t₀ = 0`; a double zero.  This file proves that such a double zero of `w` is
*uniformly* quadratic: there are constants `C, δ > 0`, depending only on `K` and `e`, such that
`‖w t‖ ≤ C (t - t₀)²` whenever `|t - t₀| ≤ δ`, simultaneously for every such `t₀`.

The mathematics is the mean value inequality applied twice, together with the fact that the knot is
periodic with period `2π`: `w'' = perpProj e ∘ K.curve'''` is continuous and periodic, hence
bounded on all of `ℝ` by a constant `M` obtained from the compact fundamental interval `[0, 2π]`,
and then

`‖w t‖ ≤ M (t - t₀)²`

for every `t` (the parameter `δ` is irrelevant, any positive value works).  No uniformity in `t₀`
has to be assumed: periodicity is exactly what makes the bound global.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open scoped RealInnerProductSpace

noncomputable section

namespace VertVelBound

/-! ## Periodicity and the chain rule for the orthogonal projection -/

/-- The derivative of a periodic function (on `ℝ`) is periodic with the same period. -/
theorem periodic_deriv {f : ℝ → R3} {c : ℝ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  have h1 := deriv_comp_add_const f c x
  rw [Function.Periodic.funext h] at h1
  exact h1.symm

/-- Chain rule for a continuous linear map preceded by a differentiable curve: the derivative of
`s ↦ L (f s)` is `L` applied to the derivative of `f`. -/
theorem deriv_clm_comp (L : R3 →L[ℝ] R3) {f : ℝ → R3} (hf : Differentiable ℝ f) (t : ℝ) :
    deriv (fun s => L (f s)) t = L (deriv f t) := by
  have h1 : HasDerivAt f (deriv f t) t := (hf t).hasDerivAt
  have h2 : HasFDerivAt (fun x : R3 => L x) L (f t) := L.hasFDerivAt
  exact (HasFDerivAt.comp_hasDerivAt (x := t) h2 h1).deriv

/-- The derivative of `s ↦ perpProj e (f s)` is `perpProj e` applied to the derivative of `f`. -/
theorem deriv_perpProj_comp (e : R3) {f : ℝ → R3} (hf : Differentiable ℝ f) (t : ℝ) :
    deriv (fun s => perpProj e (f s)) t = perpProj e (deriv f t) := by
  have hL : (fun s : ℝ => perpProj e (f s)) = fun s => perpProjCLM e (f s) := by
    funext s; rw [perpProjCLM_apply]
  rw [hL, deriv_clm_comp (perpProjCLM e) hf t, perpProjCLM_apply]

/-! ## Two mean value estimates

If the second derivative of `w` is bounded by `M` and `deriv w` vanishes at an endpoint, then
`w` moves by at most `M (b - a)²` across `[a, b]`. -/

/-- Mean value estimate with the vanishing of `deriv w` at the **left** endpoint. -/
theorem norm_sub_le_sq_of_deriv_eq_zero_left {w : ℝ → R3} (hw : Differentiable ℝ w)
    (hd : Differentiable ℝ (deriv w)) {M : ℝ} (hM : ∀ x, ‖deriv (deriv w) x‖ ≤ M)
    {a b : ℝ} (hab : a ≤ b) (h0 : deriv w a = 0) :
    ‖w b - w a‖ ≤ M * (b - a) ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hbd : ∀ x ∈ Set.Icc a b, ‖deriv w x‖ ≤ M * (b - a) := by
    intro x hx
    have hax : a ≤ x := hx.1
    have hxb : x ≤ b := hx.2
    have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv w) (s := Set.Icc a x)
      (C := M) (fun y _ => hd y) (fun y _ => hM y) (convex_Icc a x)
      (Set.left_mem_Icc.mpr hax) (Set.right_mem_Icc.mpr hax)
    simp only [h0, sub_zero, Real.norm_eq_abs] at key
    calc ‖deriv w x‖ ≤ M * |x - a| := key
      _ = M * (x - a) := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - a)]
      _ ≤ M * (b - a) := mul_le_mul_of_nonneg_left (by linarith) hM0
  have key2 := Convex.norm_image_sub_le_of_norm_deriv_le (f := w) (s := Set.Icc a b)
    (C := M * (b - a)) (fun x _ => hw x) hbd (convex_Icc a b)
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at key2
  calc ‖w b - w a‖ ≤ (M * (b - a)) * (b - a) := key2
    _ = M * (b - a) ^ 2 := by ring

/-- Mean value estimate with the vanishing of `deriv w` at the **right** endpoint. -/
theorem norm_sub_le_sq_of_deriv_eq_zero_right {w : ℝ → R3} (hw : Differentiable ℝ w)
    (hd : Differentiable ℝ (deriv w)) {M : ℝ} (hM : ∀ x, ‖deriv (deriv w) x‖ ≤ M)
    {a b : ℝ} (hab : a ≤ b) (h0 : deriv w b = 0) :
    ‖w b - w a‖ ≤ M * (b - a) ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hbd : ∀ x ∈ Set.Icc a b, ‖deriv w x‖ ≤ M * (b - a) := by
    intro x hx
    have hax : a ≤ x := hx.1
    have hxb : x ≤ b := hx.2
    have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv w) (s := Set.Icc x b)
      (C := M) (fun y _ => hd y) (fun y _ => hM y) (convex_Icc x b)
      (Set.right_mem_Icc.mpr hxb) (Set.left_mem_Icc.mpr hxb)
    simp only [h0, sub_zero, Real.norm_eq_abs] at key
    calc ‖deriv w x‖ ≤ M * |x - b| := key
      _ = M * (b - x) := by rw [abs_of_nonpos (by linarith : x - b ≤ 0)]; ring
      _ ≤ M * (b - a) := mul_le_mul_of_nonneg_left (by linarith) hM0
  have key2 := Convex.norm_image_sub_le_of_norm_deriv_le (f := w) (s := Set.Icc a b)
    (C := M * (b - a)) (fun x _ => hw x) hbd (convex_Icc a b)
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at key2
  calc ‖w b - w a‖ ≤ (M * (b - a)) * (b - a) := key2
    _ = M * (b - a) ^ 2 := by ring

/-- **A double zero of a function with bounded second derivative is quadratic, with the bound
`M` on the whole line.** -/
theorem norm_le_sq_of_double_zero {w : ℝ → R3} (hw : Differentiable ℝ w)
    (hd : Differentiable ℝ (deriv w)) {M : ℝ} (hM : ∀ x, ‖deriv (deriv w) x‖ ≤ M)
    {t₀ : ℝ} (h0 : w t₀ = 0) (h0' : deriv w t₀ = 0) (t : ℝ) :
    ‖w t‖ ≤ M * (t - t₀) ^ 2 := by
  rcases le_total t₀ t with hle | hle
  · have key := norm_sub_le_sq_of_deriv_eq_zero_left hw hd hM hle h0'
    rw [h0, sub_zero] at key
    exact key
  · have key := norm_sub_le_sq_of_deriv_eq_zero_right hw hd hM hle h0'
    rw [h0, zero_sub, norm_neg] at key
    have hs : (t₀ - t) ^ 2 = (t - t₀) ^ 2 := by ring
    rwa [hs] at key

end VertVelBound

open LeanEval.KnotTheory.PardonDistortion in
open scoped RealInnerProductSpace in
/-- At every vertical bend-free parameter the orthogonal velocity of the knot is quadratic, with constants uniform in the parameter. -/
theorem exists_uniform_sq_bound_vertVel (K : Knot) (e : R3) (he : ‖e‖ = 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t₀ : ℝ, Work.Drive.Mono.vertVel K e t₀ = 0 →
      Work.Drive.Mono.vertAcc K e t₀ = 0 →
      ∀ t : ℝ, |t - t₀| ≤ δ → ‖Work.Drive.Mono.vertVel K e t‖ ≤ C * (t - t₀) ^ 2 := by
  classical
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  -- the velocity and its derivatives are periodic with period `2π`
  have hperV : Function.Periodic (deriv K.curve) (2 * Real.pi) :=
    VertVelBound.periodic_deriv K.periodic
  have hperW : Function.Periodic (vertVel K e) (2 * Real.pi) := hperV.comp (perpProj e)
  have hperDD : Function.Periodic (deriv (deriv (vertVel K e))) (2 * Real.pi) :=
    VertVelBound.periodic_deriv (VertVelBound.periodic_deriv hperW)
  -- `deriv vertAcc` is `perpProj e` applied to the third derivative of the curve
  have hacc_form : ∀ t : ℝ,
      deriv (vertAcc K e) t = perpProj e (deriv (deriv (deriv K.curve)) t) := by
    intro t
    have hf : Differentiable ℝ (deriv (deriv K.curve)) :=
      (contDiff_deriv2_curve K).differentiable (by simp)
    show deriv (fun s : ℝ => perpProj e (deriv (deriv K.curve) s)) t
        = perpProj e (deriv (deriv (deriv K.curve)) t)
    exact VertVelBound.deriv_perpProj_comp e hf t
  have hcont3 : Continuous (fun t : ℝ => perpProj e (deriv (deriv (deriv K.curve)) t)) :=
    ((contDiff_perpProj e).comp (ContDiff.iterate_deriv 3 K.smooth)).continuous
  have hcontDD : Continuous (fun t : ℝ => deriv (deriv (vertVel K e)) t) := by
    have hfun : (fun t : ℝ => deriv (deriv (vertVel K e)) t)
        = fun t => perpProj e (deriv (deriv (deriv K.curve)) t) := by
      funext t
      rw [show deriv (deriv (vertVel K e)) = deriv (vertAcc K e) from by
        rw [show deriv (vertVel K e) = vertAcc K e from funext (deriv_vertVel K e)]]
      exact hacc_form t
    rw [hfun]
    exact hcont3
  -- a bound for the second derivative of the velocity on the compact fundamental period
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontDD.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  -- which, by periodicity, is a global bound
  have hMglob : ∀ x : ℝ, ‖deriv (deriv (vertVel K e)) x‖ ≤ M := by
    intro x
    have hred : toIcoMod hpi 0 x ∈ Set.Icc 0 (2 * Real.pi) := by
      have hmem := toIcoMod_mem_Ico hpi 0 x
      rw [zero_add] at hmem
      exact Set.Ico_subset_Icc_self hmem
    have hshift : deriv (deriv (vertVel K e)) x
        = deriv (deriv (vertVel K e)) (toIcoMod hpi 0 x) := by
      have h := hperDD.zsmul (toIcoDiv hpi 0 x) (toIcoMod hpi 0 x)
      rwa [toIcoMod_add_toIcoDiv_zsmul] at h
    rw [hshift]
    exact le_trans (hM₀ _ hred) (le_max_left _ _)
  have hWdiff : Differentiable ℝ (vertVel K e) := (contDiff_vertVel K e).differentiable (by simp)
  have hDdiff : Differentiable ℝ (deriv (vertVel K e)) := by
    rw [show deriv (vertVel K e) = vertAcc K e from funext (deriv_vertVel K e)]
    exact (contDiff_vertAcc K e).differentiable (by simp)
  refine ⟨max M 1, 1, lt_of_lt_of_le zero_lt_one (le_max_right M 1), one_pos, ?_⟩
  intro t₀ h0 h1 t ht
  have h1' : deriv (vertVel K e) t₀ = 0 := by rw [deriv_vertVel K e t₀]; exact h1
  have hkey := VertVelBound.norm_le_sq_of_double_zero hWdiff hDdiff hMglob h0 h1' t
  calc ‖vertVel K e t‖ ≤ M * (t - t₀) ^ 2 := hkey
    _ ≤ max M 1 * (t - t₀) ^ 2 := mul_le_mul_of_nonneg_right (le_max_left M 1) (sq_nonneg _)

end

end Work.Drive.Mono
