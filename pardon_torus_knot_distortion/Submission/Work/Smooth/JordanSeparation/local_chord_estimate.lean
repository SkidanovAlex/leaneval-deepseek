import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.deriv_global_norm_bounds
import Submission.Work.Smooth.JordanSeparation.deriv_uniform_continuous
import Submission.Work.Smooth.JordanSeparation.detV_I_mul

/-!
# The local chord estimate

For a `C¹` `2π`-periodic immersion `c : ℝ → ℂ` and a transverse unit field `v` along it, the
oriented area `detV (γ t' - γ t) (v t)` of the **chord** `γ t' - γ t` with the field direction
`v t` is bounded below by a positive multiple of the parameter distance `|t' - t|`, uniformly in
`t`, as long as `|t' - t| ≤ ε` stays small.

This is the elementary linearisation of the curve: writing `γ t' - γ t = (t' - t)·γ' t + ρ`, with
the mean value remainder `‖ρ‖ ≤ (κ·m/4)·|t' - t|` where `m = inf ‖γ'‖ > 0`
(`deriv_global_norm_bounds` for `m`, `deriv_uniform_continuous` for the modulus of the
remainder), and using `κ·m ≤ |detV (γ' t) (v t)|` (`IsTransverseUnitField`), one gets

`|detV (γ t' - γ t) (v t)| ≥ κ·m·|t' - t| - (κ·m/4)·|t' - t| = (3κ·m/4)·|t' - t|`.

The statement is delivered with `μ = κ·m/4`: the remaining term contributes `4μ·|t' - t| ≥ κ·m`
times the distance, while the remainder costs only `μ·|t' - t|`, so `μ` is a valid constant.
Note that the Lipschitz hypothesis on `v` is *not* needed for this direction of the estimate; it
is part of the statement because the sibling statements of the chapter carry it.

The two analytic ingredients are isolated in helpers below:

* `abs_sub_le_abs_sub_of_mem_uIcc` — the elementary interval fact controlling `|x - t|` for `x`
  in the interval spanned by `t` and `t'`;
* `norm_chord_sub_deriv_mul_le` — the mean value bound on the chord remainder
  `γ t' - γ t - (t' - t)·γ' t`.
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

/-- For `x` in the unordered interval spanned by `t` and `t'`, the distance from `x` to `t` is
at most the distance from `t'` to `t`. -/
lemma abs_sub_le_abs_sub_of_mem_uIcc {t t' x : ℝ} (hx : x ∈ Set.uIcc t t') :
    |x - t| ≤ |t' - t| := by
  rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - t),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ t' - t)]
    linarith
  · rw [abs_of_nonpos (by linarith : x - t ≤ 0),
      abs_of_nonpos (by linarith : t' - t ≤ 0)]
    linarith

/-- **Mean value bound for the chord remainder.**  If `γ'` varies by at most `C` on the interval
spanned by `t` and `t'` (i.e. `‖γ' x - γ' t‖ ≤ C` whenever `|x - t| ≤ δ`, with `|t' - t| ≤ δ`),
then the remainder of the first order Taylor expansion of the chord is small:

`‖(γ t' - γ t) - (t' - t)·γ' t‖ ≤ C·|t' - t|`.

This is the mean value inequality applied to `s ↦ γ s - (s - t)·γ' t`, whose derivative is
`s ↦ γ' s - γ' t`, on the interval spanned by `t` and `t'`. -/
lemma norm_chord_sub_deriv_mul_le (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    {t t' δ C : ℝ}
    (hC : ∀ x : ℝ, |x - t| ≤ δ → ‖deriv c.γ x - deriv c.γ t‖ ≤ C)
    (hε : |t' - t| ≤ δ) :
    ‖(c.γ t' - c.γ t) - ((t' - t : ℝ) : ℂ) * deriv c.γ t‖ ≤ C * |t' - t| := by
  have hf : ∀ x ∈ Set.uIcc t t',
      DifferentiableAt ℝ (fun s : ℝ => c.γ s - ((s - t : ℝ) : ℂ) * deriv c.γ t) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => ((y - t : ℝ) : ℂ)) 1 x :=
      HasDerivAt.ofReal_comp ((hasDerivAt_id x).sub_const t)
    have h2 : HasDerivAt (fun y : ℝ => ((y - t : ℝ) : ℂ) * deriv c.γ t)
        (deriv c.γ t) x := by
      simpa using h1.mul_const (deriv c.γ t)
    exact (((c.differentiable.differentiableAt).hasDerivAt).sub h2).differentiableAt
  have hb : ∀ x ∈ Set.uIcc t t',
      ‖deriv (fun s : ℝ => c.γ s - ((s - t : ℝ) : ℂ) * deriv c.γ t) x‖ ≤ C := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => ((y - t : ℝ) : ℂ)) 1 x :=
      HasDerivAt.ofReal_comp ((hasDerivAt_id x).sub_const t)
    have h2 : HasDerivAt (fun y : ℝ => ((y - t : ℝ) : ℂ) * deriv c.γ t)
        (deriv c.γ t) x := by
      simpa using h1.mul_const (deriv c.γ t)
    have h3 : HasDerivAt (fun s : ℝ => c.γ s - ((s - t : ℝ) : ℂ) * deriv c.γ t)
        (deriv c.γ x - deriv c.γ t) x :=
      ((c.differentiable.differentiableAt).hasDerivAt).sub h2
    rw [h3.deriv]
    exact hC x (le_trans (abs_sub_le_abs_sub_of_mem_uIcc hx) hε)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) hf hb (convex_uIcc t t')
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs] at hmvt
  have h0 : ((t - t : ℝ) : ℂ) = 0 := by simp
  rwa [show c.γ t' - ((t' - t : ℝ) : ℂ) * deriv c.γ t
        - (c.γ t - ((t - t : ℝ) : ℂ) * deriv c.γ t)
      = c.γ t' - c.γ t - ((t' - t : ℝ) : ℂ) * deriv c.γ t from by
    rw [h0, zero_mul, sub_zero]; abel] at hmvt

theorem local_chord_estimate (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (himm : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c)
    {v : ℝ → ℂ} {κ L : ℝ} (hκ : 0 < κ) (hL : 0 < L)
    (htrans : Work.Smooth.JordanSeparation.IsTransverseUnitField c κ v)
    (hlip : Work.Smooth.JordanSeparation.IsLipschitzField L v) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ μ : ℝ, 0 < μ ∧
      ∀ t t' : ℝ, 0 < |t' - t| → |t' - t| ≤ ε →
        μ * |t' - t| ≤ |Work.Smooth.JordanSeparation.detV (c.γ t' - c.γ t) (v t)| := by
  -- `m > 0` bounds `‖γ'‖` from below, and `γ'` is uniformly continuous.
  obtain ⟨m, M, hm, hM, hlow, hhigh⟩ := deriv_global_norm_bounds c himm
  obtain ⟨δ, hδpos, hδ⟩ := deriv_uniform_continuous c (κ * m / 4) (by positivity)
  refine ⟨δ, hδpos, κ * m / 4, by positivity, ?_⟩
  intro t t' _htne hle
  -- the mean value remainder of the chord
  set rem : ℂ := (c.γ t' - c.γ t) - ((t' - t : ℝ) : ℂ) * deriv c.γ t with hremdef
  have hC : ∀ x : ℝ, |x - t| ≤ δ → ‖deriv c.γ x - deriv c.γ t‖ ≤ κ * m / 4 :=
    fun x hx => hδ x t hx
  have hrem : ‖rem‖ ≤ κ * m / 4 * |t' - t| := by
    rw [hremdef]
    exact norm_chord_sub_deriv_mul_le c hC hle
  have hdecomp : c.γ t' - c.γ t = rem + ((t' - t : ℝ) : ℂ) * deriv c.γ t := by
    rw [hremdef]
    ring
  -- the remainder is small against the transverse unit field
  have hA : |detV rem (v t)| ≤ κ * m / 4 * |t' - t| := by
    have h := abs_detV_le rem (v t)
    rw [htrans.1 t, mul_one] at h
    exact le_trans h hrem
  -- the leading term `(t' - t)·detV (γ' t) (v t)` is large, by transversality
  have hDbound : κ * m ≤ |detV (deriv c.γ t) (v t)| :=
    le_trans (mul_le_mul_of_nonneg_left (hlow t) hκ.le) (htrans.2 t)
  have hB : κ * m * |t' - t| ≤ |(t' - t) * detV (deriv c.γ t) (v t)| := by
    calc κ * m * |t' - t| = |t' - t| * (κ * m) := by ring
      _ ≤ |t' - t| * |detV (deriv c.γ t) (v t)| :=
          mul_le_mul_of_nonneg_left hDbound (abs_nonneg _)
      _ = |(t' - t) * detV (deriv c.γ t) (v t)| := by rw [abs_mul]
  -- reverse triangle inequality
  have htri : |(t' - t) * detV (deriv c.γ t) (v t)| - |detV rem (v t)| ≤
      |detV rem (v t) + (t' - t) * detV (deriv c.γ t) (v t)| := by
    have h := norm_sub_le (detV rem (v t) + (t' - t) * detV (deriv c.γ t) (v t))
      (detV rem (v t))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h
    have hsub : (detV rem (v t) + (t' - t) * detV (deriv c.γ t) (v t)) - detV rem (v t)
        = (t' - t) * detV (deriv c.γ t) (v t) := by ring
    rw [hsub] at h
    linarith
  have hdet : detV (c.γ t' - c.γ t) (v t)
      = detV rem (v t) + (t' - t) * detV (deriv c.γ t) (v t) := by
    rw [hdecomp, detV_add_left, detV_smul_left]
  rw [hdet]
  -- `μ·|t' - t| = (κ·m/4)·|t' - t| = κ·m·|t' - t| - 3(κ·m/4)·|t' - t|`
  have hstep : κ * m / 4 * |t' - t| ≤ κ * m * |t' - t| - κ * m / 4 * |t' - t| := by
    nlinarith [mul_nonneg (mul_pos hκ hm).le (abs_nonneg (t' - t))]
  calc κ * m / 4 * |t' - t|
      ≤ κ * m * |t' - t| - κ * m / 4 * |t' - t| := hstep
    _ ≤ |(t' - t) * detV (deriv c.γ t) (v t)| - |detV rem (v t)| := by linarith [hB, hA]
    _ ≤ |detV rem (v t) + (t' - t) * detV (deriv c.γ t) (v t)| := htri

end

end Work.Smooth.JordanSeparation
