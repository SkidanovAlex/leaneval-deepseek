/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `C^{1,α}` bounds for the first order coefficients of a `C^{2,α}` function

Let `P` be the polydisc of radius `R > 0` about the origin in `ℂⁿ` and let `u : ℂⁿ → ℂ` be
smooth on `P` with

  `holderNorm 2 α u P ≤ ofReal b`,  `0 < α < 1`, `0 ≤ b`.

This file proves that the four families of first order coefficients of `u`,

* `z ↦ fderiv ℝ u z (e_p)` and `z ↦ fderiv ℝ u z (i e_p)` (the coordinate partial derivatives), and
* the Wirtinger derivatives `∂_p u` and `∂̄_p u`,

all have `C^{1,α}`-norm on `P` bounded by `ofReal (8 b)`.

The mechanism is the following.  The `C^{2,α}` bound on `u` gives, on `P`,

* `‖fderiv ℝ u z‖ ≤ b` (order `1` sup bound),
* `‖iteratedFDeriv ℝ 2 u z‖ = ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ b` (order `2` sup bound),
* `‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ b ‖x - y‖ ^ α` (order `2` Hölder
  seminorm),

so the coefficient function `z ↦ fderiv ℝ u z v` (`‖v‖ ≤ 1`) has value, first derivative and
modulus of continuity of the first derivative all bounded by `b`; the general `C^{1,α}` bound
`3 b + 4 b + b = 8 b` of `holderNorm_one_le_of_isC1aData` below then applies.  The
Wirtinger derivatives are `(1/2)`-combinations of two such coefficient functions, and the
pointwise data (hence the `8 b` bound) is preserved by such combinations because the
coefficients satisfy `‖1/2‖ + ‖±i/2‖ = 1`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Newton

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Convexity of the polydisc -/

lemma convex_polydisc_zero {n : ℕ} (r : Fin n → ℝ) :
    Convex ℝ (Work.CR.Flat.polydisc (0 : Fin n → ℂ) r) := by
  have h : Work.CR.Flat.polydisc (0 : Fin n → ℂ) r
      = Set.pi Set.univ (fun j : Fin n => Metric.ball (0 : ℂ) (r j)) := by
    ext z
    simp [Work.CR.Flat.polydisc, Metric.mem_ball, dist_eq_norm]
  rw [h]
  exact convex_pi fun j _ => convex_ball 0 (r j)

/-! ## (A) The derivative of a coefficient function `z ↦ fderiv ℝ u z v` -/

/-- The norm of the difference of two first iterated derivatives equals the norm of the
difference of the corresponding Fréchet derivatives (general codomain version of
`Work.NN.Core.Lev.norm_iteratedFDeriv_one_sub_eq_gen`). -/
lemma norm_iteratedFDeriv_one_sub_eq_gen' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : X → F) (x y : X) :
    ‖iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y‖ = ‖fderiv ℝ u x - fderiv ℝ u y‖ := by
  have key : ∀ z : X, continuousMultilinearCurryFin1 ℝ X F (iteratedFDeriv ℝ 1 u z)
      = fderiv ℝ u z := by
    intro z
    ext v
    rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    simp
  have hx : iteratedFDeriv ℝ 1 u x
      = (continuousMultilinearCurryFin1 ℝ X F).symm (fderiv ℝ u x) := by
    rw [← key x, LinearIsometryEquiv.symm_apply_apply]
  have hy : iteratedFDeriv ℝ 1 u y
      = (continuousMultilinearCurryFin1 ℝ X F).symm (fderiv ℝ u y) := by
    rw [← key y, LinearIsometryEquiv.symm_apply_apply]
  rw [hx, hy, ← map_sub, LinearIsometryEquiv.norm_map]

/-- The operator norm of the second derivative is the operator norm of the second multilinear
derivative. -/
lemma norm_fderiv_fderiv_eq_iteratedFDeriv_two (u : X → ℂ) (x : X) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ = ‖iteratedFDeriv ℝ 2 u x‖ := by
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (x := x) (f := fderiv ℝ u)]
  exact norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1) (f := u) (x := x)

/-- Difference version of `norm_fderiv_fderiv_eq_iteratedFDeriv_two`. -/
lemma norm_fderiv_fderiv_sub_eq_iteratedFDeriv_two (u : X → ℂ) (x y : X) :
    ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖
      = ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ := by
  rw [← norm_iteratedFDeriv_one_sub_eq_gen' (fderiv ℝ u) x y]
  have key : ∀ z : X, iteratedFDeriv ℝ 2 u z
      = (continuousMultilinearCurryRightEquiv' ℝ 1 X ℂ).symm
          (iteratedFDeriv ℝ 1 (fderiv ℝ u) z) := by
    intro z
    simpa using (iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := u) (x := z) (n := 1))
  have hsub : iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y
      = (continuousMultilinearCurryRightEquiv' ℝ 1 X ℂ).symm
          (iteratedFDeriv ℝ 1 (fderiv ℝ u) x - iteratedFDeriv ℝ 1 (fderiv ℝ u) y) := by
    rw [key x, key y]
    exact (LinearIsometryEquiv.map_sub _ _ _).symm
  rw [hsub, LinearIsometryEquiv.norm_map]

/-- Multiplication of a continuous linear map by a complex scalar. -/
lemma norm_smul_clm_le (a : ℂ) (L : X →L[ℝ] ℂ) : ‖a • L‖ ≤ ‖a‖ * ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [smul_apply, smul_eq_mul, norm_mul]
  calc ‖a‖ * ‖L v‖ ≤ ‖a‖ * (‖L‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (L.le_opNorm v) (norm_nonneg a)
    _ = ‖a‖ * ‖L‖ * ‖v‖ := by ring

/-- The evaluation `L ↦ L v` is a linear contraction for `‖v‖ ≤ 1`. -/
lemma norm_apply_clm_le (v : X) : ‖ContinuousLinearMap.apply ℝ ℂ v‖ ≤ ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun L => ?_
  rw [ContinuousLinearMap.apply_apply]
  calc ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
    _ = ‖v‖ * ‖L‖ := by ring

/-- The coefficient function `z ↦ fderiv ℝ u z v` is differentiable as soon as `fderiv ℝ u` is,
and its derivative is the evaluation of the second derivative. -/
lemma hasFDerivAt_fderiv_apply (u : X → ℂ) {x : X}
    (h : DifferentiableAt ℝ (fderiv ℝ u) x) (v : X) :
    HasFDerivAt (fun z => fderiv ℝ u z v)
      ((ContinuousLinearMap.apply ℝ ℂ v) ∘SL (fderiv ℝ (fderiv ℝ u) x)) x := by
  exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℂ v)).comp x h.hasFDerivAt

/-- Norm bound for the derivative of a coefficient function. -/
lemma norm_fderiv_fderiv_apply_le (u : X → ℂ) {x : X}
    (h : DifferentiableAt ℝ (fderiv ℝ u) x) (v : X) :
    ‖fderiv ℝ (fun z => fderiv ℝ u z v) x‖
      ≤ ‖v‖ * ‖fderiv ℝ (fderiv ℝ u) x‖ := by
  rw [(hasFDerivAt_fderiv_apply u h v).fderiv]
  calc ‖(ContinuousLinearMap.apply ℝ ℂ v) ∘SL fderiv ℝ (fderiv ℝ u) x‖
        ≤ ‖ContinuousLinearMap.apply ℝ ℂ v‖ * ‖fderiv ℝ (fderiv ℝ u) x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖v‖ * ‖fderiv ℝ (fderiv ℝ u) x‖ :=
          mul_le_mul_of_nonneg_right (norm_apply_clm_le v) (by positivity)

/-- Difference version of `norm_fderiv_fderiv_apply_le`. -/
lemma norm_fderiv_fderiv_apply_sub_le (u : X → ℂ) {x y : X}
    (hx : DifferentiableAt ℝ (fderiv ℝ u) x) (hy : DifferentiableAt ℝ (fderiv ℝ u) y)
    (v : X) :
    ‖fderiv ℝ (fun z => fderiv ℝ u z v) x - fderiv ℝ (fun z => fderiv ℝ u z v) y‖
      ≤ ‖v‖ * ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ := by
  rw [(hasFDerivAt_fderiv_apply u hx v).fderiv, (hasFDerivAt_fderiv_apply u hy v).fderiv,
    ← ContinuousLinearMap.comp_sub]
  calc ‖(ContinuousLinearMap.apply ℝ ℂ v)
          ∘SL (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y)‖
        ≤ ‖ContinuousLinearMap.apply ℝ ℂ v‖
            * ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖v‖ * ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ :=
          mul_le_mul_of_nonneg_right (norm_apply_clm_le v) (by positivity)

/-! ## (B) Pointwise data and the resulting `C^{1,α}` bound -/

/-- Pointwise data on a set guaranteeing the `C^{1,α}` bound `8 b` for a complex valued
function: the function is differentiable on the set, and its value, its derivative and the
modulus of continuity of its derivative are all bounded by `b`. -/
structure IsC1aData (Ω : Set X) (α b : ℝ) (g : X → ℂ) : Prop where
  diff : ∀ x ∈ Ω, DifferentiableAt ℝ g x
  bound : ∀ x ∈ Ω, ‖g x‖ ≤ b
  derivNorm : ∀ x ∈ Ω, ‖fderiv ℝ g x‖ ≤ b
  derivHold : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ b * ‖x - y‖ ^ α

/-- Pointwise data gives the `C^{1,α}` bound, with constant `3 b + 4 b + b = 8 b`.  The four
contributions are the sup bounds (`b` at order `0` and `b` at order `1`) and the two Hölder
seminorms, each bounded by `2 b + b` (`2 b` from the sup bound and `b` from the derivative
bound). -/
lemma holderNorm_one_le_of_isC1aData {Ω : Set X} {α b : ℝ} (hΩ : IsOpen Ω)
    (hconv : Convex ℝ Ω) (hα0 : 0 < α) (hα1 : α < 1) (hb0 : 0 ≤ b) {g : X → ℂ}
    (h : IsC1aData Ω α b g) :
    Work.CR.Flat.holderNorm 1 α g Ω ≤ ENNReal.ofReal (8 * b) := by
  -- order `0`: sup bound
  have hiter0 : Work.CR.Flat.iterDerivNorm 0 g Ω ≤ ENNReal.ofReal b := by
    refine iSup₂_le fun x hx => ?_
    rw [norm_iteratedFDerivWithin_zero]
    exact ENNReal.ofReal_le_ofReal (h.bound x hx)
  -- order `1`: sup bound
  have hiter1 : Work.CR.Flat.iterDerivNorm 1 g Ω ≤ ENNReal.ofReal b := by
    refine iSup₂_le fun x hx => ?_
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := g) 1 hΩ hx,
      norm_iteratedFDeriv_one]
    exact ENNReal.ofReal_le_ofReal (h.derivNorm x hx)
  -- order `0`: Hölder seminorm
  have hsem0 : Work.CR.Flat.holderSeminorm 0 α g Ω ≤ ENNReal.ofReal (2 * b + b) := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [Work.NN.Core.Lev.norm_iteratedFDerivWithin_zero_sub_eq g Ω x y]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmvt : ‖g x - g y‖ ≤ b * ‖x - y‖ := by
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) h.diff h.derivNorm hconv hy hx
      simpa only [norm_sub_rev] using this
    have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have ha : 0 ≤ ‖g x - g y‖ := norm_nonneg _
    by_cases hd : ‖x - y‖ ≤ 1
    · have hdα : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
        have h2' : ‖x - y‖ ^ (1 : ℝ) ≤ ‖x - y‖ ^ α :=
          Real.rpow_le_rpow_of_exponent_ge hdpos hd hα1.le
        rwa [Real.rpow_one] at h2'
      have hdαpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hdpos α
      rw [div_le_iff₀ hdαpos]
      calc ‖g x - g y‖ ≤ b * ‖x - y‖ := hmvt
        _ ≤ b * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hdα hb0
        _ ≤ (2 * b + b) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hdαpos)
    · have h1d : 1 ≤ ‖x - y‖ := le_of_lt (not_le.mp hd)
      have hdα1 : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow h1d hα0.le
      have h2' : ‖g x - g y‖ ≤ 2 * b := by
        calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
          _ ≤ b + b := add_le_add (h.bound x hx) (h.bound y hy)
          _ = 2 * b := by ring
      calc ‖g x - g y‖ / ‖x - y‖ ^ α ≤ ‖g x - g y‖ / 1 :=
            div_le_div_of_nonneg_left ha one_pos hdα1
        _ = ‖g x - g y‖ := by rw [div_one]
        _ ≤ 2 * b := h2'
        _ ≤ 2 * b + b := by linarith
  -- order `1`: Hölder seminorm
  have hsem1 : Work.CR.Flat.holderSeminorm 1 α g Ω ≤ ENNReal.ofReal (2 * b + b) := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [Work.NN.Core.Lev.norm_iteratedFDerivWithin_one_sub_eq hΩ g hx hy]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hdαpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hdpos α
    rw [div_le_iff₀ hdαpos]
    calc ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ b * ‖x - y‖ ^ α := h.derivHold x hx y hy
      _ ≤ (2 * b + b) * ‖x - y‖ ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hdαpos)
  -- assembly
  have hsum : Work.CR.Flat.holderNorm 1 α g Ω
      = (Work.CR.Flat.iterDerivNorm 0 g Ω + Work.CR.Flat.holderSeminorm 0 α g Ω)
        + (Work.CR.Flat.iterDerivNorm 1 g Ω + Work.CR.Flat.holderSeminorm 1 α g Ω) := by
    simp [Work.CR.Flat.holderNorm, Finset.sum_range_succ]
  rw [hsum]
  refine le_trans (add_le_add (add_le_add hiter0 hsem0) (add_le_add hiter1 hsem1)) ?_
  have hA : ENNReal.ofReal b + ENNReal.ofReal (2 * b + b)
      = ENNReal.ofReal (b + (2 * b + b)) :=
    (ENNReal.ofReal_add hb0 (by linarith)).symm
  have hC : ENNReal.ofReal (b + (2 * b + b)) + ENNReal.ofReal (b + (2 * b + b))
      = ENNReal.ofReal ((b + (2 * b + b)) + (b + (2 * b + b))) :=
    (ENNReal.ofReal_add (by linarith) (by linarith)).symm
  have hchain : ENNReal.ofReal b + ENNReal.ofReal (2 * b + b)
        + (ENNReal.ofReal b + ENNReal.ofReal (2 * b + b))
      = ENNReal.ofReal (8 * b) := by
    rw [hA, hC]
    congr 1
    ring
  exact le_of_eq hchain

/-- Derivative of a combination of two functions. -/
lemma fderiv_const_mul_add_const_mul {g₁ g₂ : X → ℂ} {a c : ℂ} {x : X}
    (h₁ : DifferentiableAt ℝ g₁ x) (h₂ : DifferentiableAt ℝ g₂ x) :
    fderiv ℝ (fun z => a * g₁ z + c * g₂ z) x = a • fderiv ℝ g₁ x + c • fderiv ℝ g₂ x := by
  rw [show (fun z => a * g₁ z + c * g₂ z) = (fun z => a * g₁ z) + (fun z => c * g₂ z) from rfl,
    fderiv_add (h₁.const_mul a) (h₂.const_mul c), fderiv_const_mul h₁ a,
    fderiv_const_mul h₂ c]

/-- Pointwise data is stable under complex linear combinations whose coefficient norms sum to at
most `1`. -/
lemma IsC1aData.const_mul_add {Ω : Set X} {α b : ℝ} (hb0 : 0 ≤ b) {g₁ g₂ : X → ℂ} {a c : ℂ}
    (hac : ‖a‖ + ‖c‖ ≤ 1) (h₁ : IsC1aData Ω α b g₁) (h₂ : IsC1aData Ω α b g₂) :
    IsC1aData Ω α b (fun z => a * g₁ z + c * g₂ z) where
  diff x hx := by
    have hA : DifferentiableAt ℝ (fun y => a * g₁ y) x := (h₁.diff x hx).const_mul a
    have hB : DifferentiableAt ℝ (fun y => c * g₂ y) x := (h₂.diff x hx).const_mul c
    exact hA.add hB
  bound x hx := by
    have hle : ‖a * g₁ x + c * g₂ x‖ ≤ (‖a‖ + ‖c‖) * b := by
      calc ‖a * g₁ x + c * g₂ x‖ ≤ ‖a * g₁ x‖ + ‖c * g₂ x‖ := norm_add_le _ _
        _ = ‖a‖ * ‖g₁ x‖ + ‖c‖ * ‖g₂ x‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖a‖ * b + ‖c‖ * b :=
            add_le_add (mul_le_mul_of_nonneg_left (h₁.bound x hx) (norm_nonneg a))
              (mul_le_mul_of_nonneg_left (h₂.bound x hx) (norm_nonneg c))
        _ = (‖a‖ + ‖c‖) * b := by ring
    calc ‖a * g₁ x + c * g₂ x‖ ≤ (‖a‖ + ‖c‖) * b := hle
      _ ≤ 1 * b := mul_le_mul_of_nonneg_right hac hb0
      _ = b := by ring
  derivNorm x hx := by
    rw [fderiv_const_mul_add_const_mul (h₁.diff x hx) (h₂.diff x hx)]
    calc ‖a • fderiv ℝ g₁ x + c • fderiv ℝ g₂ x‖
        ≤ ‖a • fderiv ℝ g₁ x‖ + ‖c • fderiv ℝ g₂ x‖ := norm_add_le _ _
      _ ≤ ‖a‖ * ‖fderiv ℝ g₁ x‖ + ‖c‖ * ‖fderiv ℝ g₂ x‖ :=
          add_le_add (norm_smul_clm_le a _) (norm_smul_clm_le c _)
      _ ≤ ‖a‖ * b + ‖c‖ * b :=
          add_le_add (mul_le_mul_of_nonneg_left (h₁.derivNorm x hx) (norm_nonneg a))
            (mul_le_mul_of_nonneg_left (h₂.derivNorm x hx) (norm_nonneg c))
      _ = (‖a‖ + ‖c‖) * b := by ring
      _ ≤ 1 * b := mul_le_mul_of_nonneg_right hac hb0
      _ = b := by ring
  derivHold x hx y hy := by
    rw [fderiv_const_mul_add_const_mul (h₁.diff x hx) (h₂.diff x hx),
      fderiv_const_mul_add_const_mul (h₁.diff y hy) (h₂.diff y hy)]
    have hD : a • fderiv ℝ g₁ x + c • fderiv ℝ g₂ x
          - (a • fderiv ℝ g₁ y + c • fderiv ℝ g₂ y)
        = a • (fderiv ℝ g₁ x - fderiv ℝ g₁ y)
          + c • (fderiv ℝ g₂ x - fderiv ℝ g₂ y) := by
      rw [add_sub_add_comm]
      ext w
      simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
      ring
    rw [hD]
    have ht : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    calc ‖a • (fderiv ℝ g₁ x - fderiv ℝ g₁ y)
            + c • (fderiv ℝ g₂ x - fderiv ℝ g₂ y)‖
        ≤ ‖a • (fderiv ℝ g₁ x - fderiv ℝ g₁ y)‖
            + ‖c • (fderiv ℝ g₂ x - fderiv ℝ g₂ y)‖ := norm_add_le _ _
      _ ≤ ‖a‖ * ‖fderiv ℝ g₁ x - fderiv ℝ g₁ y‖
            + ‖c‖ * ‖fderiv ℝ g₂ x - fderiv ℝ g₂ y‖ :=
          add_le_add (norm_smul_clm_le a _) (norm_smul_clm_le c _)
      _ ≤ ‖a‖ * (b * ‖x - y‖ ^ α) + ‖c‖ * (b * ‖x - y‖ ^ α) :=
          add_le_add (mul_le_mul_of_nonneg_left (h₁.derivHold x hx y hy) (norm_nonneg a))
            (mul_le_mul_of_nonneg_left (h₂.derivHold x hx y hy) (norm_nonneg c))
      _ = (‖a‖ + ‖c‖) * (b * ‖x - y‖ ^ α) := by ring
      _ ≤ 1 * (b * ‖x - y‖ ^ α) := mul_le_mul_of_nonneg_right hac (mul_nonneg hb0 ht)
      _ = b * ‖x - y‖ ^ α := by ring

/-! ## (C) Reading the pointwise data off a `C^{2,α}` bound -/

lemma iterDerivNorm_le_ofReal_of_holderNorm_le {k : ℕ} {α b : ℝ} {f : X → ℂ} {Ω : Set X}
    (h : Work.CR.Flat.holderNorm k α f Ω ≤ ENNReal.ofReal b) {i : ℕ} (hi : i ≤ k) :
    Work.CR.Flat.iterDerivNorm i f Ω ≤ ENNReal.ofReal b :=
  le_trans (Work.CR.Flat.iterDerivNorm_le_holderNorm k α f Ω hi) h

lemma norm_iteratedFDerivWithin_le_of_holderNorm_le {k : ℕ} {α b : ℝ} {f : X → ℂ}
    {Ω : Set X} (hb0 : 0 ≤ b)
    (h : Work.CR.Flat.holderNorm k α f Ω ≤ ENNReal.ofReal b) {i : ℕ} (hi : i ≤ k) {z : X}
    (hz : z ∈ Ω) :
    ‖iteratedFDerivWithin ℝ i f Ω z‖ ≤ b := by
  have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω z‖ ≤ ENNReal.ofReal b :=
    le_trans (Work.CR.Flat.le_iterDerivNorm i f Ω hz)
      (iterDerivNorm_le_ofReal_of_holderNorm_le h hi)
  exact (ENNReal.ofReal_le_ofReal_iff hb0).mp h1

lemma norm_sub_iteratedFDerivWithin_le_of_holderNorm_le {k : ℕ} {α b : ℝ} {f : X → ℂ}
    {Ω : Set X} (hα0 : 0 < α) (hb0 : 0 ≤ b)
    (h : Work.CR.Flat.holderNorm k α f Ω ≤ ENNReal.ofReal b) {i : ℕ} (hi : i ≤ k) {x y : X}
    (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖
      ≤ b * ‖x - y‖ ^ α := by
  by_cases hxy : x = y
  · subst hxy
    rw [sub_self, norm_zero, sub_self, norm_zero, Real.zero_rpow hα0.ne', mul_zero]
  · have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have h1 : ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal b :=
      le_trans (Work.CR.Flat.le_holderSeminorm i α f Ω hx hy hxy)
        (le_trans (Work.CR.Flat.holderSeminorm_le_holderNorm k α f Ω hi) h)
    have h2 := (ENNReal.ofReal_le_ofReal_iff hb0).mp h1
    rwa [div_le_iff₀ (Real.rpow_pos_of_pos hdpos α)] at h2

/-! ## (D) The main bound -/

theorem holderNorm_one_fderiv_coeff_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R)
    {u : (Fin n → ℂ) → ℂ}
    (hu : ∀ m : ℕ, ContDiffOn ℝ m u (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R)))
    {b : ℝ} (hb0 : 0 ≤ b)
    (hb : Work.CR.Flat.holderNorm 2 α u
      (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R)) ≤ ENNReal.ofReal b) :
    (∀ p : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => fderiv ℝ u z (Pi.single p 1))
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R)) ≤ ENNReal.ofReal (8 * b)) ∧
    (∀ p : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => fderiv ℝ u z (Pi.single p Complex.I))
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R)) ≤ ENNReal.ofReal (8 * b)) ∧
    (∀ p : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dCoord p u z)
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R)) ≤ ENNReal.ofReal (8 * b)) ∧
    (∀ p : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dbarCoord p u z)
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R)) ≤ ENNReal.ofReal (8 * b)) := by
  have hRpos : 0 < R := hR
  let P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R)
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc 0 (fun _ : Fin n => R)
  have hPconv : Convex ℝ P := convex_polydisc_zero (fun _ : Fin n => R)
  have hb' : Work.CR.Flat.holderNorm 2 α u P ≤ ENNReal.ofReal b := hb
  -- sup bounds and the Hölder bound at order `2`, read off `hb`
  have hb_norm : ∀ (i : ℕ), i ≤ 2 → ∀ z ∈ P, ‖iteratedFDerivWithin ℝ i u P z‖ ≤ b :=
    fun i hi z hz => norm_iteratedFDerivWithin_le_of_holderNorm_le hb0 hb' hi hz
  have hb_sub : ∀ x ∈ P, ∀ y ∈ P,
      ‖iteratedFDerivWithin ℝ 2 u P x - iteratedFDerivWithin ℝ 2 u P y‖
        ≤ b * ‖x - y‖ ^ α :=
    fun x hx y hy => norm_sub_iteratedFDerivWithin_le_of_holderNorm_le hα0 hb0 hb' le_rfl hx hy
  -- `fderiv ℝ u` is differentiable at every point of `P`
  have hdiff : ∀ z ∈ P, DifferentiableAt ℝ (fderiv ℝ u) z := by
    intro z hz
    have h3 : ContDiffAt ℝ 3 u z := ((hu 3) z hz).contDiffAt (hPopen.mem_nhds hz)
    exact (h3.fderiv_right (m := 2) (n := 3) (by norm_num)).differentiableAt (by norm_num)
  have h0 : ∀ z ∈ P, ‖fderiv ℝ u z‖ ≤ b := by
    intro z hz
    rw [← fderivWithin_of_mem_nhds (hPopen.mem_nhds hz),
      ← norm_iteratedFDerivWithin_one u (hPopen.uniqueDiffWithinAt hz)]
    exact hb_norm 1 (by norm_num) z hz
  have h1 : ∀ z ∈ P, ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ b := by
    intro z hz
    rw [norm_fderiv_fderiv_eq_iteratedFDeriv_two,
      ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := u) (s := P) 2 hPopen hz]
    exact hb_norm 2 le_rfl z hz
  have h2 : ∀ x ∈ P, ∀ y ∈ P,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ b * ‖x - y‖ ^ α := by
    intro x hx y hy
    rw [norm_fderiv_fderiv_sub_eq_iteratedFDeriv_two,
      ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := u) (s := P) 2 hPopen hx,
      ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := u) (s := P) 2 hPopen hy]
    exact hb_sub x hx y hy
  -- pointwise data for the coefficient functions
  have hcoeff : ∀ (v : Fin n → ℂ), ‖v‖ ≤ 1 → IsC1aData P α b (fun z => fderiv ℝ u z v) := by
    intro v hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      exact (hasFDerivAt_fderiv_apply u (hdiff z hz) v).differentiableAt
    · intro z hz
      calc ‖fderiv ℝ u z v‖ ≤ ‖fderiv ℝ u z‖ * ‖v‖ := (fderiv ℝ u z).le_opNorm v
        _ ≤ b * 1 := mul_le_mul (h0 z hz) hv (norm_nonneg v) hb0
        _ = b := by ring
    · intro z hz
      calc ‖fderiv ℝ (fun z => fderiv ℝ u z v) z‖
          ≤ ‖v‖ * ‖fderiv ℝ (fderiv ℝ u) z‖ := norm_fderiv_fderiv_apply_le u (hdiff z hz) v
        _ ≤ 1 * b := mul_le_mul hv (h1 z hz) (by positivity) zero_le_one
        _ = b := by ring
    · intro x hx y hy
      calc ‖fderiv ℝ (fun z => fderiv ℝ u z v) x - fderiv ℝ (fun z => fderiv ℝ u z v) y‖
          ≤ ‖v‖ * ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ :=
            norm_fderiv_fderiv_apply_sub_le u (hdiff x hx) (hdiff y hy) v
        _ ≤ 1 * (b * ‖x - y‖ ^ α) := mul_le_mul hv (h2 x hx y hy) (by positivity) zero_le_one
        _ = b * ‖x - y‖ ^ α := by ring
  have hv1 : ∀ p : Fin n, ‖(Pi.single p (1 : ℂ) : Fin n → ℂ)‖ ≤ 1 := by
    intro p
    rw [Pi.norm_single]
    norm_num
  have hvI : ∀ p : Fin n, ‖(Pi.single p (Complex.I : ℂ) : Fin n → ℂ)‖ ≤ 1 := by
    intro p
    rw [Pi.norm_single, Complex.norm_I]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    exact holderNorm_one_le_of_isC1aData hPopen hPconv hα0 hα1 hb0 (hcoeff _ (hv1 p))
  · intro p
    exact holderNorm_one_le_of_isC1aData hPopen hPconv hα0 hα1 hb0 (hcoeff _ (hvI p))
  · intro p
    have hac : ‖(1 / 2 : ℂ)‖ + ‖-(Complex.I / 2)‖ ≤ 1 := by norm_num
    have hcomb := holderNorm_one_le_of_isC1aData hPopen hPconv hα0 hα1 hb0
      ((hcoeff _ (hv1 p)).const_mul_add (a := (1 / 2 : ℂ)) (c := -(Complex.I / 2)) hb0 hac
        (hcoeff _ (hvI p)))
    have hfun : (fun z => (1 / 2 : ℂ) * fderiv ℝ u z (Pi.single p 1)
          + (-(Complex.I / 2)) * fderiv ℝ u z (Pi.single p Complex.I))
        = fun z => Work.CR.Flat.dCoord p u z := by
      funext z
      rw [Work.CR.Flat.dCoord]
      ring
    rw [hfun] at hcomb
    exact hcomb
  · intro p
    have hac : ‖(1 / 2 : ℂ)‖ + ‖Complex.I / 2‖ ≤ 1 := by norm_num
    have hcomb := holderNorm_one_le_of_isC1aData hPopen hPconv hα0 hα1 hb0
      ((hcoeff _ (hv1 p)).const_mul_add (a := (1 / 2 : ℂ)) (c := Complex.I / 2) hb0 hac
        (hcoeff _ (hvI p)))
    have hfun : (fun z => (1 / 2 : ℂ) * fderiv ℝ u z (Pi.single p 1)
          + (Complex.I / 2) * fderiv ℝ u z (Pi.single p Complex.I))
        = fun z => Work.CR.Flat.dbarCoord p u z := by
      funext z
      rw [Work.CR.Flat.dbarCoord]
      ring
    rw [hfun] at hcomb
    exact hcomb

end Work.NN.Newton
