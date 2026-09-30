import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Lipschitz bound for `eC ∘ β`

`eC t = exp (2π i t)`.  If `β : ℝ → ℝ` has derivative bounded by `Cβ` on `[1, L]`, then for
`1 ≤ h` and `h + 1 ≤ L` the two points `β h` and `β (h+1)` differ by at most `Cβ` (mean value
theorem), while `eC` is `2π`-Lipschitz on `ℝ`.  Hence
`‖eC (β (h+1)) - eC (β h)‖ ≤ 2π Cβ`.
-/

open Complex Real

namespace Work.BMF

/-- `eC` is differentiable everywhere with derivative `2π i · eC t`. -/
lemma hasDerivAt_eC (t : ℝ) :
    HasDerivAt eC (eC t * (2 * (Real.pi : ℂ) * Complex.I)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (s : ℂ))
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) t := by
    simpa using h1.const_mul ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
  exact (Complex.hasDerivAt_exp (((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (t : ℂ))).comp t h2

/-- `eC` takes values on the unit circle. -/
lemma norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  rw [show (2 * ↑Real.pi * Complex.I * ↑t) = (↑(2 * Real.pi * t)) * Complex.I by
        push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_two_pi_I : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_ofNat]

/-- The derivative of `eC` is bounded by `2π` everywhere, i.e. `eC` is `2π`-Lipschitz. -/
lemma norm_deriv_eC_le (t : ℝ) : ‖deriv eC t‖ ≤ 2 * Real.pi := by
  rw [(hasDerivAt_eC t).deriv, norm_mul, norm_eC t, one_mul, norm_two_pi_I]

theorem norm_eC_comp_sub_le (L : ℕ) (β : ℝ → ℝ) (Cβ : ℝ)
    (hβ : ∀ y ∈ Set.Icc (1:ℝ) L, HasDerivAt β (deriv β y) y)
    (hCβ : ∀ y ∈ Set.Icc (1:ℝ) L, ‖deriv β y‖ ≤ Cβ)
    {h : ℕ} (h1 : 1 ≤ h) (hL : h + 1 ≤ L) :
    ‖eC (β (h + 1)) - eC (β h)‖ ≤ 2 * Real.pi * Cβ := by
  -- `β (h+1)` is `β ((h:ℝ) + 1)`; the interval `[h, h+1]` lies inside `[1, L]`.
  have hmem : ∀ x ∈ Set.Icc (h:ℝ) ((h:ℝ)+1), x ∈ Set.Icc (1:ℝ) L := by
    intro x hx
    refine ⟨le_trans ?_ hx.1, le_trans hx.2 ?_⟩
    · exact_mod_cast h1
    · exact_mod_cast hL
  have hle : (h:ℝ) ≤ (h:ℝ)+1 := by linarith
  have hnorm : ‖((h:ℝ)+1) - (h:ℝ)‖ = 1 := by
    rw [show ((h:ℝ)+1) - (h:ℝ) = 1 by ring]; simp
  -- Mean value theorem for `β` on `[h, h+1]`.
  have hβbound : ‖β ((h:ℝ)+1) - β (h:ℝ)‖ ≤ Cβ := by
    have hthis := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := β) (s := Set.Icc (h:ℝ) ((h:ℝ)+1)) (x := (h:ℝ)) (y := (h:ℝ)+1) (C := Cβ)
      (fun x hx => (hβ x (hmem x hx)).differentiableAt)
      (fun x hx => hCβ x (hmem x hx))
      (convex_Icc _ _) ⟨le_refl _, hle⟩ ⟨hle, le_refl _⟩
    rwa [hnorm, mul_one] at hthis
  -- `2π`-Lipschitz bound for `eC`.
  calc ‖eC (β (h + 1)) - eC (β h)‖
      ≤ 2 * Real.pi * ‖β ((h:ℝ)+1) - β (h:ℝ)‖ := by
        exact Convex.norm_image_sub_le_of_norm_deriv_le
          (f := eC) (s := Set.univ) (x := β (h:ℝ)) (y := β ((h:ℝ)+1)) (C := 2*Real.pi)
          (fun x _ => (hasDerivAt_eC x).differentiableAt)
          (fun x _ => norm_deriv_eC_le x)
          convex_univ (Set.mem_univ _) (Set.mem_univ _)
    _ ≤ 2 * Real.pi * Cβ := mul_le_mul_of_nonneg_left hβbound (by positivity)

end Work.BMF
