import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Submission.Commons.Analysis.Calculus.abs_le_of_iteratedDeriv_two_bound
import Submission.Commons.Analysis.Calculus.abs_deriv_le_of_iteratedDeriv_two_bound
import Submission.Commons.Analysis.Calculus.iteratedDeriv_pow_mul_le_of_bump

/-!
# A bound on the second derivative of `τ ↦ exp (α τ) * f τ`

This file proves `Commons.Analysis.Calculus.norm_iteratedDeriv_two_exp_mul_real_le`: if `f` is
continuous on `[0, ∞)`, vanishes for `t ≥ x₀`, and is `C²` on `(0, x₀)` with `‖f''‖ ≤ B` there,
then `τ ↦ exp (α τ) * f τ` is `C²` on `(0, x₀)` and, for every `t ∈ (0, x₀)`,

  ‖(exp (α τ) * f τ)''(t)‖ ≤ exp (|α| x₀) * (B + 2|α| (B x₀ + |f 0| / x₀) + |α|² (B x₀² + |f 0|)).

The proof combines the second-order Leibniz rule for `exp (α τ) * g τ` with the commons bounds
`abs_le_of_iteratedDeriv_two_bound` (`|f t| ≤ B x₀² + |f 0|`) and
`abs_deriv_le_of_iteratedDeriv_two_bound` (`|f' t| ≤ B x₀ + |f 0| / x₀`).
-/

namespace Commons.Analysis.Calculus

/-- `s ↦ exp (c * s)` is `C^2` at every real point, as a function `ℝ → ℂ`. -/
private lemma contDiffAt_exp_const_mul_real' (c : ℂ) (t : ℝ) :
    ContDiffAt ℝ 2 (fun s : ℝ => Complex.exp (c * (s:ℂ))) t := by
  have hlin : ContDiff ℝ 2 (fun s : ℝ => c * (s:ℂ)) :=
    (contDiff_const_smul (𝕜 := ℝ) (R := ℂ) (n := 2) c).comp Complex.ofRealCLM.contDiff
  exact (Complex.contDiff_exp (𝕜 := ℝ) (n := 2)).comp hlin |>.contDiffAt

/-- Derivative of `s ↦ exp (c * s)` on the real line. -/
private lemma hasDerivAt_exp_const_mul_real' (c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (c * (s:ℂ))) (c * Complex.exp (c * (t:ℂ))) t := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (c * z)) (Complex.exp (c * (t:ℂ)) * c) (t:ℂ) := by
    simpa using (hasDerivAt_const_mul (x := (t:ℂ)) c).cexp
  have h2 := h.comp_ofReal
  rw [mul_comm] at h2
  exact h2

/-- `deriv (fun s : ℝ => exp (c * s)) = fun t => c * exp (c * t)`. -/
private lemma deriv_exp_const_mul_real' (c : ℂ) :
    deriv (fun s : ℝ => Complex.exp (c * (s:ℂ))) = fun t : ℝ => c * Complex.exp (c * (t:ℂ)) := by
  funext t
  exact (hasDerivAt_exp_const_mul_real' c t).deriv

/-- Second derivative of `s ↦ exp (c * s)` on the real line. -/
private lemma iteratedDeriv_two_exp_const_mul_real' (c : ℂ) :
    iteratedDeriv 2 (fun s : ℝ => Complex.exp (c * (s:ℂ))) = fun t : ℝ => c^2 * Complex.exp (c * (t:ℂ)) := by
  funext t
  have h1 : iteratedDeriv (1+1) (fun s : ℝ => Complex.exp (c * (s:ℂ)))
      = deriv (deriv (fun s : ℝ => Complex.exp (c * (s:ℂ)))) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [show (2:ℕ) = 1+1 from rfl, h1, deriv_exp_const_mul_real']
  have hd : HasDerivAt (fun s : ℝ => c * Complex.exp (c * (s:ℂ)))
      (c * (c * Complex.exp (c * (t:ℂ)))) t := by
    have := (hasDerivAt_exp_const_mul_real' c t).const_mul c
    simpa using this
  rw [hd.deriv]
  ring

/-- The norm of `exp (c * t)` for a real `t`. -/
private lemma norm_exp_const_mul_real' (c : ℂ) (t : ℝ) :
    ‖Complex.exp (c * (t:ℂ))‖ = Real.exp (c.re * t) := by
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Second-order Leibniz rule for `s ↦ exp (α s) * g s`, written out explicitly. -/
private lemma iteratedDeriv_two_exp_mul_eq' (α : ℝ) (g : ℝ → ℂ) (t : ℝ)
    (hg : ContDiffAt ℝ 2 g t) :
    iteratedDeriv 2 (fun s : ℝ => Complex.exp ((α:ℂ)*(s:ℂ)) * g s) t
      = Complex.exp ((α:ℂ)*(t:ℂ)) * ((α:ℂ)^2 * g t + 2*(α:ℂ)*deriv g t + iteratedDeriv 2 g t) := by
  change iteratedDeriv 2 ((fun s : ℝ => Complex.exp ((α:ℂ)*(s:ℂ))) * g) t = _
  have hE : ContDiffAt ℝ 2 (fun s : ℝ => Complex.exp ((α:ℂ)*(s:ℂ))) t :=
    contDiffAt_exp_const_mul_real' (α:ℂ) t
  rw [iteratedDeriv_mul hE hg]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.reduceSubDiff, iteratedDeriv_zero,
    iteratedDeriv_one, Nat.choose_self]
  rw [iteratedDeriv_two_exp_const_mul_real', deriv_exp_const_mul_real']
  simp only
  ring

/-- Norm version of the second-order Leibniz rule for `s ↦ exp (α s) * g s`: for arbitrary real
`α` the norm of the second derivative is bounded by
`exp (|α| x₀) * (|α|^2 M0 + 2 |α| M1 + M2)` whenever `‖g‖ ≤ M0`, `‖g'‖ ≤ M1`, `‖g''‖ ≤ M2`
on `(0, x₀)`. -/
theorem norm_iteratedDeriv_two_exp_mul_le_abs {α x₀ : ℝ} {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ 2 g (Set.Ioo (0:ℝ) x₀)) {M0 M1 M2 : ℝ}
    (h0 : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖g t‖ ≤ M0)
    (h1 : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖deriv g t‖ ≤ M1)
    (h2 : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 g t‖ ≤ M2)
    {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) x₀) :
    ‖iteratedDeriv 2 (fun s : ℝ => Complex.exp ((α : ℂ) * ((s : ℝ) : ℂ)) * g s) t‖
      ≤ Real.exp (|α| * x₀) * (|α| ^ 2 * M0 + 2 * |α| * M1 + M2) := by
  have hgAt : ContDiffAt ℝ 2 g t := hg.contDiffAt (isOpen_Ioo.mem_nhds ht)
  have hEt : ‖Complex.exp ((α:ℂ)*(t:ℂ))‖ = Real.exp (α * t) := by
    rw [norm_exp_const_mul_real', Complex.ofReal_re]
  have hnormA : ‖(α:ℂ)‖ = |α| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hX : ‖(α:ℂ)^2 * g t + 2*(α:ℂ)*deriv g t + iteratedDeriv 2 g t‖
      ≤ |α|^2 * M0 + 2*|α| *M1 + M2 := by
    have norm_a : ‖(α:ℂ)^2 * g t‖ = |α|^2 * ‖g t‖ := by
      rw [norm_mul, norm_pow, hnormA]
    have h2c : ‖(2:ℂ)*(α:ℂ)‖ = 2*|α| := by
      rw [norm_mul, Complex.norm_ofNat, hnormA]
    have norm_b : ‖2*(α:ℂ)*deriv g t‖ = 2*|α| *‖deriv g t‖ := by
      rw [norm_mul, h2c]
    have key : ‖(α:ℂ)^2 * g t + 2*(α:ℂ)*deriv g t + iteratedDeriv 2 g t‖
        ≤ |α|^2 * ‖g t‖ + 2*|α| *‖deriv g t‖ + ‖iteratedDeriv 2 g t‖ := by
      calc ‖(α:ℂ)^2 * g t + 2*(α:ℂ)*deriv g t + iteratedDeriv 2 g t‖
          ≤ ‖(α:ℂ)^2 * g t + 2*(α:ℂ)*deriv g t‖ + ‖iteratedDeriv 2 g t‖ := norm_add_le _ _
        _ ≤ (‖(α:ℂ)^2 * g t‖ + ‖2*(α:ℂ)*deriv g t‖) + ‖iteratedDeriv 2 g t‖ :=
              add_le_add (norm_add_le _ _) le_rfl
        _ = |α|^2 * ‖g t‖ + 2*|α| *‖deriv g t‖ + ‖iteratedDeriv 2 g t‖ := by rw [norm_a, norm_b]
    refine key.trans ?_
    have h1' : |α|^2 * ‖g t‖ ≤ |α|^2 * M0 := mul_le_mul_of_nonneg_left (h0 t ht) (sq_nonneg |α|)
    have h2' : 2*|α| *‖deriv g t‖ ≤ 2*|α| *M1 :=
      mul_le_mul_of_nonneg_left (h1 t ht) (by positivity)
    have h3' : ‖iteratedDeriv 2 g t‖ ≤ M2 := h2 t ht
    linarith
  rw [iteratedDeriv_two_exp_mul_eq' α g t hgAt, norm_mul, hEt]
  have hstep1 : Real.exp (α * t) * ‖(α:ℂ)^2 * g t + 2*(α:ℂ)*deriv g t + iteratedDeriv 2 g t‖
      ≤ Real.exp (|α| * x₀) * ‖(α:ℂ)^2 * g t + 2*(α:ℂ)*deriv g t + iteratedDeriv 2 g t‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    calc α * t ≤ |α| * t := mul_le_mul_of_nonneg_right (le_abs_self α) (le_of_lt ht.1)
      _ ≤ |α| * x₀ := mul_le_mul_of_nonneg_left (le_of_lt ht.2) (abs_nonneg α)
  calc Real.exp (α * t) * ‖(α:ℂ)^2 * g t + 2*(α:ℂ)*deriv g t + iteratedDeriv 2 g t‖
      ≤ Real.exp (|α| * x₀) * ‖(α:ℂ)^2 * g t + 2*(α:ℂ)*deriv g t + iteratedDeriv 2 g t‖ := hstep1
    _ ≤ Real.exp (|α| * x₀) * (|α|^2 * M0 + 2*|α| *M1 + M2) :=
          mul_le_mul_of_nonneg_left hX (Real.exp_nonneg _)

/-- If `f` is continuous on `[0, ∞)`, vanishes for `t ≥ x₀`, and is `C²` on `(0, x₀)` with
`‖f''‖ ≤ B` there, then `τ ↦ exp (α τ) * f τ` is `C²` on `(0, x₀)` and, for every `t ∈ (0, x₀)`,

  ‖(exp (α τ) * f τ)''(t)‖ ≤ exp (|α| x₀) * (B + 2|α| (B x₀ + |f 0| / x₀) + |α|² (B x₀² + |f 0|)). -/
theorem norm_iteratedDeriv_two_exp_mul_real_le {x₀ B α : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    ContDiffOn ℝ 2 (fun τ : ℝ => Real.exp (α * τ) * f τ) (Set.Ioo 0 x₀) ∧
    (∀ t ∈ Set.Ioo (0:ℝ) x₀,
      ‖iteratedDeriv 2 (fun τ : ℝ => Real.exp (α * τ) * f τ) t‖ ≤
        Real.exp (|α| * x₀) *
          (B + 2 * |α| * (B * x₀ + |f 0| / x₀) + |α| ^ 2 * (B * x₀ ^ 2 + |f 0|))) := by
  have hF2 : ContDiffOn ℝ 2 (fun τ : ℝ => Real.exp (α * τ) * f τ) (Set.Ioo 0 x₀) :=
    ((Real.contDiff_exp (n := 2)).comp (contDiff_const.mul contDiff_id)).contDiffOn.mul hf2
  refine ⟨hF2, ?_⟩
  intro t ht
  have ht_nhds := isOpen_Ioo.mem_nhds ht
  have hF2_at : ContDiffAt ℝ 2 (fun τ : ℝ => Real.exp (α * τ) * f τ) t := hF2.contDiffAt ht_nhds
  -- the inner function `g := fun u => (f u : ℂ)`
  have hgC : ContDiffOn ℝ 2 (fun u : ℝ => ((f u : ℝ) : ℂ)) (Set.Ioo 0 x₀) :=
    (Complex.ofRealCLM.contDiff.contDiffOn).comp hf2 (fun x _ => Set.mem_univ _)
  have hM0 : ∀ s ∈ Set.Ioo (0:ℝ) x₀, ‖(fun u : ℝ => ((f u : ℝ) : ℂ)) s‖ ≤ B * x₀ ^ 2 + |f 0| := by
    intro s hs
    show ‖((f s : ℝ) : ℂ)‖ ≤ B * x₀ ^ 2 + |f 0|
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le_of_iteratedDeriv_two_bound hx₀ hcont hsupp hf2 hBnd s hs
  have hM1 : ∀ s ∈ Set.Ioo (0:ℝ) x₀,
      ‖deriv (fun u : ℝ => ((f u : ℝ) : ℂ)) s‖ ≤ B * x₀ + |f 0| / x₀ := by
    intro s hs
    have hsat : ContDiffAt ℝ 2 f s := hf2.contDiffAt (isOpen_Ioo.mem_nhds hs)
    have hd : deriv (fun u : ℝ => ((f u : ℝ) : ℂ)) s = ((deriv f s : ℝ) : ℂ) :=
      (((hsat.differentiableAt (by norm_num)).hasDerivAt).ofReal_comp).deriv
    rw [hd, Complex.norm_real, Real.norm_eq_abs]
    exact abs_deriv_le_of_iteratedDeriv_two_bound hx₀ hcont hsupp hf2 hBnd s hs
  have hM2 : ∀ s ∈ Set.Ioo (0:ℝ) x₀,
      ‖iteratedDeriv 2 (fun u : ℝ => ((f u : ℝ) : ℂ)) s‖ ≤ B := by
    intro s hs
    rw [norm_iteratedDeriv_ofReal 2 f s (hf2.contDiffAt (isOpen_Ioo.mem_nhds hs))]
    exact hBnd s hs
  have hbound := norm_iteratedDeriv_two_exp_mul_le_abs (x₀ := x₀) (α := α)
    (g := fun u : ℝ => ((f u : ℝ) : ℂ))
    (M0 := B * x₀ ^ 2 + |f 0|) (M1 := B * x₀ + |f 0| / x₀) (M2 := B)
    hgC hM0 hM1 hM2 ht
  have hfun_eq : (fun y : ℝ => (((fun τ : ℝ => Real.exp (α * τ) * f τ) y : ℝ) : ℂ))
      = (fun s : ℝ => Complex.exp ((α : ℂ) * ((s : ℝ) : ℂ)) * ((f s : ℝ) : ℂ)) := by
    funext s
    simp only
    rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_mul]
  have hnorm_eq : ‖iteratedDeriv 2 (fun y : ℝ => (((fun τ : ℝ => Real.exp (α * τ) * f τ) y : ℝ) : ℂ)) t‖
      = ‖iteratedDeriv 2 (fun τ : ℝ => Real.exp (α * τ) * f τ) t‖ :=
    norm_iteratedDeriv_ofReal 2 (fun τ : ℝ => Real.exp (α * τ) * f τ) t hF2_at
  calc ‖iteratedDeriv 2 (fun τ : ℝ => Real.exp (α * τ) * f τ) t‖
      = ‖iteratedDeriv 2 (fun y : ℝ => (((fun τ : ℝ => Real.exp (α * τ) * f τ) y : ℝ) : ℂ)) t‖ :=
          hnorm_eq.symm
    _ = ‖iteratedDeriv 2 (fun s : ℝ => Complex.exp ((α : ℂ) * ((s : ℝ) : ℂ)) * ((f s : ℝ) : ℂ)) t‖ :=
          by rw [hfun_eq]
    _ ≤ Real.exp (|α| * x₀) * (|α| ^ 2 * (B * x₀ ^ 2 + |f 0|) + 2 * |α| * (B * x₀ + |f 0| / x₀) + B) :=
          hbound
    _ = Real.exp (|α| * x₀) *
          (B + 2 * |α| * (B * x₀ + |f 0| / x₀) + |α| ^ 2 * (B * x₀ ^ 2 + |f 0|)) := by ring

end Commons.Analysis.Calculus