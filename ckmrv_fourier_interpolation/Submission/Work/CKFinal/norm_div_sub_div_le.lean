import Mathlib

/-!
# Mean-value estimate for difference quotients

If the second derivative of `f : ℝ → ℂ` is bounded in norm by `C`, then the difference
quotients of `f` at `r` with steps `a` and `b` differ by at most `(|a| + |b|) * C`.

The proof splits the two difference quotients through the common value `deriv f r`:

* `‖f x - f r - deriv f r * (x - r)‖ ≤ C * |x - r|^2` (a Taylor/mean-value bound,
  proved here as `norm_taylor_remainder_le` from the mean value theorem applied to
  `fun t => f t - deriv f r * (t - r)` on the unordered interval `uIcc r x`);
* consequently `‖(f (r + s) - f r) / s - deriv f r‖ ≤ C * |s|` for `s ≠ 0`;
* combine the bounds for `a` and `b` with the triangle inequality.
-/

namespace Work.CKFinal

/-- The mean value theorem applied to `f'` shows that `f'` is `C`-Lipschitz when
`‖f''‖ ≤ C` everywhere. -/
lemma norm_deriv_sub_deriv_le {f : ℝ → ℂ} {C : ℝ}
    (hd' : ∀ x, DifferentiableAt ℝ (deriv f) x)
    (hb : ∀ x, ‖deriv (deriv f) x‖ ≤ C) :
    ∀ p q : ℝ, ‖deriv f q - deriv f p‖ ≤ C * |q - p| := by
  intro p q
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℂ)
    (f := deriv f) (s := Set.univ) (x := p) (y := q) (C := C)
    (fun z _ => hd' z) (fun z _ => hb z) convex_univ (Set.mem_univ p) (Set.mem_univ q)
  simpa using h

/-- Taylor/mean-value estimate: if `‖f''‖ ≤ C` everywhere then the first-order Taylor
remainder of `f` at `r` is bounded by `C * |x - r|^2`. -/
lemma norm_taylor_remainder_le {f : ℝ → ℂ} {C : ℝ}
    (hd : ∀ x, DifferentiableAt ℝ f x)
    (hd' : ∀ x, DifferentiableAt ℝ (deriv f) x)
    (hb : ∀ x, ‖deriv (deriv f) x‖ ≤ C) :
    ∀ r x : ℝ, ‖f x - f r - deriv f r * ((x - r : ℝ) : ℂ)‖ ≤ C * |x - r|^2 := by
  intro r x
  have hC : 0 ≤ C := le_trans (norm_nonneg (deriv (deriv f) 0)) (hb 0)
  have hlip : ∀ p q : ℝ, ‖deriv f q - deriv f p‖ ≤ C * |q - p| :=
    norm_deriv_sub_deriv_le hd' hb
  have hlin_diff : ∀ t : ℝ, DifferentiableAt ℝ (fun s : ℝ => deriv f r * ((s - r : ℝ) : ℂ)) t :=
    fun t => (((hasDerivAt_id t).sub_const r).ofReal_comp.const_mul (deriv f r)).differentiableAt
  have hderiv : ∀ t : ℝ, deriv (fun s : ℝ => f s - deriv f r * ((s - r : ℝ) : ℂ)) t
      = deriv f t - deriv f r := by
    intro t
    have h1 : HasDerivAt f (deriv f t) t := (hd t).hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => deriv f r * ((s - r : ℝ) : ℂ)) (deriv f r) t := by
      have hh := ((hasDerivAt_id t).sub_const r).ofReal_comp
      simpa using hh.const_mul (deriv f r)
    exact (h1.sub h2).deriv
  have hbound : ∀ t ∈ Set.uIcc r x,
      ‖deriv (fun s : ℝ => f s - deriv f r * ((s - r : ℝ) : ℂ)) t‖ ≤ C * |x - r| := by
    intro t ht
    rw [hderiv t]
    have h1 := hlip r t
    have h2 : |t - r| ≤ |x - r| := by
      have := Real.dist_left_le_of_mem_uIcc ht
      simpa [Real.dist_eq, abs_sub_comm] using this
    calc ‖deriv f t - deriv f r‖ ≤ C * |t - r| := h1
      _ ≤ C * |x - r| := mul_le_mul_of_nonneg_left h2 hC
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℂ)
    (f := fun s : ℝ => f s - deriv f r * ((s - r : ℝ) : ℂ))
    (s := Set.uIcc r x) (x := r) (y := x) (C := C * |x - r|)
    (fun t _ => (hd t).sub (hlin_diff t)) hbound (convex_uIcc r x) Set.left_mem_uIcc
    Set.right_mem_uIcc
  have hval : (fun s : ℝ => f s - deriv f r * ((s - r : ℝ) : ℂ)) x
      - (fun s : ℝ => f s - deriv f r * ((s - r : ℝ) : ℂ)) r
      = f x - f r - deriv f r * ((x - r : ℝ) : ℂ) := by
    simp only [sub_self, Complex.ofReal_zero, mul_zero, sub_zero]
    abel
  rw [hval] at hmvt
  calc ‖f x - f r - deriv f r * ((x - r : ℝ) : ℂ)‖ ≤ (C * |x - r|) * ‖x - r‖ := hmvt
    _ = C * |x - r|^2 := by rw [Real.norm_eq_abs]; ring

/-- Mean-value estimate: if `‖f''‖ ≤ C` everywhere, then the difference quotients of `f` at `r`
with steps `a` and `b` differ by at most `(|a| + |b|) * C`. -/
lemma norm_div_sub_div_le {f : ℝ → ℂ} {C : ℝ}
    (hd : ∀ x, DifferentiableAt ℝ f x) (hd' : ∀ x, DifferentiableAt ℝ (deriv f) x)
    (hb : ∀ x, ‖deriv (deriv f) x‖ ≤ C)
    (r a b : ℝ) (ha : a ≠ 0) (hb' : b ≠ 0) :
    ‖(f (r + a) - f r) / a - (f (r + b) - f r) / b‖ ≤ (|a| + |b|) * C := by
  have hT := norm_taylor_remainder_le hd hd' hb
  have key : ∀ s : ℝ, s ≠ 0 → ‖(f (r + s) - f r) / s - deriv f r‖ ≤ C * |s| := by
    intro s hs
    have hsc : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    have hstep : (f (r + s) - f r) / s - deriv f r
        = (f (r + s) - f r - deriv f r * ((s : ℝ) : ℂ)) / ((s : ℝ) : ℂ) := by
      rw [eq_div_iff hsc, sub_mul, div_mul_cancel₀ _ hsc]
    rw [hstep, norm_div]
    rw [show ‖((s : ℝ) : ℂ)‖ = |s| from by simp]
    rw [div_le_iff₀ (abs_pos.mpr hs)]
    have h1 := hT r (r + s)
    rw [show r + s - r = s from by ring] at h1
    calc ‖f (r + s) - f r - deriv f r * ((s : ℝ) : ℂ)‖ ≤ C * |s| ^ 2 := h1
      _ = C * |s| * |s| := by ring
  calc ‖(f (r + a) - f r) / a - (f (r + b) - f r) / b‖
      = ‖((f (r + a) - f r) / a - deriv f r) - ((f (r + b) - f r) / b - deriv f r)‖ := by
        congr 1; abel
    _ ≤ ‖(f (r + a) - f r) / a - deriv f r‖ + ‖(f (r + b) - f r) / b - deriv f r‖ :=
        norm_sub_le _ _
    _ ≤ C * |a| + C * |b| := add_le_add (key a ha) (key b hb')
    _ = (|a| + |b|) * C := by ring

end Work.CKFinal
