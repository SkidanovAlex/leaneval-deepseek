import Mathlib

namespace Work.CKFinal

open Set

/-- Second-order mean value estimate. If `f : ℝ → ℂ` is differentiable everywhere, its
derivative `deriv f` is differentiable everywhere, and `‖deriv (deriv f) x‖ ≤ C` for all `x`,
then the difference quotients of `f` at the base point `r` with steps `a` and `b` differ by at
most `(|a| + |b|) * C`. -/
lemma snd_deriv_dq_bound {f : ℝ → ℂ} {C : ℝ}
    (hd : ∀ x : ℝ, DifferentiableAt ℝ f x)
    (hd' : ∀ x : ℝ, DifferentiableAt ℝ (deriv f) x)
    (hb : ∀ x : ℝ, ‖deriv (deriv f) x‖ ≤ C)
    (r a b : ℝ) (ha : a ≠ 0) (hb' : b ≠ 0) :
    ‖(f (r + a) - f r) / a - (f (r + b) - f r) / b‖ ≤ (|a| + |b|) * C := by
  -- `C` is nonnegative since it bounds a norm.
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hb 0)
  -- First-order mean value inequality for `deriv f`, whose second derivative is bounded by `C`.
  have hMVT : ∀ x y : ℝ, ‖deriv f y - deriv f x‖ ≤ C * ‖y - x‖ := by
    intro x y
    exact Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := deriv f) (s := Set.univ)
      (fun z _ => hd' z) (fun z _ => hb z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  -- Auxiliary function whose endpoints capture the two difference quotients.
  set Φ : ℝ → ℂ := fun t => (f (r + t*a) - f r)/a - (f (r + t*b) - f r)/b with hΦ
  -- Each summand is differentiable with the expected derivative.
  have hpiece : ∀ (c : ℝ), c ≠ 0 → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => (f (r + s*c) - f r)/c) (deriv f (r + t*c)) t := by
    intro c hc t
    have h1 : HasDerivAt (fun s : ℝ => f (r + s*c)) (c • deriv f (r + t*c)) t := by
      have hg : HasDerivAt (fun s : ℝ => r + s*c) c t := by
        simpa using (((hasDerivAt_id t).mul_const c).const_add r)
      exact ((hd (r + t*c)).hasDerivAt).scomp t hg
    have h2 : HasDerivAt (fun s : ℝ => f (r + s*c) - f r) (c • deriv f (r + t*c)) t :=
      h1.sub_const (f r)
    have h3 : HasDerivAt (fun s : ℝ => (f (r + s*c) - f r)/c) ((c • deriv f (r + t*c))/c) t :=
      h2.div_const c
    convert h3 using 1
    rw [Complex.real_smul, mul_div_cancel_left₀ _ (by exact_mod_cast hc)]
  have hPhi : ∀ t : ℝ, HasDerivAt Φ (deriv f (r + t*a) - deriv f (r + t*b)) t := by
    intro t
    have hsub := (hpiece a ha t).sub (hpiece b hb' t)
    change HasDerivAt (fun s : ℝ => (f (r + s*a) - f r)/a - (f (r + s*b) - f r)/b)
      (deriv f (r + t*a) - deriv f (r + t*b)) t at hsub
    simpa [hΦ] using hsub
  -- The derivative of `Φ` is uniformly bounded by `(|a| + |b|) * C` on `[0,1]`.
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖deriv Φ t‖ ≤ (|a| + |b|) * C := by
    intro t ht
    rw [(hPhi t).deriv]
    have hbnd := hMVT (r + t*b) (r + t*a)
    have hnorm : ‖(r + t*a) - (r + t*b)‖ = |t| * |a - b| := by
      rw [show (r + t*a) - (r + t*b) = t*(a-b) by ring]
      rw [Real.norm_eq_abs, abs_mul]
    have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have hab : |a - b| ≤ |a| + |b| := by
      rw [sub_eq_add_neg]
      calc |a + -b| ≤ |a| + |-b| := abs_add_le a (-b)
        _ = |a| + |b| := by rw [abs_neg]
    calc ‖deriv f (r + t*a) - deriv f (r + t*b)‖ ≤ C * ‖(r + t*a) - (r + t*b)‖ := hbnd
      _ = C * (|t| * |a - b|) := by rw [hnorm]
      _ ≤ (|a| + |b|) * C := by
            have hle : |t| * |a - b| ≤ 1 * (|a| + |b|) :=
              mul_le_mul ht1 hab (abs_nonneg _) (by norm_num)
            calc C * (|t| * |a - b|) ≤ C * (1 * (|a| + |b|)) :=
                  mul_le_mul_of_nonneg_left hle hC
              _ = (|a| + |b|) * C := by ring
  -- Mean value inequality for `Φ` on `[0,1]`.
  have hfinal := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := Φ) (s := Set.Icc (0:ℝ) 1)
      (x := 0) (y := 1) (C := (|a| + |b|) * C)
      (fun t _ => (hPhi t).differentiableAt) hbound (convex_Icc 0 1) (by norm_num) (by norm_num)
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  have hΦ1 : Φ 1 = (f (r + a) - f r)/a - (f (r + b) - f r)/b := by simp [hΦ]
  rw [hΦ1, hΦ0, sub_zero] at hfinal
  simpa using hfinal

end Work.CKFinal
