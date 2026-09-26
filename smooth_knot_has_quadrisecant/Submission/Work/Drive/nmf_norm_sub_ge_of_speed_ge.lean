import Mathlib

set_option linter.unusedVariables false

namespace Work.Drive

/-- **A short chord of a curve with bounded-below speed and bounded-above acceleration is long.**
If `f` has `‖f'‖ ≥ mm > 0` and `‖f''‖ ≤ K` everywhere and the parameter interval `[a,b]` is short in
the sense `K * (b - a) ≤ mm / 2`, then `‖f b - f a‖ ≥ (mm/2) * (b - a)`. -/
lemma nmf_norm_sub_ge_of_speed_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' f'' : ℝ → E} {mm K a b : ℝ} (hab : a ≤ b) (hm : 0 < mm)
    (h1 : ∀ x, HasDerivAt f (f' x) x) (h2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hvel : ∀ t, mm ≤ ‖f' t‖) (hacc : ∀ t, ‖f'' t‖ ≤ K)
    (hsmall : K * (b - a) ≤ mm / 2) : (mm / 2) * (b - a) ≤ ‖f b - f a‖ := by
  have hK : 0 ≤ K := le_trans (norm_nonneg (f'' a)) (hacc a)
  -- The velocity is nearly constant on `[a,b]`: `‖f' x - f' a‖ ≤ K * (x - a)`.
  have hspeed : ∀ x ∈ Set.Icc a b, ‖f' x - f' a‖ ≤ K * (x - a) := by
    intro x hx
    exact norm_image_sub_le_of_norm_deriv_le_segment' (f := f') (f' := f'') (a := a) (b := x)
      (C := K) (fun y _ => (h2 y).hasDerivWithinAt) (fun y _ => hacc y) x ⟨hx.1, le_rfl⟩
  -- The displacement `f b - f a` equals `(b-a) • f' a` up to an error `G b`, where
  -- `G t = f t - f a - (t-a) • f' a` has derivative `f' t - f' a`.
  have hGderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => f t - f a - (t - a) • f' a) (f' x - f' a) x := by
    intro x
    have h0 : HasDerivAt (fun t : ℝ => f t - f a) (f' x) x := (h1 x).sub_const (f a)
    have h1' : HasDerivAt (fun t : ℝ => (t - a) • f' a) (f' a) x := by
      have hlin : HasDerivAt (fun t : ℝ => t - a) 1 x := (hasDerivAt_id x).sub_const a
      simpa using hlin.smul_const (f' a)
    exact h0.sub h1'
  -- The error velocity is uniformly bounded by `mm/2` on `[a,b)`.
  have hGbound : ∀ x ∈ Set.Ico a b, ‖f' x - f' a‖ ≤ mm / 2 := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, le_of_lt hx.2⟩
    have h' := hspeed x hxIcc
    have h2' : K * (x - a) ≤ mm / 2 := by
      have hxa : x - a ≤ b - a := by linarith [hx.2]
      nlinarith [hK, hxa]
    linarith
  -- Mean value inequality for the error.
  have hG := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => f t - f a - (t - a) • f' a) (f' := fun x => f' x - f' a)
      (a := a) (b := b) (C := mm / 2)
      (fun x _ => (hGderiv x).hasDerivWithinAt) hGbound b ⟨hab, le_rfl⟩
  have hGfinal : ‖f b - f a - (b - a) • f' a‖ ≤ (mm / 2) * (b - a) := by
    simpa using hG
  have hba : 0 ≤ b - a := by linarith
  have hnorm : ‖(b - a) • f' a‖ = (b - a) * ‖f' a‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hba]
  -- Triangle inequality in the form `‖x‖ - ‖y‖ ≤ ‖x + y‖`.
  have htri : ‖(b - a) • f' a‖ - ‖f b - f a - (b - a) • f' a‖
      ≤ ‖(b - a) • f' a + (f b - f a - (b - a) • f' a)‖ := by
    have h := abs_norm_sub_norm_le ((b - a) • f' a) (-(f b - f a - (b - a) • f' a))
    rw [norm_neg, sub_neg_eq_add] at h
    linarith [le_abs_self (‖(b - a) • f' a‖ - ‖f b - f a - (b - a) • f' a‖), h]
  have hmain : (b - a) * ‖f' a‖ - (mm / 2) * (b - a)
      ≤ ‖(b - a) • f' a + (f b - f a - (b - a) • f' a)‖ := by
    linarith [hnorm ▸ htri, hGfinal]
  have hfinal : f b - f a = (b - a) • f' a + (f b - f a - (b - a) • f' a) := by abel
  rw [hfinal]
  nlinarith [hmain, hvel a, hba, hm]

end Work.Drive
