import Mathlib

/-!
# The chord / second-derivative bound

If `g'' ≥ -K` on `[a,b]` (here `K = 3200`) then `g` lies below its chord on `[a,b]`
up to an error `K (b-a)^2 / 8 = 400 (b-a)^2`.

The proof is elementary: the function
`F x = g x - chord x - (K/2) (x-a)(b-x)` has `F'' = g'' + K ≥ 0`, hence is convex;
since `F a = F b = 0` the maximum principle for convex functions gives `F ≤ 0` on
`[a,b]`, i.e. `g x ≤ chord x + (K/2)(x-a)(b-x) ≤ max (g a) (g b) + K (b-a)^2 / 8`.
-/

namespace Work.CNum

/-- For a convex combination `(1-t) u + t v` of two reals with `t ∈ [0,1]`,
the result is at most the maximum of the two. -/
lemma cnum_combo_le_max {t u v : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * u + t * v ≤ max u v := by
  rcases le_total u v with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

/-- Derivative of the quadratic `x ↦ (x-a)(b-x)`. -/
lemma cnum_deriv_quad (a b x : ℝ) :
    HasDerivAt (fun x : ℝ => (x - a) * (b - x)) (a + b - 2 * x) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 x := (hasDerivAt_id x).sub_const a
  have h2 : HasDerivAt (fun x : ℝ => b - x) (-1) x := (hasDerivAt_id x).const_sub b
  have h3 := h1.mul h2
  convert h3 using 1
  all_goals first | (ext y; simp only [Pi.mul_apply]) | ring

theorem chord {a b : ℝ} (hab : a ≤ b) {g g' g'' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x, -3200 ≤ g'' x) :
    ∀ φ ∈ Set.Icc a b, g φ ≤ max (g a) (g b) + 400 * (b - a) ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    intro φ hφ
    rw [Set.mem_Icc] at hφ
    obtain ⟨h1, h2⟩ := hφ
    have : φ = a := le_antisymm h2 h1
    subst this
    simp
  · intro φ hφ
    set s : ℝ := (g b - g a) / (b - a) with hs
    have hbda : 0 < b - a := by linarith
    have hbne : b - a ≠ 0 := ne_of_gt hbda
    -- First derivative of the auxiliary function `F`.
    have hfd : ∀ x, HasDerivAt (fun x : ℝ => g x - (g a + s * (x - a)) - 1600 * (x - a) * (b - x))
        (g' x - s - 1600 * (a + b - 2 * x)) x := by
      intro x
      have hc : HasDerivAt (fun y : ℝ => g a + s * (y - a)) s x := by
        have h1 : HasDerivAt (fun y : ℝ => s * (y - a)) s x := by
          have h := (hasDerivAt_id x).sub_const a
          have h2 := h.const_mul s
          simpa using h2
        have h3 := h1.const_add (g a)
        simpa using h3
      have hq : HasDerivAt (fun y : ℝ => (y - a) * (b - y)) (a + b - 2 * x) x :=
        cnum_deriv_quad a b x
      have hr : HasDerivAt (fun y : ℝ => 1600 * ((y - a) * (b - y))) (1600 * (a + b - 2 * x)) x :=
        hq.const_mul 1600
      have hgc : HasDerivAt (g - fun y : ℝ => g a + s * (y - a)) (g' x - s) x := (hg x).sub hc
      have hP := hgc.sub hr
      convert hP using 1 <;> (try (ext y)) <;> (try (simp only [Pi.sub_apply])) <;> (try ring)
    -- Second derivative of the auxiliary function `F`.
    have hfd' : ∀ x, HasDerivAt (fun x : ℝ => g' x - s - 1600 * (a + b - 2 * x)) (g'' x + 3200) x := by
      intro x
      have h2 : HasDerivAt (fun y : ℝ => g' y - s) (g'' x) x := (hg' x).sub_const s
      have hlin : HasDerivAt (fun y : ℝ => a + b - 2 * y) (-2) x := by
        have h0 := (hasDerivAt_id x).const_mul 2
        have h1 := h0.const_sub (a + b)
        simpa using h1
      have h4 : HasDerivAt (fun y : ℝ => 1600 * (a + b - 2 * y)) (1600 * (-2)) x :=
        hlin.const_mul 1600
      have hP := h2.sub h4
      convert hP using 1 <;> (try (ext y)) <;> (try (simp only [Pi.sub_apply])) <;> (try ring)
    -- `F` is convex.
    have hconv : ConvexOn ℝ Set.univ
        (fun x : ℝ => g x - (g a + s * (x - a)) - 1600 * (x - a) * (b - x)) := by
      refine convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x => g' x - s - 1600 * (a + b - 2 * x))
        (f'' := fun x => g'' x + 3200) convex_univ ?_ ?_ ?_ ?_
      · exact fun x _ => (hfd x).continuousAt.continuousWithinAt
      · intro x _; exact (hfd x).hasDerivWithinAt
      · intro x _; exact (hfd' x).hasDerivWithinAt
      · intro x _; linarith [hg'' x]
    -- `F ≤ 0` on `[a,b]` by the maximum principle for convex functions.
    have hFφ : (fun x : ℝ => g x - (g a + s * (x - a)) - 1600 * (x - a) * (b - x)) φ ≤ 0 := by
      have hh := hconv.le_max_of_mem_Icc (Set.mem_univ a) (Set.mem_univ b) hφ
      have h1 : g a - (g a + s * (a - a)) - 1600 * (a - a) * (b - a) = 0 := by ring
      have h2 : g b - (g a + s * (b - a)) - 1600 * (b - a) * (b - b) = 0 := by
        rw [hs]; field_simp [hbne]; ring
      rw [h1, h2, max_self] at hh
      exact hh
    have hmain : g φ ≤ (g a + s * (φ - a)) + 1600 * (φ - a) * (b - φ) := by
      change g φ - (g a + s * (φ - a)) - 1600 * (φ - a) * (b - φ) ≤ 0 at hFφ
      linarith
    -- The quadratic remainder is at most `K (b-a)^2 / 8 = 400 (b-a)^2`.
    have hq : 1600 * (φ - a) * (b - φ) ≤ 400 * (b - a) ^ 2 := by
      nlinarith [sq_nonneg ((φ - a) - (b - φ))]
    -- The chord is at most the maximum of the endpoint values.
    have hc : g a + s * (φ - a) ≤ max (g a) (g b) := by
      have ht0 : 0 ≤ (φ - a) / (b - a) := div_nonneg (by linarith [hφ.1]) (le_of_lt hbda)
      have ht1 : (φ - a) / (b - a) ≤ 1 := by
        rw [div_le_iff₀ hbda]; linarith [hφ.2]
      have hcm := cnum_combo_le_max ht0 ht1 (u := g a) (v := g b)
      rw [hs]
      have key : g a + (g b - g a) / (b - a) * (φ - a)
          = (1 - (φ - a) / (b - a)) * g a + (φ - a) / (b - a) * g b := by
        field_simp [hbne]; ring
      rw [key]; exact hcm
    linarith [hmain, hc, hq]

end Work.CNum
