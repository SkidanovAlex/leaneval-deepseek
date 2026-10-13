import Mathlib

namespace Work.WilG4c

open ContinuousMultilinearMap

/-- Adding a constant to the *values* of a function does not change its `(n+1)`-st iterated
Fréchet derivative, for any `n`.  This is the function-level form of the statement; the
`m ≥ 1` hypothesis of the main theorem is exactly what allows us to use `n` producing `m = n+1`.

The proof is by induction on `n`.  Everything rests on the unconditional identity
`fderiv 𝕜 (fun y ↦ h y + c) x = fderiv 𝕜 h x` (`fderiv_add_const`), which holds even where `h`
is not differentiable because both sides degenerate to `0`. -/
private theorem iteratedFDeriv_fun_add_const_aux {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ) (h : E → G) (c : G) :
    iteratedFDeriv ℝ (n + 1) (fun y => h y + c) = iteratedFDeriv ℝ (n + 1) h := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
    -- At level `0` the two functions differ by the constant `curry0 c`.
    have h0 : iteratedFDeriv ℝ 0 (fun y => h y + c)
        = (fun y => iteratedFDeriv ℝ 0 h y + (continuousMultilinearCurryFin0 ℝ E G).symm c) := by
      ext y
      simp [iteratedFDeriv_zero_eq_comp, map_add]
    rw [h0]
    congr 1
    funext y
    rw [fderiv_add_const]
  | succ n ih =>
    -- The `(n+2)`-nd derivative is the derivative of the `(n+1)`-st one, which agrees with the
    -- corresponding derivative of `h` by the induction hypothesis.
    rw [iteratedFDeriv_succ_eq_comp_left (n := n + 1) (f := fun y => h y + c),
      iteratedFDeriv_succ_eq_comp_left (n := n + 1) (f := h), ih]

theorem iteratedFDeriv_fun_add_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ} (hm : 1 ≤ m) (f : E → F) (b : F) (x : E) :
    iteratedFDeriv ℝ m (fun y => f y + b) x = iteratedFDeriv ℝ m f x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [iteratedFDeriv_fun_add_const_aux k f b]

end Work.WilG4c
