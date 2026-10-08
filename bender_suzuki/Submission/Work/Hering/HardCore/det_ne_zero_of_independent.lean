import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-- Two vectors `u v : F × F` that are linearly independent (in the sense that a
vanishing linear combination forces both coefficients to be zero) have nonzero
determinant `u.1 * v.2 - u.2 * v.1`. -/
theorem det_ne_zero_of_independent {F : Type*} [Field F] (u v : F × F)
    (h : ∀ a b : F, a • u + b • v = 0 → a = 0 ∧ b = 0) :
    u.1 * v.2 - u.2 * v.1 ≠ 0 := by
  intro hdet
  -- The combination `v.2 • u - u.2 • v` has first coordinate the determinant
  -- and second coordinate zero, hence vanishes when the determinant does.
  have key1 : v.2 • u + (-u.2) • v = 0 := by
    have h1a : (v.2 • u + (-u.2) • v).1 = 0 := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [← hdet]; ring
    have h1b : (v.2 • u + (-u.2) • v).2 = 0 := by
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      ring
    exact Prod.ext h1a h1b
  have h1 := h v.2 (-u.2) key1
  -- Symmetrically, `-v.1 • u + u.1 • v` has first coordinate zero and second
  -- coordinate the determinant.
  have key2 : (-v.1) • u + u.1 • v = 0 := by
    have h2a : ((-v.1) • u + u.1 • v).1 = 0 := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      ring
    have h2b : ((-v.1) • u + u.1 • v).2 = 0 := by
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [← hdet]; ring
    exact Prod.ext h2a h2b
  have h2 := h (-v.1) u.1 key2
  -- Independence forces every coordinate of `u` to vanish.
  obtain ⟨_, hu2'⟩ := h1
  obtain ⟨_, hu1⟩ := h2
  have hu2 : u.2 = 0 := neg_eq_zero.mp hu2'
  have hu : u = 0 := by
    ext <;> simp [hu1, hu2]
  -- But then `1 • 0 + 0 • v = 0` contradicts `h` at `(a, b) = (1, 0)`.
  exact one_ne_zero (h 1 0 (by simp [hu])).1

end Work.Hering.HardCore
