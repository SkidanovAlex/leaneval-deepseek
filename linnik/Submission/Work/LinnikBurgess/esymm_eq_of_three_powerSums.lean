import Mathlib

namespace Work.LinnikBurgess

/-- Auxiliary algebraic core.

If two triples `x` and `y` of nonzero elements have equal power sums `p₁, p₂, p₃`
(in a field with `2 ≠ 0` and `3 ≠ 0`), then the triples `xᵢ⁻¹ - r` and `yᵢ⁻¹ - r`
have equal elementary symmetric functions.

The proof: Newton's identities show that equal power sums `p₁,p₂,p₃` force the
elementary symmetric functions `e₁,e₂,e₃` of the two triples to agree. Then `xᵢ⁻¹ - r`
is obtained from `xᵢ` by the substitution `t ↦ t⁻¹ - r`, which acts on the
elementary symmetric functions by an explicit formula determined only by
`e₁,e₂,e₃` of the input. -/
private lemma key {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (r x0 x1 x2 y0 y1 y2 : k)
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0)
    (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
    (hp1 : x0 + x1 + x2 = y0 + y1 + y2)
    (hp2 : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 = y0 ^ 2 + y1 ^ 2 + y2 ^ 2)
    (hp3 : x0 ^ 3 + x1 ^ 3 + x2 ^ 3 = y0 ^ 3 + y1 ^ 3 + y2 ^ 3) :
    (x0⁻¹ - r) + (x1⁻¹ - r) + (x2⁻¹ - r)
      = (y0⁻¹ - r) + (y1⁻¹ - r) + (y2⁻¹ - r)
    ∧ (x0⁻¹ - r) * (x1⁻¹ - r) + (x0⁻¹ - r) * (x2⁻¹ - r) + (x1⁻¹ - r) * (x2⁻¹ - r)
      = (y0⁻¹ - r) * (y1⁻¹ - r) + (y0⁻¹ - r) * (y2⁻¹ - r) + (y1⁻¹ - r) * (y2⁻¹ - r)
    ∧ (x0⁻¹ - r) * (x1⁻¹ - r) * (x2⁻¹ - r)
      = (y0⁻¹ - r) * (y1⁻¹ - r) * (y2⁻¹ - r) := by
  -- Newton's identities: `e₂ = (p₁² - p₂)/2` and `e₃ = (p₁³ - 3 p₁ p₂ + 2 p₃)/6`.
  have E2 : x0 * x1 + x0 * x2 + x1 * x2 = y0 * y1 + y0 * y2 + y1 * y2 := by
    have e : 2 * (x0 * x1 + x0 * x2 + x1 * x2)
        = (x0 + x1 + x2) ^ 2 - (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) := by ring
    have f : 2 * (y0 * y1 + y0 * y2 + y1 * y2)
        = (y0 + y1 + y2) ^ 2 - (y0 ^ 2 + y1 ^ 2 + y2 ^ 2) := by ring
    have h : 2 * (x0 * x1 + x0 * x2 + x1 * x2)
        = 2 * (y0 * y1 + y0 * y2 + y1 * y2) := by rw [e, f, hp1, hp2]
    exact mul_left_cancel₀ h2 h
  have E3 : x0 * x1 * x2 = y0 * y1 * y2 := by
    have h6 : (6 : k) ≠ 0 := by
      have h : (6 : k) = 2 * 3 := by norm_num
      rw [h]; exact mul_ne_zero h2 h3
    have e : 6 * (x0 * x1 * x2)
        = (x0 + x1 + x2) ^ 3 - 3 * (x0 + x1 + x2) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2)
          + 2 * (x0 ^ 3 + x1 ^ 3 + x2 ^ 3) := by ring
    have f : 6 * (y0 * y1 * y2)
        = (y0 + y1 + y2) ^ 3 - 3 * (y0 + y1 + y2) * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2)
          + 2 * (y0 ^ 3 + y1 ^ 3 + y2 ^ 3) := by ring
    have h : 6 * (x0 * x1 * x2) = 6 * (y0 * y1 * y2) := by rw [e, f, hp1, hp2, hp3]
    exact mul_left_cancel₀ h6 h
  refine ⟨?_, ?_, ?_⟩
  · have t : (x0⁻¹ - r) + (x1⁻¹ - r) + (x2⁻¹ - r)
        = (x0 * x1 + x0 * x2 + x1 * x2) * (x0 * x1 * x2)⁻¹ - 3 * r := by
      field_simp; ring
    have t' : (y0⁻¹ - r) + (y1⁻¹ - r) + (y2⁻¹ - r)
        = (y0 * y1 + y0 * y2 + y1 * y2) * (y0 * y1 * y2)⁻¹ - 3 * r := by
      field_simp; ring
    rw [t, t', E2, E3]
  · have t : (x0⁻¹ - r) * (x1⁻¹ - r) + (x0⁻¹ - r) * (x2⁻¹ - r)
          + (x1⁻¹ - r) * (x2⁻¹ - r)
        = (x0 + x1 + x2) * (x0 * x1 * x2)⁻¹
          - 2 * r * ((x0 * x1 + x0 * x2 + x1 * x2) * (x0 * x1 * x2)⁻¹) + 3 * r ^ 2 := by
      field_simp; ring
    have t' : (y0⁻¹ - r) * (y1⁻¹ - r) + (y0⁻¹ - r) * (y2⁻¹ - r)
          + (y1⁻¹ - r) * (y2⁻¹ - r)
        = (y0 + y1 + y2) * (y0 * y1 * y2)⁻¹
          - 2 * r * ((y0 * y1 + y0 * y2 + y1 * y2) * (y0 * y1 * y2)⁻¹) + 3 * r ^ 2 := by
      field_simp; ring
    rw [t, t', hp1, E2, E3]
  · have t : (x0⁻¹ - r) * (x1⁻¹ - r) * (x2⁻¹ - r)
        = 1 * (x0 * x1 * x2)⁻¹ - r * (x0 + x1 + x2) * (x0 * x1 * x2)⁻¹
          + r ^ 2 * ((x0 * x1 + x0 * x2 + x1 * x2) * (x0 * x1 * x2)⁻¹) - r ^ 3 := by
      field_simp; ring
    have t' : (y0⁻¹ - r) * (y1⁻¹ - r) * (y2⁻¹ - r)
        = 1 * (y0 * y1 * y2)⁻¹ - r * (y0 + y1 + y2) * (y0 * y1 * y2)⁻¹
          + r ^ 2 * ((y0 * y1 + y0 * y2 + y1 * y2) * (y0 * y1 * y2)⁻¹) - r ^ 3 := by
      field_simp; ring
    rw [t, t', hp1, E2, E3]

theorem esymm_eq_of_three_powerSums {k : Type*} [Field k]
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (a b : Fin 3 → k) (r : k)
    (hu : ∀ l : Fin 3, r + a l ≠ 0 ∧ r + b l ≠ 0)
    (H1 : (∑ l : Fin 3, (r + a l)⁻¹) = (∑ l : Fin 3, (r + b l)⁻¹))
    (H2 : (∑ l : Fin 3, ((r + a l)⁻¹) ^ 2) = (∑ l : Fin 3, ((r + b l)⁻¹) ^ 2))
    (H3 : (∑ l : Fin 3, ((r + a l)⁻¹) ^ 3) = (∑ l : Fin 3, ((r + b l)⁻¹) ^ 3)) :
    a 0 + a 1 + a 2 = b 0 + b 1 + b 2
      ∧ a 0 * a 1 + a 0 * a 2 + a 1 * a 2 = b 0 * b 1 + b 0 * b 2 + b 1 * b 2
      ∧ a 0 * a 1 * a 2 = b 0 * b 1 * b 2 := by
  -- Expand the three sums over `Fin 3`.
  have H1' : (r + a 0)⁻¹ + (r + a 1)⁻¹ + (r + a 2)⁻¹
      = (r + b 0)⁻¹ + (r + b 1)⁻¹ + (r + b 2)⁻¹ := by
    simpa only [Fin.sum_univ_three] using H1
  have H2' : ((r + a 0)⁻¹) ^ 2 + ((r + a 1)⁻¹) ^ 2 + ((r + a 2)⁻¹) ^ 2
      = ((r + b 0)⁻¹) ^ 2 + ((r + b 1)⁻¹) ^ 2 + ((r + b 2)⁻¹) ^ 2 := by
    simpa only [Fin.sum_univ_three] using H2
  have H3' : ((r + a 0)⁻¹) ^ 3 + ((r + a 1)⁻¹) ^ 3 + ((r + a 2)⁻¹) ^ 3
      = ((r + b 0)⁻¹) ^ 3 + ((r + b 1)⁻¹) ^ 3 + ((r + b 2)⁻¹) ^ 3 := by
    simpa only [Fin.sum_univ_three] using H3
  have h := key h2 h3 r ((r + a 0)⁻¹) ((r + a 1)⁻¹) ((r + a 2)⁻¹)
    ((r + b 0)⁻¹) ((r + b 1)⁻¹) ((r + b 2)⁻¹)
    (inv_ne_zero (hu 0).1) (inv_ne_zero (hu 1).1) (inv_ne_zero (hu 2).1)
    (inv_ne_zero (hu 0).2) (inv_ne_zero (hu 1).2) (inv_ne_zero (hu 2).2)
    H1' H2' H3'
  -- Rewrite `a i` and `b i` as `((r + ·)⁻¹)⁻¹ - r`.
  have e0 : a 0 = ((r + a 0)⁻¹)⁻¹ - r := by rw [inv_inv]; ring
  have e1 : a 1 = ((r + a 1)⁻¹)⁻¹ - r := by rw [inv_inv]; ring
  have e2 : a 2 = ((r + a 2)⁻¹)⁻¹ - r := by rw [inv_inv]; ring
  have f0 : b 0 = ((r + b 0)⁻¹)⁻¹ - r := by rw [inv_inv]; ring
  have f1 : b 1 = ((r + b 1)⁻¹)⁻¹ - r := by rw [inv_inv]; ring
  have f2 : b 2 = ((r + b 2)⁻¹)⁻¹ - r := by rw [inv_inv]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, e1, e2, f0, f1, f2]; exact h.1
  · rw [e0, e1, e2, f0, f1, f2]; exact h.2.1
  · rw [e0, e1, e2, f0, f1, f2]; exact h.2.2

end Work.LinnikBurgess
