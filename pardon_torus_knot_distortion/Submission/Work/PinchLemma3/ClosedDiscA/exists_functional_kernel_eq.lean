import Mathlib

namespace Work.PinchLemma3.ClosedDiscA

/-- If two elements of a submodule of `ℚ × ℚ` have nonzero "determinant"
`v.1 * w.2 - v.2 * w.1`, then the submodule is everything. -/
lemma eq_top_of_mem_of_det_ne {V : Submodule ℚ (ℚ × ℚ)} {v w : ℚ × ℚ}
    (hv : v ∈ V) (hw : w ∈ V) (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) : V = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro z
  have hd' : w.2 * v.1 - w.1 * v.2 ≠ 0 := by
    rw [show w.2 * v.1 - w.1 * v.2 = v.1 * w.2 - v.2 * w.1 by ring]; exact hdet
  set α : ℚ := (z.1 * w.2 - z.2 * w.1) / (v.1 * w.2 - v.2 * w.1) with hα
  set β : ℚ := (v.1 * z.2 - v.2 * z.1) / (v.1 * w.2 - v.2 * w.1) with hβ
  have hz : z = α • v + β • w := by
    ext <;>
      simp only [hα, hβ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
    · field_simp [hd']
      ring
    · field_simp [hd']
      ring
  rw [hz]
  exact V.add_mem (V.smul_mem α hv) (V.smul_mem β hw)

/-- A nonzero proper `ℚ`-submodule of `ℚ × ℚ` is the kernel of a nonzero
integer linear functional: there are `a b : ℤ`, not both zero, such that an
integer vector `v` lies in `V` exactly when `b * v.1 - a * v.2 = 0`. -/
theorem exists_functional_kernel_eq (V : Submodule ℚ (ℚ × ℚ))
    (h0 : V ≠ ⊥) (h1 : V ≠ ⊤) :
    ∃ (a b : ℤ), (a, b) ≠ 0 ∧
      ∀ v : ℤ × ℤ,
        (((v.1 : ℚ), (v.2 : ℚ)) ∈ V ↔ (b : ℚ) * (v.1 : ℚ) - (a : ℚ) * (v.2 : ℚ) = 0) := by
  obtain ⟨w, hwV, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  set p : ℚ := w.1 with hp
  set q : ℚ := w.2 with hq
  have hw_eq : (p, q) = w := by rw [hp, hq]
  have hpq : (p, q) ≠ 0 := by rw [hw_eq]; exact hw0
  -- `V` is exactly the kernel of `(x, y) ↦ q * x - p * y`.
  have hiff : ∀ x y : ℚ, ((x, y) ∈ V ↔ q * x - p * y = 0) := by
    intro x y
    constructor
    · intro hxy
      by_contra hne
      have hdet : (x, y).1 * w.2 - (x, y).2 * w.1 ≠ 0 := by
        show x * w.2 - y * w.1 ≠ 0
        rw [← hp, ← hq]
        intro hcon
        exact hne (by linear_combination hcon)
      exact h1 (eq_top_of_mem_of_det_ne hxy hwV hdet)
    · intro h
      rcases eq_or_ne p 0 with hp0 | hp0
      · have hq0 : q ≠ 0 := by
          intro hq0; exact hpq (by simp [hp0, hq0])
        have hx0 : x = 0 := by
          have h' : q * x = 0 := by rw [hp0] at h; simpa using h
          exact (mul_eq_zero.mp h').resolve_left hq0
        have hmem : (x, y) = (y / q) • w := by
          rw [← hw_eq, hx0, hp0]
          ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          · ring
          · field_simp
        rw [hmem]; exact V.smul_mem _ hwV
      · have hmem : (x, y) = (x / p) • w := by
          rw [← hw_eq]
          ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          · field_simp
          · field_simp
            linear_combination -h
        rw [hmem]; exact V.smul_mem _ hwV
  -- Clear denominators: write `(p, q)` with a common (integer) denominator.
  have hden : ∀ r : ℚ, (r.num : ℚ) = (r.den : ℚ) * r := by
    intro r
    have h := Rat.num_div_den r
    have hd : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
    rw [div_eq_iff hd] at h
    rw [mul_comm] at h
    exact h
  have ha : (((p.num * (q.den : ℤ) : ℤ)) : ℚ) = ((p.den : ℚ) * (q.den : ℚ)) * p := by
    push_cast
    rw [hden p]; ring
  have hb : (((q.num * (p.den : ℤ) : ℤ)) : ℚ) = ((p.den : ℚ) * (q.den : ℚ)) * q := by
    push_cast
    rw [hden q]; ring
  have hμ : ((p.den : ℚ) * (q.den : ℚ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr p.den_nz) (Nat.cast_ne_zero.mpr q.den_nz)
  refine ⟨p.num * (q.den : ℤ), q.num * (p.den : ℤ), ?_, ?_⟩
  · intro hzero
    have ha0 : p.num * (q.den : ℤ) = 0 := by
      have := congrArg Prod.fst hzero; simpa using this
    have hb0 : q.num * (p.den : ℤ) = 0 := by
      have := congrArg Prod.snd hzero; simpa using this
    have hp0 : p = 0 := by
      have hthis : (((p.num * (q.den : ℤ) : ℤ)) : ℚ) = 0 := by rw [ha0]; simp
      rw [ha] at hthis
      exact (mul_eq_zero.mp hthis).resolve_left hμ
    have hq0 : q = 0 := by
      have hthis : (((q.num * (p.den : ℤ) : ℤ)) : ℚ) = 0 := by rw [hb0]; simp
      rw [hb] at hthis
      exact (mul_eq_zero.mp hthis).resolve_left hμ
    exact hpq (by simp [hp0, hq0])
  · intro v
    rw [hiff (v.1 : ℚ) (v.2 : ℚ)]
    have key : (((q.num * (p.den : ℤ) : ℤ)) : ℚ) * (v.1 : ℚ)
                - (((p.num * (q.den : ℤ) : ℤ)) : ℚ) * (v.2 : ℚ)
              = ((p.den : ℚ) * (q.den : ℚ)) * (q * (v.1 : ℚ) - p * (v.2 : ℚ)) := by
      rw [hb, ha]; ring
    rw [key]
    exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_eq_zero.mp h).resolve_left hμ⟩

end Work.PinchLemma3.ClosedDiscA
