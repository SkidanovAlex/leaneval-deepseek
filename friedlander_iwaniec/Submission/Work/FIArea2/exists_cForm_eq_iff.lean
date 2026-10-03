import Mathlib
import Submission.Work.FIArea2.area2_r3

namespace Work.FIArea2

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The converse of (6.3)-(6.5): Cramer's rule in coordinates

Writing `z_i = a_i + b_i ī` and `w = x + y ī`, the linear form of (6.3) is

`Re(w z₁) = a₁x - b₁y`,  `Re(w z₂) = a₂x - b₂y`,

a `2×2` system with determinant `-(a₁b₂ - a₂b₁) = -Δ`.  The converse of (6.4)-(6.5) is therefore
Cramer's rule: the congruence `Δ ∣ c₁²z₂ - c₂²z₁` says exactly that `Δ` divides the two numerators,
hence that `(c₁², c₂²)` lies in the image lattice. -/

/-- Integer form of Cramer's rule for the system of (6.3): with `Δ = a₁b₂ - a₂b₁ ≠ 0`, the values
`x, y` determined by `Δx = b₂u - b₁v`, `Δy = a₂u - a₁v` are the unique solutions of
`a₁x - b₁y = u`, `a₂x - b₂y = v`. -/
private lemma cramer (a1 b1 a2 b2 u v x y : ℤ) (hΔ : a1 * b2 - a2 * b1 ≠ 0)
    (hx : (a1 * b2 - a2 * b1) * x = b2 * u - b1 * v)
    (hy : (a1 * b2 - a2 * b1) * y = a2 * u - a1 * v) :
    a1 * x - b1 * y = u ∧ a2 * x - b2 * y = v := by
  have key1 : (a1 * b2 - a2 * b1) * (a1 * x - b1 * y) = (a1 * b2 - a2 * b1) * u := by
    calc (a1 * b2 - a2 * b1) * (a1 * x - b1 * y)
        = a1 * ((a1 * b2 - a2 * b1) * x) - b1 * ((a1 * b2 - a2 * b1) * y) := by ring
      _ = a1 * (b2 * u - b1 * v) - b1 * (a2 * u - a1 * v) := by rw [hx, hy]
      _ = (a1 * b2 - a2 * b1) * u := by ring
  have key2 : (a1 * b2 - a2 * b1) * (a2 * x - b2 * y) = (a1 * b2 - a2 * b1) * v := by
    calc (a1 * b2 - a2 * b1) * (a2 * x - b2 * y)
        = a2 * ((a1 * b2 - a2 * b1) * x) - b2 * ((a1 * b2 - a2 * b1) * y) := by ring
      _ = a2 * (b2 * u - b1 * v) - b2 * (a2 * u - a1 * v) := by rw [hx, hy]
      _ = (a1 * b2 - a2 * b1) * v := by ring
  exact ⟨mul_left_cancel₀ hΔ key1, mul_left_cancel₀ hΔ key2⟩

/-- **(*FI* (6.3)-(6.5)), the §6 parametrisation of the w-sum.**  For `z₁, z₂` with
`Δ(z₁,z₂) = Im(z̄₁z₂) ≠ 0`, the map `w ↦ (Re(wz₁), Re(wz₂))` is a bijection from the Gaussian
integers onto the pairs `(c₁², c₂²)` of squares satisfying the congruence
`c₁²z₂ ≡ c₂²z₁ (mod Δ)`; the inverse is `w = star ((c₁²z₂ − c₂²z₁)/(īΔ))`.
`Submission/Work/FIArea2/area2_r3.lean` proves the forward direction (`Delta_dvd_of_cForm_eq_sq`)
and the injectivity (`cForm_pair_injective`); this is the converse. -/
theorem exists_cForm_eq_iff (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (c1 c2 : ℤ) :
    (∃ w : GaussianInt, Work.FIPlan.cForm w z1 = c1 * c1 ∧ Work.FIPlan.cForm w z2 = c2 * c2)
      ↔ (Work.FIPlan.Delta z1 z2 : GaussianInt)
          ∣ (c1 : GaussianInt) ^ 2 * z2 - (c2 : GaussianInt) ^ 2 * z1 := by
  constructor
  · rintro ⟨w, h1, h2⟩
    exact Delta_dvd_of_cForm_eq_sq h1 h2
  · intro h
    obtain ⟨q, hq⟩ := h
    obtain ⟨a1, b1⟩ := z1
    obtain ⟨a2, b2⟩ := z2
    -- `Δ` in coordinates
    have hΔcoordZ : Work.FIPlan.Delta (⟨a1, b1⟩ : GaussianInt) (⟨a2, b2⟩ : GaussianInt)
        = a1 * b2 - a2 * b1 := by
      rw [Work.FIPlan.Delta]
      simp [Zsqrtd.star_mk, Zsqrtd.im_mul]
      ring
    rw [hΔcoordZ] at hq
    have hA : a1 * b2 - a2 * b1 ≠ 0 := by
      intro hc
      apply hΔ
      rw [hΔcoordZ, hc]
    -- real and imaginary parts of the congruence `Δ ∣ c₁²z₂ - c₂²z₁`
    have hre : c1 * c1 * a2 - c2 * c2 * a1 = (a1 * b2 - a2 * b1) * q.re := by
      have hh := congrArg Zsqrtd.re hq
      simp [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast,
        Zsqrtd.im_intCast, Zsqrtd.re_sub, Zsqrtd.im_sub, pow_two] at hh
      ring_nf at hh ⊢
      exact hh
    have him : c1 * c1 * b2 - c2 * c2 * b1 = (a1 * b2 - a2 * b1) * q.im := by
      have hh := congrArg Zsqrtd.im hq
      simp [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast,
        Zsqrtd.im_intCast, Zsqrtd.re_sub, Zsqrtd.im_sub, pow_two] at hh
      ring_nf at hh ⊢
      exact hh
    obtain ⟨h1, h2⟩ := cramer a1 b1 a2 b2 (c1 * c1) (c2 * c2) q.im q.re hA
      (by rw [him.symm]; ring) (by rw [hre.symm]; ring)
    refine ⟨(⟨q.im, q.re⟩ : GaussianInt), ?_, ?_⟩
    · have key : Work.FIPlan.cForm (⟨q.im, q.re⟩ : GaussianInt) (⟨a1, b1⟩ : GaussianInt)
          = a1 * q.im - b1 * q.re := by
        simp [Work.FIPlan.cForm, Zsqrtd.re_mul]
        ring
      rw [key]
      linarith
    · have key : Work.FIPlan.cForm (⟨q.im, q.re⟩ : GaussianInt) (⟨a2, b2⟩ : GaussianInt)
          = a2 * q.im - b2 * q.re := by
        simp [Work.FIPlan.cForm, Zsqrtd.re_mul]
        ring
      rw [key]
      linarith

end

end Work.FIArea2
