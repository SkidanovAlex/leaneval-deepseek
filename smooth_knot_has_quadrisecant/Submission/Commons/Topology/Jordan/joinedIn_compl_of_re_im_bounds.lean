import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Topology.Jordan

/-- If a set `T ⊆ ℂ` is contained in a rectangle `{α ≤ re ≤ β, c ≤ im ≤ d}` and `a` lies strictly
to the left of the rectangle while `b` lies strictly to the right of it, then `a` and `b` can be
joined by a path avoiding `T`.

Suggested proof: join `a` to `a + (d + 1 - a.im) * I` by a vertical segment (its real part is
`a.re < α`, hence it misses `T`), then go horizontally at imaginary part `d + 1 > d` to
`b + (d + 1 - b.im) * I`, then down to `b` (real part `b.re > β`).  Use
`JoinedIn.of_segment_subset` and `JoinedIn.trans`. -/
theorem joinedIn_compl_of_re_im_bounds {T : Set ℂ} {α β c d : ℝ} {a b : ℂ}
    (hT : ∀ w ∈ T, α ≤ w.re ∧ w.re ≤ β ∧ c ≤ w.im ∧ w.im ≤ d)
    (ha : a.re < α) (hb : β < b.re) : JoinedIn Tᶜ a b := by
  set a' : ℂ := a + ((d + 1 - a.im : ℝ) : ℂ) * Complex.I with ha'def
  set b' : ℂ := b + ((d + 1 - b.im : ℝ) : ℂ) * Complex.I with hb'def
  have hre_a' : a'.re = a.re := by
    rw [ha'def]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have him_a' : a'.im = d + 1 := by
    rw [ha'def]; simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hre_b' : b'.re = b.re := by
    rw [hb'def]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have him_b' : b'.im = d + 1 := by
    rw [hb'def]; simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hseg1 : segment ℝ a a' ⊆ Tᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzT
    have hzre : z.re = a.re := by
      have hconv : Convex ℝ {w : ℂ | w.re = a.re} := by
        have h := convex_hyperplane (𝕜 := ℝ) (f := Complex.reLm) Complex.reLm.isLinear a.re
        simpa using h
      exact hconv.segment_subset (by simp) hre_a' hz
    have h1 := (hT z hzT).1
    linarith
  have hseg2 : segment ℝ a' b' ⊆ Tᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzT
    have hzim : z.im = d + 1 := by
      have hconv : Convex ℝ {w : ℂ | w.im = d + 1} := by
        have h := convex_hyperplane (𝕜 := ℝ) (f := Complex.imLm) Complex.imLm.isLinear (d + 1)
        simpa using h
      exact hconv.segment_subset him_a' him_b' hz
    have h2 := (hT z hzT).2.2.2
    linarith
  have hseg3 : segment ℝ b' b ⊆ Tᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzT
    have hzre : z.re = b.re := by
      have hconv : Convex ℝ {w : ℂ | w.re = b.re} := by
        have h := convex_hyperplane (𝕜 := ℝ) (f := Complex.reLm) Complex.reLm.isLinear b.re
        simpa using h
      exact hconv.segment_subset hre_b' (by simp) hz
    have h3 := (hT z hzT).2.1
    linarith
  exact (JoinedIn.of_segment_subset hseg1).trans
    ((JoinedIn.of_segment_subset hseg2).trans (JoinedIn.of_segment_subset hseg3))

end Commons.Topology.Jordan