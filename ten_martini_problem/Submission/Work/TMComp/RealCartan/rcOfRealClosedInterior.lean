import Mathlib
import Submission.Work.TMComp.RealCartanDefs

/-!
# The real line inside `ℂ` has no interior, and closed sets of reals stay closed

`Complex.ofReal : ℝ → ℂ` is a closed embedding: its image is the real axis
`{z : ℂ | z.im = 0}`, which is closed and has empty interior in `ℂ`.  Hence for
any closed `B ⊆ ℝ` the image `Complex.ofReal '' B` is closed (it is
`{z | z.im = 0 ∧ z.re ∈ B}`) and has empty interior in `ℂ`.
-/

namespace Work.TMComp.RealCartan

theorem rcOfRealClosedInterior {B : Set ℝ} (hB : IsClosed B) :
    IsClosed (Complex.ofReal '' B) ∧ interior (Complex.ofReal '' B) = ∅ := by
  -- the image of `B` is exactly the set of complex numbers on the real axis whose real part lies in `B`
  have hset : Complex.ofReal '' B = {z : ℂ | z.im = 0 ∧ z.re ∈ B} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Complex.ofReal_im x, hx⟩
    · rintro ⟨him, hre⟩
      exact ⟨z.re, hre, Complex.ext (by simp) (by simp [him])⟩
  constructor
  · -- intersection of the real axis (closed) with `re ⁻¹' B` (closed)
    rw [hset]
    exact (isClosed_eq Complex.continuous_im continuous_const).inter
      (hB.preimage Complex.continuous_re)
  · -- the real axis has empty interior in `ℂ`
    rw [hset]
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz)
    have hzim : z.im = 0 := (interior_subset hz).1
    -- a point of the ball with nonzero imaginary part
    set w : ℂ := z + ((ε / 2 : ℝ) : ℂ) * Complex.I with hw
    have hwball : w ∈ Metric.ball z ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : w - z = ((ε / 2 : ℝ) : ℂ) * Complex.I := by simp [hw]
      rw [hsub, norm_mul, Complex.norm_I, mul_one]
      have h1 : ‖(((ε / 2 : ℝ)) : ℂ)‖ = |ε / 2| := RCLike.norm_ofReal (ε / 2)
      have h2 : |ε / 2| = ε / 2 := abs_of_nonneg (by linarith)
      linarith
    have hwim : w.im = ε / 2 := by
      simp [hw, Complex.mul_im, hzim]
    have hwmem : w ∈ {z : ℂ | z.im = 0 ∧ z.re ∈ B} := interior_subset (hball hwball)
    have hthis : w.im = 0 := hwmem.1
    rw [hwim] at hthis
    linarith

end Work.TMComp.RealCartan
