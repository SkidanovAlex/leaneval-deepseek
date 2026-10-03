import Mathlib
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.Defs

/-!
# The segment between unit neighbours of a lattice point

`adjSeg u v = segment ℝ (lpt u) (lpt v)` is the closed segment joining the lattice points `u` and
`v`; when `v` is one of the four unit neighbours of `u` this is one of the unit grid segments
`hSeg`/`vSeg` used to define `wallSet A`.
-/

namespace Work.HornSC.CellBoundaryJordan.WallCycle

open Work.HornSC

/-- `adjSeg` is symmetric in its two arguments. -/
lemma adjSeg_symm (u v : ℤ × ℤ) : adjSeg u v = adjSeg v u := segment_symm ℝ _ _

/-- The segment from `u` to its eastern neighbour is `hSeg u`. -/
theorem adjSeg_east (u : ℤ × ℤ) : adjSeg u (u.1 + 1, u.2) = hSeg u := by
  rw [adjSeg, hSeg, segment_eq_image_lineMap]
  ext z
  simp only [Set.mem_image, Set.mem_Icc, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, htz⟩
    have hre : z.re = (1 - t) * (u.1 : ℝ) + t * ((u.1 : ℝ) + 1) := by
      have := congrArg Complex.re htz.symm
      simpa [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re, lpt, smul_eq_mul]
        using this
    have him : z.im = (u.2 : ℝ) := by
      have := congrArg Complex.im htz.symm
      simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.smul_im, lpt,
        smul_eq_mul] at this
      linarith [show (1 - t) * (u.2 : ℝ) + t * (u.2 : ℝ) = (u.2 : ℝ) by ring]
    exact ⟨him, by linarith [ht.1], by linarith [ht.2]⟩
  · rintro ⟨him, h1, h2⟩
    refine ⟨z.re - u.1, ⟨by linarith, by linarith⟩, ?_⟩
    apply Complex.ext
    · simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re, lpt, smul_eq_mul]
      push_cast
      ring
    · simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.smul_im, lpt, him,
        smul_eq_mul]
      ring

/-- The segment from `u` to its western neighbour is `hSeg (u.1 - 1, u.2)`. -/
theorem adjSeg_west (u : ℤ × ℤ) : adjSeg u (u.1 - 1, u.2) = hSeg (u.1 - 1, u.2) := by
  have h : u = ((u.1 - 1) + 1, u.2) := by ext <;> omega
  have key := congrArg (fun w : ℤ × ℤ => adjSeg w (u.1 - 1, u.2)) h
  rw [key, adjSeg_symm]
  exact adjSeg_east (u.1 - 1, u.2)

/-- The segment from `u` to its northern neighbour is `vSeg u`. -/
theorem adjSeg_north (u : ℤ × ℤ) : adjSeg u (u.1, u.2 + 1) = vSeg u := by
  rw [adjSeg, vSeg, segment_eq_image_lineMap]
  ext z
  simp only [Set.mem_image, Set.mem_Icc, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, htz⟩
    have him : z.im = (1 - t) * (u.2 : ℝ) + t * ((u.2 : ℝ) + 1) := by
      have := congrArg Complex.im htz.symm
      simpa [AffineMap.lineMap_apply_module, Complex.add_im, Complex.smul_im, lpt, smul_eq_mul]
        using this
    have hre : z.re = (u.1 : ℝ) := by
      have := congrArg Complex.re htz.symm
      simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re, lpt,
        smul_eq_mul] at this
      linarith [show (1 - t) * (u.1 : ℝ) + t * (u.1 : ℝ) = (u.1 : ℝ) by ring]
    exact ⟨hre, by linarith [ht.1], by linarith [ht.2]⟩
  · rintro ⟨hre, h1, h2⟩
    refine ⟨z.im - u.2, ⟨by linarith, by linarith⟩, ?_⟩
    apply Complex.ext
    · simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re, lpt, hre,
        smul_eq_mul]
      ring
    · simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.smul_im, lpt, smul_eq_mul]
      push_cast
      ring

/-- The segment from `u` to its southern neighbour is `vSeg (u.1, u.2 - 1)`. -/
theorem adjSeg_south (u : ℤ × ℤ) : adjSeg u (u.1, u.2 - 1) = vSeg (u.1, u.2 - 1) := by
  have h : u = (u.1, (u.2 - 1) + 1) := by ext <;> omega
  have key := congrArg (fun w : ℤ × ℤ => adjSeg w (u.1, u.2 - 1)) h
  rw [key, adjSeg_symm]
  exact adjSeg_north (u.1, u.2 - 1)

end Work.HornSC.CellBoundaryJordan.WallCycle
