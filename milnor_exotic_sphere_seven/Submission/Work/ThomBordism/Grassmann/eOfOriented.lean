import Mathlib
import Submission.Work.ThomBordism.Grassmann.coframingDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Grassmann

/-- **The coframing `eOf Γ i` is positively oriented for `Γ`.**  On the member `cfGoodSet Γ i` of the
covering, the sign of the `S`-minor of any frame representing `Γ y` is the sign `cfSignOf i.2` of the
index `i` (`frameSign_eq_of_mem_goodSet`), so the sign-corrected frame matrix
`(frameMatrix S f)⁻¹ * cfSignMat (cfSignOf i.2)` — the matrix of the frame `eOf Γ i y` in the frame
`f` — has positive determinant. -/
theorem eOfOriented {k m : ℕ} {M : Type} [TopologicalSpace M]
    {Γ : M → Work.ThomBordism.Grassmann.OG k m}
    {i : Work.ThomBordism.Grassmann.ChartIdx k m × Bool} {y : M}
    (hy : y ∈ Work.ThomBordism.Grassmann.cfGoodSet Γ i) :
    0 < (Matrix.det ((Work.ThomBordism.Grassmann.frameMatrix i.1 (Quotient.out (Γ y)).1)⁻¹
      * Work.ThomBordism.Grassmann.cfSignMat (Work.ThomBordism.Grassmann.cfSignOf i.2))) := by
  have hmk : Quotient.mk'' (Quotient.out (Γ y)) = Γ y := Quotient.out_eq (Γ y)
  have hbase : Quotient.mk'' (Quotient.out (Γ y)) ∈ baseSet i.1 := by rw [hmk]; exact hy.1
  have hfS : Quotient.out (Γ y) ∈ chartSet i.1 :=
    (mem_baseSet_iff i.1 (Quotient.out (Γ y))).mp hbase
  have hsign : frameSign i.1 (Γ y) = cfSignOf i.2 := frameSign_eq_of_mem_goodSet hy
  have hAdet : (frameMatrix i.1 (Quotient.out (Γ y)).1).det ≠ 0 := hfS
  have hdet : (frameMatrix i.1 (Quotient.out (Γ y)).1).det
      = cfSignOf i.2 * |(frameMatrix i.1 (Quotient.out (Γ y)).1).det| := by
    have h := frameMatrix_det_eq_sign i.1 (Quotient.out (Γ y)) hfS
    rw [hmk, hsign] at h
    exact h
  have hBdet : (cfSignMat (k := k) (cfSignOf i.2)).det = cfSignOf i.2 := by
    rw [signMat_eq_orientMat (S := i.1) (x := Γ y) (ε := cfSignOf i.2) hsign, orientMat_det,
      hsign]
  have hmain : (frameMatrix i.1 (Quotient.out (Γ y)).1)⁻¹.det
        * (cfSignMat (k := k) (cfSignOf i.2)).det
      = |(frameMatrix i.1 (Quotient.out (Γ y)).1).det|⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hBdet]
    have h3 : ((frameMatrix i.1 (Quotient.out (Γ y)).1).det⁻¹ * cfSignOf i.2)
        * |(frameMatrix i.1 (Quotient.out (Γ y)).1).det| = 1 := by
      rw [mul_assoc, ← hdet, inv_mul_cancel₀ hAdet]
    exact eq_inv_of_mul_eq_one_left h3
  rw [Matrix.det_mul, hmain]
  exact inv_pos.mpr (abs_pos.mpr hAdet)

end Work.ThomBordism.Grassmann
