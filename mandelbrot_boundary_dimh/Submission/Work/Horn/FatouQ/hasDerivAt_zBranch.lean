import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.FatouQ.zBranch_contDiff

namespace Work.Horn.FatouQ

/-- `zBranch q a j` is the branch of the inverse chart: for `0 < w.re` (so that `w ≠ 0` and
`w⁻¹` lies in the slit plane) it agrees with
`w ↦ zeta q a j * exp (log (w⁻¹) / q)`, whose derivative is computed by the chain rule. -/
theorem hasDerivAt_zBranch {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (ha : a ≠ 0) (j : Fin q) {w : ℂ}
    (hw : 0 < w.re) :
    HasDerivAt (Work.Horn.FatouQ.zBranch q a j)
      (-(Work.Horn.FatouQ.zBranch q a j w) / ((q : ℂ) * w)) w := by
  have hcc := cc_ne_zero hq ha
  have hwne : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have hu : 0 < (w⁻¹).re := by
    rw [Complex.inv_re]; exact div_pos hw (Complex.normSq_pos.mpr hwne)
  have hslit : w⁻¹ ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hu)
  rw [zBranch_eq hcc j]
  have h1 : HasDerivAt (fun u : ℂ => u⁻¹) (-(w ^ 2)⁻¹) w := hasDerivAt_inv hwne
  have h2 : HasDerivAt (fun u : ℂ => Complex.log (u⁻¹)) ((-(w^2)⁻¹) / w⁻¹) w := h1.clog hslit
  have h3 : HasDerivAt (fun u : ℂ => Complex.log (u⁻¹) / (q : ℂ))
      (((-(w^2)⁻¹) / w⁻¹) / (q : ℂ)) w := h2.div_const _
  have h4 : HasDerivAt (fun u : ℂ => Complex.exp (Complex.log (u⁻¹) / (q : ℂ)))
      (Complex.exp (Complex.log (w⁻¹) / (q:ℂ)) * (((-(w^2)⁻¹)/w⁻¹)/(q:ℂ))) w := h3.cexp
  have h5 : HasDerivAt
      (fun u : ℂ => Work.Horn.Flower.zeta q a j * Complex.exp (Complex.log (u⁻¹) / (q : ℂ)))
      (Work.Horn.Flower.zeta q a j *
        (Complex.exp (Complex.log (w⁻¹) / (q:ℂ)) * (((-(w^2)⁻¹)/w⁻¹)/(q:ℂ)))) w :=
    h4.const_mul _
  refine h5.congr_deriv ?_
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end Work.Horn.FatouQ
