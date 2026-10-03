import Mathlib
import Submission.Work.Horn.fatouQ_defs

namespace Work.Horn.FatouQ

open Work.Horn.Flower

/-- `cc q a = -1/(q a) ≠ 0` for `q ≥ 1` and `a ≠ 0`. -/
theorem cc_ne_zero {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (ha : a ≠ 0) : cc q a ≠ 0 := by
  rw [cc]
  exact div_ne_zero (by norm_num) (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) ha)

/-- The inverse chart rewritten through the *reciprocal* chart: since `cc q a ≠ 0` we have
`(cc/w)/cc = 1/w`, so `zBranch q a j w = ζ j · exp (log (1/w)/q)` as functions of `w`.  This is
the form in which differentiability is proved (the branch point of `log` is moved to `1/w`, which
lies in the right half plane as soon as `0 < w.re`). -/
theorem zBranch_eq {q : ℕ} {a : ℂ} (hcc : cc q a ≠ 0) (j : Fin q) :
    zBranch q a j = fun w : ℂ => zeta q a j * Complex.exp (Complex.log (w⁻¹) / (q : ℂ)) := by
  funext w
  rw [zBranch, rootFun]
  have : (cc q a / w) / cc q a = w⁻¹ := by field_simp
  rw [this]

theorem zBranch_contDiff {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (ha : a ≠ 0) (j : Fin q) :
    ∀ w : ℂ, 0 < w.re →
      DifferentiableAt ℂ (Work.Horn.FatouQ.zBranch q a j) w ∧
        ContinuousAt (Work.Horn.FatouQ.zBranch q a j) w := by
  intro w hw
  have hwne : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  rw [zBranch_eq (cc_ne_zero hq ha) j]
  have hu : 0 < (w⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hw (Complex.normSq_pos.mpr hwne)
  have h1 : DifferentiableAt ℂ (fun u : ℂ => u⁻¹) w := differentiableAt_inv hwne
  have h2 : DifferentiableAt ℂ (fun u : ℂ => Complex.log (u⁻¹)) w :=
    h1.clog (Complex.mem_slitPlane_iff.mpr (Or.inl hu))
  have h3 : DifferentiableAt ℂ (fun u : ℂ => Complex.log (u⁻¹) / (q : ℂ)) w := h2.div_const _
  have h4 : DifferentiableAt ℂ (fun u : ℂ => Complex.exp (Complex.log (u⁻¹) / (q : ℂ))) w := h3.cexp
  exact ⟨h4.const_mul _, h4.continuousAt.const_mul _⟩

end Work.Horn.FatouQ
