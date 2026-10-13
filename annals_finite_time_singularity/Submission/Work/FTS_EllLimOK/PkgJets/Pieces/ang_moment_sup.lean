import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKAbsLeSqrtEta
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets.Pieces

open MeasureTheory

set_option linter.unusedVariables false

/-- **Pointwise (in `z`) bound for the angular moment of a class-`C` datum.**

`Qang g m z = ∫_θ K(θ)·D_z^m g(z,θ) dθ` is bounded by `4√3·|g|_{ℋ⁶}` for **every** `z > 0`
(not merely a.e.), as soon as `m ≤ 3` and `α ∈ (0,1]`.

Route.  Weighted angular Cauchy–Schwarz (`FKAbsLeSqrtEta`, constant `4` against the weight
`sin(2θ)^{-η}`) reduces the claim to the *uniform-in-`z`* slice bound
`∫_θ sin(2θ)^{-η}(D_z^m g(z,θ))² ≤ 3·HkSq α 6 g` (`fkSliceSup_sliceSupGraded`, constant `3`,
slots with `i + j + 1 ≤ k`).  Since `m ≤ 3`, the slot `(m,0)` satisfies `m + 1 ≤ 6`, and taking
the square root gives `4·√(3·HkSq α 6 g) = 4√3·Xn6 α g`. -/
theorem ang_moment_sup {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α g) {m : ℕ} (hm : m ≤ 3) {z : ℝ} (hz : 0 < z) :
    |Work.Elliptic.Qang g m z| ≤ 4 * Real.sqrt 3 * Work.FTS.StrongGlobal.Xn6 α g := by
  -- `ℋ⁶`-honesty of `g` (the class supplies `ℋ⁷` and `ℋ⁸`)
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 6 (by norm_num) hg.mem
  -- integrability of the weighted slice of `D_z^m g` at the given `z > 0`
  have hInt : IntegrableOn
      (fun θ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter m g z θ) ^ 2) Work.Spaces.Iθ := by
    have h := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_slice_integrable
      hα hg.reg hmem6 (j := m) (i := 0) (by omega) hz
    simp only [Work.Spaces.mixed_zero_right] at h
    exact h
  -- weighted angular Cauchy–Schwarz (constant `4`)
  have hFK := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKAbsLeSqrtEta
    (Y := fun z θ => Work.Spaces.DzIter m g z θ) hInt
  -- `Qang g m z` is the angular moment of the slice `θ ↦ D_z^m g (z,θ)`
  have hQeq : Work.Elliptic.Qang g m z
      = Work.Construction.FK (fun z θ => Work.Spaces.DzIter m g z θ) z := by
    rw [Work.Elliptic.Qang, Work.Construction.FK, Work.Elliptic.Ktheta_eq_K]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => mul_comm _ _)
  -- the uniform-in-`z` slice bound (constant `3`), at level `6`
  have hslice : (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter m g z θ) ^ 2) ≤ 3 * Work.Spaces.HkSq α 6 g := by
    have h := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_sliceSupGraded
      hα hg.reg hmem6 m 0 (by omega) z hz
    simpa only [Work.Spaces.mixed_zero_right, Nat.add_zero] using h
  calc |Work.Elliptic.Qang g m z|
      = |Work.Construction.FK (fun z θ => Work.Spaces.DzIter m g z θ) z| := by rw [hQeq]
    _ ≤ 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter m g z θ) ^ 2) := hFK
    _ ≤ 4 * Real.sqrt (3 * Work.Spaces.HkSq α 6 g) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hslice) (by norm_num)
    _ = 4 * Real.sqrt 3 * Work.FTS.StrongGlobal.Xn6 α g := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        simp only [Work.FTS.StrongGlobal.Xn6, Work.Spaces.HkNorm]
        ring

end Work.FTS_EllLimOK.PkgJets.Pieces
