/-
# `E1Open/Assembly_O` — the `ℋⁿ`-bound for the transfer defect `E1` in the **open** class

The transfer defect of `CoercivityFix/Transfer/Profiles.lean` is the separated product

  `E1 α f = (D_θΓ) · radA α f`,

so its `ℋⁿ`-energy is bounded by an `α²`-factor times the *radial* slot sum
`∑_{j≤n} (D_z^j (radA α f))² w²` (`E1Norm.E1_angRad_le`, which is class-free: it only needs the
integrability of that radial sum).  The whole content of the `CoerAdmO`-version of the estimate
is therefore the *open-class* radial bound, which this file takes as an explicit hypothesis
`hSLOT` — the shape of `E1Open.radA_slotSum_le_O` (proved from the level-`n` `L₁₂`-slot bound
`E1Open.L12f_slot_le_O_of` and the level-`n` angular-moment bound
`E1Open.Qang_sq_w_sq_le_HkSq_O`).

Both statements here are the `SmoothOpen`-class twins of

* `Work.FTS.CoercivityFix.Transfer.E1Norm.E1_hkSq_le` (squared form), and
* `Work.FTS.CoercivityFix.Transfer.E1_norm` (the `ℋⁿ`-norm form, the target of
  `E1_norm_O`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Transfer.E1_norm
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E1Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The squared `ℋⁿ`-bound for `E1`, open class, given the radial slot bound.** -/
theorem E1_hkSq_le_O_of
    (hSLOT : ∃ Cs : ℝ, 0 < Cs ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ Cs * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ C * α ^ 2 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨Cs, hCspos, hS⟩ := hSLOT
  obtain ⟨Ca, hCapos, hA⟩ :=
    Work.FTS.CoercivityFix.Transfer.E1Norm.E1_angRad_le
  refine ⟨Ca * Cs + 1, by positivity, ?_⟩
  intro α hα hα1 n hn f hf
  obtain ⟨hint, hbound⟩ := hS α hα hα1 f hf n hn
  have h1 := hA α n f hα hα1 hn hint
  have hα2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have h2 : Ca * α ^ 2 * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ Ca * α ^ 2 * (Cs * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  have h3 : (0 : ℝ) ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
    have := Work.Spaces.HkSq_nonneg α n f
    have := Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)
    linarith
  calc Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
      ≤ Ca * α ^ 2 * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := h1
    _ ≤ Ca * α ^ 2 * (Cs * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) := h2
    _ = (Ca * Cs) * α ^ 2 * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
    _ ≤ (Ca * Cs + 1) * α ^ 2 * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
        rw [show (Ca * Cs) * α ^ 2 * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
            = (Ca * Cs) * (α ^ 2 * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) from by ring,
          show (Ca * Cs + 1) * α ^ 2 * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
            = (Ca * Cs + 1) * (α ^ 2 * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) from by ring]
        exact mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg hα2 h3)

/-- **The `ℋⁿ`-norm bound for `E1`, open class, given the radial slot bound.** -/
theorem E1_norm_O_of
    (hSLOT : ∃ Cs : ℝ, 0 < Cs ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ Cs * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ α * κ * (Work.Spaces.HkNorm α n f
              + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
  obtain ⟨C, hCpos, hC⟩ := E1_hkSq_le_O_of hSLOT
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro α hα hα1 n hn f hf
  have hkey := hC α hα hα1 n hn f hf
  have hNf : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
  have hNd : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) := Work.Spaces.HkSq_nonneg α n _
  -- the elementary inequality `Nf + Nd ≤ (√Nf + √Nd)²`
  have hsum : Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
      ≤ (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) ^ 2 := by
    have h1 := Real.sq_sqrt hNf
    have h2 := Real.sq_sqrt hNd
    have h3 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α n f) := Real.sqrt_nonneg _
    have h4 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := Real.sqrt_nonneg _
    nlinarith [h1, h2, h3, h4]
  have hbound : C * α ^ 2 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
      ≤ (α * Real.sqrt C * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)))) ^ 2 := by
    have h1 : C * α ^ 2 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
        ≤ C * α ^ 2 * ((Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    refine le_trans h1 (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hCpos.le]
    ring
  calc Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
      = Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)) := rfl
    _ ≤ Real.sqrt ((α * Real.sqrt C * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)))) ^ 2) :=
        Real.sqrt_le_sqrt (le_trans hkey hbound)
    _ = α * Real.sqrt C * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        Real.sqrt_sq (by positivity)
    _ = α * Real.sqrt C * (Work.Spaces.HkNorm α n f
          + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := rfl

end Work.FTS.StrongEps.EpsE4Thr.E1Open
