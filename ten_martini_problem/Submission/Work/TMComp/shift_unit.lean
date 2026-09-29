import Mathlib
import Submission.Work.TMComp.Defs
import Submission.Work.TMC16Core.Op.diagShift_spec

namespace Work.TMComp

open LeanEval.Analysis.TenMartini

/-- The two-sided shift on `ℓ²(ℤ)`: `(U f) n = f (n+1)` is an invertible bounded
operator whose inverse is the backward shift `(U⁻¹ f) n = f (n-1)`.

Both directions are obtained from `diagShift_spec` with the constant coefficient
sequence `c ≡ 1`; the unit structure is then exhibited directly. -/
theorem shift_unit : ∃ U : (LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo)ˣ,
    (∀ (f : LeanEval.Analysis.TenMartini.EllTwo) (n : ℤ),
      ((U : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo) f) n = f (n + 1)) ∧
    (∀ (f : LeanEval.Analysis.TenMartini.EllTwo) (n : ℤ),
      ((↑(U⁻¹) : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo) f) n = f (n - 1)) := by
  -- the forward shift `T f n = f (n+1)`
  obtain ⟨T, hT, -⟩ :=
    Work.TMC16Core.Op.diagShift_spec (fun _ : ℤ => (1 : ℂ)) 1 1 (fun n => by simp)
  -- the backward shift `S f n = f (n-1)`
  obtain ⟨S, hS, -⟩ :=
    Work.TMC16Core.Op.diagShift_spec (fun _ : ℤ => (1 : ℂ)) (-1) 1 (fun n => by simp)
  have hT' : ∀ (f : EllTwo) (n : ℤ), T f n = f (n + 1) := by
    intro f n; rw [hT]; simp
  have hS' : ∀ (f : EllTwo) (n : ℤ), S f n = f (n - 1) := by
    intro f n; rw [hS]; simp only [one_mul, sub_eq_add_neg]
  -- the two shifts are mutually inverse
  have h1 : T * S = 1 := by
    apply ContinuousLinearMap.ext
    intro f
    rw [mul_apply_eq_comp, one_apply_eq_self]
    ext n
    rw [hT', hS', show (n : ℤ) + 1 - 1 = n by ring]
  have h2 : S * T = 1 := by
    apply ContinuousLinearMap.ext
    intro f
    rw [mul_apply_eq_comp, one_apply_eq_self]
    ext n
    rw [hS', hT', show (n : ℤ) - 1 + 1 = n by ring]
  refine ⟨⟨T, S, h1, h2⟩, ?_, ?_⟩
  · intro f n; exact hT' f n
  · intro f n; exact hS' f n

end Work.TMComp
