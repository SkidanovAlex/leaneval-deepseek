import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-- **Smoothness and periodicity of the `ε`-regularised field.**

For `ε > 0` and any real exponent `s`, the field `y ↦ (‖w y‖² + ε²)^s • conj (w y)` is `C^∞` when
`w` is, and it is `1`-periodic in the direction `i` when `w` is.

(The base `‖w y‖² + ε² ≥ ε² > 0` never vanishes, so `t ↦ t^s` is smooth there; the field is
periodic because both `‖w ·‖` and `conj ∘ w` are.)  This is one of the pieces used by the
`ε`-regularisation proof of the sharp periodic integration by parts, see
`Submission/Work/Diff/STE/GN/ibp_rpow_complex.lean`, whose statement this reproduces. -/
theorem regularisedFieldSmooth {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (s ε : ℝ)
    (hε : 0 < ε) (w : (ι → ℝ) → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwper : Work.Diff.STE.PeriodicIn i w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ((‖w y‖ ^ 2 + ε ^ 2) ^ s) • (starRingEnd ℂ) (w y)) ∧
      Work.Diff.STE.PeriodicIn i
        (fun y : ι → ℝ => ((‖w y‖ ^ 2 + ε ^ 2) ^ s) • (starRingEnd ℂ) (w y)) := by
  -- The base `‖w y‖² + ε²` is smooth ...
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ‖w y‖ ^ 2 + ε ^ 2) :=
    (ContDiff.norm_sq ℝ hw).add contDiff_const
  -- ... and strictly positive, so the real power `t ^ s` is smooth there.
  have hpos : ∀ y : ι → ℝ, 0 < ‖w y‖ ^ 2 + ε ^ 2 := by
    intro y
    have h1 : (0 : ℝ) ≤ ‖w y‖ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
    linarith
  have hrpow : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => (‖w y‖ ^ 2 + ε ^ 2) ^ s) :=
    ContDiff.rpow hbase contDiff_const (fun y => ne_of_gt (hpos y))
  -- Complex conjugation is `ℝ`-linear and continuous, hence smooth.
  have hconj : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => (starRingEnd ℂ) (w y)) :=
    Complex.conjCLE.contDiff.comp hw
  refine ⟨?_, ?_⟩
  · exact hrpow.smul hconj
  · intro x
    simp only [hwper x]

end Work.Diff.STE.Lead.GalTame
