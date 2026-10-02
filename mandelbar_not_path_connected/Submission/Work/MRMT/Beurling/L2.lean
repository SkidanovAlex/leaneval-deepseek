/-
Work.MRMT — the Beurling transform on `L²(ℂ)`, and the `L^p` boundedness predicate.

The operator `beurlingL2` is the continuous linear map on `L²(ℂ)` whose Fourier transform is
multiplication by the Beurling symbol `ξ̄/ξ`; it is an isometry, and it is the `L²` avatar of
the singular integral with kernel `-1/(π z²)`.
-/
import Submission.Work.MRMT.Beurling.beurling_l2_isometry

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex SchwartzMap Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT

/-- The **Beurling transform on `L²(ℂ)`**: the continuous linear map whose Fourier transform
is multiplication by the Beurling symbol `ξ̄/ξ`.  (Defined by choice from
`Work.MRMT.Beurling.beurling_l2_isometry`; the defining properties are `norm_beurlingL2` and
`fourier_beurlingL2`.) -/
noncomputable def beurlingL2 :
    Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  Classical.choose Beurling.beurling_l2_isometry

/-- The Beurling transform is an isometry of `L²(ℂ)`. -/
theorem norm_beurlingL2 (f : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖beurlingL2 f‖ = ‖f‖ :=
  (Classical.choose_spec Beurling.beurling_l2_isometry).1 f

theorem beurlingL2_injective : Function.Injective beurlingL2 := by
  intro f g h
  have h' : ‖f - g‖ = 0 := by
    rw [← norm_beurlingL2 (f - g), map_sub, h, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h')

/-- Characterisation of the Beurling transform on the Fourier side. -/
theorem fourier_beurlingL2 (f : Lp ℂ 2 (volume : Measure ℂ)) :
    (((Lp.fourierTransformₗᵢ ℂ ℂ) (beurlingL2 f) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[(volume : Measure ℂ)]
      fun ξ => beurlingSymbol ξ *
        (((Lp.fourierTransformₗᵢ ℂ ℂ) f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) ξ :=
  (Classical.choose_spec Beurling.beurling_l2_isometry).2 f

/-- `BeurlingLpBound p C` says that the Beurling transform is bounded on `L^p(ℂ)` with
constant `C`, tested on `L² ∩ L^p` (which is dense in `L^p`).  This is the Calderón–Zygmund
`L^p` bound for the Beurling transform. -/
def BeurlingLpBound (p : ℝ≥0∞) (C : ℝ) : Prop :=
  ∀ f : Lp ℂ 2 (volume : Measure ℂ), MemLp ((f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) p volume →
    eLpNorm ((beurlingL2 f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) p volume ≤
      ENNReal.ofReal C *
        eLpNorm ((f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) p volume

/-- `‖S‖_{L²} = 1`, in the `BeurlingLpBound` format. -/
theorem beurlingLpBound_two : BeurlingLpBound 2 1 := by
  intro f _
  rw [ENNReal.ofReal_one, one_mul]
  refine le_of_eq ((ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_)
  · exact (Lp.memLp (beurlingL2 f)).ne
  · exact (Lp.memLp f).ne
  · rw [← Lp.norm_def, ← Lp.norm_def, norm_beurlingL2]

end Work.MRMT
