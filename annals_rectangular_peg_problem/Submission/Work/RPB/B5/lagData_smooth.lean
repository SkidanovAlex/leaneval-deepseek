import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.contDiff_piecewise_param
import Submission.Work.RPB.B5.jet_vanish
import Submission.Work.RPB.B5.collarChart_flat
import Submission.Work.RPB.B5.lagPt_negSqrt2_decomp
import Submission.Work.RPB.B5.lagData_nearZero
import Submission.Work.RPB.B5.lagData_smooth_at_negSqrt2
import Submission.Work.RPB.B5.lagData_smooth_at_zero
import Submission.Work.RPB.B5.lagData_smooth_at_sqrt2
import Submission.Work.RPB.B5.lagData_smooth_off_junctions
import Submission.Work.RPB.B2.chordSurf_period_swap

/-!
# B5: smoothness of the assembled family `ℓ τ (x,t) = lagPt W Γc Ac ρ τ x t`

The function `lagPt` is piecewise in `x`, with three seams:

* `x = -√2`: the collar branch `collarPt Γc Ac τ (sig x) t` (which is `C⁸` only for
  `sig x ≥ 0`) meets the chord chart `W τ t (ρh τ t (sig x))`;
* `x = 0`: the left half meets its `τ_π`-image;
* `x = +√2`: the reflected seam `x = -√2`, transported by `tau π`.

This file is the *assembly*: at every point of the slab `Icc 0 1 ×ˢ univ ×ˢ univ` the family is
`C⁸` within the slab, by the four region lemmas

* `lagData_smooth_at_negSqrt2` — the seam `x = -√2`, via the flat-gluing lemma
  `contDiffOn_flat_trunc_Icc` applied to the cut difference `exists_cut_negDiff`,
* `lagData_smooth_at_zero` — the two halves agree with a single smooth chord expression,
* `lagData_smooth_at_sqrt2` — the reflected seam,
* `lagData_smooth_off_junctions` — the open regions, where the branch selector is locally
  constant,

together with the case distinction on `x`.

Since `ContDiffOn ℝ 8 f s` is by definition `∀ z ∈ s, ContDiffWithinAt ℝ 8 f s z`, these four
pointwise facts assemble directly. -/

namespace Work.RPB.B5

theorem lagData_smooth (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ContDiffOn ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) := by
  intro z hz
  rcases z with ⟨τ₀, x₀, t₀⟩
  have hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1 := hz.1
  rcases eq_or_ne x₀ (-Real.sqrt 2) with h | h
  · rw [h]
    exact lagData_smooth_at_negSqrt2 CI a ha D τ₀ hτ₀ t₀
  rcases eq_or_ne x₀ 0 with h0 | h0
  · subst h0
    exact lagData_smooth_at_zero CI a ha D τ₀ hτ₀ t₀
  rcases eq_or_ne x₀ (Real.sqrt 2) with h2 | h2
  · rw [h2]
    exact lagData_smooth_at_sqrt2 CI a ha D τ₀ hτ₀ t₀
  · exact lagData_smooth_off_junctions CI a ha D τ₀ hτ₀ x₀ ⟨h, h0, h2⟩ t₀

end Work.RPB.B5
