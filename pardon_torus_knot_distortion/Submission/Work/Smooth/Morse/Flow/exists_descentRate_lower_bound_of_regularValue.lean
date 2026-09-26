import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Critical.isClosed_criticalParam
import Submission.Work.Smooth.Morse.Flow.exists_descentRate_lower_bound

/-!
# A uniform lower bound for the descent rate on a critical-free band, with room below

`Work.Smooth.Morse.Flow.exists_descentRate_lower_bound` gives a positive lower bound for the
descent rate `descentRate ψ g` on the band of parameters whose level lies in a **closed** interval
`[a, b]` of regular values of `g|_F`.

The flow construction of item 3 needs slightly more room: the normalised gradient flow has to be
followed for the whole time `b - a`, and the quantitative estimates along the way involve a
neighbourhood of the band.  This file provides the version with room below the lower end: on a
band `[a - η, b]` *slackened downwards* by a small `η > 0`, the descent rate is still bounded below
by a positive constant.

The mathematical content beyond `exists_descentRate_lower_bound` is that **the set of critical
values of `g|_F` is closed** in `ℝ`: since `a` is a regular value, some interval `(a-ε, a+ε)`
contains no critical value, and then `η = ε/2` slackens the band `[a,b]` into the critical-free
band `[a-η,b]`, to which the existing lower bound is applied.

The closedness is proved in the parameter plane.  `G = pullback ψ g` and its derivative are both
invariant under the period lattice `2πℤ²` (periodicity of the parametrisation of the torus), and
every parameter can be shifted by a lattice element into the fundamental square
`[0,2π] × [0,2π]`.  Hence the set of critical values is the image under the continuous `G` of the
*compact* set `criticalParam ∩ ([0,2π]×[0,2π])`, hence compact, hence closed.
-/

namespace Work.Smooth.Morse.Flow

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace RateBound

/-- **The set of critical values of `g|_F` is closed.**  The critical points of `pullback ψ g`
are a closed, `2πℤ²`-periodic subset of the parameter plane, so their image under `pullback ψ g`
(the critical values) is the image of the compact set
`criticalParam ψ g ∩ ([0,2π] × [0,2π])`. -/
theorem isClosed_criticalValues (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 1 g) :
    IsClosed (Work.Smooth.Morse.criticalValues ψ g) := by
  let box : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hK : IsClosed (Work.Smooth.Morse.criticalParam ψ g) :=
    Work.Smooth.Morse.Critical.isClosed_criticalParam ψ hg
  have hG : Continuous (Work.Smooth.Morse.pullback ψ g) :=
    (Work.Smooth.Morse.pullback_contDiff_one ψ hg).continuous
  have himg : Work.Smooth.Morse.criticalValues ψ g =
      Work.Smooth.Morse.pullback ψ g '' (Work.Smooth.Morse.criticalParam ψ g ∩ box) := by
    ext t
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨k, hk⟩ := exists_int_shift_mem_Icc p.1
      obtain ⟨l, hl⟩ := exists_int_shift_mem_Icc p.2
      refine ⟨(p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)), ?_, ?_⟩
      · refine ⟨?_, ⟨hk, hl⟩⟩
        show fderiv ℝ (Work.Smooth.Morse.pullback ψ g)
          (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) = 0
        rw [fderiv_pullback_add_lattice ψ g p k l]
        exact hp
      · show Work.Smooth.Morse.pullback ψ g
          (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) =
          Work.Smooth.Morse.pullback ψ g p
        exact pullback_add_lattice ψ g p k l
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp.1, rfl⟩
  rw [himg]
  exact ((hbox.inter_left hK).image hG).isClosed

end RateBound

theorem exists_descentRate_lower_bound_of_regularValue (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a ≤ b) (hreg : ∀ t ∈ Set.Icc a b, Work.Smooth.Morse.IsRegularValue ψ g t) : ∃ δ : ℝ, 0 < δ ∧ ∃ η : ℝ, 0 < η ∧ ∀ q : ℝ × ℝ, Work.Smooth.Morse.pullback ψ g q ∈ Set.Icc (a - η) b → δ ≤ Work.Smooth.Morse.descentRate ψ g q := by
  have hclosed : IsClosed (Work.Smooth.Morse.criticalValues ψ g) :=
    RateBound.isClosed_criticalValues ψ hg
  have ha : a ∉ Work.Smooth.Morse.criticalValues ψ g := hreg a ⟨le_refl a, hab⟩
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl a ha
  set η : ℝ := ε / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have hreg' : ∀ t ∈ Set.Icc (a - η) b, Work.Smooth.Morse.IsRegularValue ψ g t := by
    intro t ht
    rcases le_or_gt a t with h | h
    · exact hreg t ⟨h, ht.2⟩
    · have hdist : dist t a < ε := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1], by linarith [hεpos]⟩
      exact hεsub (Metric.mem_ball.mpr hdist)
  by_cases hb : a - η ≤ b
  · obtain ⟨δ, hδpos, hδ⟩ := exists_descentRate_lower_bound ψ hg hb hreg'
    exact ⟨δ, hδpos, η, hηpos, hδ⟩
  · refine ⟨1, one_pos, η, hηpos, fun q hq => ?_⟩
    exfalso
    exact absurd (lt_of_lt_of_le (lt_of_not_ge hb) hq.1) (not_lt.mpr hq.2)

end

end Work.Smooth.Morse.Flow
