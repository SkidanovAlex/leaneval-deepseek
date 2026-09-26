import Mathlib
import Submission.Work.Drive.Mono.CutTransverse
import Submission.Work.Step2.closedBox_subset_closure_PBox

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

noncomputable section

/-- A `T`-periodic map of `ℝ` takes at an arbitrary point `x` a value already taken in the
fundamental interval `[0, T]`. -/
theorem exists_mem_Icc_eq_of_periodic {β : Type*} (T : ℝ) (hT : 0 < T) (g : ℝ → β)
    (hg : Function.Periodic g T) (x : ℝ) : ∃ x' ∈ Set.Icc (0 : ℝ) T, g x' = g x := by
  refine ⟨Int.fract (x / T) * T, ⟨?_, ?_⟩, ?_⟩
  · exact mul_nonneg (Int.fract_nonneg _) hT.le
  · have h1 : Int.fract (x / T) < 1 := Int.fract_lt_one _
    have h2 : Int.fract (x / T) * T < 1 * T := mul_lt_mul_of_pos_right h1 hT
    simpa using h2.le
  · have h2 : Int.fract (x / T) * T + (⌊x / T⌋ : ℝ) * T = x := by
      rw [← add_mul, Int.fract_add_floor, div_mul_cancel₀ x (ne_of_gt hT)]
    have hstep : g (Int.fract (x / T) * T + (⌊x / T⌋ : ℝ) * T) =
        g (Int.fract (x / T) * T) :=
      hg.int_mul ⌊x / T⌋ _
    have hxx : g x = g (Int.fract (x / T) * T) := by
      conv_lhs => rw [← h2]
      exact hstep
    exact hxx.symm

end

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
/-- The flat level is bounded away from the knot on the box sphere, when the level is cut-transverse (and the box is non-degenerate). -/
theorem exists_margin_boxSphere (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) {s u : ℝ}
    (hs : 0 < s) (hcut : Work.Drive.Mono.CutTransverse K s c σ u) :
    ∃ m : ℝ, 0 < m ∧ ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
      m ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)| := by
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  -- the box norm along the curve and the (absolute) deviation of the `σ 2`-coordinate from the
  -- cutting level are continuous
  have hGc : Continuous (fun t : ℝ => Submission.boxNorm c σ (K.curve t)) :=
    Work.BoxSweep.continuous_boxNormCurve K c σ
  have hFc : Continuous (fun t : ℝ => |(K.curve t) (σ 2) - (c (σ 2) + u)|) := by
    have h1 : Continuous fun t : ℝ => (K.curve t) (σ 2) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).comp K.smooth.continuous
    exact continuous_abs.comp (h1.sub continuous_const)
  -- the trace of the box sphere on the knot is closed, hence compact in one period
  have hclosed : IsClosed {t : ℝ | Submission.boxNorm c σ (K.curve t) = s} :=
    isClosed_eq hGc continuous_const
  have hcompact : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi) ∩
      {t : ℝ | Submission.boxNorm c σ (K.curve t) = s}) :=
    isCompact_Icc.inter_right hclosed
  -- cut-transversality puts the trace off the cutting plane
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∩
      {t : ℝ | Submission.boxNorm c σ (K.curve t) = s},
      0 < |(K.curve t) (σ 2) - (c (σ 2) + u)| := by
    rintro t ⟨-, ht⟩
    rcases eq_or_ne (|(K.curve t) (σ 2) - (c (σ 2) + u)|) 0 with h0 | h0
    · exfalso
      have hcoord : (K.curve t) (σ 2) = c (σ 2) + u := by
        have := abs_eq_zero.mp h0
        linarith
      have hcl : K.curve t ∈ closure (Submission.PBox s c σ) :=
        Work.Step2.closedBox_subset_closure_PBox hs c σ (le_of_eq ht)
      obtain ⟨hmem, -⟩ := hcut t hcl hcoord
      rw [Submission.mem_PBox_iff] at hmem
      have hbox_eq : Submission.boxNorm c σ (K.curve t) = s := ht
      linarith
    · exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
  by_cases hne : (Set.Icc (0 : ℝ) (2 * Real.pi) ∩
      {t : ℝ | Submission.boxNorm c σ (K.curve t) = s}).Nonempty
  · -- the trace is non-empty: minimise the continuous deviation over it
    obtain ⟨t₀, ht₀, hmin⟩ := hcompact.exists_isMinOn hne hFc.continuousOn
    refine ⟨|(K.curve t₀) (σ 2) - (c (σ 2) + u)|, hpos t₀ ht₀, ?_⟩
    intro t ht
    obtain ⟨t', ht'1, ht'2⟩ :=
      exists_mem_Icc_eq_of_periodic (2 * Real.pi) hT K.curve (fun t => K.periodic t) t
    have hG' : Submission.boxNorm c σ (K.curve t') = s := by rw [ht'2]; exact ht
    have hin : t' ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∩
        {t : ℝ | Submission.boxNorm c σ (K.curve t) = s} := ⟨ht'1, hG'⟩
    have := hmin hin
    simpa [ht'2] using this
  · -- the trace is empty: the conclusion is vacuous
    refine ⟨1, one_pos, ?_⟩
    intro t ht
    obtain ⟨t', ht'1, ht'2⟩ :=
      exists_mem_Icc_eq_of_periodic (2 * Real.pi) hT K.curve (fun t => K.periodic t) t
    have hG' : Submission.boxNorm c σ (K.curve t') = s := by rw [ht'2]; exact ht
    exact absurd ⟨t', ht'1, hG'⟩ hne

end Work.Drive.Mono
