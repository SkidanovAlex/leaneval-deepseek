/-
  # The corrected cutoff lemma: `Work.WilE2.exists_smooth_cutoff_infty`

  This is the statement that the delegated lemma `Work.WilE2.exists_smooth_cutoff` *was meant* to
  be: the smoothness level is `C^∞`, i.e. `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (Mathlib's `∞`),
  and **not** `ContDiff ℝ ⊤` (which is `ω` = *analytic*, and is refuted in the sibling module
  `Submission.Work.WilE2.exists_smooth_cutoff_false`).

  Proof: `K` is bounded, so it sits in a closed ball `closedBall 0 r`; enlarge the radius to `R`
  so that `K ⊆ ball 0 R ⊆ closedBall 0 R`, and apply Mathlib's smooth cutoff
  `exists_contDiff_support_eq_eq_one_iff` to the pair
  `closedBall 0 R ⊆ ball 0 (R + 1)`, whose support is the (bounded, hence relatively compact)
  ball `ball 0 (R + 1)`.

  `sorry`-free, Mathlib only.
-/
import Mathlib

namespace Work.WilE2

/-- Smooth, compactly supported cutoff function for a compact set in `Fin m → ℝ`, at the `C^∞`
level `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (the corrected form of
`Work.WilE2.exists_smooth_cutoff`). -/
theorem exists_smooth_cutoff_infty {m : ℕ} (K : Set (Fin m → ℝ)) (hK : IsCompact K) :
    ∃ (U : Set (Fin m → ℝ)) (χ : (Fin m → ℝ) → ℝ), IsOpen U ∧ K ⊆ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      HasCompactSupport χ ∧ (∀ z ∈ U, χ z = 1) ∧ (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) := by
  -- `K` is bounded, so it is contained in a closed ball `closedBall 0 r`.
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin m → ℝ)).1 hK.isBounded
  -- Enlarge the radius a little so that `K` sits in an *open* ball `ball 0 R`.
  set R : ℝ := max r 0 + 1 with hR
  have hrR : r < R := by
    rw [hR]
    exact lt_of_le_of_lt (le_max_left r 0) (lt_add_one (max r 0))
  have hKsub : K ⊆ Metric.ball (0 : Fin m → ℝ) R := by
    intro x hx
    rw [Metric.mem_ball]
    have h1 : dist x 0 ≤ r := Metric.mem_closedBall.1 (hr hx)
    linarith
  -- `closedBall 0 R` is contained in the larger open ball `ball 0 (R+1)`.
  have hts : Metric.closedBall (0 : Fin m → ℝ) R ⊆ Metric.ball (0 : Fin m → ℝ) (R + 1) := by
    intro x hx
    rw [Metric.mem_ball, Metric.mem_closedBall] at *
    linarith
  -- Mathlib's smooth cutoff: smooth, values in `[0,1]`, support `ball 0 (R+1)`, equal to `1`
  -- exactly on `closedBall 0 R`.
  obtain ⟨f, hf_diff, hf_range, hf_supp, hf_one⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      (s := Metric.ball (0 : Fin m → ℝ) (R + 1))
      (t := Metric.closedBall (0 : Fin m → ℝ) R)
      Metric.isOpen_ball Metric.isClosed_closedBall hts
  refine ⟨Metric.ball (0 : Fin m → ℝ) R, f, Metric.isOpen_ball, hKsub, hf_diff, ?_, ?_, ?_, ?_⟩
  · rw [HasCompactSupport]
    refine (isCompact_closedBall (0 : Fin m → ℝ) (R + 1)).of_isClosed_subset
      (isClosed_tsupport f) ?_
    rw [tsupport, hf_supp]
    exact Metric.closure_ball_subset_closedBall
  · intro z hz
    exact (hf_one z).mp (Metric.ball_subset_closedBall hz)
  · intro z
    exact (hf_range (Set.mem_range_self z)).1
  · intro z
    exact (hf_range (Set.mem_range_self z)).2

end Work.WilE2
