import Mathlib
import Submission.Work.Drive.collapseTransport

/-!
# The collar function of the radial collapse

For every `0 < δ` we build a `C^∞` function `β : ℝ → ℝ` with `β > 0`, `√t ≤ β t` for all `t`, `β t = √t`
for `t ≥ δ²` and `β 1 = 1`.

The construction is a convex interpolation between the constant `1` and the identity, cut off by
`Real.smoothTransition`:

`β t = √(t + (1 - t) · smoothTransition (1 - t / d))`,  `d := min δ² 1`.

The *inner* function `ψ t = t + (1 - t) ζ t` (with `ζ t = smoothTransition (1 - t / d)`) satisfies
`ψ = id` on `[d, ∞)` (where `ζ = 0`), `ψ ≥ id` on all of `ℝ` (for `d ≤ 1`), and `ψ > 0` everywhere
(for `0 < d ≤ 1`); composing with `√·`, which is `C^∞` away from `0`, gives all the required
properties.  Note `ψ 1 = 1` because the `(1 - t)` factor kills the transition term at `t = 1`, so
`β 1 = 1` holds *without* any hypothesis relating `1` and `δ`.

The statement is the delegated interface `Work.Drive.colCollar_exists`, used in
`Submission/Work/Drive/collapseTransport.lean` (the collar of the radial collapse).
-/

namespace Work.Drive

/-- A smooth positive majorant of the square root, agreeing with `√·` from `d` onwards (for
`0 < d ≤ 1`): `collarBeta d t = √(t + (1 - t) * smoothTransition (1 - t / d))`. -/
noncomputable def collarBeta (d t : ℝ) : ℝ :=
  Real.sqrt (t + (1 - t) * Real.smoothTransition (1 - t / d))

/-- On the negative half-line the transition factor is `1`. -/
lemma collarBeta_step_one {d t : ℝ} (hd : 0 < d) (ht : t ≤ 0) :
    Real.smoothTransition (1 - t / d) = 1 :=
  Real.smoothTransition.one_of_one_le (by
    have : t / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht hd.le
    linarith)

/-- On `[d, ∞)` the transition factor vanishes. -/
lemma collarBeta_step_zero {d t : ℝ} (hd : 0 < d) (ht : d ≤ t) :
    Real.smoothTransition (1 - t / d) = 0 :=
  Real.smoothTransition.zero_of_nonpos (by
    have : 1 ≤ t / d := (one_le_div hd).mpr ht
    linarith)

/-- The inner function `t ↦ t + (1 - t) * smoothTransition (1 - t / d)` of `collarBeta` is strictly
positive, for `0 < d ≤ 1`. -/
lemma collarBeta_inner_pos {d t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    0 < t + (1 - t) * Real.smoothTransition (1 - t / d) := by
  rcases le_or_gt d t with hdt | hdt
  · rw [collarBeta_step_zero hd hdt]; linarith
  · rcases le_or_gt t 0 with ht0 | ht0
    · rw [collarBeta_step_one hd ht0]; norm_num
    · have hζ : 0 ≤ Real.smoothTransition (1 - t / d) := Real.smoothTransition.nonneg _
      nlinarith [hd1, hdt, ht0, hζ]

/-- The inner function dominates the identity, for `0 < d ≤ 1`. -/
lemma collarBeta_inner_ge {d t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    t ≤ t + (1 - t) * Real.smoothTransition (1 - t / d) := by
  rcases le_or_gt d t with hdt | hdt
  · rw [collarBeta_step_zero hd hdt]; simp
  · have hζ : 0 ≤ Real.smoothTransition (1 - t / d) := Real.smoothTransition.nonneg _
    have h1 : (0 : ℝ) ≤ 1 - t := by linarith
    nlinarith [mul_nonneg h1 hζ]

/-- `collarBeta d` is `C^∞`, for `0 < d ≤ 1`. -/
lemma collarBeta_smooth {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (collarBeta d) := by
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => t + (1 - t) * Real.smoothTransition (1 - t / d)) :=
    contDiff_id.add ((contDiff_const.sub contDiff_id).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.div_const d))))
  rw [contDiff_iff_contDiffAt]
  intro t
  exact (Real.contDiffAt_sqrt (x := t + (1 - t) * Real.smoothTransition (1 - t / d))
    (ne_of_gt (collarBeta_inner_pos (t := t) hd hd1))).comp t hψ.contDiffAt

/-- `collarBeta d` equals `√·` on `[d, ∞)`. -/
lemma collarBeta_eq_sqrt {d t : ℝ} (hd : 0 < d) (hdt : d ≤ t) :
    collarBeta d t = Real.sqrt t := by
  rw [collarBeta, collarBeta_step_zero hd hdt]; ring_nf

/-- `collarBeta d 1 = 1`. -/
lemma collarBeta_one (d : ℝ) : collarBeta d 1 = 1 := by
  rw [collarBeta]; norm_num

theorem colCollar_exists (δ : ℝ) (hδ : 0 < δ) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ (∀ t : ℝ, 0 < β t) ∧
      (∀ t : ℝ, Real.sqrt t ≤ β t) ∧
      (∀ t : ℝ, δ ^ 2 ≤ t → β t = Real.sqrt t) ∧ β 1 = 1 := by
  refine ⟨collarBeta (min (δ ^ 2) 1), collarBeta_smooth ?_ ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (pow_pos hδ 2) one_pos
  · exact min_le_right _ _
  · intro t
    exact Real.sqrt_pos.mpr (collarBeta_inner_pos (t := t) (lt_min (pow_pos hδ 2) one_pos)
      (min_le_right _ _))
  · intro t
    rcases le_or_gt 0 t with ht | ht
    · exact Real.sqrt_le_sqrt (collarBeta_inner_ge (lt_min (pow_pos hδ 2) one_pos)
        (min_le_right _ _))
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt ht)]
      exact Real.sqrt_nonneg _
  · intro t ht
    exact collarBeta_eq_sqrt (lt_min (pow_pos hδ 2) one_pos)
      (le_trans (min_le_left _ _) ht)
  · exact collarBeta_one _

end Work.Drive
