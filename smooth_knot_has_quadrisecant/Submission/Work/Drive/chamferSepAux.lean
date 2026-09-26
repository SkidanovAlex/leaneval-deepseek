import Mathlib
import Submission.Helpers
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepLoop_injective
import Submission.Work.Drive.sweepLoopProfileDefs
import Submission.Work.Drive.uniformBoundsC1

/-!
# Shared, cycle-free helpers for the chamfer-separation lemmas

This module contains the clamping/junction identities and the two global bounds for a smooth
knot that the chamfer-separation lemmas (`tailChamfer_*`, `headChamfer_*`, `chamfers_sep`)
need, **without** importing their consumer `Submission.Work.Drive.sweepLoopChamfer_injOn_small_lam`.

Rationale: the consumer of those lemmas is
`Submission.Work.Drive.sweepLoopChamfer_injOn_small_lam`, so the lemmas must not (transitively)
import it.  Do **not** import `Submission.Work.Drive.sweepChamferCaseSep`-style modules that pull
in the consumer; import this module instead.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

noncomputable section

/-!
# Injectivity of the chamfered sweep loop on one period, for small chamfer

The chamfered loop `sweepLoopChamfer r D lam s` is the composition of the loop parameter
`sweepParam` with the *profile* loop `sweepLoopProfile r D lam s`, whose four branches are

1. `w ∈ [0,1/2]`          : the retained arc, from fraction `lam` to `1-lam`;
2. `w ∈ [1/2,1/2+lam/2]`  : the segment from `sweepArc' (1-lam)` to `sweepChord' (1-lam)`;
3. `w ∈ [1/2+lam/2,1-lam/2]`: the chord, from fraction `1-lam` back to `lam`;
4. `w ∈ [1-lam/2,1]`      : the segment from `sweepChord' lam` to `sweepArc' lam`.

Since `sweepParam` is injective on the fundamental domain `[0,period)`, injectivity of the
chamfered loop reduces to injectivity of the profile loop on `[0,1)`; the latter follows from
the injectivity of each branch and the pairwise disjointness of the four ranges (up to the
shared endpoints).

This file reduces the theorem to the geometric separation statements collected in the
`SweepChamferSeparation` structure below, which are proved in the companion modules.
-/

/-! ## Clamping helpers -/

lemma clampI_coe (s : Set.Icc (0 : ℝ) 1) : clampI (s : ℝ) = s := by
  apply Subtype.ext
  show min 1 (max 0 (s : ℝ)) = (s : ℝ)
  rw [max_eq_right s.2.1, min_eq_right s.2.2]

lemma taR_coe {d : BandArcData} (D : SweepData d) (s : Set.Icc (0 : ℝ) 1) :
    taR D (s : ℝ) = D.ta s := by simp [taR, clampI_coe]

lemma tbR_coe {d : BandArcData} (D : SweepData d) (s : Set.Icc (0 : ℝ) 1) :
    tbR D (s : ℝ) = D.tb s := by simp [tbR, clampI_coe]

lemma sweepW'_coe {d : BandArcData} (D : SweepData d) (s : Set.Icc (0 : ℝ) 1) :
    sweepW' D (s : ℝ) = sweepW D s := by simp [sweepW', sweepW, taR_coe, tbR_coe]

lemma sweepArc'_coe (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (s : Set.Icc (0 : ℝ) 1) (ξ : ℝ) :
    sweepArc' r D (s : ℝ) ξ = sweepArc r D s ξ := by
  simp [sweepArc', sweepArc, taR_coe, sweepW'_coe]

lemma sweepChord'_coe (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (s : Set.Icc (0 : ℝ) 1) (ξ : ℝ) :
    sweepChord' r D (s : ℝ) ξ = sweepChord r D s ξ := by
  simp [sweepChord', sweepChord, taR_coe, tbR_coe]

/-! ## From the profile loop to the chamfered loop -/

/-- **The chamfered loop is injective on one period as soon as the profile loop is injective on
`[0,1)`.** -/
lemma chamfer_injOn_of_profile {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {s : ℝ}
    (hprof : Set.InjOn (sweepLoopProfile r D lam s) (Set.Ico (0 : ℝ) 1)) :
    Set.InjOn (sweepLoopChamfer r D lam s) (Set.Ico 0 period) := by
  intro t₁ ht₁ t₂ ht₂ h
  have hm₁ := sweepParam_mem t₁
  have hm₂ := sweepParam_mem t₂
  rw [sweepLoopChamfer_eq_profile r D h0 h1,
    sweepLoopChamfer_eq_profile r D h0 h1] at h
  have hpar : sweepParam t₁ = sweepParam t₂ :=
    hprof ⟨hm₁.1, hm₁.2⟩ ⟨hm₂.1, hm₂.2⟩ h
  rw [sweepParam_eq_div ht₁, sweepParam_eq_div ht₂] at hpar
  have h3 : t₁ / period * period = t₂ / period * period := by rw [hpar]
  rwa [div_mul_cancel₀ t₁ period_ne_zero, div_mul_cancel₀ t₂ period_ne_zero] at h3


/-! ## Geometric bounds for the knot (from the workspace's uniform family bounds) -/

/-- **Uniform geometric bounds for a smooth knot**: a positive lower bound `m` for the speed, a
small parameter scale `δ`, and a positive separation `sep` for parameters at distance between
`δ` and `period - δ`. -/
theorem knot_bounds {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ m δ sep : ℝ, 0 < m ∧ 0 < δ ∧ 0 < sep ∧
      (∀ t : ℝ, m ≤ ‖velocity r t‖) ∧
      (∀ t t' : ℝ, |t' - t| ≤ δ → (m / 2) * |t' - t| ≤ ‖r t - r t'‖) ∧
      (∀ t t' : ℝ, δ ≤ |t' - t| → |t' - t| ≤ period - δ → sep ≤ ‖r t - r t'‖) := by
  have hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => (fun t (_ : ℝ) => r t) p.1 p.2) :=
    (hr.smooth.of_le le_top).comp contDiff_fst
  have hsl : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => (fun t (_ : ℝ) => r t) t s) :=
    fun s _ => IsSmoothKnot.toCInf hr
  obtain ⟨m, δ, sep, hm, hδ, -, hsep, hb⟩ := uniformBoundsC1 hF hsl
  exact ⟨m, δ, sep, hm, hδ, hsep, (hb 0 (by norm_num)).1,
    (hb 0 (by norm_num)).2.1, (hb 0 (by norm_num)).2.2⟩


/-- **Upper Lipschitz bound for the knot on the parameter box `[0, 2*period]`.** -/
theorem knot_lipschitz_box {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ M : ℝ, 0 < M ∧ ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) (2 * period) →
      t ∈ Set.Icc (0 : ℝ) (2 * period) → ‖r s - r t‖ ≤ M * |s - t| := by
  have hp : 0 < period := period_pos
  have hvc : Continuous (fun t : ℝ => ‖velocity r t‖) := by
    show Continuous (fun t : ℝ => ‖deriv r t‖)
    exact (hr.smooth.continuous_deriv (by simp)).norm
  obtain ⟨x₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, by constructor <;> linarith [hp.le]⟩ : (Set.Icc (0 : ℝ) (2 * period)).Nonempty)
    hvc.continuousOn
  refine ⟨max (‖velocity r x₀‖) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  have hMle : ∀ x ∈ Set.Icc (0 : ℝ) (2 * period), ‖velocity r x‖ ≤ max (‖velocity r x₀‖) 1 :=
    fun x hx => le_trans (hmax hx) (le_max_left _ _)
  have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) (2 * period), DifferentiableAt ℝ r x :=
    fun x _ => (hr.smooth.differentiable (by simp)) x
  intro s t hs ht
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := r)
    (s := Set.Icc (0 : ℝ) (2 * period)) (C := max (‖velocity r x₀‖) 1) (x := s) (y := t)
    (fun x hx => hdiff x hx) (fun x hx => hMle x hx) (convex_Icc _ _) hs ht
  simpa [Real.norm_eq_abs, norm_sub_rev, abs_sub_comm] using h


end

end Work.Drive
