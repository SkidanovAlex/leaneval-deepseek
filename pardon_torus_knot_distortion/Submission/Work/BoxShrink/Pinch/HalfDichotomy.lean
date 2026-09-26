import Submission.Work.BoxShrink.Pinch.PushOffNoJump

/-!
# The residual is *exactly* the "no jump" of the pinch

Pardon's equation (1) (`Work.BoxShrink.Pinch.Equation1Input`) is a statement about the sublevel
region of *any* nice level function.  It therefore applies not only to the box sphere but also to
the two *half-box spheres*: the region `upperRegion P s c σ u` is the sublevel region of the level
function

  `upperLevel = max (boxNorm c σ - s) (-planeCoord c σ u)`

whose level set is the trace of the half-box sphere, i.e. the boundary of `upperRegion` in the
surface; and the lower half is the same with `+planeCoord`.

Consequently, *if* the two half-box traces are also inessential, the invariants of the box region
and of the two half-regions all take their values in `{⊥, ⊤}` (this module), and then
`Work.BoxShrink.Pinch.PinchNoJump` is **equivalent** to the statement that the invariant does not
jump from `⊤` to `⊥` at the pinch (`pinchNoJump_iff_noJump`).  So the residual isolated in
`SliceSpanStep.lean` is neither the dichotomy (which this module derives) nor the monotonicity
(which is a theorem), but exactly Pardon's "a single `2`-surgery changes the invariant by at most
one dimension".
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {ψ : Submission.Diffeo}

/-! ## The level functions of the two half-box spheres -/

/-- **The level function of the upper half-box sphere**: `max (boxNorm - s) (-planeCoord)`. -/
noncomputable def upperLevel (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : R3 → ℝ :=
  fun y => max (boxLevel s c σ y) (-(Work.BoxShrink.Bubble.planeCoord c σ u y))

/-- **The level function of the lower half-box sphere**: `max (boxNorm - s) planeCoord`. -/
noncomputable def lowerLevel (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : R3 → ℝ :=
  fun y => max (boxLevel s c σ y) (Work.BoxShrink.Bubble.planeCoord c σ u y)

theorem upperLevel_continuous (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Continuous (upperLevel s c σ u) :=
  (boxLevel_continuous s c σ).max ((Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).continuous.neg)

theorem lowerLevel_continuous (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Continuous (lowerLevel s c σ u) :=
  (boxLevel_continuous s c σ).max (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).continuous

/-- The sublevel region of the upper half-box level function is the upper region. -/
theorem region_upperLevel {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.Smooth.Morse.region ψ (upperLevel s c σ u) 0 =
      Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u := by
  ext x
  rw [Work.BoxShrink.Core.mem_upperRegion, Work.Smooth.Morse.region]
  simp only [Work.BoxShrink.Core.upperHalf, upperLevel, boxLevel,
    Work.BoxShrink.Bubble.planeCoord, Set.mem_setOf_eq, Set.mem_inter_iff, max_lt_iff,
    neg_lt_zero, sub_lt_zero, sub_pos, Submission.mem_PBox_iff]

/-- The sublevel region of the lower half-box level function is the lower region. -/
theorem region_lowerLevel {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.Smooth.Morse.region ψ (lowerLevel s c σ u) 0 =
      Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u := by
  ext x
  rw [Work.BoxShrink.Core.mem_lowerRegion, Work.Smooth.Morse.region]
  simp only [Work.BoxShrink.Core.lowerHalf, lowerLevel, boxLevel,
    Work.BoxShrink.Bubble.planeCoord, Set.mem_setOf_eq, Set.mem_inter_iff, max_lt_iff,
    sub_lt_zero, Submission.mem_PBox_iff]

/-! ## Pardon's equation (1) at the two half-box spheres -/

/-- **The dichotomy at the upper region**, from Pardon's equation (1), given that the half-box
trace is nice and inessential. -/
theorem pardonDichotomy_upperRegion_of_equation1 (h : Equation1Input) {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hnice : Work.Smooth.Morse.NiceLevel ψ (upperLevel s c σ u) 0)
    (htrace : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.Smooth.Morse.levelSet ψ (upperLevel s c σ u) 0)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u) := by
  refine (h ψ (upperLevel s c σ u) 0 (upperLevel_continuous s c σ u) hnice htrace).imp ?_ ?_
    <;> intro hh <;> rwa [region_upperLevel] at hh

/-- **The dichotomy at the lower region**, from Pardon's equation (1). -/
theorem pardonDichotomy_lowerRegion_of_equation1 (h : Equation1Input) {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hnice : Work.Smooth.Morse.NiceLevel ψ (lowerLevel s c σ u) 0)
    (htrace : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.Smooth.Morse.levelSet ψ (lowerLevel s c σ u) 0)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) := by
  refine (h ψ (lowerLevel s c σ u) 0 (lowerLevel_continuous s c σ u) hnice htrace).imp ?_ ?_
    <;> intro hh <;> rwa [region_lowerLevel] at hh

/-! ## The residual, in the "no jump" form -/

/-- **The residual is exactly the absence of a `⊤ → ⊥` jump at the pinch.**  Given Pardon's
equation (1) at the three spheres of the pinch — the box sphere and the two half-box spheres — the
one-sided dimension bound `PinchNoJump` is equivalent to: the pinch does not take the invariant from
the whole of `H₁` to zero, i.e. the box region cannot be full-rank while both half-regions are
inessential.

(Since the three dichotomies and monotonicity are theorems here, this is the sharpest form of the
residual: everything except the single `2`-surgery statement is discharged.) -/
theorem pinchNoJump_iff_noJump {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ))
    (hup : Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u))
    (hlo : Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) :
    (Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) + 1) ↔
    ¬ (Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) = ⊤ ∧
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u) = ⊥ ∧
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) = ⊥) := by
  have hsplit : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) =
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u) ⊔
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) :=
    Work.SurgeryInvariance.Span.union_eq_sup
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion _ s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion _ s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion _ s c σ u)
  constructor
  · intro hstep ⟨htop, hup0, hlo0⟩
    have hh : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) = ⊥ := by
      rw [hsplit, hup0, hlo0, sup_bot_eq]
    have hf : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) = 0 := by
      rw [hh, Submodule.finrank_eq_zero.mpr rfl]
    have h2 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) = 2 := by
      rw [htop, finrank_top, Module.finrank_prod, Module.finrank_self]
    rw [h2, hf] at hstep
    omega
  · intro hnojump
    rcases hdich with h0 | htop
    · rw [h0, Submodule.finrank_eq_zero.mpr rfl]
      omega
    · have hne : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u) ≠ ⊥ ∨
          Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
            (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) ≠ ⊥ := by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        exact hnojump ⟨htop, hcon.1, hcon.2⟩
      have htop' : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
            Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) = ⊤ := by
        rcases hne with h | h
        · have : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u) = ⊤ :=
            hup.resolve_left h
          rw [hsplit, this, top_sup_eq]
        · have : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) = ⊤ :=
            hlo.resolve_left h
          rw [hsplit, this, sup_top_eq]
      rw [htop, htop']
      omega

end

end Work.BoxShrink.Pinch
