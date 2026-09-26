import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Transport
import Submission.Work.SurgeryInvariance.API

/-!
# The local model at a critical value (item 4)

At a nondegenerate critical point of `g|_F` the passage through the critical value changes the
sublevel region by a local piece: passing a local minimum adds a disc around the critical point,
passing a local maximum adds a disc around the other side, and passing a saddle adds the band
between the two branches of the level set.  In every case the piece added inside a small ball
around the critical point is the trace of the surface in that ball — a disc of `F`.

This file records that local model as the predicate `DiscModel` of
`Submission.Work.Smooth.Morse.Defs` and proves the bridges to the surgery vocabulary of
`Work.SurgeryInvariance`:

* `Work.Smooth.Morse.DiscModel.toSurgeryShape`;
* `Work.Smooth.Morse.DiscModel.toSurgeryStepZero`;
* `Work.Smooth.Morse.DiscModel.windingSpan_eq` — the winding span does not change at a critical
  value whose local model is `DiscModel`;
* `Work.Smooth.Morse.isOpenInCarrier_region` — the regions are open in the surface (so the pieces
  of a surgery are open, as `SurgeryShape` requires).

## What `DiscModel` really costs

`DiscModel` is a genuine hypothesis, not a formal consequence of the Morse lemma, and it is a
*strong* one: it can only hold at a critical value at the **bottom of the range of `g|_F`**.

Indeed, write `V = region (t₀-ε)` and `U = D.interior = region (t₀+ε) \ V ⊆ {t₀-ε ≤ g}` (the union
identity of `DiscModel`).  Then

* the level set `F ∩ {g = t₀-ε}` is contained in `U`, which is open in `F`: a point of it lies in
  `region (t₀+ε)` but not in `V`;
* every cluster point `x` of `V` has `g x ≤ t₀-ε` (continuity of `g`); if `g x = t₀-ε` then
  `x ∈ U`, and since `U` is open and disjoint from `V` that is impossible, so `g x < t₀-ε` and
  `x ∈ V`.  Hence `V` is closed as well as open in `F`;
* `F` is connected (it is the continuous image of `ℝ²`), so `V = ∅` or `V = F`; and `V ≠ F` because
  `U = D.interior` is nonempty and disjoint from `V`.

So `region (t₀-ε) = ∅` for every small `ε`, i.e. `t₀ - ε ≤ g` on `F`, and letting `ε → 0` gives
`t₀ ≤ min (g|_F)`.  This is proved in
`Work.Smooth.Morse.MorseModel.not_discModel_of_lt`.  Consequently the hypothesis
`∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀` of the theorems of `Submission.Work.Smooth.Morse.Sweep`
can *never* be met by a nonconstant `g` (the maximum of `g|_F` is a critical value above the
minimum); those theorems are correct but vacuous, and the non-vacuous statements are stated in terms
of the crossing data (the winding span of the two sides) instead:

* `Work.Smooth.Morse.DiscGrowth` is the local model at the **first tangency** of a growing convex
  body with `F` — the lower region is empty and the region just above `t₀` is the interior of an
  embedded disc — and it *is* satisfiable (`Work.Smooth.Morse.DiscGrowth.of_min`); its bridges to
  `Work.SurgeryInvariance.SurgeryStepZero` and to the equality of the winding spans are proved here
  (`DiscGrowth.toSurgeryShape`, `…toSurgeryStepZero`, `…windingSpan_eq`);
* for a general critical value of a level family the change is *not* by a disc: passing a saddle of a
  Morse function on the torus turns a disc into an annulus (span `0 → ℚ·(1,0)`), and the essential
  loop of the annulus has to cross one of the level arcs.  What the sweep needs at such a parameter
  is therefore only that the change preserves the winding span
  (`Work.Smooth.Morse.windingSpan_eq_of_levelSweep_of_crossing`), which is what a family of spheres
  put in general position provides, and what `Work.Smooth.Morse.LevelFamily.crossing` records.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

variable {ψ : Submission.Diffeo} {g : R3 → ℝ} {t t₀ : ℝ}

/-- **The sublevel regions are open in the surface** (for continuous `g`): they are the traces of
the open sets `{g < t}`.  Hence the two pieces of a surgery, once identified with such regions,
are automatically open, as `SurgeryShape` requires. -/
theorem isOpenInCarrier_region (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g) (t : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) (region ψ g t) := by
  have hset : region ψ g t = (torus ψ).carrier ∩ {x : R3 | g x < t} := rfl
  rw [hset]
  exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := torus ψ)
    (isOpen_lt hg continuous_const)

/-- **The local model at a critical value gives the geometric shape of a single `2`-surgery.** -/
theorem DiscModel.toSurgeryShape (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g)
    {t₀ : ℝ} (h : DiscModel ψ g t₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Work.SurgeryInvariance.SurgeryShape (torus ψ)
        (region ψ g (t₀ - ε)) (region ψ g (t₀ + ε)) := by
  obtain ⟨ε₀, hε₀, hD⟩ := h
  refine ⟨ε₀, hε₀, fun ε hε hlt => ?_⟩
  obtain ⟨D, hcover, hdisj⟩ := hD ε hε hlt
  exact ⟨D, isOpenInCarrier_region ψ hg (t₀ - ε), isOpenInCarrier_region ψ hg (t₀ + ε),
    Or.inr ⟨hcover, hdisj⟩⟩

/-- **The local model at a critical value gives a single `2`-surgery in the loop-level form.** -/
theorem DiscModel.toSurgeryStepZero (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g)
    {t₀ : ℝ} (h : DiscModel ψ g t₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Work.SurgeryInvariance.SurgeryStepZero (torus ψ)
        (region ψ g (t₀ - ε)) (region ψ g (t₀ + ε)) := by
  obtain ⟨ε₀, hε₀, hD⟩ := h
  refine ⟨ε₀, hε₀, fun ε hε hlt => ?_⟩
  obtain ⟨D, hcover, hdisj⟩ := hD ε hε hlt
  exact ⟨D.interior, Work.SurgeryInvariance.DiscRegion.windingSpan_interior_eq_bot D,
    isOpenInCarrier_region ψ hg (t₀ - ε), isOpenInCarrier_region ψ hg (t₀ + ε),
    D.open_interior', Or.inr ⟨hcover, hdisj⟩⟩

/-! ## The satisfiable local model: the first tangency of a growing body -/

/-- `DiscGrowth` is satisfiable at any level below the minimum: if `t₀ ≤ g` on `F` (so that the
region below `t₀` is empty) and the region just above `t₀` is the interior of an embedded disc, then
`DiscGrowth ψ g t₀` holds.  This is the situation of the first tangency of a growing convex body
with `F`. -/
theorem DiscGrowth.of_min {ψ : Submission.Diffeo} {g : R3 → ℝ} {t₀ ε : ℝ}
    (hmin : ∀ x : R3, x ∈ (torus ψ).carrier → t₀ ≤ g x) (hε : 0 < ε)
    (hD : ∃ D : Work.SurgeryInvariance.DiscRegion (torus ψ), region ψ g (t₀ + ε) = D.interior) :
    DiscGrowth ψ g t₀ :=
  ⟨ε, hε, by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hgx⟩
    have hlt : g x < t₀ := lt_of_lt_of_le hgx (by linarith)
    exact absurd (hmin x hx) (not_le.mpr hlt), hD⟩

/-- **The first-tangency local model is a single `2`-surgery**: the region just above `t₀` is the
region just below it (empty) together with the interior of an embedded disc. -/
theorem DiscGrowth.toSurgeryShape (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g)
    {t₀ : ℝ} (h : DiscGrowth ψ g t₀) :
    ∃ ε : ℝ, 0 < ε ∧ Work.SurgeryInvariance.SurgeryShape (torus ψ)
      (region ψ g (t₀ - ε)) (region ψ g (t₀ + ε)) := by
  obtain ⟨ε, hε, hempty, D, hD⟩ := h
  refine ⟨ε, hε, ?_⟩
  refine ⟨D, ?_, isOpenInCarrier_region ψ hg (t₀ + ε), Or.inr ⟨?_, ?_⟩⟩
  · rw [hempty]
    simpa only [Work.SurgeryInvariance.IsOpenInCarrier, Set.preimage_empty]
      using (isOpen_empty : IsOpen (∅ : Set (torus ψ).carrier))
  · rw [hD, hempty, Set.empty_union]
  · rw [hempty]
    rw [Set.disjoint_iff]
    intro x hx
    exact hx.1

/-- **The first-tangency local model is a `2`-surgery in the loop-level form.** -/
theorem DiscGrowth.toSurgeryStepZero (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g)
    {t₀ : ℝ} (h : DiscGrowth ψ g t₀) :
    ∃ ε : ℝ, 0 < ε ∧ Work.SurgeryInvariance.SurgeryStepZero (torus ψ)
      (region ψ g (t₀ - ε)) (region ψ g (t₀ + ε)) := by
  obtain ⟨ε, hε, hshape⟩ := h.toSurgeryShape ψ hg
  exact ⟨ε, hε, hshape.toZero⟩

/-- **The winding span does not change at a first tangency.** -/
theorem DiscGrowth.windingSpan_eq (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g)
    {t₀ : ℝ} (h : DiscGrowth ψ g t₀) :
    ∃ ε : ℝ, 0 < ε ∧ Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε)) := by
  obtain ⟨ε, hε, hstep⟩ := h.toSurgeryStepZero ψ hg
  exact ⟨ε, hε, hstep.windingSpan_eq⟩

/-- **The winding span does not change at a critical value whose local model is `DiscModel`.** -/
theorem DiscModel.windingSpan_eq (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g)
    {t₀ : ℝ} (h : DiscModel ψ g t₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε)) := by
  obtain ⟨ε₀, hε₀, hD⟩ := h.toSurgeryStepZero ψ hg
  exact ⟨ε₀, hε₀, fun ε hε hlt => (hD ε hε hlt).windingSpan_eq⟩

end

end Work.Smooth.Morse
