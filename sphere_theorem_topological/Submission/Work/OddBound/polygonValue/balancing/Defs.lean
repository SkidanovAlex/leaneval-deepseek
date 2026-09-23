import Mathlib
import Submission.Work.OddBound.polygonValue.balancing.Instances
import Submission.Work.OddBound.polygonValue.brokenGeodesicDefs
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal
import Submission.EDist
import Submission.Work.OddBound.longHomotopy.curveLength_toolkit
import Submission.Work.OddBound.liftPiecewise.exists_lift_of_piecewise_short

/-!
# The arclength-balanced broken geodesic: definitions

This module sets up the vocabulary for `Work.OddBound.polygonValue.balancedBrokenLoop`.

Given the side curves `S i r τ` of the based closed `N`-gon family `w` (the point at fraction `r`
of the side `i` of the slice `τ`), we concatenate them along the slice `τ` and reparametrise
proportionally to arclength.

The **side index** `gIdx τ a` of the arclength `a` is the number of cumulative breakpoints
`cumLen τ j ≤ a` minus one; `gFin τ a` is that index as an element of `Fin N`, `gPrm τ a` the
side parameter at arclength `a`, clamped to `[0,1]`, and `gPt τ a = S (gFin τ a) (gPrm τ a) τ` the
point of the broken geodesic at arclength `a`.  Finally `gLoop τ u = gPt τ (totLen τ * u)` is the
arclength-proportional parametrisation of the slice and
`gFam s t = gLoop (clamp01 t) (Int.fract s)` the `1`-periodic-in-`s` family of loops.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

namespace Work.OddBound.polygonValue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]

noncomputable section

/-! ## 1. The index, parameter and point at a given arclength -/

/-- **The side index at arclength `a` of the slice `τ`**: the number of breakpoints
`cumLen τ j ≤ a` (for `j < N`) minus one.  It is the index of the side carrying the arclength
`a`. -/
noncomputable def gIdx (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (τ a : ℝ) : ℕ :=
  ((Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ a)).card - 1

/-- The side index as an element of `Fin N`. -/
noncomputable def gFin (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M) (τ a : ℝ) :
    Fin N :=
  ⟨gIdx (I := I) p w τ a, by
    have h1 : ((Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ a)).card ≤ N := by
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun j => cumLen (I := I) p w τ j ≤ a) (Finset.range N))
    have h2 : gIdx (I := I) p w τ a ≤ N - 1 := by
      simp only [gIdx]
      exact le_trans (Nat.sub_le_sub_right h1 1) le_rfl
    omega⟩

/-- **The side parameter at arclength `a` of the slice `τ`**: the fraction of the way along the
side `gIdx τ a` at which the arclength `a` is reached, clamped to `[0,1]` (so that it is a total
function). -/
noncomputable def gPrm (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (τ a : ℝ) : ℝ :=
  clamp01 ((a - cumLen (I := I) p w τ (gIdx (I := I) p w τ a))
    / sideLen (I := I) p w τ (gIdx (I := I) p w τ a))

/-- **The point of the broken geodesic of the slice `τ` at arclength `a`.** -/
noncomputable def gPt (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M)
    (S : Fin N → ℝ → ℝ → M) (τ a : ℝ) : M :=
  S (gFin (I := I) p hN w τ a) (gPrm (I := I) p w τ a) τ

/-- **The arclength-proportional parametrisation of the slice `τ`**: `gLoop τ u` is the point of
the broken geodesic of the slice at arclength `totLen τ * u`. -/
noncomputable def gLoop (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M)
    (S : Fin N → ℝ → ℝ → M) (τ u : ℝ) : M :=
  gPt (I := I) p hN w S τ (totLen (I := I) p w τ * u)

/-- **The `1`-periodic-in-`s` balanced loop family** of the slices `t ∈ [0,1]`. -/
noncomputable def gFam (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M)
    (S : Fin N → ℝ → ℝ → M) (s t : ℝ) : M :=
  gLoop (I := I) p hN w S (clamp01 t) (Int.fract s)

/-! ## 2. Elementary bookkeeping -/

@[simp] theorem gIdx_def (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (τ a : ℝ) :
    gIdx (I := I) p w τ a
      = ((Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ a)).card - 1 := rfl

@[simp] theorem gFin_val (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M) (τ a : ℝ) :
    ((gFin (I := I) p hN w τ a : Fin N) : ℕ) = gIdx (I := I) p w τ a := rfl

@[simp] theorem gPrm_def (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (τ a : ℝ) :
    gPrm (I := I) p w τ a
      = clamp01 ((a - cumLen (I := I) p w τ (gIdx (I := I) p w τ a))
        / sideLen (I := I) p w τ (gIdx (I := I) p w τ a)) := rfl

@[simp] theorem gPt_def (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M)
    (S : Fin N → ℝ → ℝ → M) (τ a : ℝ) :
    gPt (I := I) p hN w S τ a
      = S (gFin (I := I) p hN w τ a) (gPrm (I := I) p w τ a) τ := rfl

@[simp] theorem gLoop_def (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M)
    (S : Fin N → ℝ → ℝ → M) (τ u : ℝ) :
    gLoop (I := I) p hN w S τ u = gPt (I := I) p hN w S τ (totLen (I := I) p w τ * u) := rfl

@[simp] theorem gFam_def (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M)
    (S : Fin N → ℝ → ℝ → M) (s t : ℝ) :
    gFam (I := I) p hN w S s t
      = gLoop (I := I) p hN w S (clamp01 t) (Int.fract s) := rfl

theorem gIdx_le (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (τ a : ℝ) :
    gIdx (I := I) p w τ a ≤ N - 1 := by
  have h1 : ((Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ a)).card ≤ N := by
    simpa using Finset.card_le_card
      (Finset.filter_subset (fun j => cumLen (I := I) p w τ j ≤ a) (Finset.range N))
  simp only [gIdx]
  exact le_trans (Nat.sub_le_sub_right h1 1) le_rfl

theorem gIdx_lt (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M) (τ a : ℝ) :
    gIdx (I := I) p w τ a < N := by
  have := gIdx_le (I := I) p w τ a
  omega

theorem gPrm_mem (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (τ a : ℝ) :
    gPrm (I := I) p w τ a ∈ Set.Icc (0 : ℝ) 1 :=
  clamp01_mem _

theorem sideLen_eq_sub (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (τ : ℝ) (i : ℕ) :
    sideLen (I := I) p w τ i = cumLen (I := I) p w τ (i + 1) - cumLen (I := I) p w τ i := by
  have := cumLen_succ (I := I) p w τ i
  linarith

/-! ## 3. The invariant: `cumLen τ (gIdx τ a) ≤ a ≤ cumLen τ (gIdx τ a + 1)` -/

/-- **The lower invariant**: the breakpoint before the arclength is at most the arclength. -/
theorem cumLen_gIdx_le (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M) (τ a : ℝ)
    (ha : 0 ≤ a) :
    cumLen (I := I) p w τ (gIdx (I := I) p w τ a) ≤ a := by
  classical
  rw [gIdx_def]
  set Sf : Finset ℕ := (Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ a) with hSf
  have hmem : ∀ j, j ∈ Sf ↔ j < N ∧ cumLen (I := I) p w τ j ≤ a := by
    intro j; rw [hSf, Finset.mem_filter, Finset.mem_range]
  have h0mem : (0 : ℕ) ∈ Sf := (hmem 0).mpr ⟨hN, by rw [cumLen_zero]; exact ha⟩
  have hcpos : 1 ≤ Sf.card := Finset.card_pos.mpr ⟨0, h0mem⟩
  have hcN : Sf.card ≤ N := by
    rw [hSf]; simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.range N))
  have hlt : Sf.card - 1 < N := by omega
  by_contra hcon
  push_neg at hcon
  have hnotmem : Sf.card - 1 ∉ Sf := by
    rw [hmem]; exact fun h => absurd h.2 (not_le.mpr hcon)
  have hsub : Sf ⊆ Finset.range (Sf.card - 1) := by
    intro j hj
    rw [Finset.mem_range]
    by_contra hjc
    push_neg at hjc
    have hj' := (hmem j).mp hj
    exact hnotmem ((hmem _).mpr ⟨hlt, le_trans (cumLen_mono (I := I) p w τ hjc) hj'.2⟩)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  omega

/-- **The upper invariant**: the arclength is at most the breakpoint after it. -/
theorem le_cumLen_gIdx_succ (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M) (τ a : ℝ)
    (ha : a ≤ totLen (I := I) p w τ) :
    a ≤ cumLen (I := I) p w τ (gIdx (I := I) p w τ a + 1) := by
  classical
  have haN : a ≤ cumLen (I := I) p w τ N := by rwa [totLen_eq_cumLen] at ha
  rw [gIdx_def]
  rcases le_or_gt 0 a with ha0 | ha0
  · set Sf : Finset ℕ := (Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ a) with hSf
    have hmem : ∀ j, j ∈ Sf ↔ j < N ∧ cumLen (I := I) p w τ j ≤ a := by
      intro j; rw [hSf, Finset.mem_filter, Finset.mem_range]
    have h0mem : (0 : ℕ) ∈ Sf := (hmem 0).mpr ⟨hN, by rw [cumLen_zero]; exact ha0⟩
    have hcpos : 1 ≤ Sf.card := Finset.card_pos.mpr ⟨0, h0mem⟩
    have hcN : Sf.card ≤ N := by
      rw [hSf]; simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.range N))
    rw [show Sf.card - 1 + 1 = Sf.card by omega]
    rcases eq_or_lt_of_le hcN with hN' | hlt
    · rw [hN']; exact haN
    · by_contra hcon
      push_neg at hcon
      have hsub : Finset.range (Sf.card + 1) ⊆ Sf := by
        intro j hj
        rw [Finset.mem_range] at hj
        exact (hmem j).mpr ⟨by omega,
          le_trans (cumLen_mono (I := I) p w τ (by omega : j ≤ Sf.card)) (le_of_lt hcon)⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_range] at hcard
      omega
  · exact le_trans (le_of_lt ha0) (cumLen_nonneg (I := I) p w τ _)

/-- **The upper invariant, strict form**: if the arclength is smaller than the total length then it
is strictly smaller than the breakpoint after it. -/
theorem lt_cumLen_gIdx_succ (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M) (τ a : ℝ)
    (ha : a < totLen (I := I) p w τ) :
    a < cumLen (I := I) p w τ (gIdx (I := I) p w τ a + 1) := by
  classical
  have haN : a < cumLen (I := I) p w τ N := by rwa [totLen_eq_cumLen] at ha
  rw [gIdx_def]
  rcases lt_or_ge a 0 with ha0 | ha0
  · exact lt_of_lt_of_le ha0 (cumLen_nonneg (I := I) p w τ _)
  · set Sf : Finset ℕ := (Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ a) with hSf
    have hmem : ∀ j, j ∈ Sf ↔ j < N ∧ cumLen (I := I) p w τ j ≤ a := by
      intro j; rw [hSf, Finset.mem_filter, Finset.mem_range]
    have h0mem : (0 : ℕ) ∈ Sf := (hmem 0).mpr ⟨hN, by rw [cumLen_zero]; exact ha0⟩
    have hcpos : 1 ≤ Sf.card := Finset.card_pos.mpr ⟨0, h0mem⟩
    have hcN : Sf.card ≤ N := by
      rw [hSf]; simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.range N))
    rw [show Sf.card - 1 + 1 = Sf.card by omega]
    by_contra hcon
    push_neg at hcon
    have hcardN : Sf.card = N := by
      by_contra hne
      have hclt : Sf.card < N := lt_of_le_of_ne hcN hne
      have hsub : Finset.range (Sf.card + 1) ⊆ Sf := by
        intro j hj
        rw [Finset.mem_range] at hj
        exact (hmem j).mpr ⟨by omega,
          le_trans (cumLen_mono (I := I) p w τ (by omega : j ≤ Sf.card)) hcon⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_range] at hcard
      omega
    rw [hcardN] at hcon
    exact absurd hcon (not_le.mpr haN)

/-- **The side at the arclength `a < totLen τ` (with `a ≥ 0`) has positive length.** -/
theorem sideLen_gIdx_pos (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M) (τ a : ℝ)
    (ha0 : 0 ≤ a) (ha : a < totLen (I := I) p w τ) :
    0 < sideLen (I := I) p w τ (gIdx (I := I) p w τ a) := by
  have hstrict := lt_cumLen_gIdx_succ (I := I) p hN w τ a ha
  have hle := cumLen_gIdx_le (I := I) p hN w τ a ha0
  rw [sideLen_eq_sub]
  linarith

end

end Work.OddBound.polygonValue
