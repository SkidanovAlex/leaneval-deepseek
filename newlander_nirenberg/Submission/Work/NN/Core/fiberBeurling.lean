/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The fibrewise Beurling transform and the band of the fixed-disc potential

This file collects the definitions used to bound the fixed-disc Cauchy potential
`Work.NN.Core.fiberPot` on the Hölder scale.

* `fiberSlice j v z` is the slice `w ↦ v (z with z j replaced by w)` of `v` in the `j`-th
  coordinate at the transverse coordinates of `z`;
* `fiberBand R j v` is the hypothesis that `v` is supported in the band `‖z j‖ < R` on which the
  fixed-disc integral `∫_{‖w‖ < R}` may be replaced by the full plane;
* `fiberBeurling R j v` is the fibrewise Beurling transform of `v`, i.e. the `(1,0)`-derivative
  of the fixed-disc potential: for `‖z j‖ < R` one has
  `∂_j (fiberPot R j v) z = fiberBeurling R j v z`
  (see `Work.NN.Core.dCoord_fiberPot_self`);
* `fiberAccess r j R = polydisc 0 (Function.update r j R)` is the polydisc of the `j`-th fibre over
  which the potential is evaluated, i.e. the region of the data that is actually read when
  `fiberPot R j v` is evaluated on `polydisc 0 r` with `r i < R` for all `i`.
-/
import Mathlib
import Submission.Work.NN.Core.fiberPot
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy

noncomputable section

open scoped NNReal ENNReal
open Set MeasureTheory

namespace Work.NN.Core

/-- The slice of `v` in the `j`-th coordinate at the transverse coordinates of `z`:
`fiberSlice j v z = fun w => v (Function.update z j w)`. -/
def fiberSlice {n : ℕ} (j : Fin n) (v : Cn n → ℂ) (z : Cn n) : ℂ → ℂ :=
  fun w => v (Function.update z j w)

@[simp] lemma fiberSlice_apply {n : ℕ} (j : Fin n) (v : Cn n → ℂ) (z : Cn n) (w : ℂ) :
    fiberSlice j v z w = v (Function.update z j w) := rfl

/-- `v` is supported in the band `‖z j‖ < R`: this is the hypothesis under which the fixed-disc
integral defining `fiberPot R j v` agrees (after translating the pole) with a fibrewise
translation-invariant Cauchy transform. -/
def fiberBand {n : ℕ} (R : ℝ) (j : Fin n) (v : Cn n → ℂ) : Prop :=
  ∀ z : Cn n, R ≤ ‖z j‖ → v z = 0

/-- The fibrewise Beurling transform of `v`: the fibrewise Cauchy transform of the slice is
`cauchyTransform (2R) (fiberSlice j v z) (z j)`, and its `(1,0)`-derivative is the Beurling
transform of the slice. -/
noncomputable def fiberBeurling {n : ℕ} (R : ℝ) (j : Fin n) (v : Cn n → ℂ) : Cn n → ℂ :=
  fun z => Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z j)

@[simp] lemma fiberBeurling_apply {n : ℕ} (R : ℝ) (j : Fin n) (v : Cn n → ℂ) (z : Cn n) :
    fiberBeurling R j v z
      = Work.CR.Flat.beurlingTransform (2 * R) (fiberSlice j v z) (z j) := rfl

/-- The region of the data read when evaluating the fixed-disc potential on `polydisc 0 r`:
the polydisc with the `j`-th radius replaced by `R`. -/
def fiberAccess {n : ℕ} (r : Fin n → ℝ) (j : Fin n) (R : ℝ) : Set (Cn n) :=
  Work.CR.Flat.polydisc 0 (Function.update r j R)

/-- Membership in the access polydisc, spelled out coordinatewise. -/
lemma mem_fiberAccess {n : ℕ} {r : Fin n → ℝ} {j : Fin n} {R : ℝ} {z : Cn n} :
    z ∈ fiberAccess r j R ↔ (∀ i, i ≠ j → ‖z i‖ < r i) ∧ ‖z j‖ < R := by
  rw [fiberAccess, Work.CR.Flat.mem_polydisc]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have h' := h i
      rw [Function.update_of_ne hi] at h'
      simpa using h'
    · have h' := h j
      rw [Function.update_self] at h'
      simpa using h'
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i = j
    · subst hi; simpa using h2
    · rw [Function.update_of_ne hi]; simpa using h1 i hi

lemma fiberAccess_isOpen {n : ℕ} (r : Fin n → ℝ) (j : Fin n) (R : ℝ) :
    IsOpen (fiberAccess r j R) :=
  Work.CR.Flat.isOpen_polydisc 0 _

/-- The polydisc `0 r` is contained in the access region `fiberAccess r j R` as soon as
`r j < R`. -/
lemma polydisc_subset_fiberAccess {n : ℕ} {r : Fin n → ℝ} {j : Fin n} {R : ℝ}
    (hR : r j < R) : Work.CR.Flat.polydisc (0 : Cn n) r ⊆ fiberAccess r j R := by
  intro z hz
  rw [mem_fiberAccess]
  have hzi : ∀ i, ‖z i‖ < r i := by
    intro i
    have h' := hz i
    simpa using h'
  exact ⟨fun i _ => hzi i, lt_trans (hzi j) hR⟩

end Work.NN.Core
