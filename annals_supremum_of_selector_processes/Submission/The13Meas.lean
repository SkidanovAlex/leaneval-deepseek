import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ChallengeDeps
/-!
# TASK (child): prove ALL four lemmas in this file.  They are generic
# measurability / sup identities over a finite index type.  Statements are FIXED; add helpers.
# Namespace Submission.The13Meas.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Classical
open scoped NNReal ENNReal BigOperators

namespace Submission

namespace The13Meas

/-- max' over the image of a finite family of real measurable functions is measurable -/
lemma measurable_finset_maxR {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    (hI : (Finset.univ : Finset ι).Nonempty)
    (a : ι → α → ℝ) (ha : ∀ i : ι, Measurable (a i)) :
    Measurable (fun x : α => (Finset.univ.image (fun i : ι => a i x)).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i x, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) := by
  classical
  -- the pointwise max' over the image equals the pointwise sup over the finite type ι,
  -- which is measurable by Measurable.iSup (real valued, countable index).
  have hfun : (fun x : α => (Finset.univ.image (fun i : ι => a i x)).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i x, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) = (fun x : α => ⨆ i : ι, a i x) := by
    ext x
    rw [← Finset.Nonempty.csSup_eq_max']
    rw [Finset.coe_image]
    simp
    rfl
  rw [hfun]
  exact Measurable.iSup (f := fun (i : ι) (x : α) => a i x) ha

/-- the real cast of the max of NNReal values equals the max of the real casts -/
lemma maxR_coe_ident {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hI : (Finset.univ : Finset ι).Nonempty) (a : ι → ℝ≥0) :
    ((Finset.univ.image a).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) : ℝ)
      = (Finset.univ.image (fun i : ι => (a i : ℝ))).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨(a i : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
  classical
  let L : ℝ≥0 := (Finset.univ.image a).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  let R : ℝ := (Finset.univ.image (fun i : ι => (a i : ℝ))).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨(a i : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  change (L : ℝ) = R
  apply le_antisymm
  · -- (L : ℝ) ≤ R : pick an index i₀ realising L and use le_max' on the real-valued image
    have hmemL : L ∈ Finset.univ.image a := Finset.max'_mem _ _
    rcases Finset.mem_image.mp hmemL with ⟨i0, hi0, ha0⟩
    rw [← ha0]
    exact Finset.le_max' (Finset.univ.image (fun i : ι => (a i : ℝ))) ((a i0 : ℝ))
      (Finset.mem_image.mpr ⟨i0, hi0, rfl⟩)
  · -- R ≤ (L : ℝ) : every real-cast value is bounded by the cast of the NNReal max
    exact Finset.max'_le (s := Finset.univ.image (fun i : ι => (a i : ℝ)))
      (H := by
        rcases hI with ⟨i, hi⟩
        exact ⟨(a i : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
      (x := (L : ℝ))
      (by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
        exact_mod_cast Finset.le_max' (Finset.univ.image a) (a i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩))

/-- the ∞-sup over the finite type equals the coe of the max' -/
lemma iSup_coe_max' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hI : (Finset.univ : Finset ι).Nonempty) (a : ι → ℝ≥0) :
    (⨆ i : ι, (a i : ℝ≥0∞)) = ((Finset.univ.image a).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) : ℝ≥0∞) := by
  classical
  let L : ℝ≥0 := (Finset.univ.image a).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  change (⨆ i : ι, (a i : ℝ≥0∞)) = (L : ℝ≥0∞)
  apply le_antisymm
  · -- sup ≤ cast max : every term is bounded by the cast of the NNReal max
    apply iSup_le
    intro i
    exact ENNReal.coe_le_coe.mpr
      (Finset.le_max' (Finset.univ.image a) (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  · -- cast max ≤ sup : realised by the index attaining the NNReal max
    have hmemL : L ∈ Finset.univ.image a := Finset.max'_mem _ _
    rcases Finset.mem_image.mp hmemL with ⟨i0, hi0, ha0⟩
    rw [← ha0]
    exact le_iSup (fun i : ι => (a i : ℝ≥0∞)) i0

/-- the max over the type of NNReal values is attained -/
lemma maxR_att {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hI : (Finset.univ : Finset ι).Nonempty) (a : ι → ℝ≥0) :
    ∃ i : ι, a i = (Finset.univ.image a).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
  classical
  -- max' is a member of the image, so it is attained at some index
  have hmem : (Finset.univ.image a).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) ∈ Finset.univ.image a :=
    Finset.max'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨i, hi, hai⟩
  exact ⟨i, hai⟩

end The13Meas
end Submission
