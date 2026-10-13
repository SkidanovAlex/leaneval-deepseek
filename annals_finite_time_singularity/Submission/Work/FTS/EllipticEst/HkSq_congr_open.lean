/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HkSq` only sees the values of `f` on the open quadrant

The `H^k`-square of `Work.Spaces` is the iterated integral, over `[0,∞) × [0,π/2]`,
of `HkIntegrand`, a sum of squares of weighted derivatives `D_z^i f` and `D_z^j D_θ^i f`.
A derivative at an **interior** point `z > 0`, `0 < θ < π/2` of the quadrant only depends
on the values of `f` on a *neighbourhood* of that point, and a small enough neighbourhood
is again contained in the open quadrant.  Hence if two functions agree on the open
quadrant `(0,∞) × (0,π/2)`, then all the weighted derivatives appearing in `HkIntegrand`
agree there too, so the two integrands agree off the null set
`{z = 0} ∪ {θ = 0} ∪ {θ = π/2}` inside `[0,∞) × [0,π/2]`.

That is the content of the file: `HkSq α k f = HkSq α k g` as soon as `f = g` on the open
quadrant.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllipticEst

/-- `F` and `G` agree on the open quadrant `(0,∞) × (0,π/2)`. -/
def AgreeOnQ (F G : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ

/-! ## Local congruence of the partial derivatives

If two functions agree on a neighbourhood of a point, their derivatives there agree.
For our functions of two variables this reads: agreement on a neighbourhood in the `z`
variable (at fixed `θ`) gives equality of `∂_z`, and likewise in the `θ` variable. -/

lemma pz_congr_of_eventuallyEq {F G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, F z' θ = G z' θ) :
    Work.Spaces.pz F z θ = Work.Spaces.pz G z θ :=
  Filter.EventuallyEq.deriv_eq h

lemma pth_congr_of_eventuallyEq {F G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ θ' in 𝓝 θ, F z θ' = G z θ') :
    Work.Spaces.pth F z θ = Work.Spaces.pth G z θ :=
  Filter.EventuallyEq.deriv_eq h

/-! ## Agreement of the weighted derivatives on the open quadrant

The open quadrant is open, so a function that vanishes on it has all its derivatives
vanishing on it; iterating, the same is true for `D_z`, `D_θ` and all their mixed
iterates. -/

lemma AgreeOnQ.pz {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    AgreeOnQ (Work.Spaces.pz F) (Work.Spaces.pz G) := by
  intro z θ hz hθ hlt
  refine pz_congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact h z' θ hz' hθ hlt

lemma AgreeOnQ.pth {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    AgreeOnQ (Work.Spaces.pth F) (Work.Spaces.pth G) := by
  intro z θ hz hθ hlt
  refine pth_congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ hlt] with θ' hθ'
  exact h z θ' hz hθ'.1 hθ'.2

lemma AgreeOnQ.Dz {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    AgreeOnQ (Work.Spaces.Dz F) (Work.Spaces.Dz G) := by
  intro z θ hz hθ hlt
  simp only [Work.Spaces.Dz]
  rw [h.pz z θ hz hθ hlt]

lemma AgreeOnQ.Dth {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    AgreeOnQ (Work.Spaces.Dth F) (Work.Spaces.Dth G) := by
  intro z θ hz hθ hlt
  simp only [Work.Spaces.Dth]
  rw [h.pth z θ hz hθ hlt]

lemma AgreeOnQ.DthIter {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    ∀ i : ℕ, AgreeOnQ (Work.Spaces.DthIter i F) (Work.Spaces.DthIter i G) := by
  intro i
  induction i with
  | zero => exact h
  | succ i ih => exact ih.Dth

lemma AgreeOnQ.DzIter {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    ∀ j : ℕ, AgreeOnQ (Work.Spaces.DzIter j F) (Work.Spaces.DzIter j G) := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih => exact ih.Dz

lemma AgreeOnQ.mixed {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) (j i : ℕ) :
    AgreeOnQ (Work.Spaces.mixed j i F) (Work.Spaces.mixed j i G) :=
  (h.DthIter i).DzIter j

/-! ## Equality of the `H^k` integrands on the open quadrant -/

lemma HkIntegrand_congr {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ} (h : AgreeOnQ f g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α k f z θ = Work.Spaces.HkIntegrand α k g z θ := by
  intro z θ hz hθ hlt
  simp only [Work.Spaces.HkIntegrand]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [h.DzIter i z θ hz hθ hlt]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [h.mixed j i z θ hz hθ hlt]

/-! ## The main result -/

theorem HkSq_congr_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.HkSq α k f = Work.Spaces.HkSq α k g := by
  have hI := HkIntegrand_congr (α := α) (k := k) h
  -- For each `z > 0` the two inner integrands agree off the two endpoints `θ = 0`,
  -- `θ = π/2` of `[0,π/2]`, hence the two inner integrals agree.
  have hinner : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
    intro z hz
    apply integral_congr_ae
    show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k f z θ = Work.Spaces.HkIntegrand α k g z θ
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ) ∪ {Real.pi / 2}) ?_ ?_
    · intro θ hθ
      simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Icc, Work.Spaces.Iθ,
        Set.mem_union, Set.mem_singleton_iff] at hθ ⊢
      obtain ⟨⟨h0, h1⟩, hne⟩ := hθ
      rcases eq_or_lt_of_le h0 with h0' | h0'
      · exact Or.inl h0'.symm
      · refine Or.inr ?_
        by_contra h2
        exact hne (hI z θ hz h0' (lt_of_le_of_ne h1 h2))
    · exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
        (MeasureTheory.measure_singleton (Real.pi / 2))
  -- The outer integrands then agree for every `z ∈ [0,∞)` with `z ≠ 0`.
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  apply integral_congr_ae
  show ∀ᵐ a ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f a θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g a θ
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ)) ?_
    (MeasureTheory.measure_singleton 0)
  intro z hz
  simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Ici, Work.Spaces.Iz,
    Set.mem_singleton_iff] at hz ⊢
  obtain ⟨h0, hne⟩ := hz
  by_contra h1
  exact hne (hinner z (lt_of_le_of_ne h0 (Ne.symm h1)))

end Work.FTS.EllipticEst
