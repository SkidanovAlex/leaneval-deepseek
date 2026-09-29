import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.mv_lex_coeff_summable

/-!
# Multivariable lexicographic-minimum coefficient bound: shared vocabulary

This file collects the small definitions and elementary lemmas used in the proof of
`Work.Holonomy3.mv_lex_general_case`, the general (non-polynomial) form of the
lexicographic-minimum coefficient bound.

* `degLe d N` is the finite set of multi-indices `m : Fin d →₀ ℕ` of total degree `≤ N`;
* `truncF a N` is the truncation of a coefficient family `a` to degrees `≤ N`, as a finitely
  supported family, so that the polynomial bound `hpoly` of the main theorem may be applied to it;
* `pevalF_truncF_tor` identifies its evaluation on the torus with the partial sum of the series.
-/

namespace Work.Holonomy3

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- Every coordinate of a torus point has norm one. -/
lemma norm_tor_apply {d : ℕ} (s : Fin d → ℝ) (j : Fin d) : ‖tor s j‖ = 1 := by
  have h : tor s j = Complex.exp ((((2 * Real.pi * s j : ℝ)) : ℂ) * Complex.I) := by
    rw [tor]; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The finite set of multi-indices of total degree at most `N`. -/
def degLe (d N : ℕ) : Finset (Fin d →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := Fin d) N).toFinset

@[simp] lemma mem_degLe {d N : ℕ} {m : Fin d →₀ ℕ} : m ∈ degLe d N ↔ m.degree ≤ N := by
  rw [degLe, Set.Finite.mem_toFinset]
  rfl

/-- `degLe` is monotone in the degree bound. -/
lemma degLe_mono {d N N' : ℕ} (h : N ≤ N') : degLe d N ⊆ degLe d N' := fun _ hm =>
  mem_degLe.mpr (le_trans (mem_degLe.mp hm) h)

/-- The degree truncations of the multi-index set exhaust all finite sets. -/
lemma tendsto_degLe (d : ℕ) :
    Filter.Tendsto (fun N : ℕ => degLe d N) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro s
  refine Filter.eventually_atTop.mpr ⟨s.sup (fun m => m.degree), fun N hN => ?_⟩
  intro m hm
  rw [mem_degLe]
  exact le_trans (Finset.le_sup (f := fun m : Fin d →₀ ℕ => m.degree) hm) hN

/-- Truncation of a coefficient family to total degree at most `N`. -/
def truncF {d : ℕ} (a : (Fin d →₀ ℕ) → ℂ) (N : ℕ) : (Fin d →₀ ℕ) →₀ ℂ :=
  Finsupp.ofSupportFinite (fun m : Fin d →₀ ℕ => if m.degree ≤ N then a m else 0)
    (Set.Finite.subset (Finsupp.finite_of_degree_le (σ := Fin d) N) (by
      intro m hm
      by_contra h
      rw [Function.mem_support] at hm
      exact hm (if_neg h)))

@[simp] lemma truncF_apply {d : ℕ} (a : (Fin d →₀ ℕ) → ℂ) (N : ℕ) (m : Fin d →₀ ℕ) :
    truncF a N m = if m.degree ≤ N then a m else 0 := by
  rw [truncF]
  exact congrFun Finsupp.ofSupportFinite_coe m

/-- The support of a truncation is contained in the set of multi-indices of degree at most `N`. -/
lemma support_truncF_subset {d : ℕ} (a : (Fin d →₀ ℕ) → ℂ) (N : ℕ) :
    (truncF a N).support ⊆ degLe d N := by
  intro m hm
  rw [mem_degLe]
  by_contra h
  rw [Finsupp.mem_support_iff, truncF_apply, if_neg h] at hm
  exact hm rfl

/-- A truncation is nonzero as soon as one of the retained coefficients is nonzero. -/
lemma truncF_ne_zero_of {d : ℕ} {a : (Fin d →₀ ℕ) → ℂ} {n : Fin d →₀ ℕ} {N : ℕ}
    (hn : a n ≠ 0) (hN : n.degree ≤ N) : truncF a N ≠ 0 := by
  intro h
  have h0 : truncF a N n = 0 := by rw [h]; rfl
  rw [truncF_apply, if_pos hN] at h0
  exact hn h0

/-- Evaluation of a truncation on the torus is the partial sum of the coefficient series over
all multi-indices of degree at most `N`. -/
lemma pevalF_truncF_tor {d : ℕ} (a : (Fin d →₀ ℕ) → ℂ) (N : ℕ) (t : Fin d → ℝ) :
    pevalF (truncF a N) (tor t) = ∑ m ∈ degLe d N, a m * ∏ j, tor t j ^ (m j) := by
  rw [pevalF]
  have h1 : (∑ m ∈ (truncF a N).support, truncF a N m * ∏ j, tor t j ^ (m j))
      = ∑ m ∈ degLe d N, truncF a N m * ∏ j, tor t j ^ (m j) := by
    refine Finset.sum_subset (support_truncF_subset a N) fun m _ hms => ?_
    rw [Finsupp.notMem_support_iff.mp hms, zero_mul]
  rw [h1]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [truncF_apply, if_pos (mem_degLe.mp hm)]

/-- A truncation is bounded on the torus by the sum of the norms of its coefficients. -/
lemma norm_pevalF_truncF_le {d : ℕ} (a : (Fin d →₀ ℕ) → ℂ) (N : ℕ) (t : Fin d → ℝ) :
    ‖pevalF (truncF a N) (tor t)‖ ≤ ∑ m ∈ degLe d N, ‖a m‖ := by
  rw [pevalF_truncF_tor]
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [norm_mul, norm_prod]
  simp [norm_tor_apply]

/-- The normalized torus measure is a probability measure. -/
instance mvLexInstIsProbabilityMeasureTorMeasure (d : ℕ) : IsProbabilityMeasure (torMeasure d) := by
  haveI : IsProbabilityMeasure (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩
  rw [torMeasure]
  infer_instance

end

end Work.Holonomy3
