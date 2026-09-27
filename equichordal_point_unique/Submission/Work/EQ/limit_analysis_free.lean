import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.limit_analysis
import Submission.Work.EQ.la_tail_bounds_free
import Submission.Work.EQ.la_datum_finite
import Submission.Work.EQ.la_periodic_free
import Submission.Work.EQ.LAFree

/-! # `limit_analysis` from the four inputs, with the inputs supplied here

`Work.EQ.limit_analysis_of` (proved, in `Submission/Work/EQ/limit_analysis.lean`) consumes the four
inputs `TailBound`, `TailBoundSeq`, `DatumFinite` and the periodicity `hP`, and returns the
statement of `Work.EQ.limit_analysis`.  This module supplies them:

* `TailBound` (value form) from `Work.EQ.la_tail_bound_value_free`,
* `TailBoundSeq` from `Work.EQ.la_tail_bound_seq_free`,
* `DatumFinite` from `Work.EQ.la_datum_finite`,
* `hP` from `Work.EQ.la_periodic_free` (which is cycle-free: it does not import
  `Work.EQ.limit_analysis`).

The result is `Work.EQ.limit_analysis_v2`, with the statement of `Work.EQ.limit_analysis`; the node
`Work.EQ.exists_compact_regular_cycle` uses it (through `Work.EQ.MCAFree`) so that it does not
depend on the assembly of the canonical file. -/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

open scoped Topology

/-- The **value** tail bound in the shape of `Work.EQ.TailBound`. -/
theorem la_tailBound_free {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, TailBound a h δ := by
  obtain ⟨δ, hδ, htb⟩ := la_tail_bound_value_free (a := a) (h := h) (r := r) ha0 ha1 hh
  refine ⟨δ, hδ, fun r₁ r₂ hr₁ hr₁₂ hr₂δ hratio c hnd S hS => ?_⟩
  exact htb r₁ r₂ hr₁ hr₁₂ hr₂δ hratio c S hS hnd

/-- The **sequential** tail bound in the shape of `Work.EQ.TailBoundSeq`. -/
theorem la_tailBoundSeq_free {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h) :
    ∃ δ : ℝ, TailBoundSeq a h δ := by
  obtain ⟨δ, hδ, htb⟩ := la_tail_bound_seq_free (a := a) (h := h) (r := r) ha0 ha1 hh hpos
  exact ⟨δ, hδ, htb⟩

/-- The **datum finiteness** input in the shape of `Work.EQ.DatumFinite`. -/
theorem la_datumFinite_free {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h) :
    ∃ δ : ℝ, DatumFinite a h δ := by
  obtain ⟨δ, hδ, htb⟩ := la_datum_finite (a := a) (h := h) (r := r) ha0 ha1 hh hpos
  exact ⟨δ, hδ, fun r₁ r₂ hr₁ hr₁₂ hr₂δ hratio M f b hf hb hM₁ hM₂ =>
    htb r₁ r₂ hr₁ hr₁₂ hr₂δ hratio M f b hf hb hM₁ hM₂⟩

/-- **The limit analysis of Rychlik's Lemma 5.1**, assembled from the four inputs. -/
theorem limit_analysis_v2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ) (N : ℕ),
      0 < r₁ → r₁ < r₂ → r₂ < δ → r₂ / r₁ > 1 / eqLam a →
      (eqLam a : ℝ) ^ N * r₂ < δ →
        (eqLam a : ℝ) ^ N * (2 * rhoStar a h) / r₁ < δ →
      (∀ (S : ℕ → Set ChainData) (c : ℕ → ℂ) (c₀ : ℂ),
        (∀ n, IsRegComp a h (S n) (c n)) →
          (∀ n, ‖c n‖ ≤ 2 * rhoStar a h) →
          Filter.Tendsto c Filter.atTop (nhds c₀) →
        (∃ μ₁ ∈ CharSet a h, ∃ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧
            ∃ T : Set ChainData, IsRegComp a h T (c₀ * μ₁ * μ₂)) ∨
          ∃ k : ℕ, ∀ n ≥ k, c n = c₀) ∧
      (∀ c : ℂ, ‖c‖ ≤ 2 * rhoStar a h →
        (∃ μ₁ ∈ CharSet a h, ∃ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧
            ∃ T : Set ChainData, IsRegComp a h T (c * μ₁ * μ₂)) ∨
          {S : Set ChainData | IsRegComp a h S c}.Finite) := by
  classical
  by_cases hreg : ∃ S : Set ChainData, ∃ c : ℂ, IsRegComp a h S c
  · obtain ⟨S₀, c₀, hS₀⟩ := hreg
    have hpos : 0 < rhoStar a h := LAFree.rhoStar_pos_of_isRegComp ha0 ha1 hh hS₀
    exact limit_analysis_of ha0 ha1 hh
      (la_tailBound_free (a := a) (h := h) (r := r) ha0 ha1 hh)
      (la_tailBoundSeq_free (a := a) (h := h) (r := r) ha0 ha1 hh hpos)
      (la_datumFinite_free (a := a) (h := h) (r := r) ha0 ha1 hh hpos)
      (fun c hc hnd => la_periodic_free (a := a) (h := h) (r := r) ha0 ha1 hh hpos hc hnd)
  · refine ⟨1, one_pos, ?_⟩
    intro r₁ r₂ N hr₁ hr₁₂ hr₂δ hratio hN₁ hN₂
    refine ⟨?_, ?_⟩
    · intro S c c₀ hSreg hc hlim
      exact absurd ⟨S 0, c 0, hSreg 0⟩ hreg
    · intro c hc
      exact Or.inr (Set.Finite.subset Set.finite_empty (fun S hS => absurd ⟨S, c, hS⟩ hreg))

end

end Work.EQ
