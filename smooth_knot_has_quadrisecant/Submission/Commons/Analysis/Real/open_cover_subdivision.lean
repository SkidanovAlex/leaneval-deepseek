import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact

namespace Commons.Analysis.Real

/-
# Record of the received request (quoted verbatim)

This commons file was requested with the declaration quoted below, but the
request text wrapped it in the module skeleton and glued the proof placeholder
after the closing `end Commons.Analysis.Real` (and carried a stale
`import Mathlib.Topology.Instances.Real`, a module that does not exist in the
pinned Mathlib).  The received text is kept here exactly as sent, truncated
just before the placeholder, for the record; the declaration is then stated
afresh with the identical header and proved.
theorem open_cover_subdivision {a b : ℝ} (hab : a ≤ b) {ι : Type*}
    (U : ι → Set ℝ) (hUo : ∀ i : ι, IsOpen (U i))
    (hcover : Set.Icc a b ⊆ ⋃ i : ι, U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      y - x ≤ δ → ∃ i : ι, Set.Icc x y ⊆ U i

end Commons.Analysis.Real := by
-/

/-- A compact real interval covered by open sets admits a **uniform
subdivision**: there is a positive `δ` such that every subinterval of
`[a,b]` of length at most `δ` lies entirely inside one of the covering
sets.  (Lebesgue-number-style statement for finite-indexed families;
`ι` may be empty only if `[a,b]` is, which `hab : a ≤ b` rules out.) -/
theorem open_cover_subdivision {a b : ℝ} (hab : a ≤ b) {ι : Type*}
    (U : ι → Set ℝ) (hUo : ∀ i : ι, IsOpen (U i))
    (hcover : Set.Icc a b ⊆ ⋃ i : ι, U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      y - x ≤ δ → ∃ i : ι, Set.Icc x y ⊆ U i := by
  obtain ⟨ε, hε0, hε⟩ := lebesgue_number_lemma_of_metric (s := Set.Icc a b) (c := U)
    (hs := isCompact_Icc) hUo hcover
  refine ⟨ε / 2, half_pos hε0, ?_⟩
  intro x y hx hy hxy hlen
  obtain ⟨i, hi⟩ := hε x hx
  refine ⟨i, ?_⟩
  intro z hz
  apply hi
  rw [Metric.mem_ball]
  have hzx : x ≤ z := (Set.mem_Icc.mp hz).1
  have hzy : z ≤ y := (Set.mem_Icc.mp hz).2
  have hdist : |z - x| = z - x := abs_of_nonneg (sub_nonneg.mpr hzx)
  have h1 : z - x ≤ y - x := sub_le_sub_right hzy x
  have h2 : y - x ≤ ε / 2 := hlen
  have h3 : ε / 2 < ε := div_two_lt_of_pos hε0
  rw [Real.dist_eq]
  rw [hdist]
  exact lt_of_le_of_lt (le_trans h1 h2) h3

end Commons.Analysis.Real