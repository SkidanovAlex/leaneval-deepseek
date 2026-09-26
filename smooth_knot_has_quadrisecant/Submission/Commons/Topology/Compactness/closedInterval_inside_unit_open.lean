import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

namespace Commons.Topology.Compactness

/-- The closed sub-interval `{r | ε ≤ r ≤ 1−ε}` inside the open unit
interval `(0,1)` (as a subset of the SUBTYPE `{t : ℝ // t ∈ Ioo 0 1}`)
is compact, for `0 < ε < 1/2`.  (The subtype carries the subspace
topology of ℝ; the set equals the preimage of the compact real interval
`Icc ε (1−ε)` under the subtype embedding, and the embedding restricted
to it is a homeomorphism onto `Icc ε (1−ε)` — or use
`isCompact_Icc` + `isCompact_iff_compactSpace` + the transfer.) -/
theorem closedInterval_inside_unit_open {ε : ℝ} (hε0 : 0 < ε) (hε12 : ε < 1 / 2) :
    IsCompact ({r : {t : ℝ // t ∈ Set.Ioo 0 1} | ε ≤ (r : ℝ) ∧ (r : ℝ) ≤ 1 - ε} :
      Set {t : ℝ // t ∈ Set.Ioo 0 1}) := by
  -- x ∈ Icc ε (1-ε) implies x ∈ Ioo 0 1, given 0 < ε < 1/2
  have memIoo_of_memIcc : ∀ {t : ℝ}, t ∈ Set.Icc ε (1 - ε) → t ∈ Set.Ioo 0 1 := by
    intro t ht
    have hlt : ε ≤ t ∧ t ≤ 1 - ε := Set.mem_Icc.mp ht
    exact ⟨lt_of_lt_of_le hε0 hlt.1, lt_of_le_of_lt hlt.2 (by linarith)⟩
  -- continuous map from the (compact) closed interval to the open interval subtype
  let D := {t : ℝ // t ∈ Set.Icc ε (1 - ε)}
  let f : D → {t : ℝ // t ∈ Set.Ioo 0 1} := fun x => ⟨x.1, memIoo_of_memIcc x.2⟩
  have hf_cont : Continuous f := by
    dsimp [f]
    exact Continuous.subtype_mk continuous_subtype_val (fun x => memIoo_of_memIcc x.2)
  haveI : CompactSpace D := by
    dsimp [D]
    exact isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc ε (1 - ε) : Set ℝ))
  have hD_compact : IsCompact (Set.univ : Set D) := isCompact_univ
  have hf_range_compact : IsCompact (Set.range f) := by
    simpa [Set.image_univ] using (IsCompact.image hD_compact hf_cont)
  -- the set in the statement is exactly the range of f
  have hS_eq_range : ({r : {t : ℝ // t ∈ Set.Ioo 0 1} | ε ≤ (r : ℝ) ∧ (r : ℝ) ≤ 1 - ε} :
      Set {t : ℝ // t ∈ Set.Ioo 0 1}) = Set.range f := by
    ext y
    constructor
    · intro hy
      refine ⟨⟨(y : ℝ), ?_⟩, ?_⟩
      · exact Set.mem_Icc.mpr hy
      · apply Subtype.ext
        simp [f]
    · rintro ⟨x, hx⟩
      have hx1 : (x : ℝ) ∈ Set.Icc ε (1 - ε) := x.2
      have hxv : (x : ℝ) = (y : ℝ) := by
        -- from f x = y, compare first components
        exact congrArg Subtype.val hx
      change ε ≤ (y : ℝ) ∧ (y : ℝ) ≤ 1 - ε
      rw [← hxv]
      exact Set.mem_Icc.mp hx1
  simpa [hS_eq_range] using hf_range_compact

end Commons.Topology.Compactness