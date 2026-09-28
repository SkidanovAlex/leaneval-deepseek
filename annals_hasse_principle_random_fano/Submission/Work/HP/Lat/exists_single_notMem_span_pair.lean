import Mathlib

namespace Work.HP.Lat

/-- In `ℚ^ι` with at least three coordinates, the two vectors `a, b` cannot span all
standard basis vectors `e_j = Pi.single j 1`: the span of two vectors has dimension at
most two, whereas `ℚ^ι` has dimension `card ι ≥ 3`. -/
lemma exists_single_notMem_span_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℚ)
    (hcard : 3 ≤ Fintype.card ι) :
    ∃ j : ι, (Pi.single j (1 : ℚ) : ι → ℚ) ∉ Submodule.span ℚ {a, b} := by
  by_contra h
  simp only [not_exists, not_not] at h
  -- If every `e_j` lies in `span {a,b}`, then the span is everything.
  have htop : Submodule.span ℚ ({a, b} : Set (ι → ℚ)) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    have hf : f = ∑ j : ι, f j • (Pi.single j (1 : ℚ) : ι → ℚ) := by
      ext i
      rw [Finset.sum_apply]
      simp [Pi.single_apply]
    rw [hf]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (h j))
  -- The span of two vectors has dimension at most two.
  have hle : Module.finrank ℚ (Submodule.span ℚ ({a, b} : Set (ι → ℚ))) ≤ 2 := by
    have h1 := finrank_span_le_card (R := ℚ) ({a, b} : Set (ι → ℚ))
    have h2 : ({a, b} : Set (ι → ℚ)).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact Finset.card_le_two
    linarith
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at hle
  omega

end Work.HP.Lat
