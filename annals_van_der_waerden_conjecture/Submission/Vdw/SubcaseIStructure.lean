import Submission.Vdw.FinalAssembly
import Submission.Vdw.RadicalSq

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Structure of the Case-III-subcase-(i) slice `SubcaseI_P3`

The final assembly splits the primitive-proper irreducible bad polynomials
`SubcaseI` (the complement of the counted Case-III-subcase-(ii)/`DD = 0`
slice) into the four regions

    SubcaseI_direct   (C_f ≤ H,          D_f > H^(2+2δ))
    SubcaseI_P1resid  (H < C_f ≤ H^(1+δ), D_f > H^(2+2δ))
    SubcaseI_P2       (D_f ≤ H^(2+2δ))
    SubcaseI_P3       (C_f > H^(1+δ)).

This module records the elementary structure of the last slice: by
squarefullness of `D_f` and `C_f^2 ≤ D_f` (`RadicalSq`), every member of
`SubcaseI_P3 n H` has field discriminant exceeding `H^(2+2δ)` — the paper's
remark "`C > H^(1+δ)` implies `D > H^(2+2δ)`" opening Case III.  In
particular `SubcaseI_P2` and `SubcaseI_P3` are disjoint, and the `D`-value of
a `SubcaseI_P3` member is never in the Case-II range.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

/-- **`SubcaseI_P3` members have `D_f > H^(2+2δ)`.** -/
theorem SubcaseI_P3_subset_large_fieldDisc (n H : ℕ) (hn : 3 ≤ n) :
    SubcaseI_P3 n H ⊆
      {f : ℤ[X] | ∃ h : Irreducible (f.map φℚ),
        (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (fieldDiscExp f h : ℝ)} := by
  intro f hf
  obtain ⟨hsub, h, hC⟩ := hf
  have hprim : f ∈ PrimitiveBad n H := SubcaseI_subset_PrimitiveBad n H hsub
  obtain ⟨h', _, hsq'⟩ := PrimitiveBad_exists_squarefull_fieldDisc n H f hprim
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨h'⟩
  have hsq : Squarefull (fieldDisc f) := by simpa [fieldDiscExp] using hsq'
  have hgt := fieldDisc_gt_of_radical_gt n H (by omega) f hsq hC
  exact ⟨h, by simpa [fieldDiscExp] using hgt⟩

/-- **`SubcaseI_P2` and `SubcaseI_P3` are disjoint.** -/
theorem SubcaseI_P2_disjoint_P3 (n H : ℕ) (hn : 3 ≤ n) :
    ∀ f : ℤ[X], f ∈ SubcaseI_P2 n H → f ∈ SubcaseI_P3 n H → False := by
  intro f h2 h3
  obtain ⟨hsub2, h2w, hD2⟩ := h2
  obtain ⟨h3w, hD3⟩ := SubcaseI_P3_subset_large_fieldDisc n H hn h3
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨h2w⟩
  have e2 : fieldDiscExp f h2w = fieldDisc f := rfl
  have e3 : fieldDiscExp f h3w = fieldDisc f := rfl
  rw [e2] at hD2
  rw [e3] at hD3
  linarith


/-- **`SubcaseI_P2` members have `C_f ≤ H^(1+δ)`.**  This is the converse of the
Case-III remark: if `C_f > H^(1+δ)` then (by squarefullness) `D_f > H^(2+2δ)`,
contradicting the `SubcaseI_P2` size condition.  Consequently the `SubcaseI_P2`
slice is *exactly* the paper's Case II (restricted to `SubcaseI`):
`C_f ≤ H^(1+δ)` and `D_f ≤ H^(2+2δ)`. -/
theorem SubcaseI_P2_subset_small_radical (n H : ℕ) (hn : 3 ≤ n) :
    SubcaseI_P2 n H ⊆
      {f : ℤ[X] | ∃ h : Irreducible (f.map φℚ),
        (radical (fieldDiscExp f h) : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))} := by
  intro f hf
  obtain ⟨hsub, h, hD⟩ := hf
  have hprim : f ∈ PrimitiveBad n H := SubcaseI_subset_PrimitiveBad n H hsub
  obtain ⟨h', _, hsq'⟩ := PrimitiveBad_exists_squarefull_fieldDisc n H f hprim
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨h'⟩
  have hsq'' : Squarefull (fieldDisc f) := by simpa [fieldDiscExp] using hsq'
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_le] at hcon
  have hgt := fieldDisc_gt_of_radical_gt n H (by omega) f hsq'' (hcon h')
  have e : fieldDiscExp f h = fieldDisc f := rfl
  rw [e] at hD
  linarith [hD, hgt]

/-- **`SubcaseI_P2` is the paper's Case II slice**: an element of `SubcaseI`
lies in `SubcaseI_P2` if and only if both `C_f ≤ H^(1+δ)` and
`D_f ≤ H^(2+2δ)` hold (for a suitable irreducibility witness). -/
theorem SubcaseI_P2_iff_small_radical_and_small_disc (n H : ℕ) (hn : 3 ≤ n)
    (f : ℤ[X]) :
    f ∈ SubcaseI_P2 n H ↔
      f ∈ SubcaseI n H ∧ ∃ h : Irreducible (f.map φℚ),
        (radical (fieldDiscExp f h) : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) ∧
        (fieldDiscExp f h : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
  constructor
  · intro hf
    have hsmall := SubcaseI_P2_subset_small_radical n H hn hf
    obtain ⟨hsub, h, hD⟩ := hf
    exact ⟨hsub, h, hsmall.2, hD⟩
  · rintro ⟨hsub, h, _, hD⟩
    exact ⟨hsub, h, hD⟩

end Submission.Vdw
