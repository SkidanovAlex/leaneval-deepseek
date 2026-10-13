import Mathlib
import Submission.Work.WilE9.Ift.OneShotDefs

namespace Work.WilE9.Ift.OneShot

open WilkiesDesign WilkiesDesign.E

/-- A basic condition is empty — hence holds everywhere — as soon as its degree vanishes.
Indeed `Basic.deg` is a sum of `atomDeg`s, each of which is `totalDegree + 1 ≥ 1`, so a
vanishing degree forces both lists of polynomials to be empty. -/
theorem basic_holds_of_deg_eq_zero {k r : ℕ} {c : EAChain k r} {B : Basic k r}
    (h : B.deg = 0) (x : Fin k → ℝ) : B.holds c x := by
  have hsum : ((B.eqs ++ B.pos).map atomDeg).sum = 0 := h
  have hnil : B.eqs ++ B.pos = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro Q hQ
    have hmem : atomDeg Q ∈ (B.eqs ++ B.pos).map atomDeg := List.mem_map.mpr ⟨Q, hQ, rfl⟩
    have hz : atomDeg Q = 0 := (List.sum_eq_zero_iff.mp hsum) _ hmem
    simp [atomDeg] at hz
  obtain ⟨heqs, hpos⟩ := List.append_eq_nil_iff.mp hnil
  have hB : B = ⟨[], []⟩ := by cases B; simp_all
  rw [hB]
  exact ⟨fun f hf => by simp at hf, fun g hg => by simp at hg⟩

/-- If some disjunct of `Y` is the empty condition then `Y.set` is the whole closed cube. -/
theorem semiPf_set_eq_cubeC_of_mem_deg_zero {k : ℕ} {Y : SemiPf k}
    (h : ∃ B ∈ Y.basics, B.deg = 0) : Y.set = cubeC k := by
  obtain ⟨B, hBmem, hBdeg⟩ := h
  apply Set.Subset.antisymm
  · intro x hx; exact hx.1
  · intro x hx
    exact ⟨hx, B, hBmem, basic_holds_of_deg_eq_zero hBdeg x⟩

/-- **Cleaning a semi-Pfaffian set.**  Every semi-Pfaffian set `Y` can be replaced by a
semi-Pfaffian set `Y1` with the same point set, no larger format and no larger degree, and whose
DNF list has length at most `Y.deg + 1`: if some disjunct of `Y` is the empty condition (degree
`0`), then `Y.set` is the whole cube and one unconstrained disjunct suffices; otherwise every
disjunct has degree `≥ 1`, so their number is at most their total degree. -/
theorem exists_clean (k : ℕ) (Y : WilkiesDesign.E.SemiPf k) :
    ∃ Y1 : WilkiesDesign.E.SemiPf k, Y1.set = Y.set ∧ Y1.r ≤ Y.r ∧ Y1.deg ≤ Y.deg ∧
      Y1.basics.length ≤ Y.deg + 1 := by
  by_cases h : ∃ B ∈ Y.basics, B.deg = 0
  · -- the empty condition occurs: `Y.set` is the whole cube, one disjunct suffices.
    obtain ⟨B, hBmem, hBdeg⟩ := h
    refine ⟨⟨Y.r, Y.c, [⟨[], []⟩]⟩, ?_, le_refl _, ?_, ?_⟩
    · rw [semiPf_set_eq_cubeC_of_mem_deg_zero ⟨B, hBmem, hBdeg⟩]
      apply Set.Subset.antisymm
      · intro x hx; exact hx.1
      · intro x hx
        exact ⟨hx, ⟨[], []⟩, by simp,
          basic_holds_of_deg_eq_zero (B := (⟨[], []⟩ : Basic k Y.r)) (by simp [Basic.deg]) x⟩
    · simp [SemiPf.deg, Basic.deg]
    · simp
  · -- every disjunct has degree `≥ 1`: keep `Y` unchanged.
    refine ⟨Y, rfl, le_refl _, le_refl _, ?_⟩
    have hge : ∀ B ∈ Y.basics, 1 ≤ B.deg := fun B hB =>
      Nat.one_le_iff_ne_zero.mpr (fun hz => h ⟨B, hB, hz⟩)
    have hlen : Y.basics.length ≤ Y.deg := by
      have h1 := List.length_le_sum_of_one_le (Y.basics.map Basic.deg)
        (by
          intro i hi
          obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hi
          exact hge B hB)
      simpa [SemiPf.deg, List.length_map] using h1
    exact le_trans hlen (Nat.le_succ _)

end Work.WilE9.Ift.OneShot
