import Mathlib
import Submission.Work.WilE6.E6Frontier.Defs
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.SubPfAux.unionSet_set
import Submission.Work.WilE5.Basic

namespace Work.WilE6.E6Frontier

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- `conjCat B C`, viewed over the concatenated chain `cat c₁ c₂`, holds exactly when `B` holds
over `c₁` and `C` holds over `c₂`: the two halves of the conjunction live in disjoint ranges of
the concatenated chain. -/
lemma conjCat_holds {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂)
    (B : Basic k r₁) (C : Basic k r₂) (x : Fin k → ℝ) :
    (Work.WilE6.conjCat B C).holds (Work.WilE7.EAChain.cat c₁ c₂) x ↔
      B.holds c₁ x ∧ C.holds c₂ x := by
  simp only [Work.WilE6.conjCat]
  rw [Work.WilE5.conj_holds, Work.WilE7.SubPfAux.Basic.holds_cat_inl,
    Work.WilE7.SubPfAux.Basic.holds_cat_inr]

/-- Membership in the `interCat` set: the product DNF is a disjunction over pairs of disjuncts,
and the cube condition is required only once. -/
lemma mem_interCat {k : ℕ} (X Y : SemiPf k) (x : Fin k → ℝ) :
    x ∈ (Work.WilE6.interCat X Y).set ↔
      (x ∈ cubeC k ∧ ∃ B ∈ X.basics, B.holds X.c x) ∧
      (x ∈ cubeC k ∧ ∃ C ∈ Y.basics, C.holds Y.c x) := by
  simp only [SemiPf.set, Work.WilE6.interCat]
  constructor
  · rintro ⟨hcube, D, hD, hDh⟩
    obtain ⟨B, hB, hD'⟩ := List.mem_flatMap.mp hD
    obtain ⟨C, hC, hD''⟩ := List.mem_map.mp hD'
    rw [← hD''] at hDh
    rw [conjCat_holds X.c Y.c B C x] at hDh
    exact ⟨⟨hcube, B, hB, hDh.1⟩, hcube, C, hC, hDh.2⟩
  · rintro ⟨⟨hcube, B, hB, hBh⟩, _, C, hC, hCh⟩
    exact ⟨hcube, Work.WilE6.conjCat B C,
      List.mem_flatMap.mpr ⟨B, hB, List.mem_map.mpr ⟨C, hC, rfl⟩⟩,
      (conjCat_holds X.c Y.c B C x).mpr ⟨hBh, hCh⟩⟩

theorem interCat_set {k : ℕ} (X Y : WilkiesDesign.E.SemiPf k) :
    (Work.WilE6.interCat X Y).set = X.set ∩ Y.set := by
  ext x
  rw [Set.mem_inter_iff, mem_interCat]
  rfl

end Work.WilE6.E6Frontier
