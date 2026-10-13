import Mathlib
import Submission.Work.WilE7.DecompDefs

namespace Work.WilE7

open WilkiesDesign

/-- Every cell of `cfs C s` is a cell of `ℝ^{n+1}` and is nonempty. -/
theorem decomp_isCell {n q : ℕ} {C : Set (Fin n → ℝ)} {s : Fin q → (Fin n → ℝ) → ℝ}
    (hC : WilkiesDesign.IsCell n C) (hCne : C.Nonempty) (hs : ∀ j, ContinuousOn (s j) C)
    (hmono : ∀ x ∈ C, StrictMono fun j : Fin q => s j x)
    (hbnd : ∀ x ∈ C, ∀ j, |s j x| < 1) :
    ∀ κ ∈ cfs C s, WilkiesDesign.IsCell (n+1) κ ∧ κ.Nonempty := by
  intro κ hκ
  rw [mem_cfs] at hκ
  rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · -- graph of the level `lvl s · i`
    refine ⟨isCell_gr hC (continuous_lvl hs i), ?_⟩
    obtain ⟨x, hx⟩ := hCne
    exact ⟨Fin.snoc x (lvl s x i), by
      refine ⟨?_, ?_⟩
      · rwa [Fin.init_snoc]
      · rw [Fin.init_snoc, Fin.snoc_last]⟩
  · -- band between the consecutive levels `lvl s · (castSucc i)` and `lvl s · i.succ`
    have hmono_i : ∀ x ∈ C,
        lvl s x (Fin.castSucc i) < lvl s x i.succ := fun x hx =>
      (strictMono_lvl (hmono x hx) (hbnd x hx)) Fin.castSucc_lt_succ
    refine ⟨isCell_bd hC (continuous_lvl hs (Fin.castSucc i)) (continuous_lvl hs i.succ)
      hmono_i, ?_⟩
    obtain ⟨x, hx⟩ := hCne
    have hlt := hmono_i x hx
    refine ⟨Fin.snoc x ((lvl s x (Fin.castSucc i) + lvl s x i.succ) / 2), ?_, ?_, ?_⟩
    · rwa [Fin.init_snoc]
    · simp only [Fin.init_snoc, Fin.snoc_last]; linarith
    · simp only [Fin.init_snoc, Fin.snoc_last]; linarith

end Work.WilE7
