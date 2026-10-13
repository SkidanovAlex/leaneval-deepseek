import Mathlib
import Submission.Work.WilE7.DecompDefs

namespace Work.WilE7

/-- Every cell `κ` of the family `cfs C s` projects onto `C` under `Fin.init`. -/
theorem decomp_initImage {n q : ℕ} {C : Set (Fin n → ℝ)} {s : Fin q → (Fin n → ℝ) → ℝ}
    (hmono : ∀ x ∈ C, StrictMono fun j : Fin q => s j x)
    (hbnd : ∀ x ∈ C, ∀ j, |s j x| < 1) :
    ∀ κ ∈ cfs C s, Fin.init '' κ = C := by
  intro κ hκ
  rw [mem_cfs] at hκ
  rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · -- graph cell `gr C (lvl s · i)`
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.1
    · intro hx
      refine ⟨Fin.snoc x (lvl s x i), ⟨by simpa using hx, by simp⟩, by simp⟩
  · -- band cell `bd C (lvl s · (castSucc i)) (lvl s · i.succ)`
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.1
    · intro hx
      have hlt : lvl s x (Fin.castSucc i) < lvl s x i.succ :=
        strictMono_lvl (hmono x hx) (hbnd x hx) Fin.castSucc_lt_succ
      refine ⟨Fin.snoc x ((lvl s x (Fin.castSucc i) + lvl s x i.succ) / 2),
        ⟨by simpa using hx, ?_, ?_⟩, by simp⟩
      · simp only [Fin.init_snoc, Fin.snoc_last]; linarith
      · simp only [Fin.init_snoc, Fin.snoc_last]; linarith

end Work.WilE7
