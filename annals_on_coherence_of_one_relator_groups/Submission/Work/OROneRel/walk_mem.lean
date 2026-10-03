import Mathlib
import Submission.Work.OROneRel.walkDefs
import Submission.Work.OROneRel.letters_closure_iff

namespace Work.OROneRel

theorem walk_mem {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (b : ℤ)
    (hm : 0 ≤ b + 1 - (p : ℤ) * (q : ℤ)) :
    Work.OROneRel.walkA p q (b + 1 - (p : ℤ) * (q : ℤ)) ∈
        Subgroup.closure (FreeGroup.of '' Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 b) ∧
      Work.OROneRel.walkB p q (b + 1 - (p : ℤ) * (q : ℤ)) ∈
        Subgroup.closure (FreeGroup.of '' Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 b) := by
  have hq1 : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hq0 : (0 : ℤ) ≤ (q : ℤ) := by linarith
  refine ⟨?_, ?_⟩
  · -- The `a`-block minus its last symbol: every letter is read at a level in `[0, b]`.
    unfold walkA
    apply mk_mem_closure
    intro a c hmem
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmem
    have ha : a = ((0 : Fin 2), (b + 1 - (p : ℤ) * (q : ℤ)) + (j : ℤ) * (q : ℤ)) := by
      have h1 := congrArg Prod.fst hj
      simpa using h1.symm
    rw [ha, mem_winE]
    simp only []
    have hjle : (j : ℤ) ≤ (p : ℤ) - 2 := by
      have := j.isLt
      omega
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
    have hjq : (0 : ℤ) ≤ (j : ℤ) * (q : ℤ) := mul_nonneg hj0 hq0
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith [hm, hjq]
    · have hj2 : (2 : ℤ) ≤ (p : ℤ) - (j : ℤ) := by linarith
      have h4 : (0 : ℤ) ≤ (p : ℤ) - (j : ℤ) := by linarith
      have hprod : (2 : ℤ) * (1 : ℤ) ≤ ((p : ℤ) - (j : ℤ)) * (q : ℤ) :=
        mul_le_mul hj2 hq1 (by norm_num) h4
      have hexp : ((p : ℤ) - (j : ℤ)) * (q : ℤ) = (p : ℤ) * (q : ℤ) - (j : ℤ) * (q : ℤ) := by
        ring
      have h1 : (1 : ℤ) ≤ (p : ℤ) * (q : ℤ) - (j : ℤ) * (q : ℤ) := by
        rw [← hexp]; linarith
      linarith [h1]
    · rw [tlW_zero]
      linarith [hm, hjq, hq0]
    · rw [tlW_zero]
      have hj1 : (1 : ℤ) ≤ (p : ℤ) - (j : ℤ) - 1 := by linarith
      have h4b : (0 : ℤ) ≤ (p : ℤ) - (j : ℤ) - 1 := by linarith
      have hprod2 : (1 : ℤ) * (1 : ℤ) ≤ ((p : ℤ) - (j : ℤ) - 1) * (q : ℤ) :=
        mul_le_mul hj1 hq1 (by norm_num) h4b
      have hexp2 : ((p : ℤ) - (j : ℤ) - 1) * (q : ℤ)
          = (p : ℤ) * (q : ℤ) - (j : ℤ) * (q : ℤ) - (q : ℤ) := by ring
      have h1' : (1 : ℤ) ≤ (p : ℤ) * (q : ℤ) - (j : ℤ) * (q : ℤ) - (q : ℤ) := by
        rw [← hexp2]; linarith
      linarith [h1']
  · -- The `b`-block minus its first symbol: every letter is read at a level in `[0, b]`.
    unfold walkB
    apply mk_mem_closure
    intro a c hmem
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hmem
    have ha : a = ((1 : Fin 2),
        (b + 1 - (p : ℤ) * (q : ℤ)) + (p : ℤ) * (q : ℤ) - ((k : ℤ) + 1) * (p : ℤ)) := by
      have h1 := congrArg Prod.fst hk
      simpa using h1.symm
    rw [ha, mem_winE]
    simp only []
    rw [tlW_one]
    ring_nf
    have hk2 : (k : ℤ) + 2 ≤ (q : ℤ) := by
      have := k.isLt
      omega
    have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := by linarith
    have hbq : (q : ℤ) * (p : ℤ) ≤ b + 1 := by nlinarith [hm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hmk : ((k : ℤ) + 1) * (p : ℤ) ≤ (q : ℤ) * (p : ℤ) :=
        mul_le_mul_of_nonneg_right (by linarith) hp0
      linarith
    · have hk1 : (1 : ℤ) ≤ (k : ℤ) + 1 := by linarith
      have hprod : (1 : ℤ) * (1 : ℤ) ≤ ((k : ℤ) + 1) * (p : ℤ) :=
        mul_le_mul hk1 hp1 (by norm_num) (by linarith)
      linarith
    · have hmk : ((k : ℤ) + 2) * (p : ℤ) ≤ (q : ℤ) * (p : ℤ) :=
        mul_le_mul_of_nonneg_right (by linarith) hp0
      linarith
    · have hk1 : (1 : ℤ) ≤ (k : ℤ) + 2 := by linarith
      have hprod : (1 : ℤ) * (1 : ℤ) ≤ ((k : ℤ) + 2) * (p : ℤ) :=
        mul_le_mul hk1 hp1 (by norm_num) (by linarith)
      linarith

end Work.OROneRel
