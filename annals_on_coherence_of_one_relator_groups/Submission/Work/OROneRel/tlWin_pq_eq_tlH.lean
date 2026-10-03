import Mathlib
import Submission.Work.OROneRel.band_hnnConjMap_injective
import Submission.Work.OROneRel.mem_winRho_range_iff

namespace Work.OROneRel

theorem tlWin_pq_eq_tlH (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    Work.OROneRel.tlWin p q ((p : ℤ) * (q : ℤ)) = Work.OROneRel.tlH p q Wt := by
  -- The gauge-free window subgroup `tlWin` is the closure of the set of elements spelled by
  -- closed walks of weight `0` staying in the window `[0, p*q]`; the band vertex `tlH` is the
  -- range of the class map `winRho`.  `mem_winRho_range_iff` identifies the latter with exactly
  -- that set, so the closure of the set is the range itself.
  have key : ∀ x : FreeGroup (Fin 2),
      (x ∈ {y : FreeGroup (Fin 2) | ∃ L : List (Fin 2 × Bool), FreeGroup.mk L = y ∧
          lsig (tlW p q) L = 0 ∧
          ∀ e ∈ decor (tlW p q) 0 L, coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))})
      ↔ x ∈ (winRho Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))).range := by
    intro x
    have hiff := mem_winRho_range_iff p q hp hq hcop Wt hW0 hcoh hwin htree x
    rw [Set.mem_setOf_eq]
    constructor
    · rintro ⟨L, hmk, hlsig, hwalk⟩
      exact hiff.mpr ⟨L, hwalk, hlsig, hmk⟩
    · intro hx
      obtain ⟨L, hwalk, hlsig, hmk⟩ := hiff.mp hx
      exact ⟨L, hmk, hlsig, hwalk⟩
  have hS : Subgroup.closure {y : FreeGroup (Fin 2) | ∃ L : List (Fin 2 × Bool),
      FreeGroup.mk L = y ∧ lsig (tlW p q) L = 0 ∧
      ∀ e ∈ decor (tlW p q) 0 L, coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))}
      = (winRho Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))).range := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      intro x hx
      exact (key x).mp hx
    · intro x hx
      exact Subgroup.subset_closure ((key x).mpr hx)
  unfold tlWin
  exact hS

end Work.OROneRel
