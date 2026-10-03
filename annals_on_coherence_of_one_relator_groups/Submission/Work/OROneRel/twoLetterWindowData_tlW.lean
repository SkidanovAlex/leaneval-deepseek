import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetterWindowData
import Submission.Work.OROneRel.twoLetterFreiheitssatz
import Submission.Work.OROneRel.bandGaugeExtend

namespace Work.OROneRel

theorem twoLetterWindowData_tlW (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hcop : Nat.Coprime p q) :
    ∃ Wt : ℤ → FreeGroup (Fin 2),
      Wt 0 = 1 ∧
      (∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i) ∧
      (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
          (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) ∧
      (∀ k : ℤ, k ≠ 0 →
        ¬ (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
              (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
            0 ≤ e.1.2 + k ∧ 0 ≤ e.1.2 + Work.OROneRel.tlW p q e.1.1 + k ∧
              e.1.2 + k ≤ (p : ℤ) * (q : ℤ) ∧
              e.1.2 + Work.OROneRel.tlW p q e.1.1 + k ≤ (p : ℤ) * (q : ℤ))) ∧
      (∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
        ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
          Work.OROneRel.coverEdge e ∈
            Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) ∧
      (∃ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
          (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) ∧
      (∀ x : FreeGroup (Work.OROneRel.winBeta Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))),
        Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)) x ∈
            Subgroup.normalClosure ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
          x ∈ Subgroup.normalClosure
            ({Work.OROneRel.winRoot Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))
                (Work.OROneRel.tlU p q) ^ l} :
              Set (FreeGroup (Work.OROneRel.winBeta Wt (Work.OROneRel.tlW p q) 0
                ((p : ℤ) * (q : ℤ)))))) := by
  classical
  -- A deck element `τ` of weight `1` (`Work.OROneRel.exists_coh_tau_tlW`).
  obtain ⟨τ, hτ⟩ := exists_coh_tau_tlW p q hp hq hcop
  -- The tree-path gauge of the band `[0, pq]` (`Work.OROneRel.treeGauge_band_facts`).
  obtain ⟨hG0, hGcoh, hGtree⟩ := treeGauge_band_facts p q hp hq hcop
  -- Extend it off the band by the powers of `τ` (`Work.OROneRel.bandGaugeExtend`); the loop classes
  -- of the window edges do not see the extension.
  obtain ⟨Wt, hW0, hWcoh, hWtree, hclass⟩ :=
    bandGaugeExtend p q hp hq hτ hG0 hGcoh hGtree
  -- Some traversed edge of the walk is a tree edge of the band gauge
  -- (`Work.OROneRel.bandTreeEdge_local`); being a tree edge is a condition on the loop class of the
  -- edge, which the extension preserves.
  obtain ⟨e₀, he₀, hte₀⟩ := bandTreeEdge_local p q hp hq
  refine ⟨Wt, hW0, hWcoh, tlU_walk_mem_winE p q, tlU_walk_tight p q hp, hWtree, ?_, ?_⟩
  · refine ⟨e₀, he₀, ?_⟩
    rw [mem_winTree] at hte₀ ⊢
    exact ⟨hte₀.1, by rw [hclass (coverEdge e₀) hte₀.1]; exact hte₀.2⟩
  · -- The Freiheitssatz of the band domain, in the form proved in `twoLetterFreiheitssatz`.
    exact twoLetterFreiheitssatz p q l hp hq hl hcop hW0 hWcoh (cohom_tlW_tlU p q) hτ
      (tlU_walk_mem_winE p q) (tlU_walk_tight p q hp) hWtree

end Work.OROneRel
