import Mathlib
import Submission.Work.Peluse.SwapA.p3Heart_all
import Submission.Work.Peluse.SwapA.lemma51P_succ_of_heart
import Submission.Work.Peluse.Pel51.lemma51P_one_of_two

/-!
# Every level of Peluse's Lemma 5.1, from the heart

`Work.Peluse.LadderP.lemma51P t` (Peluse, arXiv:1909.00309, Lemma 5.1) holds at every level `t ≥ 1`:

* `t = 1` is `Work.Peluse.Pel51.lemma51P_one_of_two` applied to level `2`;
* every other level is the adapter `Work.Peluse.SwapA.lemma51P_succ_of_heart` applied to the heart
  `Work.Peluse.SwapA.p3Heart_all_of` at the previous level.

This removes Peluse's Lemma 5.4/5.5 (the P1/P2/P3 nodes on the old critical path) from the closure.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

open scoped BigOperators

namespace Work.Peluse.SwapA

noncomputable section

open Work.Peluse

/-- **The heart at every level, at the window `symIcc N`** (the `S`-free form `p3HeartB`), from the
two dense-concatenation nodes. -/
theorem p3HeartB_all_of (hAll : ConcatAllP) (hEnd : DenseEndgameP) :
    ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.p3HeartB t := by
  intro t ht B₀
  obtain ⟨s', hs'1, e, he1, C, hC0, hC1, hH⟩ := p3Heart_all_of hAll hEnd t ht B₀
  refine ⟨s', hs'1, e, he1, C, hC0, hC1, ?_⟩
  intro M₁ M₂ D N b γ η ε f hM₂ hM₂M₁ hD1 hN hsup hMN hb hbd hγ0 hγ1 hη0 hηC hε0 hεC hDs hDn
    hbad hbox
  refine hH M₁ M₂ D N (Work.Peluse.symIcc N) b γ η ε f hM₂ hM₂M₁ hD1 hN hsup ?_ hMN hb hbd hγ0
    hγ1 hη0 hηC hε0 hεC hDs hDn hbad hbox
  have hcard : (((Work.Peluse.symIcc N).card : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [Work.Peluse.LadderP.card_symIcc]
    push_cast
    ring
  have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
  rw [hcast, hcard]
  linarith

/-- **Peluse's Lemma 5.1 at every level**, from the two dense-concatenation nodes. -/
theorem lemma51P_all_of (hAll : ConcatAllP) (hEnd : DenseEndgameP) :
    ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.lemma51P t := by
  intro t ht
  by_cases h1 : t = 1
  · subst h1
    exact Work.Peluse.Pel51.lemma51P_one_of_two
      (lemma51P_succ_of_heart 1 le_rfl (p3Heart_all_of hAll hEnd 1 le_rfl))
  · have h2 : 1 ≤ t - 1 := by omega
    have h3 : t - 1 + 1 = t := by omega
    rw [← h3]
    exact lemma51P_succ_of_heart (t - 1) h2 (p3Heart_all_of hAll hEnd (t - 1) h2)

/-- **Peluse's Lemma 5.1 at every level**, from all three frozen nodes of the route. -/
theorem lemma51P_all_of_step (hStep : ConcatStepP) (hAll : ConcatAllP) (hEnd : DenseEndgameP) :
    ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.lemma51P t :=
  lemma51P_all_of hAll hEnd

end

end Work.Peluse.SwapA
