import Mathlib
import Submission.Work.Peluse.UControl.petChapter5_of_levelChainV3
import Submission.Work.Peluse.UControl.petLevelChainGen

namespace Work.Peluse.UControl

/-!
# `petChapter5Holds` — the PET chapter of Peluse's Proposition 3.4

`PetChapter5 P` is Peluse's Lemma 4.9 for the configuration `(x, x+y, …, x+P(y))`.  It is now
**complete** (this file is sorry-free and rests only on `propext`/`Classical.choice`/`Quot.sound`):
it is assembled from the *level chain* of the PET induction (Peluse's Lemma 4.8 iterated `d - 2`
times, followed by the comparison with the level-`(d-1)` linear family) and the following pieces:

* `petChapter5_of_levelChainV3 P : PetLevelChain P → PetChapter5 P` is **proved** (sorry-free), the
  full assembly — phase-1 chain (`petHistInit_inv`, `histPhase1RunInv`, `histPhase1Inv`,
  `phase1Chain_done`), the closing step (`histCloseLinkWin`), the level chain, the box-average
  comparison (`linFamAvg_radius_le`), the window bookkeeping (`petWindow_hwin`,
  `PetWindowBookkeeping`), the corner (`petCornerZero`) and the sharp shift bound
  (`terminalShiftBoundL`);
* `PetLevelChain P` for `P.natDegree = 2` is **proved** (`petLevelChain_quadratic`): the
  `Phase1Terminal` state is already linear, `Nstep = 1`, `D = levelOneDatum n`, `C₀ = 3^n`;
* `PetLevelChain P` for `P.natDegree ≤ 1` is **vacuously true** (below): `Phase1Terminal` forces the
  live slots to have degree `d - 1 ≥ 1` (`HistData.hnc`), hence `d ≥ 2`;
* `PetLevelChain P` for `2 ≤ P.natDegree` is **proved** (`petLevelChainGen`, `petLevelChainGen.lean`,
  assembled from `petLevelAux.lean` and `petLevelFinal.lean`): the level-`1` state is iterated to
  level `d - 2`, the last round is applied with its closing step exposed, and the terminal analysis
  transports the analytic data along the `Reach`-chain to the pre-closing state, where the closing
  step is applied explicitly.
-/

/-- **The level chain** (Peluse's Lemma 4.8 iterated `d - 2` times): from a `Phase1Terminal` state
one reaches the level-`(d-1)` linear state whose direction family is the datum's, losing only the
factor `petChainLevel B Nstep`. -/
theorem petLevelChain (P : Polynomial ℤ) : PetLevelChain P := by
  by_cases hd : 2 ≤ P.natDegree
  · exact petLevelChainGen P hd
  · -- `P.natDegree ≤ 1`: there is no `Phase1Terminal` state at all
    intro n hn lc Y hT
    exfalso
    have hne : ∃ h : Fin n → Bool, h ≠ 0 := by
      refine ⟨fun i => decide (i = (⟨0, by omega⟩ : Fin n)), ?_⟩
      intro hcon
      have h1 := congrFun hcon (⟨0, by omega⟩ : Fin n)
      simp at h1
    obtain ⟨h0, hh0⟩ := hne
    have hmem : ((Sum.inr 0 : InitIdx P.natDegree), h0) ∈ Y.H := hT.2 h0 hh0
    obtain ⟨-, -, hdeg, -⟩ := hT.1 _ hmem
    have hnc := Y.hnc _ hmem
    omega

theorem petChapter5Holds (P : Polynomial ℤ) : Work.Peluse.UControl.PetChapter5 P :=
  petChapter5_of_levelChainV3 P (petLevelChain P)

end Work.Peluse.UControl
