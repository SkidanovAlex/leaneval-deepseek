import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.NibbleRoundDefs
import Submission.Work.Deep.Kahn.RoundDefs
import Submission.Work.Deep.Kahn.nibbleWSetup
import Submission.Work.Deep.Kahn.roundListLost
import Submission.Work.Deep.Kahn.roundUncolAct
import Submission.Work.Deep.Kahn.roundKeptUnact
import Submission.Work.Deep.Kahn.nibbleWExistsGood
import Submission.Work.Deep.Kahn.nibbleWAssembly

/-!
# The regularised one-round nibble step

This file proves `Work.Deep.Kahn.RegularisedNibbleStatement` from four ingredients, following
the wasteful (Reed--Sudakov) procedure as analysed in Kang--Kelly--Kühn--Methuku--Osthus,
*A special case of Vũ's conjecture* (arXiv:2109.11438), Lemma `lemma:nibble`:

* `Work.Deep.Kahn.roundListLost` — for every edge `e`, the number of colours that `e` **loses**
  in the round (the colours of activated edges meeting `e`) exceeds
  `Λ(1-retention) + ηΛ` only with probability `≤ exp(-D^{1/4})`; equivalently the residual list
  `residual ω e` has at least `newLambda - ηΛ` colours;
* `Work.Deep.Kahn.roundUncolAct` and `Work.Deep.Kahn.roundKeptUnact` — the two halves of the
  colour-degree estimate: the "activated but blocked" count `uncolActCount` (paper:
  `uncolActivatedNbrsRV`) and the "unactivated survivor" count `keptUnactCount` (paper:
  `keptUnactColsRV`) each exceed their mean by `ηD/4` only with probability
  `≤ exp(-D^{1/4})/2`; together with `Round.newColDeg_le` and `Round.prob_badDegSet_le` this
  gives the colour-degree tail bound for `Round.newColDeg`;
* `Work.Deep.Kahn.nibbleWExistsGood` — the Lovász local lemma step producing a *single* round
  outcome `ω` for which both estimates hold simultaneously;
* `Work.Deep.Kahn.nibbleWAssembly` — the deterministic bookkeeping which turns such an outcome
  into the `(𝓗₀, φ, L')` of the statement, with `𝓗₀ := Round.keptSub ω`,
  `φ := Round.keptColoring ω` and `L' e := Round.residual ω e`.

The construction differs from the one used in the first-generation files
(`roundUsedColours`/`nibbleAssembly`/`nibbleExistsGood`), which removed only the colours *used*
by kept edges: that list is too long, and the resulting colour-degree estimate exceeds
`newDeg + ηD` when `C² ≳ K` (the affine-space instance with equal lists is a counterexample at
the level of the one-round estimates).  The wasteful update removes the colour as soon as an
activated edge names it, which is exactly what `newDeg` is calibrated for.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

theorem nibbleRegularised : Work.Deep.Kahn.RegularisedNibbleStatement := by
  intro C hC ε η hε hη
  obtain ⟨D₁, hD₁, hD₁le, hList⟩ := roundListLost (C := C) hC ε η hε hη
  obtain ⟨D₂, hD₂, hD₂le, hUncol⟩ := roundUncolAct (C := C) hC ε η hε hη
  obtain ⟨D₃, hD₃, hD₃le, hKept⟩ := roundKeptUnact (C := C) hC ε η hε hη
  obtain ⟨D₄, hD₄, hD₄le, hGood⟩ := nibbleWExistsGood (C := C) hC ε η hε hη
  refine ⟨max (max D₁ D₂) (max D₃ D₄), ?_, ?_, ?_⟩
  · positivity
  · exact max_le (max_le hD₁le hD₂le) (max_le hD₃le hD₄le)
  · intro n c 𝓗 L D Λ K hD hΛ hK hηK h16 hlin hsize hlist hdeg hDΛ hΛD hDmin hlogD hKD hCKD
    haveI : Fintype 𝓗 := Fintype.ofFinite 𝓗
    haveI : NeZero K := ⟨by omega⟩
    have hD₁' : D₁ ≤ (D : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hDmin
    have hD₂' : D₂ ≤ (D : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hDmin
    have hD₃' : D₃ ≤ (D : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hDmin
    have hD₄' : D₄ ≤ (D : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hDmin
    have hP₁ : ∀ e : 𝓗,
        Work.Deep.Conc.prob (Work.Deep.Kahn.Round.badListSet (K := K) (L := L) C D Λ η e)
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) :=
      fun e => hList n c 𝓗 L D Λ K hD hΛ hK hηK h16 hlin hsize hlist hdeg hDΛ hΛD hD₁'
        hlogD hKD hCKD e
    have hP₂ : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Work.Deep.Conc.prob (Work.Deep.Kahn.Round.badDegSet (K := K) (L := L) C D Λ η x γ)
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) := by
      intro x γ hxγ
      refine le_trans (Work.Deep.Kahn.Round.prob_badDegSet_le (K := K) (L := L) C D Λ η
        (le_of_lt hη) x γ) ?_
      have h1 := hUncol n c 𝓗 L D Λ K hD hΛ hK hηK h16 hlin hsize hlist hdeg hDΛ hΛD hD₂'
        hlogD hKD hCKD x γ hxγ
      have h2 := hKept n c 𝓗 L D Λ K hD hΛ hK hηK h16 hlin hsize hlist hdeg hDΛ hΛD hD₃'
        hlogD hKD hCKD x γ hxγ
      calc Work.Deep.Conc.prob
              (Work.Deep.Kahn.Round.badUncolSet (K := K) (L := L) C D Λ η x γ)
            + Work.Deep.Conc.prob
              (Work.Deep.Kahn.Round.badKeptSet (K := K) (L := L) C D Λ η x γ)
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) / 2
            + Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) / 2 := add_le_add h1 h2
        _ = Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) := by ring
    obtain ⟨ω, hω₁, hω₂⟩ :=
      hGood n c 𝓗 L D Λ K hD hΛ hK hηK h16 hlin hsize hlist hdeg hDΛ hΛD hD₄' hlogD hKD hCKD
        hP₁ hP₂
    exact nibbleWAssembly (C := C) hC ε η hε hη n c 𝓗 L D Λ K hD hΛ hK hηK h16 hlin hsize
      hlist hdeg hDΛ hΛD ω hω₁ hω₂

end Work.Deep.Kahn
