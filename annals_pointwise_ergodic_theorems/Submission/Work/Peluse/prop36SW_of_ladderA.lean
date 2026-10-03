import Mathlib
import Submission.Work.Peluse.Prop36SW.degenerateBranch

/-!
# O2: the corrected Proposition 3.6 (`Prop36SW`) from the corrected Lemma 5.7 (`PeluseLadderA`)

`Work.Peluse.C46.Prop36SW P` is Peluse's Proposition 3.6 with the window that the §5 ladder actually
delivers, and `Work.Peluse.C46.PeluseLadderA` is her Lemma 5.7 with the constants
`(K, C₀, t', c)` quantified *before* the instance data (as the paper's `O_{t,(k_ω)}(1)`).

## The proof strategy: the *support chain*

> **WARNING (session 2 — read `NOTES_prop36SW_of_ladderA_SESSION2.md` first).**  The state described
> below is the *single-direction* state `γ ≤ E_a uNormPow m (arithIcc (Λ · dir ℓ i …) L) f`, and its
> intended production from `D.famAvg` by "level-lowering" is **impossible**: the inequality supplied
> by `boxNormPow_succ_ge_general` is
> `(1/2)·(boxNormPow t (Q ∘ castSucc))² ≤ boxNormPow (t+1) Q`, i.e. the higher level dominates the
> *square* of the lower one, so the level-1 norm of a single member is bounded **above** by the
> family box norm, never below.  The correct state is the **ladder's own hypothesis shape**
> `E_{a ∈ A} E_{a' ∈ paramBox} boxNorm (card (FamIdx kω)) (pDirFam p M₁ a a') (g a)` with the
> multiplicity function `kω` of the *full* direction family, the initial state coming from
> `D.famNorm` by an *identification* (no level-lowering), and each step being
> "one `PeluseLadderA` application + absorption of the produced long directions into the parameter
> set via `boxNormPow_peel_append`".  See §1–§3 of the session-2 note for the derivation and §6 for
> the remaining obligations.  The lemmas `parBox_succ_eq_image` / `parBox_succ_average` below are the
> (proved) box-splitting input of that route.

The `d - 1`-fold iteration of Lemma 5.7 is organised around a single finite object, the **support**
of the current uniformity norm, and *no* mixed (long/short) families ever occur.  This is the point
that makes the iteration formalisable: at every stage one manufactures a ladder hypothesis whose
multiplicity function `kω` is supported on the **full** subset `univ` of the slots of the support.
Then the ladder's conclusion has *no* short directions left — every `ω ∈ J` is a *proper* subset of
`univ`, so `k'_ω = k_ω = 0` — hence it is *already* a uniformity-norm power at the new level `t'`,
whose single direction has the coefficient of the *peeled* slot.  So the ladder is applied once per
slot peeled, the support moves to the parent of the peeled slot, and the level index drops by one;
after `d - 1` peels the coefficient is exactly `d!·lc P`.

Let `d = P.natDegree ≥ 2`, `D : IdxDatum`, `κ = dirCoeff P = d!·lc P`, and `H = ⌊δ'M⌋`.  Write
`dir ℓ i a = D.dir d (lc P) ℓ i a` for the level-`ℓ` direction of the index `i ∈ I ℓ`.  By
`IdxDatum.dir`,

* `dir (j+1) ω a = ∑_{s ∈ ω} ((d - j) · dir j (par j s) a) · a_{j+1,s}`  (`slotCoeff` below),
* `dir (d-1) ω a = d! · lc P · (∏ of parameters)` — the top level carries the whole `d!`.

**State `j`** (`j = 1, …, d-1`): a support `i_j ∈ I (d-j)` (nonempty) and constants `Λ_j = j!`,
`L_j`, `m_j`, `γ_j` with

  `E_{a ∈ B_j} (uNormPow m_j (arithIcc (Λ_j · dir (d-j) i_j a) L_j) f) ≥ γ_j`,

the average running over the *restricted* parameter box `B_j` (the parameters of the levels not yet
peeled, each in `Ioo (-H) H`).

**Step `j`**: apply `PeluseLadderA` to the datum

* `ι := ↥i_j` (the slots of the support), `k i := 1`, so `Slot ι k ≃ ↥i_j`;
* `p s a := Λ_j · slotCoeff D d (lc P) (d-j-1) s a` (the slot's coefficient);
* `kω ω := if ω = univ then m_j else 0`;
* `M₁ := L_j`, `M₂ := min H L_j`, `γ := γ_j - (additive loss)`, `γ' := γ_j ^ Kl / C₀`,
  `A := B_j ∩ {a : ∀ s ∈ i_j, 0 < p s a}`, `f a := f`.

The hypothesis is an *identity*: `∑_{s ∈ univ} p s a · a'_s = Λ_j · dir (d-j) i_j a`
(`dir_succ_eq_sum_slotCoeff`), and the box `M₂` matches the restricted box
(`paramBox_eq_piFinset`).  The sign of `p s a` is handled by the reflection `a'_s ↦ -a'_s` of the
(symmetric) box, so the "good set" is the complement of the *zero* set, of density `≲ 1/H`; all the
losses are additive and are absorbed by `η ^ E · H ≳ 1`, which the hypotheses give with `K ≥ d` and
`A` large (`A (ηδ')^{-K} ≤ N ≤ A₀ M^d` and `δ' M ≥ H`).

The conclusion is

  `E_a (uNormPow t' (arithIcc (p s₀ a) L_{j+1}) f) ≥ c (γ γ')^{Kl}`,  `L_{j+1} = ⌊γ' M₁ M₂⌋`,

which is the state at stage `j+1` with `i_{j+1} := par (d-j-1) s₀`, `Λ_{j+1} = Λ_j (j+1)`,
`m_{j+1} := t'`, `γ_{j+1} := c (γ γ')^{Kl}`.

**End of the iteration.**  After `d - 1` steps the level is `0`, the support lies in `I 0`, `Λ_d = d!`
and `dir 0 i a = lc P`, so the state reads `uNormPow m_d (arithIcc (d!·lc P) L_d) f ≥ γ_d` with
`L_d = H · ∏_j (γ'_j H)` and `γ_d = c_D · η^{E_D}`, constants depending only on `D`, `P` and the
ladder's constants for the finitely many data of the chain.

**Final transfer.**  Choose the statement's `K`, `A` with `K ≥ E_D`, `K ≥ 2 E_D` and
`A ≥ c_D^{-1}·(constants)`; then `L_d ≥ L_target` and `A γ_d ≥ η^K`, so shortening the window
(`uNormPow_shrink_ambient`) and raising the level `m_d → s := max 2 m_d`
(`uNormPow_level_raise`) give the conclusion.  (For the degenerate datum with `I (d-1) = ∅` the
hypothesis is a *mean* bound and the conclusion follows from `uNormPow (κ[1]) ≥ (mean)^{2^s}`.)

## Status

> **SESSION 26 UPDATE — READ THIS FIRST.**  Both branches of this target are now **PROVED,
> complete and axiom-clean**:
>
> * the **non-degenerate** case (`2 ≤ Fintype.card (D.I (P.natDegree - 1))`) is
>   `Work.Peluse.prop36SW_body` (`Prop36SW/nodeBody.lean`, the §5 chain plus the two-regime window
>   split on `x = η^K δ'^d M^d / A`);
> * the **degenerate** case (`Fintype.card (D.I (P.natDegree - 1)) ≤ 1`) is
>   `Work.Peluse.prop36SW_degenerate` (`Prop36SW/degenerateBranch.lean`), by *enlarging* the index
>   datum: `extDatum D` adjoins two fresh slots at every level, so that
>   `Fintype.card ((extDatum D).I j) = 2^(|D.S j| + 2) - 1 ≥ 3` and the chain applies to the
>   extension.  The transfer is the family-average comparison `famAvg_le_extFamAvg`
>   (`∃ C ∈ (0,1], C · D.famAvg ≤ (extDatum D).famAvg`), which rests on the level-raise
>   `Work.Prop36SW.boxNorm_le_levelRaise_first` at the inflated ambient `N₁ := K₀N+1` and on the
>   ambient ratio `boxNorm_symIcc_ratio`.  Since `C ≤ 1`, the rescaling `η ↦ Cη`,
>   `A ↦ A'/C^{K'}` maps the datum's hypotheses *verbatim* onto those of the extension and leaves
>   the window `⌊max 1 (η^K δ'^d M^d / A)⌋` unchanged.
>
> **On the earlier `REFUTATION_Prop36SW_degenerate.md`**: it only rules out `A = 1` for its family
> (`A` is the *statement's* existential, not the datum's), and the rescaling above exhibits
> `A = A'/C^{K'} ≥ 1` with `C ∈ (0,1]`.  No repair of `C46.Prop36SW` is needed.

Verified below: the slot coefficient with the **family identity** (the exact shape of the ladder
hypothesis, `dir_succ_eq_sum_slotCoeff`) and the **box identification**
(`paramBox_eq_piFinset`). Remaining: the `d-1`-step induction over the support (the ladder
application described above), the bookkeeping of the restricted boxes and of the good set, and the
final window/level transfer.  The strategy above is complete
and the pieces it needs are the ones named
(`boxNormPow_succ_ge_general` for the level-lowering, `boxNormPow_perm` for the direction order,
`boxNormPow_le_one` for the linearity of the level-lowering, `uNormPow_shrink_ambient` and
`uNormPow_level_raise` for the final transfer).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

open Work.Peluse.UControl
open Work.Prop36SW

/-- **The target**: the corrected Proposition 3.6 from the corrected Lemma 5.7.

The proof splits on the degeneracy of the top slot set `D.S (d-1)`:

* `2 ≤ Fintype.card (D.I (d-1))` (equivalently `2 ≤ |D.S (d-1)|`): the §5 chain, supplied by
  `Work.Peluse.prop36SW_body` (`Submission/Work/Peluse/Prop36SW/nodeBody.lean`);
* `Fintype.card (D.I (d-1)) ≤ 1`: the extension route, supplied by
  `Work.Peluse.prop36SW_degenerate` (`Submission/Work/Peluse/Prop36SW/degenerateBranch.lean`),
  which scales the datum by `η ↦ Cη`, `A ↦ A'/C^{K'}` for the constant `C ∈ (0,1]` of
  `Work.Peluse.famAvg_le_extFamAvg` and applies the first branch to `extDatum D`.
-/
theorem prop36SW_of_ladderA (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (h : Work.Peluse.C46.PeluseLadderA) : Work.Peluse.C46.Prop36SW P := by
  classical
  intro D
  by_cases hI : 2 ≤ Fintype.card (D.I (P.natDegree - 1))
  · -- ### the non-degenerate case: the §5 chain — **PROVED** (`Prop36SW/nodeBody.lean`)
    exact prop36SW_body P hd h D hI
  · -- ### the degenerate case (`card (D.I (d-1)) ≤ 1`) — **PROVED** (`Prop36SW/degenerateBranch.lean`)
    exact prop36SW_degenerate P hd h D (by omega)

end

end Work.Peluse
