import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.HallPerPrime_aux
import Submission.Work.CORE2B.Core18HallPerPrime

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# AREA CORE2B — the per-prime step of Bender's Theorem 2.10

Bender's proof of Theorem 2.10 (p. 222) has a per-prime step: for `s ∈ S − S₀` and every prime
`p`,

> `O_p(U) ≤ C_G(s)` or `O_p(U) ∩ C_G(s) = 1`,

i.e. an involution `s ∈ S − S₀` either centralizes or acts fixed-point-freely on each `p`-core of
`U = O(H)` (`H = C_G(t)`).  Via `C_{O_p(U)}(s) = 1 ⟺ s` inverts `O_p(U)`
(`inverts_of_inf_centralizer_eq_bot`, from `Work.BMAX.InvolutionInverts`) this is exactly the
hypothesis
`hact : ∀ p prime, (∀ z ∈ O_p(U), s z s⁻¹ = z) ∨ (∀ z ∈ O_p(U), s z s⁻¹ = z⁻¹)`
of `invSet_le_centralizer_fittingIn` (`HallAux.lean`), whence `I_U(s) ≤ F(U)` and finally `I_U(s)`
is a Hall subgroup of `F(U)` normal in `U` (`Thm210_hall_and_normal`).

## Status of this file (read before continuing!)

* `Work.CORE2B.HallPerPrime_aux` (imported here) proves the sorry-free scaffolding:
  `involution_inverts_of_no_fixed`, `inverts_of_inf_centralizer_eq_bot`,
  `pCore_two_eq_bot_of_odd`, `odd_card_U`, `pCoreIn_two_eq_bot`, `t_commutes_U`, `S_le_H`,
  `S_normalizes_U`.
* The `p = 2` case of `HallPerPrime` is proved below (from `pCoreIn_two_eq_bot`).
* **The odd case is now proved** (lead's design pass 18, item A′): the area first judged it not
  derivable (the note below is kept as history), but Bender's argument does go through with
  Lemma 2.7's conclusion `[M,t] ≤ F_{π'}(M)` as the contradiction, applied to a coatom
  `M ⊇ N_S(⟨t,s⟩)` — not `M ⊇ S`.  The proof is `Work.GW18.Core18HallPerPrime`
  (assembly `Core18HallPerPrimeCase2` over the leaves H1–H6).
* Sibling results proved meanwhile, usable by a later attempt:
  * `HallPerPrime_Xodd` (`Submission.Work.CORE2B.HallPerPrime_Xodd`):
    `O_p(U) ⊓ C_G(s) ≤ O(C_G(s))` for `s ∈ S − S₀`;
  * `HallPerPrime_tSylow` (`Submission.Work.CORE2B.HallPerPrime_tSylow`): there is a
    `t`-invariant Sylow `p`-subgroup of `O(C_G(s))` containing `O_p(U) ⊓ C_G(s)`;
  * `HallPerPrime_hall_implies` (`Submission.Work.CORE2B.HallPerPrime_hall_implies`): the
    *converse* direction, `I_U(s)` Hall in `F(U)` ⟹ the dichotomy (Bender's Case (1) route);
  * `HallPerPrime_pi_not_negation` (`Submission.Work.CORE2B.HallPerPrime_pi_not`): from the
    hypotheses of the failure configuration plus `IsCoatom M`, `N_G(X) ≤ M`, `S ≤ M`,
    `¬ M ≤ Ĥ` one derives `⁅M, t⁆ ≤ F_{π'}(M)` — the *negation* of the π'-claim on which
    Bender's per-prime argument rests.

## Why the odd case is not derivable as stated

Write `X := O_p(U) ⊓ C_G(s)`.  Bender's argument (p. 222) is

> assume `1 ≠ X ≠ O_p(U)`; then (1.1(ii)) there is a `t`-invariant Sylow `p`-subgroup `P` of
> `O(C_G(s))` with `X ≤ P`, and (1.1(iv)) `[t, N_G(X)] ≠ 1`; hence `[t,M]` is not a `π'`-group
> for `M ⊇ N_G(X)`, so Lemma 2.7 applied to `M` (with `¬ Case2` forcing `t ∉ E(M)`) gives a
> contradiction.

The last step is formalizable only if `M` satisfies the hypotheses of `Lemma27Prop`; and then the
*proved* sibling lemma `HallPerPrime_pi_not_negation` shows that `h27` and `¬ Case2` already force
`[M,t] ≤ F_{π'}(M)`, i.e. they confer the *opposite* of Bender's π'-claim.  So the contradiction
cannot be produced that way; the only surviving configurations are those where `Lemma27Prop` is
unavailable (`S ⊄ M`, `|S ⊓ M| < 8`, `t ∉ O²(M)`), and there Bender's 1.1(ii)+1.1(iv) step —
the fleet's still-open `owed_bad` / `Thm210_bad_normalizer` obligation — is needed and is not
implied by `T, h26, h27, h28, hFT, hCtx, B, ¬Case1, ¬Case2`.  In other words the request presumes
one extra input, namely the configuration statement that produces Case 2 from the failure of the
dichotomy.
-/

theorem HallPerPrime (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (h27 : Work.GW2.Lemma27Prop) (h28 : Work.GW2.Lemma28Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (hnot1 : ¬ Work.GW2.Case1 B) (hnot2 : ¬ Work.GW2.Case2 B)
    (s : G) (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) :
    ∀ p : ℕ, Nat.Prime p →
      Work.GW2.pCoreIn p B.U ≤ Subgroup.centralizer ({s} : Set G) ∨
      Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) = ⊥ :=
  Work.GW18.Core18HallPerPrime T h26 h27 h28 G hFT hCtx B hnot1 hnot2 s hs hs0

end Work.CORE2B
