import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV3.step3
import Submission.Work.ThmF.ChV3.step4
import Submission.Work.ThmF.ChV3.step6aux_count
import Submission.Work.ThmF.ChV3.step7
import Submission.Work.ThmF.ChV3.step8
import Submission.Work.ThmF.Tools.External
import Submission.Work.ThmF.Tools.burnsideCorollary

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.step9` — VERDICT: mis-stated (the source's inputs of step (9) are not among the
hypotheses, and two of them are recorded `wrong` upstream)

The conclusion below is verbatim Peterfalvi II, Ch. V §3, step (9) (p. 250), with `p = |P|` and
`f = orderOf (s * t)`:

> **(9)** Suppose `Q₁ ≠ 1`.  Then `p = f ≠ ℓ` (`ℓ = |Σ|`).
> *Proof.* By (F2) and **Burnside's transfer theorem**, `P` is not a Sylow `p`-subgroup of `G`, so
> by (2) and (7), `p` divides `|F|·|F*|·|Σ|`.  By (3), `p ∤ |F*|`, so by (8) `p = f` or `p = ℓ`.
> Suppose `p = f = ℓ` … contradicts (3).  Suppose `p = ℓ ≠ f` … Hall–Wielandt, Schur–Zassenhaus,
> `[H I.14.9]`, §1 Prop. 3, §2 Lemma 2 b) … a quotient of order `p`, contradicting (F2).
> USES: Burnside transfer; (2), (3), (4), (7), (8); [recursion]; [H I.14.9]; [HallWielandt];
> Schur–Zassenhaus; §2 Lemma 2 b); §1 Prop. 3.

The statement is **vacuously true in reality** — Théorème F makes `CtxF` contradictory, and that is
exactly `ThmFProp`, i.e. the very chain step (9) belongs to — but the hypotheses it carries are
strictly weaker than the source's setting, and the conclusion does not follow from them.  The
genuine inputs of the source's argument are neither among the hypotheses nor available in the
workspace:

1. **`p = f` (the first half) is a divisibility statement about `Q`, not an arithmetic consequence
   of `hF`.**  From `hF` alone one only knows the *cardinality* `|C_Q(P)| + 1 = f^m` (`f` prime,
   `m ≥ 1`), i.e. `|F| = f^m`; the source's route to `p = f` is the divisibility
   `p ∣ |F|·|F*|·|Σ| = |C_Q(P)|·(|C_Q(P)|+1)·|Σ|` obtained from Burnside's transfer theorem
   *together with* `N_G(P) = C_G(P)` (step (1)) and `C_G(P)/N ≅ (F ⋊ C_Q(P)) ⋊ Σ` (step (2),
   App. XI Prop. 1) and `N = P` (step (7)).  None of (1), (2), (7) is a hypothesis; step (1) is
   already recorded `outcome: wrong` (it silently drops `FeitThompsonProp`), and (2) has no
   formalization anywhere in the repository (no near-field / App. XI material exists; App. XI
   Prop. 1 in turn rests on App. III (2), i.e. Feit–Thompson, the project's single open hole).
   The on-disk `Tools.burnsideCorollary` applies only to a genuine Sylow `p`-subgroup, so it says
   nothing about the order-`p` subgroup `P` without (1) and the `p`-part bookkeeping of (4)/(10).
   `hF` gives **no** relation between `Nat.card P` and `Nat.card ↥(CQ Q P)`, `orderOf (s*t)` or
   `Nat.card ↥(Sig H t P)`; and `p ∤ |F*|` — the source's (3) — is precisely the missing input that
   rules out `p = ℓ ≠ f`.
2. **`p ≠ ℓ` (the second half) needs (8) and the Hall–Wielandt argument.**  The source gets
   `ℓ = |Σ|` prime with `|F| ∈ {3^ℓ, 5^ℓ, 9^ℓ}` from (8) — unproven (its proof uses the near-field
   input (2) and `ArithmeticNineTwoSeven`), and then excludes `p = ℓ ≠ f` with Hall–Wielandt +
   Schur–Zassenhaus + `[H I.14.9]`, whose cardinality input `|Q| = |C_Q(P)|^{|P|}` is step (4).
   Step (4) is recorded `wrong`: `WielandtFixedPoint` cannot be instantiated under `CtxF` because
   its Frobenius hypothesis `K ⊓ K^g = ⊥` (`g ∈ P#`) is provably false (`P ≤ C_D(t)` normalises
   `Kset H t`) and its coprimality hypothesis `p ∤ |Q|` (the `r ≠ p` half of (3)) is unavailable;
   step (3) itself (App. V, Clifford, the Frobenius dimension formula `[Is 15.16]`) is likewise not
   formalized.  So nothing in the hypotheses controls `Σ = Sig H t P` at all.

**Repair.**  State (9) as a wrapper consuming the outputs of (2), (3), (7), (8), i.e. add
`Nat.card P ∣ Nat.card ↥(CQ Q P) + 1` (with `hF` this gives `p = f` immediately, see
`card_eq_orderOf_of_dvd_card_CQ`) and `¬ Nat.card P ∣ Nat.card ↥(Sig H t P)` (which gives
`p ≠ ℓ`); `step9_repaired` below is the resulting statement, proved here sorry-free.  The same
verdict is already recorded for the sibling steps `ChV3/step1`, `ChV3/step3`, `ChV3/step4`,
`ChV3/step6`, `ChV3/step10`.

## What is proved in this file (sorry-free)

* `card_eq_orderOf_of_dvd_card_CQ` — `hF` + `Nat.card P ∣ |C_Q(P)| + 1` ⟹ `p = f` (pure arithmetic:
  `p ∣ f^m` with `p`, `f` prime);
* `card_eq_orderOf_iff_dvd_omega` — the *equivalence* identifying exactly where the missing input
  lies; with the two counting lemmas that **are** on disk and sorry-free
  (`ChV3/step6aux_count`: `|C_Q(P)| + 1 = |Ω^P|`; `ChV3/step6aux_count.card_omega_eq`:
  `|Ω| = |Q| + 1`, `Ω = G ⧸ H`) and the orbit congruence for the `p`-group `P` acting on `Ω`
  (`IsPGroup.card_modEq_card_fixedPoints`), the first half of the conclusion is equivalent to the
  single divisibility `Nat.card P ∣ Nat.card (G ⧸ H)` (`= Nat.card P ∣ Nat.card Q + 1`), i.e. to
  "`H` contains no Sylow `p`-subgroup of `G`" — the Burnside/Hall–Wielandt content above;
* `step9_repaired` — the repaired statement (with the two divisibility hypotheses of the repair).

All three are sorry- and axiom-clean; the target `step9` below is left as stated.

**One well-formedness repair.**  As received, the statement did not even elaborate: the binders
`{G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}` were placed
*after* the hypothesis `hF`, whose type mentions `s`, `t`, `Q`, `P`, and the project sets
`autoImplicit = false` (lakefile), so `(orderOf (s * t))` was stuck on unresolved metavariables
(`HMul ?m ?m ?m`).  I hoisted those binders to the front (the position they have in
`_design/chV3_steps.lean`, where they come from the surrounding `variable` block).  The
proposition is unchanged and the explicit-argument order `hHW hA hF hC4 hnil c hQ1` is unchanged,
so any caller written against the request is unaffected.
-/

set_option linter.unusedVariables false

namespace Work.ThmF.ChV3

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

/-! ## `hF` plus `p ∣ |C_Q(P)| + 1` gives `p = f` -/

/-- **Arithmetic core**: if `|C_Q(P)| + 1 = f^m` with `f` prime, `m ≥ 1`, and `p = Nat.card P` is a
prime dividing `|C_Q(P)| + 1`, then `p = f`.  This is the elementary half of step (9): with it, the
source's divisibility `p ∣ |F|·|F*|·|Σ|` (step (1)+(2)+(7)+Burnside) and `p ∤ |F*|` (step (3))
would give `p = f` at once. -/
theorem card_eq_orderOf_of_dvd_card_CQ {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t s r : G} {P : Subgroup G} (c : CtxF H Q t s r P)
    (hF : (orderOf (s * t)).Prime ∧ ∃ m : ℕ, 1 ≤ m ∧
      Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m)
    (hdiv : Nat.card P ∣ Nat.card ↥(CQ Q P) + 1) : Nat.card P = orderOf (s * t) := by
  obtain ⟨hf, m, _hm1, hm⟩ := hF
  have hp : (Nat.card P).Prime := c.P_prime
  have h1 : Nat.card P ∣ orderOf (s * t) ^ m := by rw [← hm]; exact hdiv
  have h3 : Nat.card P ∣ orderOf (s * t) := hp.dvd_of_dvd_pow h1
  rcases hf.eq_one_or_self_of_dvd (Nat.card P) h3 with h | h
  · exact absurd h hp.ne_one
  · exact h

/-! ## Where the missing input lies: `p = f` is equivalent to `p ∣ |Ω|` -/

/-- **The first half of step (9) is equivalent to `Nat.card P ∣ Nat.card (G ⧸ H)`.**

With the two counting lemmas that are available sorry-free (`step6aux_count`:
`|C_Q(P)| + 1 = |Ω^P|`, and `card_omega_eq`: `|Ω| = |Q| + 1`) and the orbit congruence for the
`p`-group `P` acting on `Ω = G ⧸ H`, the hypothesis `hF` pins `|Ω^P| = f^m`, so
`|Q| + 1 = |Ω| ≡ |Ω^P| = f^m (mod p)`: hence `p ∣ |Ω|` iff `p ∣ f^m` iff `p = f`.  So the source's
`p = f` is exactly the statement that `H` contains no Sylow `p`-subgroup of `G` — the
Burnside/Hall–Wielandt content of (9), which is what the hypotheses are missing. -/
theorem card_eq_orderOf_iff_dvd_omega {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t s r : G} {P : Subgroup G} (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (hF : (orderOf (s * t)).Prime ∧ ∃ m : ℕ, 1 ≤ m ∧
      Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m) :
    Nat.card P = orderOf (s * t) ↔ Nat.card P ∣ Nat.card (G ⧸ H) := by
  obtain ⟨hf, m, hm1, hm⟩ := hF
  have hp : (Nat.card P).Prime := c.P_prime
  haveI : Fact (Nat.card P).Prime := ⟨hp⟩
  have hpg : IsPGroup (Nat.card P) ↥P :=
    IsPGroup.of_card (n := 1) (pow_one (Nat.card P)).symm
  have hcong0 : Nat.card (G ⧸ H) ≡
      Nat.card (MulAction.fixedPoints ↥P (G ⧸ H)) [MOD Nat.card P] :=
    hpg.card_modEq_card_fixedPoints (G ⧸ H)
  rw [Nat.card_coe_set_eq] at hcong0
  have hfixset : (fixedPts H P : Set (G ⧸ H)) = MulAction.fixedPoints ↥P (G ⧸ H) := by
    ext ω
    simp [fixedPts, MulAction.mem_fixedPoints]
  have hfix : (MulAction.fixedPoints ↥P (G ⧸ H)).ncard = orderOf (s * t) ^ m := by
    rw [← hfixset, ← step6aux_count hC4 c, hm]
  have hcong := hcong0
  rw [hfix] at hcong
  constructor
  · intro hpf
    refine Nat.modEq_zero_iff_dvd.mp (hcong.trans ?_)
    rw [hpf]
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by omega))
  · intro hdvd
    have h0 : Nat.card (G ⧸ H) ≡ 0 [MOD Nat.card P] := Nat.modEq_zero_iff_dvd.mpr hdvd
    have h1 : Nat.card P ∣ orderOf (s * t) ^ m :=
      Nat.modEq_zero_iff_dvd.mp (hcong.symm.trans h0)
    have h3 : Nat.card P ∣ orderOf (s * t) := hp.dvd_of_dvd_pow h1
    rcases hf.eq_one_or_self_of_dvd (Nat.card P) h3 with h | h
    · exact absurd h hp.ne_one
    · exact h

/-- The same equivalence in the form in which the missing input is a condition on `Q` alone
(`|Ω| = |Q| + 1` is `card_omega_eq`): `p = f` iff `Nat.card P ∣ Nat.card Q + 1`, i.e. iff `H`
contains no Sylow `p`-subgroup of `G`. -/
theorem card_eq_orderOf_iff_dvd_card_Q_succ {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t s r : G} {P : Subgroup G} (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (hF : (orderOf (s * t)).Prime ∧ ∃ m : ℕ, 1 ≤ m ∧
      Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m) :
    Nat.card P = orderOf (s * t) ↔ Nat.card P ∣ Nat.card Q + 1 := by
  rw [card_eq_orderOf_iff_dvd_omega hC4 c hF, card_omega_eq c.split]

/-! ## The repaired statement -/

/-- **Repaired step (9)**: with the outputs of the source's (2)+(3)+(7) (`p ∣ |C_Q(P)| + 1`, cf.
`card_eq_orderOf_of_dvd_card_CQ`) and of (8) (`p ∤ |Σ|`) added as hypotheses, the conclusion of
step (9) follows immediately. -/
theorem step9_repaired {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : CtxF H Q t s r P)
    (hF : (orderOf (s * t)).Prime ∧ ∃ m : ℕ, 1 ≤ m ∧
      Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m)
    (hdiv : Nat.card P ∣ Nat.card ↥(CQ Q P) + 1)
    (hSig : ¬ Nat.card P ∣ Nat.card ↥(Sig H t P)) :
    Nat.card P = orderOf (s * t) ∧ Nat.card P ≠ Nat.card ↥(Sig H t P) := by
  refine ⟨card_eq_orderOf_of_dvd_card_CQ c hF hdiv, ?_⟩
  intro heq
  exact hSig (heq ▸ dvd_refl (Nat.card P))


end Work.ThmF.ChV3
