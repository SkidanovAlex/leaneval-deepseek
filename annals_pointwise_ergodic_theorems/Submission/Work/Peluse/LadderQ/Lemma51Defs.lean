import Mathlib
import Submission.Work.Peluse.LadderB.stepDefs

/-!
# The §5 chain of Peluse (arXiv:1909.00309) in the form the ladder consumes it

`Work.Peluse.LadderB.ladderStepQ j` is Peluse's **Lemma 5.6** rewritten in the ladder's
normalisation (short slots `c((h-h')·ω)[L]` averaged over `(h,h') ∈ [M₁]^{j+1}`, long slots
`c[D'']`, `D'' = ⌊γ'²M₁M₂⌋`, `L = ⌊γ'M₂⌋`).  The paper proves Lemma 5.6 by applying Lemma 5.1
*once* per ladder step, at level `s = j+1`, to the function `Δ'f` (the long slots ride along), plus
a pigeonhole over the `(h,h')`-average which uses Lemma 5.2; Lemma 5.1 itself is proved by
induction on `s`, with the cases `s = 1, 2` being Lemmas 5.4, 5.5.

## Why the paper's statements cannot be used verbatim

* the paper's loss in Lemmas 5.1/5.4/5.5/5.6 is a **power** `γ^{O_s(1)}`, while the ladder's
  conclusion `C·u ≤ boxLadderNorm j …` with `C₁γ^K ≤ u` is a **constant-factor** statement: a
  power loss cannot be upgraded (`u^{K'} ≤ u` for `u ≤ 1` is weaker), so the loss in the
  statements below is the *observed value* `γ` itself;
* the paper's literal Lemma 5.1 is **false** (`Concat.not_peluseConcatenationLemma51`, the
  collapsed window `M₂ = 1` with a chirp), so the non-degeneracy must be carried explicitly.

## The repair used here

Each statement carries the *sandwich* of `ladderStepQ`, i.e. the data conditions

`A γ' ≤ γ^K`,   `A ≤ M₂(γγ')^K`,   `A ≥ max 8 (C₁^{-10^6})`   (`A` existential),

which are exactly the conditions under which the constant-factor form is intended to hold: they
force `M₂` large (`M₂ ≥ (A/γ^K)^{K+1}`, killing the collapsed window of the paper's literal
Lemma 5.1) and — through the ladder's state bound `C₁γ^K ≤ u ≤ boxLadderNorm …` — also force `M₂`
to be *bounded* in terms of the observed state, which rules out the long-averaging families on
which the paper's power loss is genuine (cf. `Submission/Work/Peluse/LadderB/ladderStepQFinal.lean`
§2–§3).

## What is here

* `Peluse54S` — Lemma 5.4 (`s = 1`), sandwich form, constant loss, output level `2` (the paper's
  `U²`), in the `(a,b)`-average form of the paper;
* `Peluse55S` — Lemma 5.5 (`s = 2`), sandwich form, constant loss, output level `5` (the paper's
  `U⁵`);
* `Peluse51S` — the general Lemma 5.1 (all `s`), sandwich form, with the paper's gcd/size
  exceptional-set hypothesis.

Nothing here is proved.  The consumer is the pigeonhole reduction (to be written in
`LadderQ/LadderStepOf51.lean`), which turns `Peluse51S` at `s = j+1` into `ladderStepQ j`: each
ladder step applies Lemma 5.1 with `b_ω = -h_s' + (h₁-h₁',…)'·ω` after a pigeonhole over `h_s`,
exactly as in the paper's proof of Lemma 5.6 (the gcd conditions coming from Lemma 5.2, i.e. the
tree's `Concat.cardBadPairs`).

## The constant-loss form is the crux (finding of the review of `Peluse51StepS`, 2026-10-03)

The reviewer of `Peluse/LadderQ/Peluse51StepSThm` established the following, and it is the central
mathematical point of this lane:

* the paper's induction step (Lemma 5.1, `s → s+1`) produces only a **power** loss: the level-`(s+1)`
  datum yields `E_{a'} E_a ‖Δ'f‖^{2^s}_{□^s} ≫ γ^{O(1)}`, and pigeonholing in `a'` supplies the
  `s`-case's hypothesis at `γ^{O(1)}`, **not** at `γ`;
* hence the loss `C·γ` asserted by `caseS` is *strictly stronger* than what the stated sandwich
  supports, and the sandwich alone (without the ladder's own state bound `C₁γ^K ≤ u ≤ boxLadderNorm`)
  does not repair it.

This is exactly the tension the ladder lives in.  `ladderStepQ` needs the **constant** loss: its
conclusion is `C·u ≤ …` with `u` only *bounded below* (`C₁γ^K ≤ u ≤ boxLadderNorm (j+1)`), and a
power loss `C'γ^k` cannot be upgraded to `C·u ≤ …` because `u^k ≤ u` for `u ≤ 1` and `k ≥ 1`
(a power loss is *weaker* than the constant loss).  The frozen `C46.ConcatBridgeShortA` — the
sibling lane's statement — needs only the **power** loss, so the paper's §5 chain as proved serves
that lane, while this lane's `ladderStepQ` asserts a genuine sharpening of Peluse's Lemma 5.6.

The two constant-loss base cases are already out to the fleet (`Peluse54SThm`, `Peluse55SThm`); if
either comes back `declare_false`, then `ladderStepQ` is false and the lane must be reported as
such (with the refuting family); if they are proved, the constant-loss step is the remaining crux
and the *faithful* form to delegate next is the power-loss step `caseS s → caseS s` at exponent `k`
(the paper's own statement), not `Peluse51StepS` as written.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderQ

noncomputable section

open Work.Peluse

/-- The paper's averaged box-norm hypothesis `E_{a∈[M₁]}‖f‖_{□^s_{(c(a+b_i)[M₂])}([-N,N])}`. -/
def boxAvgA (s : ℕ) (c : ℤ) (M₁ M₂ : ℕ) (b : Fin s → ℤ) (N : ℕ) (f : ℤ → ℂ) : ℝ :=
  ((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
    Work.Peluse.boxNorm s (fun i : Fin s => Work.Peluse.arithIcc (c * ((a : ℤ) + b i)) M₂)
      (Work.Peluse.symIcc N) f

/-- The output window `c[⌊γ'M₁M₂⌋]` of Lemmas 5.1/5.4/5.5. -/
def outWin (c : ℤ) (γ' : ℝ) (M₁ M₂ : ℕ) : Finset ℤ :=
  Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat

/-- **Peluse's Lemma 5.4** (`s = 1` case of Lemma 5.1), in the ladder's sandwich form: from a lower
bound `γ` for the average over `a ∈ [M₁]` of the level-`1` box norm of `f` with the direction set
`c(a+b)[M₂]`, conclude a **constant** multiple of `γ` for the level-`2` uniformity norm of `f` at
the concatenated window `c[⌊γ'M₁M₂⌋]`.

`2 ≤ M₂` is the repaired collapsed-window condition; the sandwich `A γ' ≤ γ^K`,
`A ≤ M₂(γγ')^K` with `A ≥ max 8 (C₁^{-10^6})` is the ladder's non-degeneracy. -/
def Peluse54S : Prop :=
  ∀ (C₁ : ℝ), 0 < C₁ → ∃ A : ℝ, max 8 (C₁ ^ (-(10 ^ 6 : ℝ))) ≤ A ∧ ∃ K : ℕ, 2 ≤ K ∧
    ∃ C : ℝ, 0 < C ∧
    ∀ (c : ℤ), 0 < c → ∀ (M₁ M₂ : ℕ) (b : ℤ) (γ γ' : ℝ) (N : ℕ) (f : ℤ → ℂ),
      2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
      0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 →
      A * γ' ≤ γ ^ K → A ≤ (M₂ : ℝ) * (γ * γ') ^ K →
      SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      γ ≤ boxAvgA 1 c M₁ M₂ (fun _ => b) N f →
      C * γ ≤ Work.Peluse.uNorm 2 (outWin c γ' M₁ M₂) (Work.Peluse.symIcc N) f

/-- **Peluse's Lemma 5.5** (`s = 2` case of Lemma 5.1), sandwich form: from a lower bound `γ` for
the average over `a ∈ [M₁]` of the level-`2` box norm of `f` with the direction sets
`c(a+b₁)[M₂], c(a+b₂)[M₂]`, conclude a **constant** multiple of `γ` for the level-`5` uniformity
norm of `f` at the concatenated window `c[⌊γ'M₁M₂⌋]`.

The paper's `γ''` (gcd/size parameter) is folded into the sandwich: `A ≤ M₂(γγ')^K` already gives
`M₂ ≫ (γγ')^{-O(1)}`, and the almost-invariance loss `O(γ'')` of the paper's argument is absorbed by
taking `γ''` comparable to `γ'` (both are `≤ γ^K/A`). -/
def Peluse55S : Prop := by
  classical
  exact
  ∀ (C₁ : ℝ), 0 < C₁ → ∃ A : ℝ, max 8 (C₁ ^ (-(10 ^ 6 : ℝ))) ≤ A ∧ ∃ K : ℕ, 2 ≤ K ∧
    ∃ C : ℝ, 0 < C ∧
    ∀ (c : ℤ), 0 < c → ∀ (M₁ M₂ : ℕ) (b : Fin 2 → ℤ) (γ γ' : ℝ) (N : ℕ) (f : ℤ → ℂ),
      2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
      0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 →
      A * γ' ≤ γ ^ K → A ≤ (M₂ : ℝ) * (γ * γ') ^ K →
      -- the paper's gcd/size exceptional set (Lemma 5.2 supplies it in the applications)
      (((Finset.Icc 1 M₁).filter (fun a : ℕ =>
          ¬ (((Int.gcd ((a : ℤ) + b 0) ((a : ℤ) + b 1) : ℕ) : ℝ) < 1 / γ'
              ∧ γ' * (M₁ : ℝ) ≤ |((a : ℤ) + b 0)|))).card : ℝ)
        ≤ C * γ * (M₁ : ℝ) →
      SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      γ ≤ boxAvgA 2 c M₁ M₂ b N f →
      C * γ ≤ Work.Peluse.uNorm 5 (outWin c γ' M₁ M₂) (Work.Peluse.symIcc N) f

/-- **The `s`-instance of the sandwich form of Peluse's Lemma 5.1.**

The singled-out index of the paper's size condition (`|a+b_1| ≥ γ''M₁`) is carried as a parameter
`i₀ : Fin s`: for every `s ≥ 1` the paper's condition is the one for any chosen index, and the
statements below quantify `i₀` universally.

`caseS s` is a clean `ℕ → Prop`, so that the induction of Lemma 5.1 can be written as
`Peluse51StepS : ∀ s ≥ 2, caseS s → caseS (s+1)` with the base cases `caseS 1`, `caseS 2`. -/
def caseS (s : ℕ) : Prop := by
  classical
  exact
  ∀ (C₁ : ℝ), 0 < C₁ → ∃ A : ℝ, max 8 (C₁ ^ (-(10 ^ 6 : ℝ))) ≤ A ∧ ∃ K : ℕ, 2 ≤ K ∧
    ∃ C : ℝ, 0 < C ∧ ∃ s' : ℕ, 1 ≤ s' ∧
    ∀ (i₀ : Fin s) (c : ℤ), 0 < c →
      ∀ (M₁ M₂ : ℕ) (b : Fin s → ℤ) (γ γ' : ℝ) (N : ℕ) (f : ℤ → ℂ),
      2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
      0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 →
      A * γ' ≤ γ ^ K → A ≤ (M₂ : ℝ) * (γ * γ') ^ K →
      (((Finset.Icc 1 M₁).filter (fun a : ℕ =>
          ¬ ((∀ i j : Fin s, i ≠ j →
                ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b j) : ℕ) : ℝ) < 1 / γ')
              ∧ γ' * (M₁ : ℝ) ≤ |((a : ℤ) + b i₀)|))).card : ℝ)
        ≤ C * γ * (M₁ : ℝ) →
      SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      γ ≤ boxAvgA s c M₁ M₂ b N f →
      C * γ ≤ Work.Peluse.uNorm s' (outWin c γ' M₁ M₂) (Work.Peluse.symIcc N) f

/-- **Peluse's Lemma 5.1** (general `s`), sandwich form: the conjunction of its instances
`caseS s` for `s ≥ 1`.  (This is the same statement as the `Prop` of the same name in
`Concat.peluse51Defs`, with the two repairs: the sandwich `A γ' ≤ γ^K`, `A ≤ M₂(γγ')^K` with
`A ≥ max 8 (C₁^{-10^6})`, and the loss as the observed value `C·γ`.) -/
def Peluse51S : Prop := ∀ (s : ℕ), 1 ≤ s → caseS s

/-- **The induction step of Peluse's Lemma 5.1**: the case `s` (for `s ≥ 2`) implies the case
`s+1`.

The paper's proof is: given the datum for the level `s+1`, apply Lemma 5.3 (`twoDimInverse`, the
two-dimensional inverse theorem for the level-`2` box norm, already proved in the tree) to the pair
of directions `s`, `s+1` after the change of variables `Δ'f = f(·+Σ) g`, Cauchy–Schwarz twice, and
then the induction hypothesis (the `s`-case) **twice** — once for the average over `a` and once for
the average over `a'`.  All the losses are the observed-value constants of the two uses. -/
def Peluse51StepS : Prop := ∀ (s : ℕ), 2 ≤ s → caseS s → caseS (s + 1)

/-- The base cases together with the induction step give the general statement (bookkeeping). -/
theorem peluse51S_of_cases (h1 : caseS 1) (h2 : caseS 2) (hstep : Peluse51StepS) :
    Peluse51S := by
  intro s hs
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  induction n with
  | zero => simpa using h1
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simpa using h2
    · exact hstep (k + 1) (by omega) (ih (by omega))

/-! ## The constant-loss step with the ladder's *state* bound carried

`caseS` uses a single parameter `γ` both for the data's frozen *normalisation* (the sandwich
`A γ' ≤ γ^K`, `A ≤ M₂(γγ')^K`) and for the *observed* box-norm average (`γ ≤ boxAvgA s …`).  The
ladder separates the two roles: it carries a frozen `γ, γ', A, K, M₂` *and* a state value `u` with

`C₁γ^K ≤ u ≤ boxLadderNorm (j+1) n M₁ c (omegaOf (j+1)) L D'' N f`

and its conclusion is in terms of `u` (`C·u ≤ boxLadderNorm j …`), so the statement it consumes must
be the **observed-value** one: with `θ` the observed box-norm average, `C·θ ≤ uNorm s' …`.

`caseST s` is that statement at level `s`: the sandwich is carried by the frozen `γ`, while the
loss's base is the observed `θ`, sandwiched between `C₁γ^K` and the box-norm average.  This is the
form the ladder consumes step by step, and it is deliberately *independent* of the constant-loss
base cases `Peluse54S`/`Peluse55S` (the `s = 1, 2` instances of `caseS`): whichever way those land,
the step below is the statement that has to be settled for the ladder to close.

**Status.**  The same review finding applies: the paper's induction gives a power of the *observed*
value, `Cθ^k`, and `θ^k ≤ θ` for `θ ≤ 1`, so `caseST` is precisely the sharpening at issue.  It is
recorded here as the target of the constant-loss step, with the state bound explicit, so that the
strengthening is visible on the face of the statement rather than hidden in a docstring. -/
def caseST (s : ℕ) : Prop := by
  classical
  exact
  ∀ (C₁ : ℝ), 0 < C₁ → ∃ A : ℝ, max 8 (C₁ ^ (-(10 ^ 6 : ℝ))) ≤ A ∧ ∃ K : ℕ, 2 ≤ K ∧
    ∃ C : ℝ, 0 < C ∧ ∃ s' : ℕ, 1 ≤ s' ∧
    ∀ (i₀ : Fin s) (c : ℤ), 0 < c →
      ∀ (M₁ M₂ : ℕ) (b : Fin s → ℤ) (γ γ' θ : ℝ) (N : ℕ) (f : ℤ → ℂ),
      2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
      0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 →
      A * γ' ≤ γ ^ K → A ≤ (M₂ : ℝ) * (γ * γ') ^ K →
      (((Finset.Icc 1 M₁).filter (fun a : ℕ =>
          ¬ ((∀ i j : Fin s, i ≠ j →
                ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b j) : ℕ) : ℝ) < 1 / γ')
              ∧ γ' * (M₁ : ℝ) ≤ |((a : ℤ) + b i₀)|))).card : ℝ)
        ≤ C * γ * (M₁ : ℝ) →
      SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      -- the ladder's state bound: the observed value `θ` is sandwiched by `C₁γ^K` and the average
      C₁ * γ ^ K ≤ θ → θ ≤ boxAvgA s c M₁ M₂ b N f →
      C * θ ≤ Work.Peluse.uNorm s' (outWin c γ' M₁ M₂) (Work.Peluse.symIcc N) f

/-- **The constant-loss induction step with the state bound**: `caseST s → caseST (s+1)`. -/
def Peluse51StepST : Prop := ∀ (s : ℕ), 2 ≤ s → caseST s → caseST (s + 1)

/-! ### The quantifier obstacle of the reduction `caseST ⟹ ladderStepQ` (review finding)

The review of `Peluse/LadderQ/LadderStepOfCaseST` found — correctly — that `caseST` (and `caseS`,
and `Peluse51S`) cannot be consumed by `ladderStepQ` as stated, for a reason independent of the
power/constant-loss question:

* the family is `∀ s C₁, ∃ A₀ K₀ C s', (instance at A₀, K₀, C, s')`: the witnesses are chosen *per
  `(s, C₁)`*, before the datum;
* `ladderStepQ` instead has the datum's `A, K, C₁` **universally quantified**, with only
  `max 8 (C₁^{-10^6}) ≤ A` and `2 ≤ K`.  The caller must therefore establish the instance's
  sandwich `A₀γ' ≤ γ^{K₀}`, `A₀ ≤ M₂(γγ')^{K₀}` from the *datum's* `Aγ' ≤ γ^K`,
  `A ≤ M₂(γγ')^K`, and nothing relates `A₀` to `A`: the datum may sit at the minimal allowed
  `A = 8, K = 2` (e.g. `γ = 1`, `γ' = 1/8`, `M₂ = 512`, `C₁ = u = θ = 1`, where both frozen
  inequalities are equalities), while `h` may supply `A₀ = 10⁶`.

**The fix** (to be written as `caseSW (s : ℕ) (A : ℝ) (K : ℕ) (C₁ : ℝ) : Prop`): state the case with
the *datum's own* `A, K, C₁` as **parameters**, i.e.

`∃ C > 0, ∃ s' ≥ 1, ∀ (i₀ : Fin s) (c) … (γ γ' θ) … , (structural) → 0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1
 → A γ' ≤ γ^K → A ≤ M₂(γγ')^K → (exceptional set) → SupportIn → 1-bounded
 → C₁ γ^K ≤ θ → θ ≤ boxAvgA s … → C·θ ≤ uNorm s' (outWin c γ' M₁ M₂) …`

so that the reduction `∀ j, ladderStepQ j` is a *direct application* (the datum's hypotheses match
the instance's hypotheses definitionally, at the same `A, K, C₁`), with only `C` and `s'` new
(witnesses per `(s, A, K, C₁)`).  This is the form in which the constant-loss chain must be
proved — and it is the form the three base cases `Peluse54S/55S` and the step `Peluse51StepST`
should be re-expressed in before the reduction can be assembled. -/

/-- **The constant-loss case at level `s`, with the datum's own constants.**

The review of the reduction `caseST ⟹ ladderStepQ` showed that the existential witnesses `A₀, K₀` of
`caseST` cannot be transferred to the datum's universally quantified `A, K, C₁` (the datum may sit at
the minimal `A = 8`, `K = 2`, while `caseST` may supply `A₀ = 10⁶`).  `caseSW` removes the mismatch:
the sandwich is stated **at the datum's own `A`, `K`, `C₁`**, and the only witnesses are the loss's
constant `C` and the output level `s'`.  The ladder's datum therefore matches the instance's
hypotheses definitionally, and the reduction is a direct application.

The output level `s'` and constant `C` may depend on `(s, A, K, C₁)` — i.e. on the level and on the
datum's normalisation, which is exactly what `ladderStepQ`'s `∃ s' C` (before the datum's `K, A`
quantifiers) permits. -/
def caseSW (s : ℕ) (A : ℝ) (K : ℕ) (C₁ : ℝ) : Prop := by
  classical
  exact
  ∃ C : ℝ, 0 < C ∧ ∃ s' : ℕ, 1 ≤ s' ∧
    ∀ (i₀ : Fin s) (c : ℤ), 0 < c →
      ∀ (M₁ M₂ : ℕ) (b : Fin s → ℤ) (γ γ' θ : ℝ) (N : ℕ) (f : ℤ → ℂ),
      2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
      0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 →
      A * γ' ≤ γ ^ K → A ≤ (M₂ : ℝ) * (γ * γ') ^ K →
      (((Finset.Icc 1 M₁).filter (fun a : ℕ =>
          ¬ ((∀ i j : Fin s, i ≠ j →
                ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b j) : ℕ) : ℝ) < 1 / γ')
              ∧ γ' * (M₁ : ℝ) ≤ |((a : ℤ) + b i₀)|))).card : ℝ)
        ≤ C * γ * (M₁ : ℝ) →
      SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      C₁ * γ ^ K ≤ θ → θ ≤ boxAvgA s c M₁ M₂ b N f →
      C * θ ≤ Work.Peluse.uNorm s' (outWin c γ' M₁ M₂) (Work.Peluse.symIcc N) f

/-! ### The quantifier order forced by `ladderStepQ` (review finding, third round)

The reviews of the reductions `caseST ⟹ ladderStepQ` and `caseSW ⟹ ladderStepQ` pinned the
interface down to a single shape.  `ladderStepQ j` is

`∃ s' C, 1 ≤ s' ∧ 0 < C ∧ C ≤ 1 ∧ ∀ (C₁ A) (K M₂) …, C·u ≤ boxLadderNorm j (n+s') …`

— the witnesses `s', C` are quantified **before** the datum's constants `C₁, A, K, M₂`, hence must
be **uniform in the datum**.  Therefore:

* the case family must have its witnesses at the **outer** level too, i.e.

  `caseSU s : Prop := ∃ C > 0, ∃ s' ≥ 1, ∀ (A : ℝ) (K : ℕ) (C₁ : ℝ), 8 ≤ A → 2 ≤ K → 0 < C₁ →
     (the data list with the sandwich **at the datum's own `A, K`** and the state bound
      `C₁γ^K ≤ θ ≤ boxAvgA s …`) → C·θ ≤ uNorm s' (outWin c γ' M₁ M₂) (symIcc N) f`

  (in particular *no* `max 8 (C₁^{-10^6}) ≤ A` hypothesis: the uniformity in `C₁` is what
  `ladderStepQ` needs, and it is the datum's own floor that the ladder's hypotheses carry);
* the ladder's slot data must be matched by the case's: the ladder's short window is
  `L = ⌊γ'M₂⌋` and its long window `D'' = ⌊γ'²M₁M₂⌋ = ⌊γ'M₁L⌋`, so the case is applied with its
  `M₂ := L` and its own `γ'` (the ladder's `γ'`), whose output window `⌊γ'M₁L⌋` is `D''` — the
  slot sets then coincide up to the floor;
* the `s'` of the case gives the ladder's output level `n + s'`, and the level raise to
  `max (n+s') 2` is supplied downstream by `Work.Peluse.LadderB.uNorm_le_uNorm_max_two`.

With `caseSU` (or any family with the same outer quantification) the reduction is a direct
application: `h (j+1)`, then the datum's `C₁, A, K, M₂` instantiate the `∀`-binders.  Nothing else
is needed from `caseS`/`caseST`/`caseSW`, which are recorded here only as the (incorrect for this
purpose) earlier shapes; the four delegated statements `Peluse54S`, `Peluse55S`, `Peluse51StepS`,
`Peluse51StepST` should be reformulated in the `caseSU` shape before the reduction is assembled. -/

/-- **The case family in the shape `ladderStepQ` can consume.**  This is the interface pinned by the
three reviews recorded above: the witnesses `C, s'` are quantified **before** the datum's constants
`A, K, C₁` (so they are uniform in the datum, matching `ladderStepQ`'s `∃ s' C` before `∀ C₁ A K`),
the sandwich is stated **at the datum's own `A, K`**, and the loss's base is the observed value `θ`,
sandwiched by `C₁γ^K ≤ θ ≤ boxAvgA s …`.

The only floor hypotheses on the datum's constants are `8 ≤ A`, `2 ≤ K`, `1 ≤ C₁`, which
`ladderStepQ` provides (its hypothesis is `max 8 (C₁^{-10^6}) ≤ A`, and `C₁ > 0` with the ladder's
assembly choosing `C₁ ≥ 1`); in particular there is no `max 8 (C₁^{-10^6}) ≤ A` hypothesis here, since
the uniformity in `C₁` is exactly what the ladder needs.

The conclusion is stated at the window `outWin c γ' M₁ M₂ = c[⌊γ'M₁M₂⌋]`; in the reduction the case
is applied with `M₂ := L = ⌊γ'M₂⌋` and the ladder's own `γ'`, so that
`⌊γ'M₁L⌋ = ⌊γ'²M₁M₂⌋ = D''`.  The level raise from `s'` to the ladder's level
`2^j-1+n+s'` is *not* part of the case: it is supplied by the slot monotonicity
(`Concat.boxNormPow_succ_ge_general`) together with `uNorm_le_uNorm_max_two`. -/
def caseSU (s : ℕ) : Prop := by
  classical
  exact
  ∃ C : ℝ, 0 < C ∧ ∃ s' : ℕ, 1 ≤ s' ∧
    ∀ (A : ℝ) (K : ℕ) (C₁ : ℝ), 8 ≤ A → 2 ≤ K → 0 < C₁ →
      ∀ (i₀ : Fin s) (c : ℤ), 0 < c →
        ∀ (M₁ M₂ : ℕ) (b : Fin s → ℤ) (γ γ' θ : ℝ) (N : ℕ) (f : ℤ → ℂ),
        2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 →
        A * γ' ≤ γ ^ K → A ≤ (M₂ : ℝ) * (γ * γ') ^ K →
        (((Finset.Icc 1 M₁).filter (fun a : ℕ =>
            ¬ ((∀ i j : Fin s, i ≠ j →
                  ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b j) : ℕ) : ℝ) < 1 / γ')
                ∧ γ' * (M₁ : ℝ) ≤ |((a : ℤ) + b i₀)|))).card : ℝ)
          ≤ C * γ * (M₁ : ℝ) →
        SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        C₁ * γ ^ K ≤ θ → θ ≤ boxAvgA s c M₁ M₂ b N f →
        C * θ ≤ Work.Peluse.uNorm s' (outWin c γ' M₁ M₂) (Work.Peluse.symIcc N) f

/-- **The induction step in the `caseSU` shape** (witnesses at the outer level, per `s` only). -/
def CaseSUStep : Prop := ∀ (s : ℕ), 2 ≤ s → caseSU s → caseSU (s + 1)

/-- **The `caseSU` interface with the output level forced to `s' ≥ 3`.**

The review of `CaseSU1` recorded why this is the right existential: the comb `1_{qℤ}` has
`boxAvgA ≈ m(q)/q` while `uNorm s' (arithIcc c D) ≈ q^{-(s'+1)/2^{s'}}` (with `m(q) = ∏_{p|q}(1+1/p-1/p²)`),
which refutes `s' ∈ {1,2}` but not `s' ≥ 3`.  Baking the bound into the statement (rather than
leaving the prover to discover it) makes the target for the fleet unambiguous.

The ladder has no constraint on `s'` other than `1 ≤ s'` (the output level is `n+s'`, and the level
raise to `max (n+s') 2` is supplied downstream by `uNorm_le_uNorm_max_two`), so using `s' ≥ 3` here
costs nothing for the consumer. -/
def caseSU3 (s : ℕ) : Prop := by
  classical
  exact
  ∃ C : ℝ, 0 < C ∧ ∃ s' : ℕ, 3 ≤ s' ∧
    ∀ (A : ℝ) (K : ℕ) (C₁ : ℝ), 8 ≤ A → 2 ≤ K → 0 < C₁ →
      ∀ (i₀ : Fin s) (c : ℤ), 0 < c →
        ∀ (M₁ M₂ : ℕ) (b : Fin s → ℤ) (γ γ' θ : ℝ) (N : ℕ) (f : ℤ → ℂ),
        2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 →
        A * γ' ≤ γ ^ K → A ≤ (M₂ : ℝ) * (γ * γ') ^ K →
        (((Finset.Icc 1 M₁).filter (fun a : ℕ =>
            ¬ ((∀ i j : Fin s, i ≠ j →
                  ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b j) : ℕ) : ℝ) < 1 / γ')
                ∧ γ' * (M₁ : ℝ) ≤ |((a : ℤ) + b i₀)|))).card : ℝ)
          ≤ C * γ * (M₁ : ℝ) →
        SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        C₁ * γ ^ K ≤ θ → θ ≤ boxAvgA s c M₁ M₂ b N f →
        C * θ ≤ Work.Peluse.uNorm s' (outWin c γ' M₁ M₂) (Work.Peluse.symIcc N) f

/-- `caseSU3` is stronger than `caseSU` (only the witness bound `1 ≤ s'` vs `3 ≤ s'` differs). -/
theorem caseSU_of_caseSU3 (s : ℕ) (h : caseSU3 s) : caseSU s := by
  rcases h with ⟨C, hC, s', hs', H⟩
  exact ⟨C, hC, s', by omega, H⟩

/-- **The induction step in the `caseSU3` shape** (witnesses at the outer level, per `s` only). -/
def CaseSUStep3 : Prop := ∀ (s : ℕ), 2 ≤ s → caseSU3 s → caseSU3 (s + 1)

/-! **The `C₁` floor: `0 < C₁`, not `1 ≤ C₁`.**

The review of `Peluse/LadderQ/LadderStepOfCaseSU` found that `caseSU`/`caseSU3` as first stated
required `1 ≤ C₁`, while `ladderStepQ` only assumes `0 < C₁` (its hypothesis is
`max 8 (C₁^{-10^6}) ≤ A`, which is monotone in `C₁` but says nothing at `C₁ < 1`).  The regime
`C₁γ^K ≤ boxLadderNorm (j+1) < γ^K` is realisable (`C₁ = 1/2`, `A ≥ 2^{10^6}`, `γ = 1`, with the
frozen conditions satisfiable), and `ladderStepQ`'s conclusion is a state-to-state ratio there, so
the floor had to be removed.  Both `caseSU` and `caseSU3` now quantify `∀ A K C₁, 8 ≤ A → 2 ≤ K →
0 < C₁ → …`. -/

/-! ## The peel: proof recipe for `Peluse/LadderQ/LadderStepOfCaseSU`

The reduction `(∀ s ≥ 1, caseSU3 s) → ∀ j, ladderStepQ j` is the paper's proof of Lemma 5.6, in five
steps.  The first half of each step is a pigeonhole (an average bounds its own max, or its own
average over a sub-ensemble), so every step is *lossless up to an absolute constant*:

1. **Unfold the state.**  `ladderStepQ`'s hypothesis gives `u ≤ boxLadderNorm (j+1) n M₁ c
   (omegaOf (j+1)) L D'' N f`, an average over `(h,h') ∈ [M₁]^{j+1}` of the level-`(2^{j+1}-1+n)`
   box **norms** at the slots `ladderSlots`.  Pigeonhole once: some `(h,h')` has norm
   `≥ u` (hence `≥ C₁γ^K`).
2. **Peel the `n` long slots** (`Work.Peluse.BoxNormDilation.boxNormPow_succ_peel`): the
   level-`(t+1)` **pow** with a last slot `Q` is the average over `(h_s,h_s') ∈ Q²` of the level-`t`
   pows of `Δ'_{(h_s,h_s')}f`.  Pigeonhole once per long slot, converting norm-bounds to pow-bounds
   through `x ↦ x^{2^t}` (Jensen, constant loss), ending with `s = j+1` short slots at level `s` of a
   single `g := Δ'_{long shifts}f`.
3. **Match the short-slot family to the case's `(a,b_ω)` family.**  With `a := h_{j+1}` (the
   singled-out coordinate) and `b_ω := -h'_{j+1} + (h₁-h₁',…,h_j-h_j')·ω`, one has
   `c(a + b_ω)[L] = c(ω·(h-h'))[L]` for every nonzero sign pattern `ω ∈ {0,1}^{j+1}` — that is
   exactly the ladder's short slots.  Apply the case at `s := j+1`, `M₂ := L = ⌊γ'M₂⌋`, the ladder's
   own `γ'` (so `outWin c γ' M₁ L = c[⌊γ'M₁L⌋] = c[⌊γ'²M₁M₂⌋] = c[D'']`), `A, K, C₁` the datum's, and
   `θ` the observed `(a,b_ω)`-average.
4. **The exceptional set** (gcd and `|a+b i₀|` conditions) comes from Lemma 5.2, i.e. the tree's
   `Work.Peluse.Concat.cardBadPairs` / `badPairsBound`, applied to the `h_{j+1}`-average; the state
   bound `C₁γ^K ≤ θ` comes from step 1 (the same pigeonhole that produced `u`).
5. **Conclusion.**  The case gives `C·θ ≤ uNorm s' (c[D'']) (symIcc N) g'`.  The ladder's output
   family is a **super-multiset** of the case's (the same `s'` long slots plus the `2^j-1` short ones
   and the `n` long ones), and `Work.Peluse.Concat.boxNormPow_succ_ge_general` says that adding a
   slot raises the norm up to a constant factor; so `boxLadderNorm j (n+s') ≥ c·uNorm s'` up to
   constants, and `u ≤ θ` closes the argument.  The level raise to `max (n+s') 2` is downstream
   (`Work.Peluse.LadderB.uNorm_le_uNorm_max_two`).

Nothing here needs any of the base cases: the recipe consumes the *family* `∀ s ≥ 1, caseSU3 s`,
which `CaseSUGlue` produces from `caseSU3 1` + `caseSU3 2` + `CaseSUStep3`. -/

/-! ### Verified dependency map for the peel (names and locations, checked in this workspace)

| step | tool | module |
|---|---|---|
| 2 (peel a slot) | `Work.Peluse.boxNormPow_succ_peel` | `Ulower/rankInduction.lean`, `BoxNormDilation/dilated_directions_ge.lean` |
| 2, 5 (add a slot / raise the level) | `Concat.boxNormPow_succ_ge_general` | `Concat/boxNormPow_succ_ge_general.lean` |
| 5 (level raise at the end) | `Work.Peluse.LadderB.uNorm_le_uNorm_max_two` | `concatBridgeShortA.lean` |
| 4 (gcd/size exceptional set) | `Concat.cardBadPairs`, `Concat.badPairsBound` | `Concat/cardBadPairs.lean`, `Concat/badPairsBound.lean` |
| 5 (window shrink, if needed) | `Concat.arithIcc_shrink_ge_two` | `Concat/arithIcc_shrink_ge_two.lean` |
| 1 (state unfolding) | `Work.Peluse.LadderB.boxLadderNorm_zero` | `LadderB/ladderStepQZero.lean` |
| norms ↔ pows | `Work.Peluse.LadderB.boxLadder_le_norm` | `LadderB/boxLadder_le_norm.lean` |
| phase/invariance bounds | `Work.Peluse.uNormPow_arithIcc_phase_ge` | `BoxNorm/uNormPow_arithIcc_phase_ge2.lean` |

So the peel needs no new library: every ingredient is already proved in the tree.  What remains is
the assembly of the five steps, the pigeonholes included. -/

/-! ### Constant bookkeeping for `Peluse/LadderQ/LadderNormGeUNorm` (step 5, exactly)

Let `m := 2^j - 1 + n` (the number of slots the ladder's state has *beyond* the case's `s'` long
windows) and `t := m + s'` (the ladder's level).  `boxNormPow_succ_ge_general` says, for any family
and any last slot, `c·boxNormPow (t-1)(family minus last)² ≤ boxNormPow t (family)`; with its
constant `1/2`, one removal gives

`boxNormPow (t-1) ≤ (2 · boxNormPow t)^{1/2}`.

Iterating `m` times (each time permuting the next slot to be removed to the end, via
`BoxNorm.boxNormPow_perm`) and using `1 + 1/2 + … + 1/2^{m-1} < 2`:

`boxNormPow s' ≤ 2^{2 - 2^{1-m}} · (boxNormPow t)^{1/2^m} ≤ 4 · (boxNormPow t)^{1/2^m}`.

Since `t - m = s'`, `(boxNormPow t)^{1/2^m} = boxNorm (t)^{2^t/2^m} = boxNorm(t)^{2^{s'}}`, so taking
`2^{s'}`-th roots gives **`boxNorm s' ≤ 4^{1/2^{s'}} · boxNorm t ≤ 4 · boxNorm t`** — a uniform
constant, independent of `j`, `n`, `s'`.  Averaging over `(h,h')` and using
`‖f‖ ≤ 1` (so `boxNorm ≤ 1`) finishes `LadderNormGeUNorm` with `C = 1/4`:
`boxNorm s' (c[D'']) ≤ 4·boxNorm t (ladderSlots)`, hence `C·uNorm s' ≤ boxLadderNorm j (n+s')`.

The exponent identity `2^t / 2^m = 2^{t-m} = 2^{s'}` is where the level bookkeeping is exact; the
`1 ≤ L` hypothesis of `LadderNormGeUNorm` is what keeps the short slots nonempty (the reviewer's
`L = 0` counterexample). -/

/-! ## DECISIVE FINDING: the `caseS`/`caseSU`/`caseSU3` route is dead (L6201, L6200, 2026-10-03)

The prover of `Peluse51StepSTThm` refuted the whole case family by an argument that no amount of
`s' ≥ 3` or witness-tying repairs:

> `caseST n` bounds the level-`n` box average `boxAvgA n c M₁ M₂ b N f` — direction sets
> `(c(a+b_i))[M₂]` of **fixed length `M₂`**, averaged over `a ∈ [M₁]` — from below by `θ`, and
> demands `C·θ ≤ uNorm s' (c[⌊γ'M₁M₂⌋])`, a uniformity norm whose **direction length is
> `D = ⌊γ'M₁M₂⌋`, proportional to the averaging parameter `M₁`**, while the box average does not
> depend on `M₁` at all.  The sandwich gives only *lower* bounds (`M₂ ≥ A^{K+1}/γ^{K(K+1)}`,
> `γ' ≤ min(γ^K/A, Cγ)`) and never bounds `M₁M₂` from above, so the statement is decided by the
> unbounded `M₁`, on which the two sides scale differently.

Concretely (their family): `c = 1`, `b i = i`, `f` the chirp `e(x^{s'+1}/(q(s'+1)!))` (prime `q`,
`|f| = 1` on `symIcc N`), `M₂` large enough for `A ≤ M₂(γγ')^K`, and then `M₁ → ∞` with `M₂, N, q`
fixed: the hypothesis's average stays `≥ θ`, the conclusion's norm decays.  All hypotheses of
`caseST n` (and of `caseS`/`caseSW`/`caseSU`/`caseSU3`, which differ only in the witness order, the
`C₁` floor, the level of `s'`, and the state-bound bookkeeping) hold; the conclusion fails.

**Consequence for this lane.**  The (a,b)-form with a *fixed* direction length `M₂` is strictly
weaker than — and not equivalent to — the ladder's state, and it is false with a constant loss.  So
the route `caseSU3 → LadderStepOfCaseSU → ladderStepQ` cannot work: the middle statements are
refuted.  What must replace it is the step in the **ladder's own normalisation** — i.e. Peluse's
Lemma 5.6, whose hypothesis already carries *both* scales: the short slots `c((h-h')·ω)[L]` (window
`L`, dilations up to `(j+1)M₁`) *and* the `n` long slots `c[D'']`, averaged over
`(h,h') ∈ [M₁]^{j+1}`.  That is exactly `ladderStepQ`'s hypothesis, and the constant-loss question
for it is the one the numerical sweep in `LadderB/ladderStepQFinal.lean` §3 probes (every
threshold-reaching family had `B₀/B₁ ≥ 0.8`): the D′′-slots and the level `2^{j+1}-1+n` are what
make the ladder's statement different in kind from the refuted case family, not merely stronger in
its constants.

`LadderNormGeUNorm`, `LadderStatePigeonhole` and the peel recipe remain valid as *pieces* of the
ladder step (they are statements about `boxLadderNorm` and its slots only); it is the intermediate
(a,b)-form bridge that has to be dropped. -/

/-! ## H1 corrected: the peel removes the **first** coordinate (needs the permutation)

Checked in source this session, because the first two guesses were wrong and a mis-stated H1 would
have cost a child:

* `Work.Peluse.Peel.boxSumPow_peel` (`Submission/Work/Peluse/Peel/boxSumPow_peel.lean:132`) is the
  **general-family** peel (any `Q : Fin (t+1) → Finset ℤ`):

  `boxSumPow (t+1) Q S f = |Q 0|⁻² · ∑_{h,h' ∈ Q 0} boxSumPow t (fun i => Q i.succ) S
      (fun u => f (u+h) * star (f (u+h')))`,

  i.e. it peels the **first** slot and the differenced function is `conj ∘ DeltaP h h'`
  (`Basic.lean:65`: `DeltaP h h' f u = star (f (u+h)) * f (u+h')` — same modulus, hence the same
  box-norm powers);
* `Work.Peluse.BoxNormDilation.boxNormPow_succ_peel` (`dilated_directions_ge.lean:108`) is only the
  **uniform-family** specialisation (`fun _ => A`), and there is *no* second copy of it in
  `Ulower/rankInduction.lean` (grep found none), so the general form to use is `boxSumPow_peel`
  together with `Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow` to pass to powers;
* the ladder's long slots `arithIcc c D''` are the **trailing** `n` slots of
  `ladderSlots (j+1) n …` (the `if i < 2^j - 1` branch puts the short ones first), so peeling them
  requires `Work.Peluse.BoxNorm.boxNormPow_perm` to move one long slot to the front at each step.

So H1 is: `n` iterations of *(permute a trailing long slot to the front, apply `boxSumPow_peel`,
pass to powers via `boxSumPow_eq_boxNormPow`)*, starting from the single `(a,b)`-term that
`LadderStatePigeonhole` extracts, ending with a single `Δ'`-composite `g` and a lower bound
(constant loss `2^{2-2^{1-n}} ≤ 4`) on `boxNormPow (2^{j+1}-1) (the short slots) (symIcc N) g`.
H2 is then `rfl` against `ladderSlots (j+1) 0 …` at the same `(a,b)`; H3 is L6212 + the level
bookkeeping already recorded. -/

/-! ## H1: the exact algebraic shape to type in (one long slot at a time)

From `LadderStatePigeonhole` one gets a single `(a,b) : (Fin (j+1) → Fin M₁)²` with
`u ≤ boxNorm (2^(j+1)-1+n) Q_{a,b} (symIcc N) f`, `Q_{a,b} := ladderSlots (j+1) n M₁ c (omegaOf (j+1)) L D'' a b`.

**One peel step** (`t := 2^(j+1) - 1 + n`, the current level).  With `P := boxNormPow`:

1. norm → pow: `boxNorm t Q = P t Q ^ (1/2^t)`, so `u^(2^t) ≤ P t Q`;
2. permute a *trailing* long slot `arithIcc c D''` to the front (`BoxNorm.boxNormPow_perm`), giving
   `Q'` with `Q' 0 = arithIcc c D''` and `P t Q = P t Q'`;
3. peel the first coordinate (`Peel.boxSumPow_peel` + `BoxNorm.boxSumPow_eq_boxNormPow`):
   `P t Q' = |Q' 0|⁻² · ∑_{h,h' ∈ Q' 0} P (t-1) (fun i => Q' i.succ) (fun x => f (x+h) * star (f (x+h')))`,
   and the differenced function has the same modulus as `DeltaP h h' f` (`Basic.lean:65`), hence the
   same box-norm powers;
4. pigeonhole the average (`0 < |Q' 0|`, as `1 ≤ D''`): there are `h h' ∈ arithIcc c D''` with
   `u^(2^t) ≤ P (t-1) (fun i => Q' i.succ) (Δ'_{h,h'} f)`.

So each step trades one long slot for one `Δ'` and squares the exponent on the left: after `n` steps,

  `u ^ (2^t) ≤ P (2^(j+1)-1) (fun i => arithIcc (c * dotZ (omegaOf (j+1) i) (tupSub a b)) L)
                        (symIcc N) (the iterated Δ'-composite g)` with `t = 2^(j+1)-1+n`,

**no constant lost at all** in this direction (the peel is an identity, the pigeonholes are
lossless).  That is H1; its `n`-fold iteration is what needs the bookkeeping, and the composite `g`
is best introduced by its own `def` (a fold over `Fin n → ℤ × ℤ`) so that the induction has a name
to induct on.

H2 (`rfl`): the family shown above is literally `ladderSlots (j+1) 0 M₁ c (omegaOf (j+1)) L D'' a b`.
H3: `LadderNormGeUNorm` (L6212) + the `t - m = s'` level bookkeeping already recorded. -/

/-! ## The composite `g` of H1: the iterated `Δ'` -/

/-- The iterated difference `Δ'_{(h₁,h₁')} ∘ ⋯ ∘ Δ'_{(hₙ,hₙ')}` built by the peel of H1: `l` is
processed **front first**, and each step pre-composes the current function with
`u ↦ f (u + p.1) * star (f (u + p.2))` — the exact shape produced by
`Work.Peluse.Peel.boxSumPow_peel` (whose differenced function is `conj ∘ DeltaP`, same modulus).
So `iterDeltaP l f` is the function whose level-`(2^(j+1)-1)` pow H1 lands on after peeling `l.length`
long slots, and `l` is the list of the `(h,h')` pairs produced by the successive pigeonholes. -/
def iterDeltaP : List (ℤ × ℤ) → (ℤ → ℂ) → (ℤ → ℂ)
  | [], f => f
  | p :: ps, f => iterDeltaP ps (fun x : ℤ => f (x + p.1) * star (f (x + p.2)))

@[simp] lemma iterDeltaP_nil (f : ℤ → ℂ) : iterDeltaP [] f = f := rfl

@[simp] lemma iterDeltaP_cons (p : ℤ × ℤ) (ps : List (ℤ × ℤ)) (f : ℤ → ℂ) :
    iterDeltaP (p :: ps) f = iterDeltaP ps (fun x : ℤ => f (x + p.1) * star (f (x + p.2))) := rfl

/-- The iterated `Δ'` preserves the unit bound: the peel of H1 needs this at every step, since
`boxSumPow_peel`'s differenced function has the modulus `‖f (u + p.1)‖ * ‖f (u + p.2)‖`. -/
lemma iterDeltaP_norm_le_one (l : List (ℤ × ℤ)) (f : ℤ → ℂ) (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    ∀ x : ℤ, ‖iterDeltaP l f x‖ ≤ 1 := by
  induction l generalizing f with
  | nil => simpa using hb
  | cons p ps ih =>
    intro x
    rw [iterDeltaP_cons]
    refine ih _ (fun y => ?_) x
    rw [norm_mul, norm_star]
    calc ‖f (y + p.1)‖ * ‖f (y + p.2)‖ ≤ 1 * 1 :=
          mul_le_mul (hb _) (hb _) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

/-! ## H2: with no long slots the ladder's family *is* the short-slot family -/

/-- **H2.**  With `n = 0` every index of `Fin (2^j - 1)` satisfies `i < 2^j - 1`, so the
`arithIcc c D''` branch of `ladderSlots` is unreachable and the family is exactly the short-slot
family `i ↦ arithIcc (c * dotZ (ωOf i) (tupSub a b)) L` at the same `(a, b)`.  This is the family
H1's peel leaves behind after removing the long slots. -/
lemma ladderSlots_zero (j M₁ : ℕ) (c : ℤ) (ωOf : Fin (2 ^ j - 1) → (Fin j → Bool))
    (L D'' : ℕ) (a b : Fin j → Fin M₁) :
    Work.Peluse.Holds.ladderSlots j 0 M₁ c ωOf L D'' a b
      = fun i : Fin (2 ^ j - 1 + 0) =>
          Work.Peluse.arithIcc
            (c * Work.Peluse.Concat.dotZ (ωOf (Fin.cast (Nat.add_zero (2 ^ j - 1)).symm i))
              (Work.Peluse.Concat.tupSub a b)) L := by
  funext i
  have hp : (i : ℕ) < 2 ^ j - 1 := by
    have h := i.isLt; simpa using h
  rw [Work.Peluse.Holds.ladderSlots, dif_pos hp]
  congr 2

/-! ## FINDING (bug class): weakening a hypothesis to match a consumer can make a statement vacuous

Recorded as a result, for every lane in this workspace, because it is easy to repeat and hard to see.

**The instance.**  The reviewer of the reduction `LadderStepOfCaseSU` correctly observed that `caseSU`
required `1 ≤ C₁` while `ladderStepQ` only provides `0 < C₁`, and offered two repairs: drop the floor,
or add the missing bridge.  I dropped the floor — and the statement became **vacuous**:

> with only `0 < C₁`, any datum with `boxAvgA > 0` may take `C₁ := boxAvgA/(2γ^K) > 0` and
> `θ := boxAvgA`, so `C₁γ^K = boxAvgA/2 ≤ θ ≤ boxAvgA` holds trivially.  The two-sided state bound
> adds nothing and the statement degenerates into the *unconditional* constant-loss inequality
> `C·boxAvgA ≤ uNorm s' (outWin c γ' M₁ M₂)`, which is false — the pseudo-random family.

(caught by the prover of `CaseSU3One`; the same refutation is already on disk at
`NOTES_ladderStepQZero_SESSION.md` §7.)

**The class.**  A hypothesis whose *content* is a lower bound on a free parameter is destroyed by
allowing that parameter to be chosen from the data side.  Here the state bound `C₁γ^K ≤ θ` is content
only if `C₁` is bounded **below**; that bound is supplied by the datum's `max 8 (C₁^{-10^6}) ≤ A`,
which for `A ≥ 8` forces `C₁ ≥ 8^{-10^{-6}}`.  Dropping the floor (or, in general, moving the
non-degeneracy constant from the *statement* into the *data*) removes the content while leaving the
syntax intact, so no type error, no review of shape, and no build failure flags it: the symptom is
**vacuity**, which shows up only as a false-looking *unconditional* corollary.

**The distinguisher, which is why the ladder is unaffected.**  In `ladderStepQ` the datum brings both
`max 8 (C₁^{-10^6}) ≤ A` *and* `A ≤ M₂(γγ')^K`; eliminating gives
`B_{j+1} ≥ C₁γ^K ≥ γ^K (2L^{1/K}γ^K)^{-10^{-6}}`, which at minimal `γ^K = 8(2L)^{-1/K}` is
`≈ 8·2^{-1/K}L^{-1/K}` (`5.66/√L` at `K = 2`).  So in the ladder the state bound is *not* vacuous, the
threshold is real, and the numerical sweep's verdict stands (the pseudo-random and chirp families sit
at or below the threshold; every threshold-reaching family had `B₀/B₁ ≥ 0.8`).

**Summary of the three independent refutations of the fixed-window `(a,b)` family** (all recorded):
(i) unbounded-`M₁` chirp scaling (L6201: the hypothesis's direction length `M₂` is fixed while the
conclusion's `⌊γ'M₁M₂⌋` grows with `M₁`);  (ii) multiplicative-lag set vs additive window — the
workspace's shared wall, with the known forms `Concat.ConcatDilationSq` and
`Concat.concatLevelOneSqDilation` already refuted (L6195);  (iii) vacuity of the state bound with a
free `C₁` (L6208).  None of the three reaches `ladderStepQ`. -/

/-! ## Fourth obstruction (L6207) and the one negative that matters

**Obstruction 4 (slot matching).**  Even granting the whole case family, the reduction to
`ladderStepQ` cannot be built: the only tools moving between box norms (`Peel.boxSumPow_peel`,
`Concat.boxNormPow_succ_ge_general`, the window shrinks) relate the case's box norms to the ladder's
only when the case's slot sets are *subsets* of the surviving ladder slots, which forces
`M₂^{case} ≤ L = ⌊γ'M₂⌋`.  Matching into the long slots instead constrains
`M₂^{case}(a + b i) ≤ D''` for every `a` in the averaging range, and together with the
conclusion-side requirement `⌊γ'^{case}M₁^{case}M₂^{case}⌋ ≥ D''` this forces `γ'^{case} ≥ 1`, hence
`A^{case} ≤ 1 < 8` — contradicting the case's own hypothesis.  So the fixed-window case family is not
merely false (obstructions 1–3): it is *uninstantiable* on the ladder's data.

**The negative that matters.**  L6207 states explicitly: *"I have no counterexample to `ladderStepQ`
itself."*  Combined with L6195, L6200, L6201, L6207 and L6208 — five independent experts, each
attacking the neighbourhood of this target — the record is:

* four independent obstructions kill every *bridge* from a fixed-direction-length `(a,b)`-form to
  `ladderStepQ`: unbounded-`M₁` scaling, the multiplicative-vs-additive lag wall, the vacuity of the
  state bound with a free `C₁`, and slot matching;
* **no refutation of `ladderStepQ` itself has appeared**, and the positive evidence is the threshold
  `≈ 8·2^{-1/K}L^{-1/K}` (`5.66/√L` at `K = 2`, derived from `max 8 (C₁^{-10^6}) ≤ A` *together with*
  `A ≤ M₂(γγ')^K`, which is what pins `C₁` off zero) with every refuting family sitting at or below
  it and every threshold-reaching family at `B₀/B₁ ≥ 0.8`.

That asymmetry — four dead bridges, no dead target — is the sharpest statement this session can make
about `ladderStepQ`, and it is the reason the lane ends open rather than closed as false. -/

/-! ## Step 4 landed — in a REPAIRED form; use `LadderNormGeUNorm_of_one_le_s'`, not `LadderNormGeUNorm`

The prover of L6212 found a machine-checked counterexample to the statement as I wrote it — the edge
case `s' = 0, D'' = 0` with `j = 0, n = 1, M₁ = c = L = N = 1`, `f = 1_{0}`: with `D'' = 0` every slot
`arithIcc c 0 = ∅` is empty so `boxLadderNorm 0 1 1 1 (omegaOf 0) 1 0 1 f = 0` for every `f`, while
`uNorm 0 ∅ (symIcc 1) f = 1/3` (the level-zero box norm is the normalised mean and ignores the
direction family), so the conclusion would force `C ≤ 0`.  The hypotheses `1 ≤ M₁, 1 ≤ L, 1 ≤ N` and
the (vacuous, since `D'' = 0`) bound `hQ` do not exclude that datum.

**Three repairs, all PROVED sorry-free and axiom-clean in
`Submission/Work/Peluse/LadderQ/LadderNormGeUNorm.lean`:**

* `Work.Peluse.LadderQ.LadderNormGeUNorm_of_one_le_s'` — the statement plus `1 ≤ s'`.  **This is the
  one the peel recipe consumes** (the output level comes from the case witnesses, which are `≥ 1`,
  chosen `≥ 3` by `caseSU3`); use this name in step 4, not the un-repaired `LadderNormGeUNorm`.
* `Work.Peluse.LadderQ.LadderNormGeUNorm_of_one_le_D''` — plus `1 ≤ D''`, uniform, no case split.
* `Work.Peluse.LadderQ.LadderNormGeUNorm_of_nonempty` — plus `1 ≤ s' ∨ 1 ≤ D''`.

Their constant is `2^{-(2^j-1+n)}`, which is *per-`j`* — and that is fine for this lane, since
`ladderStepQ j`'s `∃ C` is quantified before the datum and may depend on `j`.

With step 4 landed in this form, **every piece of the peel is proved**: entry pigeonhole (L6213),
step lemma (L6216), family identification (H2, `ladderSlots_zero`), composite + unit bound
(`iterDeltaP_norm_le_one`), and this conclusion half.  What remains is the `n`-fold induction on
`iterDeltaP` that assembles them — bookkeeping over five proved pieces, with the `C = 1/4` (or
`2^{-(2^j-1+n)}`) level bookkeeping exact because `t - m = s'`. -/

/-! ## The peeled-family reindexing: the last piece before the induction -/

/-- **`LadderSlotsPeelLong`.**  One long slot brought to the front of the ladder's family and dropped
leaves the ladder's family with one fewer long slot: `ladderSlots (j+1) (k+1) …` restricted along
`Fin.castSucc` (i.e. dropping its *last* index, which is a long slot) *is* `ladderSlots (j+1) k …`.
The short slots (`m < 2^(j+1)-1`) are unaffected because `Fin.castSucc` fixes them, and the long ones
go to `arithIcc c D''` on both sides.  This is the general-`k` sibling of `ladderSlots_zero`, which is
its `k = 0` case, and it is the only bookkeeping the `n`-fold induction on `iterDeltaP` needs. -/
theorem ladderSlots_peel_long (j k M₁ : ℕ) (c : ℤ) (L D'' : ℕ) (a b : Fin (j+1) → Fin M₁) :
    (fun m : Fin (2 ^ (j+1) - 1 + k) =>
        Work.Peluse.Holds.ladderSlots (j+1) (k+1) M₁ c (Work.Peluse.Holds.omegaOf (j+1)) L D'' a b
          (Fin.castSucc m))
      = Work.Peluse.Holds.ladderSlots (j+1) k M₁ c (Work.Peluse.Holds.omegaOf (j+1)) L D'' a b := by
  funext m
  by_cases hm : (m : ℕ) < 2 ^ (j+1) - 1
  · have hm' : ((Fin.castSucc m : Fin (2 ^ (j+1) - 1 + (k+1))) : ℕ) < 2 ^ (j+1) - 1 := by
      simpa using hm
    rw [Work.Peluse.Holds.ladderSlots, dif_pos hm', Work.Peluse.Holds.ladderSlots, dif_pos hm]
    congr 2
  · have hm' : ¬ (((Fin.castSucc m : Fin (2 ^ (j+1) - 1 + (k+1))) : ℕ) < 2 ^ (j+1) - 1) := by
      simpa using hm
    rw [Work.Peluse.Holds.ladderSlots, dif_neg hm', Work.Peluse.Holds.ladderSlots, dif_neg hm]

/-! ## The invariant of the `n`-fold peel (the induction's target) -/

/-- **The peel invariant.**  The statement the `n`-fold induction on `iterDeltaP` carries: after
peeling `k = l.length ≤ n` long slots (the pairs recorded in `l`), the `u`-power with the *fixed*
exponent `2^(2^(j+1)-1+n)` dominates the box-norm power at level `2^(j+1)-1+(n-k)` of the
`iterDeltaP l f` composite, at the ladder's family with exactly `n-k` long slots left — the family
that `ladderSlots_peel_long` reindexes and `ladderSlots_zero` recognises at `k = n`.

The exponent on the left never changes (each round is lossless), which is why the invariant is stated
with `u^(2^(2^(j+1)-1+n))` throughout; `2^(2^(j+1)-1+n)` is the value forced by the norm-to-power
conversion at the level the state bound is taken (`LadderStatePigeonhole`).

* base case `k = 0`: `iterDeltaP [] f = f` and the family is the ladder's own — this is exactly the
  output of `LadderStatePigeonhole`, converted through the norm-to-power step;
* step: `boxNormPow_perm` brings a long slot to the front, `BoxNormPowPeelPigeonhole` peels it and
  pigeonholes a witness pair `(i,i')`, `iterDeltaP_cons` records the new composite, and
  `ladderSlots_peel_long` reindexes the surviving family — with `iterDeltaP_norm_le_one` supplying
  the unit bound the next round needs;
* at `k = n`: `ladderSlots_zero` turns the family into the short-slot family, and
  `LadderNormGeUNorm_of_one_le_s'` gives the conclusion, `t - m = s'` producing the constant. -/
def PeelInvariant (j n M₁ : ℕ) (c : ℤ) (L D'' N : ℕ) (f : ℤ → ℂ) (u : ℝ)
    (a b : Fin (j+1) → Fin M₁) (k : ℕ) (l : List (ℤ × ℤ)) : Prop :=
  l.length = k ∧ k ≤ n ∧
    u ^ (2 ^ (2 ^ (j+1) - 1 + n)) ≤
      Work.Peluse.boxNormPow (2 ^ (j+1) - 1 + (n - k))
        (Work.Peluse.Holds.ladderSlots (j+1) (n - k) M₁ c (Work.Peluse.Holds.omegaOf (j+1)) L D'' a b)
        (Work.Peluse.symIcc N) (iterDeltaP l f)

end

end Work.Peluse.LadderQ
