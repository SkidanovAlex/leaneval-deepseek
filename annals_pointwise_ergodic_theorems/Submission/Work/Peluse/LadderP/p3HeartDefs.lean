import Mathlib
import Submission.Work.Peluse.LadderP.p3Vocab

/-! # P3: the `c = 1` heart of the induction step (definitions)

This module names the ingredient of the reduction of the frozen **induction step**
`Work.Peluse.LadderP.lemma51P_succ` to its `c = 1` instance with an *arbitrary* window: the analogue
of the P2 lane's `p2BoxAvg` / `p2Heart` (`Submission/Work/Peluse/LadderP/p2Defs.lean`), one level up.

* `p3BoxAvg s M₁ M₂ b S f` — the averaged level-`s` box norm
  `M₁⁻¹ ∑_{a ∈ [1,M₁]} ‖f‖_{□^s_{((a+b_i)[M₂])_i}(S)}` with an *arbitrary* window (normalisation)
  set `S`; the frozen `LadderQ.boxAvgA s c M₁ M₂ b N` is the case `S = symIcc N` with all the
  direction steps dilated by `c`.

* `p3Heart t` — the level-`(t+1)` statement with `c = 1` and an arbitrary pair of windows: `f` is
  supported in `symIcc N`, `S` is a normalisation window of the same order as `symIcc N`
  (`2N+1 ≤ 4|S|`), and the direction window fits inside the support (`M₁M₂ ≤ N`).  The hypothesis
  scheme is otherwise *literally* the frozen `lemma51P (t+1)`'s with `c` set to `1` and `symIcc N`
  replaced by `S` (both in the averaged box norm and in the conclusion).

The reduction `(∀ t, 2 ≤ t → p3Heart t) ⟹ lemma51P_succ` — the paper's "split `ℤ` into arithmetic
progressions mod `c`" step, exactly as `Work.Peluse.LadderP.lemma51P_two_of_p2Heart` does it at
level `2` — is stated in `Submission/Work/LadderP/lemma51P_succ_of_p3Heart.lean`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- The averaged level-`s` box norm over `a ∈ [1, M₁]` with the undilated direction steps `a + b i`
and an arbitrary normalisation set `S`.  The frozen `LadderQ.boxAvgA s c M₁ M₂ b N` is the case
`S = symIcc N` with the directions dilated by `c` (see `Work.Peluse.LadderP.p3BoxAvg_dilate`). -/
def p3BoxAvg (s : ℕ) (M₁ M₂ : ℕ) (b : Fin s → ℤ) (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  ((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
    Work.Peluse.boxNorm s (fun i : Fin s => Work.Peluse.arithIcc ((a : ℤ) + b i) M₂) S f

/-- **The `c = 1` heart of the induction step at level `t + 1`** (the form the assembly of the
frozen node consumes): the level-`(t+1)` statement of `lemma51P` with the polynomial coefficient
`c = 1` and with an arbitrary normalisation window `S` comparable to `symIcc N`.

`S` is the window produced by the class splitting of `symIcc N` (a residue class mod `c`), where
`2N+1 ≤ 4|S|` says that `S` is of the same order as `symIcc N`; `M₁M₂ ≤ N` is the `c = 1` form of
the frozen direction-window fit `M₁M₂ ≤ N/c`.

The parameter `t` is the level of the *induction hypothesis*: the proof of `p3Heart t` may use
`lemma51P t`, and it concludes the level-`(t+1)` statement (`(t+1)` direction steps `a + b i`). -/
def p3Heart (t : ℕ) : Prop :=
  ∀ B₀ : ℕ, ∃ s' : ℕ, 1 ≤ s' ∧ ∃ e : ℕ, 1 ≤ e ∧ ∃ C : ℝ, 0 < C ∧ C ≤ 1 ∧
  ∀ (M₁ M₂ D N : ℕ) (S : Finset ℤ) (b : Fin (t + 1) → ℤ) (γ η ε : ℝ) (f : ℤ → ℂ),
    2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ D → 1 ≤ N → SupportIn f N →
    (((2 * N + 1 : ℕ) : ℝ) ≤ 4 * ((S.card : ℕ) : ℝ)) →
    ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) →
    (∀ i : Fin (t + 1), |b i| ≤ (B₀ : ℤ) * (M₁ : ℤ)) →
    (∀ x : ℤ, ‖f x‖ ≤ 1) →
    0 < γ → γ ≤ 1 → 0 < η → η ≤ C * γ ^ e → 0 ≤ ε → ε ≤ C * γ ^ e →
    (D : ℝ) ≤ C * (γ * η) ^ e * ((M₁ : ℝ) * (M₂ : ℝ)) →
    ((M₁ : ℝ) * (M₂ : ℝ)) ^ e ≤ C * (γ * η * (D : ℝ)) ^ e * (M₂ : ℝ) →
    (((Finset.Icc 1 M₁).filter (fun a : ℕ => ¬ p3good (t + 1) M₁ b η a)).card : ℝ)
      ≤ ε * (M₁ : ℝ) →
    γ ≤ p3BoxAvg (t + 1) M₁ M₂ b S f →
    C * γ ^ e ≤ Work.Peluse.uNorm s' (Work.Peluse.arithIcc 1 D) S f

end

end Work.Peluse.LadderP
