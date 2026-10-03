import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The transfer `lemma51P 2 → lemma51P 1`: shared definitions

This is the local area (`Work.Peluse.Pel51`, owner: the node `Work.Peluse.ucontrol_of_concat`)
for the proof that **Peluse's Lemma 5.1 at level `1` follows from Lemma 5.1 at level `2`**.

## Why this matters

The frozen ladder (`Submission/Work/Peluse/Holds/LadderP.lean`) has three open leaves,
`LadderP.lemma51P 1` (P1), `LadderP.lemma51P 2` (P2) and `LadderP.lemma51P_succ` (P3), together
with `prop36SW_of_ladderA` (O2).  P1 is the *analytic heart* (Peluse's Lemma 5.4, i.e. the
bilinear-kernel ⟹ `U²` step via the Fourier/Gowers–Cauchy–Schwarz chain), whereas P2 — which is
needed **anyway** — is the `s = 2` concatenation step.  So a proof of `lemma51P 2 → lemma51P 1`
removes P1 from the critical path entirely.

## The mathematical mechanism

`lemma51P t`'s only `t`-dependence is in its *hypothesis* `γ ≤ boxAvgA t c M₁ M₂ b N f` and in
its gcd/size exceptional-set condition; the conclusion is level-independent.  The level raising

`(1/2) * (‖f‖^{2}_{□¹_Q(S)})^2 ≤ ‖f‖^{4}_{□²_{(Q,Q)}(S)}`

(`Work.Peluse.LadderA.levelRaiseAppendBd` — the Gowers–Cauchy–Schwarz step, which needs the
`[-N,N]`-bound only on the *appended* direction set, and no bound on the first one) shows that a
level-`2` datum with the *padded* direction family dominates the level-`1` datum.  Padding the
second direction by `b₀` itself (resp. `b₀ + 1`) keeps the gcd condition of the level-`2` good set
true on the level-`1` good set, at the cost of enlarging the ambient window from `symIcc N` to
`symIcc (Cw*N)` (paid for by the exact scaling `|S| * ‖f‖^{2^t}_{□^t_Q(S)}` being independent of
`S`), and hence costs only an absolute constant in `γ`.

Two regimes are needed for the exceptional set:
* if `η * M₁ * (B₀+1) ≤ 1` the level-`1` good set is contained in the level-`2` good set with the
  *same* `η` (the gcd condition `gcd(a+b₀,a+b₀) = |a+b₀| ≤ 1/η` holds because `|a+b₀| ≤
  M₁(B₀+1)`), and the bad sets satisfy `bad₂ ⊆ bad₁`;
* otherwise, padding by `b₀ + 1` makes the gcd condition automatic (`gcd(x,x+1) = 1`) and only the
  size condition can fail, at the *single* value `a + b₀ = -⌈ηM₁⌉`; the extra element is absorbed
  by the `η * M₁ * (B₀+1) > 1` hypothesis, which forces `γ^{e₂} M₁ ≳ 1`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Pel51

open Work.Peluse

/-- **The bad set of Peluse's Lemma 5.1 at level `t`**: the `a ∈ [1,M₁]` at which the gcd/size
condition of `LadderP.lemma51P t` fails.  It is the `filter` appearing verbatim in the hypothesis
of the frozen `Work.Peluse.LadderP.lemma51P` (see `badP_eq_lemma51P_filter` below, which holds by
`rfl`). -/
noncomputable def badP (t : ℕ) (M₁ : ℕ) (b : Fin t → ℤ) (η : ℝ) : Finset ℕ :=
  (Finset.Icc 1 M₁).filter (fun a : ℕ =>
    ¬ ((∀ i k : Fin t, i ≠ k →
          ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b k) : ℕ) : ℝ) ≤ 1 / η)
        ∧ ∀ i : Fin t, η * (M₁ : ℝ) ≤ ((|((a : ℤ) + b i)| : ℤ) : ℝ)))

/-- `badP` is *definitionally* the bad set of the frozen statement (the two expressions differ only
in the bracketing of `|(a : ℤ) + b i|`). -/
theorem badP_eq_lemma51P_filter (t : ℕ) (M₁ : ℕ) (b : Fin t → ℤ) (η : ℝ) :
    badP t M₁ b η
      = (Finset.Icc 1 M₁).filter (fun a : ℕ =>
          ¬ ((∀ i k : Fin t, i ≠ k →
                ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b k) : ℕ) : ℝ) ≤ 1 / η)
              ∧ ∀ i : Fin t, η * (M₁ : ℝ) ≤ ((|(a : ℤ) + b i| : ℤ) : ℝ))) := rfl

end Work.Peluse.Pel51
