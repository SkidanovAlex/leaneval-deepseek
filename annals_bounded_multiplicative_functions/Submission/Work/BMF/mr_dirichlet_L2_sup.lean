import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_dirichlet_L2_direct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mr_dirichlet_L2_sup` — the Matomäki–Radziwiłł `k = 0` Dirichlet-polynomial input

## The statement

For `0 < θ < 1` and every `ε > 0` there are `B, C, X₀` with `0 < B`, `0 < C`, `1 ≤ X₀` such that
every `1`-bounded multiplicative `g : ℕ → ℂ` with `g 1 = 1` that is `B`-far in the pretentious
distance `𝔻` from every archimedean twist `n ↦ n^{iu}` with `|u| ≤ C·Y/H` satisfies, for every
`Y ≥ X₀`, every `H` with `Y^θ ≤ H ≤ Y` and *every* `T ≥ Y/H`,

`(Y/H)/T · ∫_{-2T}^{2T} ‖Σ_{Y ≤ n ≤ 3Y} g n · n^{-(1+it)}‖² dt ≤ ε`.

This is the `k = 0` case of the main theorem, in the Dirichlet-polynomial form in which it is
consumed: "a non-pretentious bounded multiplicative function has small short Dirichlet sums on
average".  It is the input for which the paper's proof for `k = 0` cites [MRT] (Matomäki,
Radziwiłł, Tao, *An averaged form of Chowla's conjecture*, ANT 9 (2015), Theorem A.1/A.2);
the footnote in `paper/polyphases4.tex` records precisely that the difference from loc. cit. is
that the integral over `|t| ≥ CX/(2H)` must be treated by the mean value theorem, so that the
statement can be used with `M(f; CX/H, Q)` rather than `M(f; X, Q)`.

## Why it is not elementary

Writing `A(t) = Σ_{Y ≤ n ≤ 3Y} g n · n^{-1-it}`, the mean square sees the correlations
`Σ_n g n ḡ(n+d)` for `|d| ≲ Y/T`.  The trivial (mean value / Montgomery–Vaughan) bound
`∫_{|t|≤2T}‖A‖² ≤ C(T+Y)/Y` gives only

`(Y/H)/T · ∫_{|t| ≤ 2T}‖A‖² ≤ C(1+Y/T)/H`,

which is a *constant* (namely `C·(1+H)/H ≈ C`) at the critical height `T = Y/H`; that constant has
to be improved to `ε`, and doing so is exactly Matomäki–Radziwiłł's theorem.  Concretely, the
proof splits at `T = (2C₀/ε)·(Y/H)`:

* `T ≥ (2C₀/ε)·(Y/H)` (`ℓ := Y/T ≤ (ε/2C₀)·H`): the mean value theorem for Dirichlet polynomials
  `Work.BMF.mv_sharp_dirichlet` gives `(Y/H)/T·∫_{|t|≤2T}‖A‖² ≤ C₀(1+ℓ)/H ≤ ε/2`;
* `Y/H ≤ T ≤ (2C₀/ε)·(Y/H)`: this is the genuine content
  (`Work.BMF.CoreInput`, proved in `Submission/Work/BMF/mr_core/main.lean` by the Buchstab
  decomposition, Halász's theorem and the large-values estimate).

## Where this statement is proved

`Work.BMF.mr_dirichlet_L2_direct` (`Submission/Work/BMF/mr_dirichlet_L2_direct.lean`) is this
statement verbatim: the two reductions `mr_direct_largeT` and `CoreInput` are assembled there into
exactly the claim above.  That chain is complete and `sorry`-free — in particular the whole
`mr_core`/`mr_direct` development it rests on is `sorry`-free — and `#print axioms` for it returns
only `propext`, `Quot.sound`, `Classical.choice`.  The mean value input `mv_sharp_dirichlet` used by
its easy regime was established (together with the independent inputs
`Work.BMF.dirichlet_parseval_shortint`, `Work.BMF.halasz_long_avg_L2` and
`Work.BMF.mr_weighted_shortint`) while this file was being developed.

We therefore obtain the requested lemma by importing that verified theorem; the statement below is
byte-for-byte the requested one, so the requester may build on it as written.
-/

namespace Work.BMF

open MeasureTheory
open scoped BigOperators
open BoundedMultiplicativeFunctions

/-- **Matomäki–Radziwiłł `k = 0`, Dirichlet-polynomial form (supremum in `T`).**
See the module documentation for the reduction and for the location of the proof. -/
theorem mr_dirichlet_L2_sup (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (g : ℕ → ℂ), g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ (Y H : ℝ), X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
      (∀ u : ℝ, |u| ≤ C * Y / H →
        B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
      ∀ T : ℝ, Y/H ≤ T →
        (Y/H)/T * (∫ t in -(2*T)..(2*T),
          ‖∑ n ∈ Work.BMF.natIcc Y (3*Y), g n * (n:ℂ)^(-(1 + Complex.I*t))‖^2) ≤ ε :=
  mr_dirichlet_L2_direct θ hθ₀ hθ₁

end Work.BMF
