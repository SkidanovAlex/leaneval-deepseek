/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Peluse.Basic
import Submission.Work.Analysis.InverseTheory.MajorArcs

/-!
# Area A2: Peluse's inverse theorem in the form used by Krause–Mirek–Tao

This module contains the *statement* of the deliverable of `Submission/Work/Peluse/`:
`PeluseInverseKMT P` for `P ∈ ℤ[X]` (Area A2 of `Submission/Work/KMTPlan/ROUTE_LEAD.md` §1.3), and
the area proposition `AreaA2`.

## What the statement is

`PeluseInverseKMT P` is the inverse theorem of S. Peluse (`Bounds for sets with no polynomial
progressions`, Forum Math. Pi **8** (2020), Theorem 3.3) specialised to the progression
`(x, x + n, x + P(n))` — exactly the form in which Krause–Mirek–Tao use it (their Theorem `pp`).
Informally: let `deg P = d ≥ 2` and `A ≥ 1`.  There are `C, K > 0` depending only on `P` and `A`
such that for `1`-bounded `f, g, h` supported in `[-N₀, N₀]` with `N₀ ≤ A N ^d`, if

  `|⟨Ã_N(f,g), h⟩| ≥ δ N^d`

then either `N ≤ C δ^{-K}`, or there are `q ≤ C δ^{-K}` and `N' ≥ δ^K N / C` with

  `∑_x |E_{m ≤ N'} f (x + q m)| ≥ δ^K N^d / C`.

Here `Ã_N` is the workspace's halved bilinear average `Work.Analysis.InverseTheory.AhalfZ` and
`⟨·,·⟩` is the pairing `bilinPair`.

## Corrections relative to the older statements in the workspace

`Work.Analysis.InverseTheory.PeluseInverseTheorem` (and `Work.Analysis.Concentration.PeluseInverse`)
are **false as stated** — see F3 of `Submission/Work/KMTPlan/ROUTE_LEAD.md`: the absolute value
there is outside the sum over `x`, so that conclusion (ii) reads "`f` has large mean", which is not
what Peluse's theorem says (Peluse's Theorem 3.3, and its proof, have `∑_x |E_m f (x + q m)|`), and
its constants `2 ^ 100`, `100` are absolute whereas Peluse's depend on `P`.  `PeluseInverseKMT`
below is the corrected form: the absolute value is *inside* the `x`-sum, and the constants `C, K`
are allowed to depend on `P` (and on `A`).

Note also that `Work.Analysis.InverseTheory.PeluseTheorem`-style statements require
`f, g, h ∈ 𝓢(ℤ)`; here finite support (`SupportIn`) is assumed, which is stronger and matches the
use in `improv` (all functions are `1`-bounded and supported on an interval).

## Status

`PeluseInverseKMT` is a *deep external theorem* and is recorded here as a `Prop`-valued
definition, exactly as `Work.Analysis.IWMultiplier.IWMultiplierBoundStatement_even` records the
Ionescu–Wainger multiplier theorem.  Nothing in this area is an axiom: the intermediate theorems of
Peluse's paper are recorded in `Submission/Work/Peluse/Nodes.lean`, the parts that are elementary
(number theory of the `μ_L` weights, van der Corput, the PET step, the box-norm calculus) are
*proved* in `Submission/Work/Peluse/`, and `Submission/Work/Peluse/Assembly.lean` derives
`AreaA2` from the nodes.

## Compatibility with the contract subproject

The contract subproject `KMTContract` freezes Area A2 under the name `PeluseInverseKMT` with the
same body as below (see `ROUTE_LEAD.md` §1.3).  If it is frozen with a different name or namespace,
nothing else in this area has to change: all the results of this area mention only
`PeluseInverseKMT` at the top level, and every intermediate statement is about the concrete
operators `AhalfZ`, `LambdaZ`, `dualFn` of `Submission/Work/Peluse/Basic.lean`.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse

open Work.Analysis.InverseTheory (AhalfZ bilinPair SupportIn)

noncomputable section

/-- **Area A2 — Peluse's inverse theorem, in the form used by Krause–Mirek–Tao** (their Theorem
`pp`; Peluse, *Bounds for sets with no polynomial progressions*, Theorem 3.3, specialised to the
progression `x, x+n, x+P(n)`).

`P ∈ ℤ[X]` is a polynomial, `A ≥ 1` a support parameter.  There are constants `C, K > 0` depending
on `P` and `A` only, such that for every `N ≥ 1`, `0 < δ ≤ 1`, `N₀ ≤ A N ^ P.natDegree` and
`1`-bounded functions `f, g, h : ℤ → ℂ` supported in `[-N₀, N₀]` with
`δ N ^ P.natDegree ≤ ‖⟨Ã_N(f,g), h⟩‖`, either

* `N ≤ C δ^{-K}`, or
* there are `q, N'` with `1 ≤ q`, `q ≤ C δ^{-K}`, `1 ≤ N' ≤ N`, `δ^K N ≤ C N'` and
  `δ^K N ^ P.natDegree ≤ C ∑_x |E_{m ≤ N'} f (x + q m)|`.

The absolute value in the last display is *inside* the sum over `x` (this is the correction of
F3 of `ROUTE_LEAD.md`), and `C, K` may depend on `P`.  The constant `A` is needed only to allow
the support `N₀ ≍ N ^ d` of the applications. -/
def PeluseInverseKMT (P : ℤ[X]) : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
      (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
      SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
      (N : ℝ) ≤ C * δ⁻¹ ^ K ∨
        ∃ q N' : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * δ⁻¹ ^ K ∧ 1 ≤ N' ∧ N' ≤ N ∧
          δ ^ K * (N : ℝ) ≤ C * (N' : ℝ) ∧
          δ ^ K * (N : ℝ) ^ P.natDegree ≤ C * progAvgSum N' (q : ℤ) f

/-- **Area A2, quantified form.**  Peluse's inverse theorem holds for every polynomial of degree
at least `2`.  (`P.natDegree` is used rather than `P.degree` for definiteness; the two agree
whenever `P ≠ 0`.) -/
def AreaA2 : Prop := ∀ P : ℤ[X], 2 ≤ P.natDegree → PeluseInverseKMT P

/-- The equivalence of the two `SupportIn` of the workspace (they are the same predicate; the one
in `Work.Peluse.Basic` is the local copy and is what the box-norm lemmas are stated with). -/
theorem supportIn_iff (f : ℤ → ℂ) (N : ℕ) : SupportIn f N ↔ Work.Peluse.SupportIn f N :=
  Iff.rfl

end

end Work.Peluse
