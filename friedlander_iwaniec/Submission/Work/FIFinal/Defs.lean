/-
# `Submission.Work.FIFinal.Defs` — the vocabulary of the final assembly

This directory is the **final wiring chapter** of the Friedlander–Iwaniec project: it takes the
composition of the seven round-6 areas (`Work.FITop4.prop41_of_areas6f`, the producer of
`Work.FITop4.Prop41StatementPiBig`) plus the FIChain endgame
(`Work.FIChain.primeSum_bound_of_prop41'`, the producer of the prime-sum asymptotic of the paper's
Theorem 1) and lands the *challenge statement*

  `{p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}.Infinite`.

The names below are the four objects the wiring speaks about:

* `ChallengeTheorem` — the challenge (the same `Prop` as `Challenge.lean`'s `friedlander_iwaniec`);
* `S3Input` — **verbatim** the `hS3` binder of `Work.FIChain.primeSum_bound_of_prop41'`, i.e. the
  §8 `S₃`-average at the corrected `B`-dependent scale;
* `PrimeSumBound` — **verbatim** the conclusion of `Work.FIChain.primeSum_bound_of_prop41'`, i.e.
  the paper's Theorem 1 for `a`;
* `PiRemoval` — the one *further* input that the current workspace does **not** supply: the passage
  from the `Π`-restricted Proposition 4.1 (the *areas'* output, `Prop41StatementPiBig`) to the
  `Π`-free pointwise contract `Work.FITop.Prop41Statement` that the FIChain endgame consumes.

## Why `PiRemoval` is a separate name (read this before wiring)

`Work.FIChain.primeSum_bound_of_prop41'` carries the binder `h : Prop41Stmt`, and
`Work.FIChain.Prop41Stmt` is by definition `Work.FITop.Prop41Statement` — the *`Π`-free*,
*pointwise* form of Proposition 4.1 (`Work.FITop.BformAtil`).  The seven round-6 areas, however,
produce `Work.FITop4.Prop41StatementPiBig`, whose bilinear form is the `Π`-*restricted*
`Work.FITop.BformPi`.  These are genuinely different statements and **neither implies the other**:

* the textbook obstruction is recorded at `Submission/Work/FITop4/Red5/Vocab.lean:22` ("the removal
  `BformAtil ≤ BformPi + err` ... that *pointwise* statement is FALSE") and in
  `Submission/Work/FIChain/NOTES.md` §38 (the comparison `BformPi ≤ BformAtil` fails *inside* the
  `m`-sum, because the absolute values sit inside the `m`-sum and `|Σ_{S₁} f| ≤ |Σ_{S₂} f|` does not
  follow from `S₁ ⊆ S₂` for a signed inner sum);
* the paper's §10 (companion, Theorem 3) runs **(B\*) ⟹ (∫B)**, i.e. it derives the `Π`-free bound
  *in integrated form* from the `Π`-restricted one — integration costs a `log` factor
  (`log(sc·zc) ≍ (1/4) log x`), and that is exactly why FIChain's integrated consumers
  (`Work.FIChain.BprimeWindowIntegrated`, `Work.FIChain.RhoWindowIntegrated2`) are fuelled by
  `Prop41StatementPiBig` and *not* by `Prop41Stmt`.

So the honest chain is

    Area1Sieve6 … Area7_6b  ⟹  Prop41StatementPiBig  ⟹  Prop41Stmt  ⟹  (FIChain)  ⟹  challenge,

where the middle arrow `PiRemoval` is the missing chapter (the paper's §10 `Π`-removal in the
pointwise form the endgame needs), and it is exposed as an explicit hypothesis everywhere below.

## What this directory supplies (module by module)

| module | content |
|---|---|
| `Defs.lean` | the vocabulary below (`ChallengeTheorem`, `S3Input`, `PrimeSumBound`, `PiRemoval`, the prime-sum objects) |
| `Area1Bridge.lean` | **area 1**: `Work.FIArea1.area1s_r6 : Work.FITop4.Area1Sieve6` — the repair of `Submission/Work/FITop4/Bridge/area1Sieve6.lean`, whose proof does not compile (three undeclared `Work.FITop4.seqOf`, five `rw`-sites frozen at the pre-6.3 shape of `IsBetaCoeff6`), with its imports re-pointed from the `FIArea1/shim/*` copies to the `FIArea1/*` originals (the shims re-declare `Work.FITop3.*` and clash with `Submission.Work.FITop3.Areas3`) |
| `CL/` | 24 verbatim copies of the `FIArea6Hecke`/`FIArea6V` modules on the `LHBHead`-ward path, with the single import of the non-clash-free `Work.FIArea7.card_pairs_gBox_absDelta_lt` re-pointed to the clash-free `Work.FIArea7CF.card_pairs_gBox_absDelta_lt` |
| `Clean6.lean` | **area 6**: `Work.FIFinal.area6_6e : Work.FITop4.Area6_6e` along that copy lane — `Work.FIArea6V.area6_6e` cannot be imported together with `Work.FIArea7.area7_6b` because the two `FIArea7` lanes declare `Work.FIArea7.gRadius` twice |
| `Prop41.lean` | `Work.FIFinal.prop41 (h4 : Area4_6c) : Prop41StatementPiBig` (area 4 as a hypothesis) and `prop41_unconditional` (area 4 from disk; currently inherits `sorryAx` from the live area-4 hole `Work.FIArea4.A4c.pieceSum_le`) |
| `Endgame.lean` | `challenge_of_primeSumBound : PrimeSumBound → ChallengeTheorem` (the last mile: margin + absorption + pair count) |
| `Bridge.lean` | `challenge_of_prop41`, `challenge_of_PiBig`, `challenge_of_inputs`, `challenge_of_inputs_unconditional` |
| `IntTools.lean` | the `ASP`/`FIChain` vocabulary for the two integrated consumer restatements (delegated separately: `Work.FIFinal.abs_smAvg_S2_int_le`, the `S₂` half of the integrated route) |
| `AxCheck.lean` | `#print axioms` for everything claimed |

## The remaining binder of the challenge

**One** input is still open: `PiRemoval`, the passage from the areas' output (the `Π`-*restricted*
`Prop41StatementPiBig`) to the `Π`-*free* pointwise contract `Work.FITop.Prop41Statement` that the
FIChain endgame consumes (for both its `(B′)`-window, `Work.FIChain.windows_at_Bstar`, and its
signed `S₃` bound, `Work.FIChain.S3fixed_signed_Bstar` — both take `h : Prop41Stmt`).

The `S₃` half, which was a second binder while `Work.FIChain.primeSum_bound_of_prop41'` carried
`hS3`, has since been **discharged on disk** by FIChain (`Work.FIChain.S3fixed_signed_Bstar` /
`Work.FIChain.PrimeSumSigned_of_prop41`), so the signature of `primeSum_bound_of_prop41'` is now
`(h : Prop41Stmt) → PrimeSumBound` (the abbreviation `S3Input` below records the superseded binder).
Note also `Work.FIChain/NOTES.md` §43: the *position*-integrated `ρ`-window `RhoWindowInt2` cannot
feed the `S₃` consumer at all (explicit counterexample), so the `S₃` half is genuinely tied to the
pointwise contract and cannot be rerouted through the integrated `Π`-free windows; the
`Π`-removal is therefore the single remaining mathematical input of the challenge.
-/
import Mathlib
import Submission.Work.FIChain.Target
import Submission.Work.FITop4.Red5.Vocab

set_option autoImplicit false

namespace Work.FIFinal

open Finset Filter
open scoped BigOperators

noncomputable section

/-- **The challenge.**  `{p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}` is infinite — the
Friedlander–Iwaniec theorem (Annals 148 (1998), 945–1040).  This is definitionally the statement of
the trusted file `Challenge.lean`. -/
abbrev ChallengeTheorem : Prop := {p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}.Infinite

/-- **The `S₃` input of the FIChain endgame** — kept as documentation of the shape that was live
while `Work.FIChain.primeSum_bound_of_prop41'` carried the `hS3` binder: for every `B > 0` there is
`K > 0` with, eventually in `x`, for every sieve weight `λ` at the level `Δ = Deltac x` and every
constant `C_sieve` satisfying `Work.FIChain.SieveInput`, the `y`-integrated `S₃` of the chain is at
most `J·K·Ã(x)·(log x)^{−4}·log⌊s·z⌋` on the window `[Yc, e·Yc]` (same binders and body as
`Work.FIChain.FIChainS3Gap`).

**This binder has since been discharged on disk** by FIChain: `Work.FIChain.S3fixed_signed_Bstar`
(supplied by `h : Prop41Stmt` alone, the fixed-`z` signed `S₃` family `Work.FIChain.S3fixed_signed_K`
at its own witness `Bstar`) feeds `Work.FIChain.PrimeSumSigned_of_prop41`, so
`Work.FIChain.primeSum_bound_of_prop41'` now takes the single binder `h : Prop41Stmt`.  The
definition below is retained only as the exact type of that (superseded) binder. -/
abbrev S3Input : Prop :=
  ∀ B : ℝ, 0 < B → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in Filter.atTop,
    (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ) →
    ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
      Work.FIChain.SieveInput Submission.ASP.FIgtil (Work.FIChain.Deltac x) lam C_sieve →
      (∫ y in Work.FIChain.Yc x B..(Real.exp 1 * Work.FIChain.Yc x B),
          |Submission.ASP.S3 Work.FIChain.atilc lam x (Work.FIChain.zc x B)
            (Work.FIChain.sc x B * y) (Work.FIChain.sc x B * Work.FIChain.zc x B)| / y)
        ≤ (Work.FIChain.Jc x B : ℝ)
            * (K * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
            * Real.log (((⌊Work.FIChain.sc x B * Work.FIChain.zc x B⌋₊ : ℕ) : ℝ))

/-! ## The prime-sum vocabulary

The three objects below are `Work.FITop.primeSumFI`, `Work.FITop.AcountF` and
`Work.FITop.AcountTil` of `Submission/Work/FITop/Top.lean`, restated here (that module is not
importable: it carries the `sorry`ed leaf `Work.FITop.primeSum_bound_of_prop41`, which is exactly
the statement this chapter provides by other means). -/

/-- `Σ_{p ≤ N} (log p)·a_p`, the prime sum of the chain (`a = FIa`). -/
def primeSumFI (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * Work.FITop.FIaR p

/-- `A(N) = Σ_{n ≤ N} a_n`, the counting function of `a`. -/
def AcountF (N : ℕ) : ℝ := Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)

/-- `Ã(N) = Σ_{n ≤ N} μ(n)²ã(n)`, the counting function of `ã = atil FIa`. -/
def AcountTil (N : ℕ) : ℝ := Submission.ASP.Acount Work.FITop.atilFIa (N : ℝ)

/-- **The paper's Theorem 1 for `a`** — the target of the FIChain endgame, in the vocabulary of
`Work.FITop`:

  `|Σ_{p ≤ N} (log p)·a_p − (4/π)·A(N)| ≤ C·Ã(N)·loglog N/log N`  eventually in `N`,

where `a = FIa`, `A(N) = Σ_{n ≤ N} a_n` and `Ã(N) = Σ_{n ≤ N} μ(n)²ã(n)`.  This is
definitionally the conclusion of `Work.FITop.primeSum_bound_of_prop41` (the single `sorry` of
`Submission/Work/FITop/Top.lean`) and of `Work.FIChain.primeSum_bound_of_prop41'`. -/
abbrev PrimeSumBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
    |primeSumFI N - (4 / Real.pi) * AcountF N|
      ≤ C * AcountTil N * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))

/-- **The same target in the FIChain vocabulary** — verbatim the conclusion of
`Work.FIChain.primeSum_bound_of_prop41'`; `Bridge.lean` converts it to `PrimeSumBound`. -/
abbrev PrimeSumBoundFIChain : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
    |(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * Submission.ASP.FIa p)
        - (4 / Real.pi) * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)|
      ≤ C * Work.FIChain.AcountAtilC N
          * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))

/-- **The `Π`-removal of the companion's §10** — the chapter that is *not* in the workspace.

The seven round-6 areas produce the `Π`-restricted Proposition 4.1
(`Work.FITop4.Prop41StatementPiBig`, the bilinear form `Work.FITop.BformPi`), while the FIChain
endgame consumes the `Π`-free pointwise contract `Work.FITop.Prop41Statement` (the form
`Work.FITop.BformAtil`).  See the module docstring for why neither direction is available as a
formal implication: the paper's §10 gives `(B*) ⟹ (∫B)` (integrated), and the pointwise form is
needed by `Work.FIChain.bprimeWindowC`/`Work.FIChain.rhoWindowC_param` and by
`Submission.ASP.abs_smAvg_S2_le`.

The name is an abbreviation of a function type between two `Prop`s, so it is used as a hypothesis
(`hπ : PiRemoval`) and applied (`hπ (prop41 h4)`). -/
abbrev PiRemoval : Prop :=
  Work.FITop4.Prop41StatementPiBig → Work.FITop.Prop41Statement

end

end Work.FIFinal
