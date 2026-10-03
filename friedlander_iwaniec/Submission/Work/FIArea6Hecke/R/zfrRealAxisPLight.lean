/-
# `Work.FIArea6Hecke.R.zfrRealAxisPLight`

**Lemma 16.1 (*FI*, Landau–Siegel) on the real axis: from the `PsiReal` form of the Siegel input to
the `PsiRealPrimary` form.**

The two classical inputs of the zero-free region are stated in `R/ZFRStatementDefs.lean`:
`ZFRoffAxis` (*FI* (16.20), de la Vallée Poussin, with the exceptional set `s.im = 0 ∧
PsiRealPrimary χ m`) and `ZFRrealAxis ε` (Lemma 16.1, Siegel: no zero on the segment
`s > 1 - c d^{-ε}` when `ψ` is real).  The target `heckeStripZFR` combines them, and for the
combination to cover the region *exhaustively*, the Siegel half must be available with the very
same notion of "`ψ` real" as the exceptional set of (16.20), namely `PsiRealPrimary` — realness on
the *primary* elements, i.e. of the odd-ideal character (16.16).

This file supplies that bridge:

  `ZFRrealAxis ε  ⟹  ZFRrealAxisP ε`   (`zfrRealAxisPLight`),

and, as it is a one-line effect of the weakening `PsiReal ⟹ PsiRealPrimary`
(`ZFRStatementDefs.psiReal_implies_psiRealPrimary`) that the two hypotheses are nested, the
converse implication `ZFRrealAxisP ε ⟹ ZFRrealAxis ε`
(`zfrRealAxis_of_zfrRealAxisP`); together the two forms are therefore *equivalent*, as claimed in
the docstring of `ZFRStatementDefs.ZFRrealAxisP`.

## Why the non-trivial direction is not merely a weakening

`ZFRrealAxisP ε` quantifies over the *larger* class of pairs `(χ, m)` with `ψ` real only on the
primary elements, so one cannot simply feed such a pair to `ZFRrealAxis ε`.  The reduction replaces
the pair by one which *is* `PsiReal` while carrying the same `L`-function (and hence the same
completion, hence the same zeros):

* `PsiRealPrimary χ m` forces `m = 0` (`R/m_eq_zero_of_psiReal.zpr_m_eq_zero_of_psiRealPrimary`,
  tested at the primary unit `1 + 4d·i`), and says that `χ` is real on the primary elements;
* the primary associate `z ↦ primAssoc z` produces the real-valued strict partner `χ' = chiPrime d χ`
  with the *same* Hecke eigenvalues and `L`-series (`R/chiPrimeDefs`, `R/chiPrimeAgree`), which is
  exactly the statement of `R/exists_realCharacter_agreeing_on_primary`;
* `χ'` is nontrivial on the primary units (otherwise `Λ` would be an entire completion of the
  trivial-character pair, impossible by `R/noCompletion_of_primaryTrivial`), so
  `R/heckeCompletionImprimitive` completes the pair `(χ', 0)`, the Siegel input applies to it, and
  the identity theorem on the half-plane `re s > 0` transports the non-vanishing of `Lval` back
  (`R/lvalSameSeries`).

That reduction — the mathematical content of this bridge — is formalised in
`R/heckeZFRrealAxisP_of_psiReal` (`Work.FIArea6Hecke.R.heckeZFRrealAxisP_of_psiReal`), which is
*not* available to `R/logDerivCore` (the module that consumes the present lemma) because
`logDerivCore` sits above it; the present module is the interface through which that result is
consumed.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.R.chiPrimeDefs
import Submission.Work.FIArea6Hecke.R.chiPrimeAgree
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_psiReal
import Submission.Work.FIArea6Hecke.R.exists_realCharacter_agreeing_on_primary
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea6Hecke.R.heckeZFRrealAxisP_of_psiReal

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

/-- **The two forms of the Siegel input are nested**: `ZFRrealAxisP ε` implies `ZFRrealAxis ε`.
The statements differ only in their hypothesis on `ψ`, and `PsiReal χ m → PsiRealPrimary χ m`
(`ZFRStatementDefs.psiReal_implies_psiRealPrimary`), so the same constant `c` works. -/
theorem zfrRealAxis_of_zfrRealAxisP (ε : ℝ) (h : Work.FIArea6Hecke.R.ZFRrealAxisP ε) :
    Work.FIArea6Hecke.R.ZFRrealAxis ε := by
  obtain ⟨c, hcpos, hreg⟩ := h
  exact ⟨c, hcpos, fun d chi m Lam hd hchi hAn hagr hr s hsim hs1 hs2 =>
    hreg d chi m Lam hd hchi hAn hagr (psiReal_implies_psiRealPrimary hr) s hsim hs1 hs2⟩

/-- **`ZFRrealAxis` in the primary form `ZFRrealAxisP`** (*FI* Lemma 16.1 with the exceptional set
of (16.20)): the Siegel zero-free region on the real axis holds not only for `ψ` real on all of
`ℤ[i]`, but for the weaker and correct hypothesis that `ψ` is real on the *primary* elements, i.e.
that the Hecke eigenvalues `λ(n) = Σ_{z primary, |z|²=n} ψ(z)` are real.

The proof is the transfer to the real partner `χ'(z) = χ(primAssoc z)` with the same `L`-series,
worked out in `R/heckeZFRrealAxisP_of_psiReal`; see the module docstring above. -/
theorem zfrRealAxisPLight (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (h : Work.FIArea6Hecke.R.ZFRrealAxis ε) :
    Work.FIArea6Hecke.R.ZFRrealAxisP ε :=
  Work.FIArea6Hecke.R.heckeZFRrealAxisP_of_psiReal ε hε hε4 h

end Work.FIArea6Hecke.R
