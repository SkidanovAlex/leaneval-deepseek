import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API

namespace Work.CORE4

/-! ## Prover's note (verdict: under-hypothesised as a standalone leaf)

This file is left elaborating (the statement below is untouched).  The requested implication is
not derivable from its hypothesis list; the two non-trivial branches need the §4 (8) *object
layer*, which the hypotheses do not carry:

* **First disjunct `Case2InvNormal B C.D`.**  It demands that the *set* `invSet B.U D.s` be the
  carrier of a subgroup of `Ĥ` (so in particular be multiplicatively closed).  The hypotheses
  relate `I_U(s)` only to `B₀ = C_U(s)` (`Case2Pre.B0_eq`); Bender's case-3 argument needs
  `I_U(s) = F(C_U(Q))`, equivalently `C_U(Q) ⊓ C_U(s) = ⊥`, which is the §4 (5)/(8) configuration
  fact "`Q ⊄ M` implies `C_U(Q) ∩ F = 1`".  Closure is *not* implied: the prover of
  `CORE4/EightExCase3` gave the configuration `p = 3`, `U = C₃ × C₃ × R` (`R` extraspecial of
  order `5³`, exponent 5), `s` inverting the `C₃ × C₃` and inverting `a, b ∈ R` while fixing its
  centre; then `Q = Ω₁(Z₂(O_3(U))) = C₃ × C₃` is non-cyclic and `s`-inverted, yet `I_U(s)` is not
  closed (see the header of `Submission/Work/CORE4/EightExCase3.lean`).
* **Second disjunct `u ≤ p ∧ A ⊴ F(U) ∧ (¬U ≤ M → 3 ≤ p₀)`.**  It needs the middle case of the
  §4 (8) trichotomy — `A ≤ Ω₁(Z₂(O_p(U))) ≤ O_p(U)`, `|Ω₁(Z₂(O_p(U)))| = p³`, `Z(Q) < A`,
  `Q ⊄ M` — to get `A ⊴ F(U)` (from `⁅P,A⁆ ≤ ⁅P,Q⁆ ≤ Z(Q) ≤ A`) and `u ≤ p` (the `U`-conjugates of
  `A` are then among the `≤ p + 1` subgroups of `Q` of order `p²` containing `Z(Q)`, and `u` is
  odd).  The hypotheses bound neither `|Ω₁(Z₂(O_p(U)))|` (they record only the `s`-decomposition
  `U ⊓ M = K ⊔ B₀`, `K` cyclic, and the *prime-divisor sets* of (7)) nor `A`'s position in
  `Z₂(O_p(U))`; the prover of `CORE4/EightExTrich` reported the same verdict.

Moreover the conclusion is *literally* the last conjunct of `Case2EightFacts`, so this leaf is a
projection of the parent target `CORE4/Case2Eight`: its proof would duplicate the parent's own
§4 (8) analysis, whose intermediate layer (`Qsub`, the trichotomy, `N_U(A) = (U ⊓ M) ⊔ F(U)`,
`U = (U ⊓ M) ⊔ F(U)`) lives in the parent's module and cannot be imported here.

Recommended restatement: add the object layer as explicit hypotheses, or prove the dichotomy
inside `CORE4/Case2Eight` once that layer is derived.  The elementary parts are already available
in `CORE4/Case2Eight` (`A = Ω₁(F ⊔ K)`, `U ⊓ M ≤ N_G(A)`, `Odd p₀`, `N_U(P) = U ⊓ M`) and in
`CORE4/EightIdxDefs` (`Qsub`, `Asub`). -/

/-- Bender 1981, §4 (8), the exceptional dichotomy: given the prime `p`, `P ≤ D.F` of order `p`,
and the `(p,p)`-subgroup `A` of §4(8) (`Case2EightObj D p P A`), either `Case2InvNormal B D`
holds, or `u = |U : N_U(A)| ≤ p` and `A ⊴ F(U)` and (`U ⊄ M` implies `3 ≤ p₀`). -/
theorem Case2EightExcept (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A →
          (Work.GW2.Case2InvNormal B C.D ∨
            (Work.GW2.Case2EightU B A ≤ p ∧
              (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal ∧
              (¬ B.U ≤ C.D.M → 3 ≤ Work.GW2.Case2EightP0 B P A))) := by sorry

end Work.CORE4
