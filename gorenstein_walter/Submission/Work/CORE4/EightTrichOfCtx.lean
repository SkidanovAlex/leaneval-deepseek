import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.Case2EightQfacts

/-!
# REPORT (owner of `Work.CORE4.EightTrichOfCtx`): the requested statement is not derivable

The statement is Bender 1981, §4 (8), p. 226, *as printed*:

> With `Q := Ω₁(Z₂(O_p(U)))`, a non-cyclic subgroup of exponent `p`, either `A = Q`, or
> `Z(Q) ⊊ A ⊊ Q` and `|Q : A| = p`, or `s` inverts `Q`.

Bender asserts it without proof (it is the input of his derivation of (8)), and it is *not* a
consequence of the hypotheses recorded here (`BenderCtx`, `Case2`, `Case2Ctx` (i.e. §4 (1)–(9)),
`Case2EightObj`).  The recorded data pin down neither the position of `A` in `Q` nor the action of
`s` on `Q`; what Bender's argument additionally uses is a structural input that is *not* among the
conjuncts of `Case2Ctx` — in case 3 (`s` inverts `Q`) the assertion `C_U(Q) ⊓ C_U(s) = ⊥` (i.e.
`s` inverts `C_U(Q)`, Bender's "`Q ⊄ M` implies `C_U(Q) ∩ F = 1`"), and in cases 1–2 the position
`A ≤ Q` with `A = Q` or `Z(Q) < A`.

## Explicit model showing that the recorded (local) data do not imply the conclusion

Let `p` be odd and let `U := ⟨v₁⟩ × ⟨v₂⟩ × ⟨v₃⟩ ≅ C_p³` (`= 𝔽_p³` written additively), with the
involution `σ := diag(1, -1, -1)` (so `σ v₁ = v₁`, `σ v₂ = v₂⁻¹`, `σ v₃ = v₃⁻¹`).  Put

* `U ⊓ M := ⟨v₁, v₂⟩` (so `U ⊓ M` is a subgroup of index `p` in `U`),
* `B₀ := C_U(σ) = ⟨v₁⟩`  (order `p`),
* `K := I_{U⊓M}(σ) = ⟨v₂⟩` (cyclic, of order `p`, inverted by `σ`),
* `F := B₀ ⊓ F(U) = ⟨v₁⟩` (`U` is a `p`-group, so `F(U) = U`), `K₀ := F(U) ⊓ K = ⟨v₂⟩`,
* `P := ⟨v₁⟩ ≤ F` of order `p`, `A := Ω₁(F ⊔ K₀) = ⟨v₁, v₂⟩ ≅ C_p × C_p`.

This satisfies all the local facts the hypotheses use: `K = I_{U⊓M}(s)` is cyclic inverted by `s`,
`B₀ = C_U(s)`, `F = B₀ ⊓ F(U) ≠ 1` cyclic and `p ∣ |F| ≤ |K₀|`, `A = Ω₁(F ⊔ K₀) = Ω₁(F ⊔ K)` is
the *unique* subgroup of `F ⊔ K` of order `p²` of exponent `p` containing `P`
(`F ⊔ K = ⟨v₁,v₂⟩ = A`), `A ≤ F(U)`, `[S₀, U] = 1` (the action of `S = S₀ ∪ sS₀` on `U` is
`σ`), `U ⊄ M`, and `Q := Ω₁(Z₂(O_p(U))) = Ω₁(U) = U = C_p³` is normal in `U`, non-cyclic, of
exponent `p`, with `Q ≤ F(U)` and `|U : B₀ K F(U)| = 1 ≤ p`.  Nonetheless **both disjuncts fail**:

* `s` does *not* invert `Q` (`v₁ ∈ Q` is fixed), so the first disjunct is false;
* `A ≤ Q` holds, but `A ≠ Q` (order `p²` vs `p³`) and `Z(Q) = Q = C_p³ ≰ A`, so
  `A = Q ∨ centerIn Q < A` is false.

So the conclusion can fail while everything the recorded hypotheses assert *about this local
structure* holds; the missing ingredient is a genuine structural input of Bender's situation, not a
formal consequence of §4 (1)–(9).

## Corroboration in this workspace

The same obstruction is recorded repeatedly in the area: `Case2EightTrich9`, `EightIdxTrich`,
`EightExTrich`, `Case2EightUAnormalCtx`, `EightANF_QsubPos`, `EightQsubA`, `APcoreCtx`,
`CtxDisjANormal`, `Case2DisjANormal`, `Case2DisjULeP`, `Case2EightCasesOfCtx`,
`EightQposCtx/QposOfCtx` are all unproved, and `NOTES_CASE2NUMERIC.md` §2/§2b,
`NOTES_CASE2EIGHTALLOFCTX.md` and `EightExCase3.lean` (countermodel) record that this trichotomy
"is the one missing mathematical fact" and was twice reported not derivable.

## Suggested repair

Record the missing input as data, e.g. add to the hypothesis list (or as a field of `Case2Ctx`)
one of

* `A ≤ Qsub p B ∧ (A = Qsub p B ∨ centerIn (Qsub p B) < A)`  (Bender's cases 1–2), or
* `C_U(Q) ⊓ C_U(s) = ⊥` resp. `C_U(Q) ≤ invSet B.U D.s`  (Bender's case 3, which yields `s` inverts
  `Q` via `Q = C_Q(s) I_Q(s)`),

or split the statement accordingly.  With either input, the disjunction requested here is immediate
(`I.toolkit.c15` gives `Q = C_Q(s) · I_Q(s)`, so `C_Q(s) = ⊥` forces `s` to invert all of `Q`).

The statement below is left untouched (unproved); see the verdict reported to the requester.
-/

namespace Work.CORE4

theorem EightTrichOfCtx (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
          Work.GW2.Case2EightObj h.D p P A →
          ((∀ x ∈ Work.CORE4.Qsub p B, h.D.s * x * h.D.s⁻¹ = x⁻¹) ∨
            (A ≤ Work.CORE4.Qsub p B ∧ (A = Work.CORE4.Qsub p B ∨
              Work.CORE4.centerIn (Work.CORE4.Qsub p B) < A))) := by sorry

end Work.CORE4
