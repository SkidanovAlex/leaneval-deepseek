import Submission.Work.BG.Thm43Defs

/-!
# Area BG: a corrected Lemma 4.1 (iii) statement

`Work.GW2.C23.L41iiiProp` (`BG/Thm43Defs.lean`, copied from the lead's
`_design_gw/Core23B.lean`) asserts, for **every** `χ : ClassFunction G ℂ` with `IsPmIrr χ`,

* `(bset' C β₂ χ).Finite`, and
* `χ ≡ Σ_{ν ∈ bset' C β₂ χ} ν̂` (mod 2) on `B`,

with no hypothesis that `𝒮'(χ) := bset' C β₂ χ` is non-empty.  The source
(Bender–Glauberman 1981, Lemma 4.1, p. 212) states it *"for `χ ∈ ±Irr(G)` with `𝒮'(χ)` not
empty"*, and the sibling leaf `Lemma41Prop` (BG Lemma 4.1 (i),(ii),(iv)) does carry
`(bset' C β₂ χ).Nonempty`.

With `𝒮'(χ) = ∅` the right-hand side is the empty sum `0`, so the conclusion becomes
`AlgIntModTwo (χ b) 0` for **every** `b ∈ B`, i.e. `χ(b)/2` is an algebraic integer for all
`b ∈ B` — in particular `χ(1)` even.  Nothing in `Compat`, `D.n = 2`, `IsPmIrr` forces that,
and the printed route (Lemma 24 (iii) plus the bijection `𝒮(χ) ↔ 𝒮'(χ)`) gives no information
when the index set is empty.  See `NOTES_FALSE_L41iiiProp.md`.

`L41iiiProp'` below is the corrected statement: exactly the design's Prop with the source's
hypothesis `(bset' C β₂ χ).Nonempty` inserted.  Every consumer (`L41vProp`, `CongContraProp`,
`CaseAProp`, `CaseBProp`) works with an *inhabited* `bset'` (it is invoked at some
`ν ∈ bset' C β₂ χ`), so the correction costs nothing downstream.
-/

namespace Work.GW2.C23

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **L41-iii, corrected** (BG p. 212): for `χ ∈ ±Irr(G)` with `𝒮'(χ) ≠ ∅`,
`χ ≡ Σ_{ν ∈ 𝒮'(χ)} ν̂` (mod 2) on `B`. -/
def L41iiiProp' (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 →
    ∀ χ : ClassFunction G ℂ, IsPmIrr χ → (bset' C β₂ χ).Nonempty →
      (bset' C β₂ χ).Finite ∧
      ∀ θ : ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥D.B ℂ,
        (∀ ν ∈ bset' C β₂ χ, HatOf D C ν (θ ν)) →
        ∀ b : ↥D.B, AlgIntModTwo (χ (b : G)) (∑ᶠ ν ∈ bset' C β₂ χ, θ ν b)

end Work.GW2.C23
