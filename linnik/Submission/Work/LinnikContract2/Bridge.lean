/-
# LinnikContract2 — Bridge.lean

**What round 1 gives round 2, for free.**  Every round-1 definition that round 2 keeps
unchanged is a *definitional* copy, so the corresponding propositions are *definitionally
equal*; the `rfl`/`Iff.rfl` theorems below are machine-checked proofs of that, and they are what
makes the round-1 development (`Submission/Work/A7/`, `Submission/Work/LinnikAreas/A7/`,
`Submission/Work/ZeroFreeTables/`, `Submission/Work/LinnikAreas/A5/`, …) reusable verbatim.

The only definition round 2 changes is `IsMin1`, whose round-1 meaning is kept as `IsMin1N`
(`= IsMin1H 1`), definitionally equal to round 1's `IsMin1`.  Hence:

* `IsMin1N χ₁ ρ₁ ↔ Work.LinnikContract.IsMin1 χ₁ ρ₁` (definitional),
* `IsMin1 χ₁ ρ₁ → Work.LinnikContract.IsMin1 χ₁ ρ₁` (`IsMin1.toRound1`),
* `rows15`, `rows14`, `table13`, `Area1`, `Area2`, `Area5`, `Area6` are *definitionally*
  round 1's, so the round-1 proofs of `Area5` (and any future proof of `Area1`/`Area2`/`Area6`)
  transport with `exact`;
* round-1 `DensityCert` implies the round-2 one (`(D2)`'s round-2 hypothesis is over the *wide*
  region, hence stronger than round 1's, so round 2's statement is weaker);
* round-1 `ZeroFreeCert` implies the round-2 one **for the wide minimisers that lie in the working
  region** (with that side condition: round 1's certificate is stated for narrow-minimal pairs, and
  a round-2 pair is narrowed-minimal only when it lies in `|Im| ≤ 1`).
-/
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikContract.Areas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

variable {q : ℕ} [NeZero q]

/-! ## The definitions are round 1's, definitionally -/

theorem lamOf_eq (q : ℕ) (ρ : ℂ) : lamOf q ρ = Work.LinnikContract.lamOf q ρ := rfl
theorem zeroMult_eq {χ : DirichletCharacter ℂ q} {ρ : ℂ} :
    zeroMult χ ρ = Work.LinnikContract.zeroMult χ ρ := rfl
theorem IsZ_iff_round1 {χ : DirichletCharacter ℂ q} {ρ : ℂ} :
    IsZ χ ρ ↔ Work.LinnikContract.IsZ χ ρ := Iff.rfl
theorem lamMax_eq (q : ℕ) : lamMax q = Work.LinnikContract.lamMax q := rfl
theorem lamChar_eq {χ : DirichletCharacter ℂ q} :
    lamChar χ = Work.LinnikContract.lamChar χ := rfl
theorem Ncount_eq (q : ℕ) [NeZero q] (lam : ℝ) :
    Ncount q lam = Work.LinnikContract.Ncount q lam := rfl
theorem wHB_eq (x : ℝ) : wHB x = Work.LinnikContract.wHB x := rfl
theorem Bfun_eq (K lam : ℝ) : Bfun K lam = Work.LinnikContract.Bfun K lam := rfl
theorem F2_eq (K : ℝ) (z : ℂ) : F2 K z = Work.LinnikContract.F2 K z := rfl
theorem Hk_eq (L K : ℝ) (z : ℂ) : Hk L K z = Work.LinnikContract.Hk L K z := rfl
omit [NeZero q] in
theorem InBox_iff {R : ℝ} {ρ : ℂ} : InBox q R ρ ↔ Work.LinnikContract.InBox q R ρ := Iff.rfl
theorem boxSum_eq (q : ℕ) [NeZero q] (L K R : ℝ) (χ : DirichletCharacter ℂ q) :
    boxSum q L K R χ = Work.LinnikContract.boxSum q L K R χ := rfl
theorem boxAbs_eq (q : ℕ) [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) :
    boxAbs q K R χ = Work.LinnikContract.boxAbs q K R χ := rfl
theorem SiegelZero_iff {lamS : ℝ} :
    SiegelZero q lamS ↔ Work.LinnikContract.SiegelZero q lamS := Iff.rfl
theorem Lam0Bound_iff {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {c : ℝ} :
    Lam0Bound χ₁ ρ₁ c ↔ Work.LinnikContract.Lam0Bound χ₁ ρ₁ c := Iff.rfl
theorem Lam2Bound_iff {χ₁ : DirichletCharacter ℂ q} {c : ℝ} :
    Lam2Bound χ₁ c ↔ Work.LinnikContract.Lam2Bound χ₁ c := Iff.rfl
theorem Lam3Bound_iff {χ₁ : DirichletCharacter ℂ q} {c : ℝ} :
    Lam3Bound χ₁ c ↔ Work.LinnikContract.Lam3Bound χ₁ c := Iff.rfl

/-! ## The tables are round 1's -/

theorem rows15_eq : rows15 = Work.LinnikContract.rows15 := rfl
theorem rows14_eq : rows14 = Work.LinnikContract.rows14 := rfl
theorem table13_eq : table13 = Work.LinnikContract.table13 := rfl

/-! ## The minimality: round 1's predicate is `IsMin1N` -/

/-- Round 1's `IsMin1` **is** `IsMin1N`, definitionally. -/
theorem IsMin1N_iff_round1 {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} :
    IsMin1N χ₁ ρ₁ ↔ Work.LinnikContract.IsMin1 χ₁ ρ₁ := Iff.rfl

/-- Round 1's `IsMin1` **is** `IsMin1N`, definitionally (the function form). -/
theorem IsMin1N_round1 (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) :
    IsMin1N χ₁ ρ₁ = Work.LinnikContract.IsMin1 χ₁ ρ₁ := rfl

/-- **The bridge that carries round-1 proofs over.**  If a round-2 `IsMin1` pair happens to lie in
the working region (`IsZ χ₁ ρ₁` — supplied by `Z1` in the branch `λ₁ < 0.348`), then it *is* a
round-1 `IsMin1` pair, so every round-1 lemma stated for round-1 `IsMin1` applies to it verbatim. -/
theorem IsMin1.toRound1 {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsMin1 χ₁ ρ₁)
    (hZ : Work.LinnikContract.IsZ χ₁ ρ₁) : Work.LinnikContract.IsMin1 χ₁ ρ₁ :=
  IsMin1.toIsMin1N h hZ

/-- Conversely a round-1 `IsMin1` is an `IsMin1N`. -/
theorem IsMin1N.ofRound1 {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : Work.LinnikContract.IsMin1 χ₁ ρ₁) : IsMin1N χ₁ ρ₁ := h

/-! ## The areas that do not mention the minimality's height -/

theorem Area1_iff : Work.LinnikContract.Area1 ↔ Area1 := Iff.rfl
theorem Area2_iff : Work.LinnikContract.Area2 ↔ Area2 := Iff.rfl
theorem PerCharCert_iff : Work.LinnikContract.PerCharCert ↔ PerCharCert := Iff.rfl
theorem Area5_iff : Work.LinnikContract.Area5 ↔ Area5 := Iff.rfl
theorem Area6_iff : Work.LinnikContract.Area6 ↔ Area6 := Iff.rfl

/-- Area 1 transports between the two editions. -/
theorem area1_round1 (h : Work.LinnikContract.Area1) : Area1 := h
/-- Area 2 transports between the two editions. -/
theorem area2_round1 (h : Work.LinnikContract.Area2) : Area2 := h
/-- Area 5 transports between the two editions. -/
theorem area5_round1 (h : Work.LinnikContract.Area5) : Area5 := h
/-- Area 6 transports between the two editions. -/
theorem area6_round1 (h : Work.LinnikContract.Area6) : Area6 := h

/-! ## The certificates: round 1 implies round 2 -/

/-- **The round-1 zero-free certificate covers the round-2 pairs that lie in the working region.**
The `Z`-clauses are literally the same propositions; what round 2 changes is the *class of pairs*
they are stated for (the wide minimisers).  Round 1's certificate covers the subclass of wide
minimisers that happen to lie in `|Im| ≤ 1`, which is exactly the class `A7/Area7.lean` runs the
§§14–15 machinery on. -/
theorem zeroFreeCert_round1_to_round2 (h : Work.LinnikContract.ZeroFreeCert)
    (hisZ : ∀ (q : ℕ) [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1 χ₁ ρ₁ → Work.LinnikContract.IsZ χ₁ ρ₁) : ZeroFreeCert := by
  intro lamS hS
  obtain ⟨q₀, hq⟩ := h lamS hS
  exact ⟨q₀, fun q hq' _ χ₁ ρ₁ hmin => hq q hq' χ₁ ρ₁ (hmin.toRound1 (hisZ q χ₁ ρ₁ hmin))⟩

/-- The round-1 density certificate implies the round-2 one.  `(D1)` is common, and for `(D2)`
the round-1 hypothesis (over `IsZ`) is weaker than round 2's (over `IsZW`), hence round 1's
statement is stronger. -/
theorem densityCert_round1_to_round2 (h : Work.LinnikContract.DensityCert) : DensityCert := by
  refine ⟨h.1, fun e he => ?_⟩
  obtain ⟨q₀, hq⟩ := h.2 e he
  exact ⟨q₀, fun q hq' _ hwide => hq q hq' (fun χ ρ hZ => hwide χ ρ (IsZ.toIsZW hZ))⟩

/-- `Area3` transports, under the same side condition as
`zeroFreeCert_round1_to_round2`. -/
theorem area3_round1_to_round2 (h : Work.LinnikContract.Area3)
    (hisZ : ∀ (q : ℕ) [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1 χ₁ ρ₁ → Work.LinnikContract.IsZ χ₁ ρ₁) : Area3 :=
  fun h1 => zeroFreeCert_round1_to_round2 (h h1) hisZ

/-- `Area4` transports: round 1's area 4 implies round 2's.  (Round 2 is the *weaker*
statement here, since it assumes more about `λ₁` in `(D2)`.) -/
theorem area4_round1_to_round2 (h : Work.LinnikContract.Area4) : Area4 :=
  fun h1 => densityCert_round1_to_round2 (h h1)

end Work.LinnikContract2
