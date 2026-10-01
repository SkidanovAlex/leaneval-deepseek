/-
# LinnikContract2 — API.lean

The interface of the round-2 predicates, for the live area agents and for the assembly:
projections, monotonicity in the height `H`, the narrow/wide bridges, and the two forms of the
minimality (over `IsZ`, i.e. round-1's, and over `IsZW`, i.e. HB §12's) that consumers need.

Naming conventions (round 2):

| name | meaning |
|---|---|
| `IsZ χ ρ` | HB's working region: `χ ≠ 1`, `ρ` a zero, `\|Im ρ\| ≤ 1` (unchanged) |
| `IsZH H χ ρ` | HB's region at height `H`: `χ ≠ 1`, `ρ` a zero, `\|Im ρ\| ≤ H` |
| `IsZW χ ρ` | `IsZH 50 χ ρ` (the frozen round-2 wide region) |
| `IsMin1H H χ₁ ρ₁` | `IsZH H χ₁ ρ₁ ∧ ∀ χ u, IsZH H χ u → λ(ρ₁) ≤ λ(u)` (the wide minimiser) |
| `IsMin1 χ₁ ρ₁` | `IsMin1H 50 χ₁ ρ₁` — **the round-2 `IsMin1`** |
| `IsMin1N χ₁ ρ₁` | `IsMin1H 1 χ₁ ρ₁` — round 1's `IsMin1` (definitionally) |

The tables `rows15`, `rows14`, `table13` are round 1's, definitionally; see `Bridge.lean`.
-/
import Submission.Work.LinnikContract2.Defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

variable {q : ℕ} [NeZero q]

/-! ## The region predicates -/

@[simp] theorem isZ_ne_one {χ : DirichletCharacter ℂ q} {ρ : ℂ} (h : IsZ χ ρ) : χ ≠ 1 := h.1
@[simp] theorem isZ_mult_ne_zero {χ : DirichletCharacter ℂ q} {ρ : ℂ} (h : IsZ χ ρ) :
    zeroMult χ ρ ≠ 0 := h.2.1
@[simp] theorem isZ_im_le_one {χ : DirichletCharacter ℂ q} {ρ : ℂ} (h : IsZ χ ρ) : |ρ.im| ≤ 1 :=
  h.2.2

@[simp] theorem isZH_ne_one {H : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ} (h : IsZH H χ ρ) :
    χ ≠ 1 := h.1
@[simp] theorem isZH_mult_ne_zero {H : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZH H χ ρ) : zeroMult χ ρ ≠ 0 := h.2.1
@[simp] theorem isZH_im_le {H : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ} (h : IsZH H χ ρ) :
    |ρ.im| ≤ H := h.2.2

/-- `IsZ` is `IsZH 1`. -/
theorem isZ_iff_isZH_one {χ : DirichletCharacter ℂ q} {ρ : ℂ} : IsZ χ ρ ↔ IsZH 1 χ ρ := Iff.rfl

/-- **Coarsening the height.**  `IsZH H` implies `IsZH H'` for `H ≤ H'`. -/
theorem isZH_mono {H H' : ℝ} (hHH : H ≤ H') {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZH H χ ρ) : IsZH H' χ ρ := ⟨h.1, h.2.1, h.2.2.trans hHH⟩

/-- The working region is contained in the region of any height `≥ 1`, in particular in
`IsZW` (height `50`). -/
theorem IsZ.toIsZH {χ : DirichletCharacter ℂ q} {ρ : ℂ} {H : ℝ} (h : IsZ χ ρ) (hH : 1 ≤ H) :
    IsZH H χ ρ := ⟨h.1, h.2.1, h.2.2.trans hH⟩

/-- `IsZ` sits inside the wide region. -/
theorem IsZ.toIsZW {χ : DirichletCharacter ℂ q} {ρ : ℂ} (h : IsZ χ ρ) : IsZW χ ρ :=
  h.toIsZH (by norm_num)

/-! ## The minimality predicates -/

/-- **Restriction to a sub-region.**  `λ₁`-minimality over `|Im| ≤ H` gives `λ₁`-minimality over
any smaller region `|Im| ≤ H'`, `H' ≤ H`, provided the numbered zero itself lies in that smaller
region.  (This is the form in which `IsMin1` gives round 1's `IsMin1N`; note that the family is *not*
monotone as a predicate in `H`, since the bundled membership of `ρ₁` moves with `H`.) -/
theorem IsMin1H.of_le {H H' : ℝ} (hHH : H' ≤ H) {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1H H χ₁ ρ₁) (hZ : IsZH H' χ₁ ρ₁) : IsMin1H H' χ₁ ρ₁ :=
  ⟨hZ, fun _ _ hu => h.2 _ _ (isZH_mono hHH hu)⟩

/-- **The round-2 `IsMin1` implies round 1's**, provided the numbered zero lies in the working
region.  (Round 2 does *not* require that; it is supplied by `Z1` in the branch `λ₁ < 0.348`.) -/
theorem IsMin1.toIsMin1N {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsMin1 χ₁ ρ₁)
    (hZ : IsZ χ₁ ρ₁) : IsMin1N χ₁ ρ₁ :=
  IsMin1H.of_le (by norm_num) h hZ

/-- Round-1 minimality is round-2 minimality at height 1. -/
theorem isMin1N_iff {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} :
    IsMin1N χ₁ ρ₁ ↔ IsMin1H 1 χ₁ ρ₁ := Iff.rfl

/-! ### Projections of the frozen round-2 `IsMin1` -/

@[simp] theorem IsMin1.isZH {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsMin1 χ₁ ρ₁) :
    IsZW χ₁ ρ₁ := h.1

@[simp] theorem IsMin1.ne_one {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsMin1 χ₁ ρ₁) :
    χ₁ ≠ 1 := h.1.1

@[simp] theorem IsMin1.mult_ne_zero {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1 χ₁ ρ₁) : zeroMult χ₁ ρ₁ ≠ 0 := h.1.2.1

@[simp] theorem IsMin1.im_le {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsMin1 χ₁ ρ₁) :
    |ρ₁.im| ≤ 50 := h.1.2.2

-- NOTE (round 2, height 50): the old height-`10` projection `IsMin1.im_le_ten : |ρ₁.im| ≤ 10`
-- is *false* at the frozen height `50` (a wide minimiser may have `|Im| ≤ 50`); it has been
-- deleted.  Consumers wanting a bound on `ρ₁.im` use `IsMin1.im_le : |ρ₁.im| ≤ 50`.

/-- **The wide form of the minimality**: every non-principal zero of height `≤ 50` has
`λ ≥ λ₁`.  This is the hypothesis `DensityCert (D2)` consumes. -/
theorem IsMin1.le_lamOf {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsMin1 χ₁ ρ₁)
    {χ : DirichletCharacter ℂ q} {u : ℂ} (hu : IsZW χ u) : lamOf q ρ₁ ≤ lamOf q u :=
  h.2 χ u hu

/-- **The narrow form of the minimality**: every working-region zero has `λ ≥ λ₁` (this needs no
extra hypothesis: `IsZ` implies `IsZW`). -/
theorem IsMin1.le_lamOf_of_isZ {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsMin1 χ₁ ρ₁)
    {χ : DirichletCharacter ℂ q} {u : ℂ} (hu : IsZ χ u) : lamOf q ρ₁ ≤ lamOf q u :=
  h.le_lamOf hu.toIsZW

/-- The narrow form of the minimality for the family `IsMin1H`, `H ≥ 1`. -/
theorem IsMin1H.le_lamOf_of_isZ {H : ℝ} (hH : 1 ≤ H) {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1H H χ₁ ρ₁) {χ : DirichletCharacter ℂ q} {u : ℂ} (hu : IsZ χ u) :
    lamOf q ρ₁ ≤ lamOf q u :=
  h.2 χ u (hu.toIsZH hH)

/-- Round-2 `IsMin1` in round 1's *two-conjunct* shape, given that the numbered zero is in the
working region. -/
theorem IsMin1.toRound1Shape {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsMin1 χ₁ ρ₁)
    (hZ : IsZ χ₁ ρ₁) :
    IsZ χ₁ ρ₁ ∧ ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZ χ u → lamOf q ρ₁ ≤ lamOf q u :=
  ⟨hZ, fun _ _ hu => h.le_lamOf_of_isZ hu⟩

/-- `IsMin1H H` propagates to any zero of height `≤ H` with no larger `λ`. -/
theorem IsMin1H.trans_le {H : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ ρ₁' : ℂ}
    (h : IsMin1H H χ₁ ρ₁) (hZ : IsZH H χ₁ ρ₁') (hle : lamOf q ρ₁' ≤ lamOf q ρ₁) :
    IsMin1H H χ₁ ρ₁' :=
  ⟨hZ, fun _ _ hu => hle.trans (h.2 _ _ hu)⟩

/-! ## Interface lemmas for `(D2)` (HB Table 13 via Lemma 12.1) -/

/-- **The hypothesis of `(D2)` from the numbered pair.**  If `λ₁ = λ(ρ₁)` is the minimum of `λ`
over the wide region (round-2 `IsMin1`) and the table's column bound `e.1` is at most `λ₁`, then
`e.1` bounds the `λ` of *every* non-principal zero of height `≤ 10` — which is exactly the
hypothesis under which HB Lemma 12.1 (and hence Table 13) may be applied. -/
theorem d2_hyp_of_isMin1 {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (hmin : IsMin1 χ₁ ρ₁)
    {c : ℝ} (hcol : c ≤ lamOf q ρ₁) :
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZW χ u → c ≤ lamOf q u :=
  fun _ _ hu => hcol.trans (hmin.le_lamOf hu)

/-- The same at any smaller height `H ≤ 50` — the form in which the `P₃` engine of HB §§6–10 and
Lemma 12.1 use it (their windows have height `21 + δ` resp. `40 + δ`). -/
theorem d2_hyp_of_isMin1H {H : ℝ} (hH : H ≤ 50) {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hmin : IsMin1 χ₁ ρ₁) {c : ℝ} (hcol : c ≤ lamOf q ρ₁) :
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZH H χ u → c ≤ lamOf q u :=
  fun _ _ hu => hcol.trans (hmin.le_lamOf (isZH_mono hH hu))

/-- **The window form**: `λ₁` is at most the `λ` of every zero in a window of height `≤ 50`. -/
theorem IsMin1.window {H : ℝ} (hH : H ≤ 50) {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1 χ₁ ρ₁) :
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZH H χ u → lamOf q ρ₁ ≤ lamOf q u :=
  fun _ _ hu => h.le_lamOf (isZH_mono hH hu)

/-- The minimality over the working region, in the round-1 form (used by round-1 code that
applied `hmin.2` to a working-region zero). -/
theorem d2_hyp_narrow_of_isMin1 {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (hmin : IsMin1 χ₁ ρ₁)
    {c : ℝ} (hcol : c ≤ lamOf q ρ₁) :
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZ χ u → c ≤ lamOf q u :=
  fun _ _ hu => hcol.trans (hmin.le_lamOf_of_isZ hu)

/-- The wide minimality and the narrow minimality together (the `ZeroFreeTables`/`§15` interface):
round-2 `IsMin1` gives the working-region minimality without any extra input, and the narrow form
follows from the wide one applied to `IsZ.toIsZW`. -/
theorem IsMin1.parts {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsMin1 χ₁ ρ₁) :
    IsZW χ₁ ρ₁ ∧ (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZ χ u → lamOf q ρ₁ ≤ lamOf q u) ∧
      (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZW χ u → lamOf q ρ₁ ≤ lamOf q u) :=
  ⟨h.1, fun _ _ hu => h.le_lamOf_of_isZ hu, fun _ _ hu => h.le_lamOf hu⟩

end Work.LinnikContract2
