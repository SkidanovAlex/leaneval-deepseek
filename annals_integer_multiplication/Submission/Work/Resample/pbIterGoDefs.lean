import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.pbRoundDefs

/-!
# `Work.Resample.pbIterGo`: the aggregate budget

`pbIterGo` iterates the round block `Work.Resample.pbRound` `HvdH.D` times.  The budget of the
iterated program is the sum of the `D` per-round budgets `PBBracket` of `pbIterDefs`, which is
bounded by the single aggregate below (the estimate uses `(ss.take j).prod ≤ (ts.take j).prod`
together with `∏_{k<j} t k * t j * ∏_{k>j} t k = ts.prod` and `Σ_j (t j + 1) = ts.sum + D`).

* `PBAgg` — the aggregate budget of `pbIterGo`.
* `PBBracket_eq` — the per-round budget of `pbRound` is `PBBracket` (its statement writes the last
  summand as a product instead of a square).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-- The aggregate cost budget of `Work.Resample.pbIterGo`: the sum of the `D` per-round budgets
`PBBracket` over the `D` rounds (it does not depend on `ss`). -/
def PBAgg (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ts : List ℕ) : ℕ :=
    HvdH.D * (Kb * (ts.sum + 1) * (p + 1) ^ Kb)
  + ts.prod * (ts.sum + 1) *
      (Kb * (ts.sum + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
       + Kb * (ts.sum + 1) * (p + 1) ^ 2)
  + HvdH.D * ((ts.prod * (ts.sum + 1) + 1) * ((2 * p + 8) + (ts.prod * (ts.sum + 1)).size + 1) *
      ((ts.prod * (ts.sum + 1)).size + 1))
  + HvdH.D * (32 * (ts.prod * (2 * p + 8) + 2))
  + HvdH.D * (800 * (HvdH.D * (p + 1)))
  + HvdH.D * ((2 * Work.Resample.PBTab Kb p ts + 5) * (2 * Work.Resample.PBTab Kb p ts + 5))
  + HvdH.D * 100

/-- The per-round budget in the statement of `Work.Resample.pbRound` is exactly `PBBracket`. -/
theorem PBBracket_eq (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) :
    PBBracket Kb Cm p α ss ts j =
      (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb
      + ((ss.take j).prod * (ts.drop (j + 1)).prod) *
          (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
           + Kb * (ts.getD j 0 + 1) * (p + 1) ^ 2)
      + ((ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + ss.getD j 0 + 1) + 1) *
          ((2 * p + 8) + ((ss.take j).prod * (ts.drop (j + 1)).prod *
            (ts.getD j 0 + ss.getD j 0 + 1)).size + 1) *
          (((ss.take j).prod * (ts.drop (j + 1)).prod *
            (ts.getD j 0 + ss.getD j 0 + 1)).size + 1)
      + 32 * (ts.prod * (2 * p + 8) + 2)
      + 800 * (HvdH.D * (p + 1))
      + (2 * Work.Resample.PBTab Kb p ts + 5) * (2 * Work.Resample.PBTab Kb p ts + 5)
      + 100) := by
  simp only [PBBracket, pow_two]

end Work.Resample

namespace Work.Resample

open HvdH

/-- **The slice-application word** (paper Lemma 2.11, non-degenerate case), in the form needed to
build a round of `Work.Resample.pbRound`: there is a word constructor `comb` which, given a word `q`
mapping an `m`-slice to an `n`-slice (uniformly, at cost `c`), applies `q` to every slice of a flat
`A × m × B` array in the `slices`/`unslices` layout of `HvdH.LayoutLib.applyAlong`, at cost
`A*B*c` plus a polynomial overhead.  This is the statement of `Work.Resample.pbApplyAlong` (and of
`Work.Layout.applyAlongWord`); it is recorded here as a `Prop` so that the round block of
`pbIterGo` can be proved from it. -/
def ApplyAlongWord : Prop :=
  ∃ (comb : Cmd → Cmd) (K : ℕ),
    ∀ (main q : Cmd) (rest : List Val) (m n A B : ℕ)
      (P : List Val → Prop) (Q : List Val → List Val → Prop) (c L : ℕ),
      1 ≤ A → 1 ≤ m → 1 ≤ n → 1 ≤ B →
      (∀ sl : List Val, sl.length = m → P sl →
        WordR main q (fun vs => vs = ofList sl :: rest)
          (fun _ out => ∃ ol, out = ofList ol :: rest ∧ ol.length = n ∧ Q sl ol ∧
            ∀ y ∈ ol, vsz y ≤ L)
          (fun _ => c)) →
      ∀ (es : List Val), es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      (∀ s < A * B, P ((slices A m B es).getD s [])) →
      WordR main (comb q)
        (fun vs => vs = .int A :: .int m :: .int n :: .int B :: ofList es :: rest)
        (fun _ out => ∃ outs : List (List Val),
          out = ofList (unslices A n B outs) :: rest ∧ outs.length = A * B ∧
          ∀ s < A * B, (outs.getD s []).length = n ∧
            Q ((slices A m B es).getD s []) (outs.getD s []))
        (fun _ => A * B * c +
          K * (A * B * (m + n + 1) + 1) * (L + (A * B * (m + n + 1)).size + 1) *
            ((A * B * (m + n + 1)).size + 1) +
          K * (isz A + isz m + isz n + isz B))

end Work.Resample

namespace Work.Resample

open HvdH

/-- `PBAgg` is (definitionally) the aggregate budget written out in the statement of
`Work.Resample.pbIterGo`. -/
theorem PBAgg_eq (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ts : List ℕ) :
    PBAgg Kb Cm p α ts =
      (HvdH.D * (Kb * (ts.sum + 1) * (p + 1) ^ Kb)
      + ts.prod * (ts.sum + 1) *
          (Kb * (ts.sum + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
           + Kb * (ts.sum + 1) * (p + 1) ^ 2)
      + HvdH.D * ((ts.prod * (ts.sum + 1) + 1) * ((2 * p + 8) + (ts.prod * (ts.sum + 1)).size + 1) *
          ((ts.prod * (ts.sum + 1)).size + 1))
      + HvdH.D * (32 * (ts.prod * (2 * p + 8) + 2))
      + HvdH.D * (800 * (HvdH.D * (p + 1)))
      + HvdH.D * ((2 * Work.Resample.PBTab Kb p ts + 5) * (2 * Work.Resample.PBTab Kb p ts + 5))
      + HvdH.D * 100) := rfl

end Work.Resample
