import Mathlib
import Submission.Work.Resample.pb2eDefs
import Submission.Work.Resample.pb2eBrFacts
import Submission.Work.Resample.paProdWordCost

namespace Work.Resample

open HvdH

/-!
# The cost of a product word over a bounded list (budget `PB2Br`)

Mirror of `Submission/Work/Resample/paProdWordCost.lean` for the `B̃` half of paper Theorem 4.1.
The `B̃` program multiplies, inside one axis step, a list `l` of natural numbers (the exponents of
the table it builds) against a running product whose size is bounded by
`B ≤ (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)`.

The estimate `Kw * (l.length + 1) * (Σ isz t + B.size + 2) * (B.size + 2)` is bounded by a constant
multiple of the per-axis budget `PB2Br`, uniformly in `Kb`, `Cm`, `p`, `α`, `ss`, `ts`, `j`.  The
proof is the same pure size arithmetic as in the `Ã` half: `Σ_{t∈l} isz (t:ℤ) ≤ l.length * (p+2)`
(`Work.Resample.paSumIszLe`), `B.size ≤ X.size` for the explicit running product `X`
(`Work.Resample.pb2Xge6` gives `X ≥ 6`), and the third summand of `PB2Br`
(`Work.Resample.pb2PB2BrThird`) absorbs the quadratic size term through
`Work.Resample.paWordCostArith`.
-/

/-- The cost estimate with the running-product bound `X` as an explicit parameter. -/
theorem pb2WordCostAux {Kb Kw p α j X : ℕ} {Cm : ℕ → ℕ} {ss ts : List ℕ}
    (hXdef : X = (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1))
    (hX : 6 ≤ X) (l : List ℕ) (B : ℕ) (hlen : l.length ≤ HvdH.D)
    (hit : ∀ t ∈ l, t < 2 ^ p) (hB : B ≤ X) :
    Kw * (l.length + 1) * (((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum) + B.size + 2) * (B.size + 2)
      ≤ 7 * Kw * (HvdH.D + 1) * Work.Resample.PB2Br Kb Cm p α ss ts j := by
  set S : ℕ := (l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum with hSdef
  have hsum : S ≤ HvdH.D * (p + 2) := by
    rw [hSdef]
    exact le_trans (paSumIszLe l p hit) (Nat.mul_le_mul_right _ hlen)
  have hsz : B.size ≤ X.size := Nat.size_le_size hB
  have harith := paWordCostArith (D := HvdH.D) (p := p) (X := X) (by rw [HvdH.D]) hX
  have hthird : 64 * ((X + 1) * ((2 * p + 8) + X.size + 1) * (X.size + 1))
      ≤ Work.Resample.PB2Br Kb Cm p α ss ts j := by
    rw [hXdef]
    exact pb2PB2BrThird Kb Cm p α ss ts j
  have hcore : (l.length + 1) * (S + B.size + 2) * (B.size + 2)
      ≤ 7 * (HvdH.D + 1) * (64 * ((X + 1) * ((2 * p + 8) + X.size + 1) * (X.size + 1))) := by
    have hA : S + B.size + 2 ≤ HvdH.D * (p + 2) + X.size + 2 := by omega
    have hB2 : B.size + 2 ≤ X.size + 2 := by omega
    have hn1 : l.length + 1 ≤ HvdH.D + 1 := by omega
    have hstep1 : (l.length + 1) * (S + B.size + 2) * (B.size + 2)
        ≤ (HvdH.D + 1) * ((HvdH.D * (p + 2) + X.size + 2) * (X.size + 2)) := by
      have h := Nat.mul_le_mul (Nat.mul_le_mul hn1 hA) hB2
      calc (l.length + 1) * (S + B.size + 2) * (B.size + 2)
          ≤ (HvdH.D + 1) * (HvdH.D * (p + 2) + X.size + 2) * (X.size + 2) := h
        _ = (HvdH.D + 1) * ((HvdH.D * (p + 2) + X.size + 2) * (X.size + 2)) := by ring
    calc (l.length + 1) * (S + B.size + 2) * (B.size + 2)
        ≤ (HvdH.D + 1) * ((HvdH.D * (p + 2) + X.size + 2) * (X.size + 2)) := hstep1
      _ ≤ (HvdH.D + 1) * (448 * (X + 1) * (2 * p + 8 + X.size + 1) * (X.size + 1)) :=
          Nat.mul_le_mul_left _ harith
      _ = 7 * (HvdH.D + 1) * (64 * ((X + 1) * ((2 * p + 8) + X.size + 1) * (X.size + 1))) := by
          ring
  calc Kw * (l.length + 1) * (S + B.size + 2) * (B.size + 2)
      = Kw * ((l.length + 1) * (S + B.size + 2) * (B.size + 2)) := by ring
    _ ≤ Kw * (7 * (HvdH.D + 1) *
          (64 * ((X + 1) * ((2 * p + 8) + X.size + 1) * (X.size + 1)))) :=
        Nat.mul_le_mul_left _ hcore
    _ ≤ Kw * (7 * (HvdH.D + 1) * (Work.Resample.PB2Br Kb Cm p α ss ts j)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hthird)
    _ = 7 * Kw * (HvdH.D + 1) * (Work.Resample.PB2Br Kb Cm p α ss ts j) := by ring

theorem pb2ProdWordCost {Kb Kw p α j : ℕ} {Cm : ℕ → ℕ} {ss ts : List ℕ}
    (hRes : HvdH.ResParams p α ss ts) (hj : j < HvdH.D) (l : List ℕ) (B : ℕ)
    (hlen : l.length ≤ HvdH.D) (hit : ∀ t ∈ l, t < 2 ^ p)
    (hB : B ≤ (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)) :
    Kw * (l.length + 1) * (((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum) + B.size + 2) * (B.size + 2)
      ≤ 7 * Kw * (HvdH.D + 1) * Work.Resample.PB2Br Kb Cm p α ss ts j :=
  pb2WordCostAux (Kb := Kb) (Kw := Kw) (p := p) (α := α) (j := j)
    (X := (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1))
    rfl (pb2Xge6 hRes hj) l B hlen hit hB

end Work.Resample
