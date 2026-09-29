import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paBasic

namespace Work.Resample

open HvdH

/-!
# The cost of a product word over a bounded list (budget `PABr`)

The `Ã` program multiplies, inside one axis step, a list `l` of natural numbers (the exponents of
the table it builds) against a running product whose size is bounded by
`B ≤ (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)`.

This file proves the resulting *cost* estimate: the naive multiply-accumulate cost
`Kw * (l.length + 1) * (Σ_{t ∈ l} isz t + B.size + 2) * (B.size + 2)` is bounded by a constant
multiple of the per-axis budget `PABr`, uniformly in `Kb`, `Cm`, `p`, `α`, `ss`, `ts`, `j`.

The proof is pure size arithmetic:

* `Σ_{t ∈ l} isz (t : ℤ) ≤ l.length * (p + 2)` because `t < 2^p` gives `t.size ≤ p` and
  `isz (t : ℤ) = t.size + 2` (`Work.Resample.paSumIszLe`);
* `B.size ≤ X.size` for `X = (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)`;
* `X ≥ 6` in a `ResParams` setting (`Work.Resample.paXge6`), because every `ss`-entry is `≥ 2`,
  every `ts`-entry is `> ss`-entry, and products of non-empty lists of naturals are `≥ 1`;
* the budget `PABr` contains the summand `64 * (X + 1) * ((2p + 8) + X.size + 1) * (X.size + 1)`
  (`Work.Resample.paPABrThird`), which absorbs the quadratic size term
  (`Work.Resample.paWordCostArith`).
-/

/-! ## Elementary product facts -/

/-- The product of a list of naturals all `≥ 1` is `≥ 1`. -/
theorem paOneLeProd {l : List ℕ} (h : ∀ x ∈ l, 1 ≤ x) : 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    exact Nat.mul_le_mul (h a (List.mem_cons_self ..))
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

/-- Every entry of `ts` is `≥ 1` in a `ResParams` setting (in fact `≥ 3`). -/
theorem paOneLeTs {p α : ℕ} {ss ts : List ℕ} (hRes : HvdH.ResParams p α ss ts) :
    ∀ x ∈ ts, 1 ≤ x := by
  intro x hx
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  have hiD : i < HvdH.D := by rw [← hRes.2.1]; exact hi
  have h1 := (hRes.2.2.2.2.2 i hiD).1
  have h2 := (hRes.2.2.2.2.2 i hiD).2.1
  rw [← hix, ← List.getD_eq_getElem ts 0 hi]
  omega

/-! ## The two size bounds -/

/-- `isz (t : ℤ) = t.size + 2 ≤ p + 2` for the entries of `l` (all of which are `< 2^p`), hence
`Σ_{t ∈ l} isz (t : ℤ) ≤ l.length * (p + 2)`. -/
theorem paSumIszLe (l : List ℕ) (p : ℕ) (hit : ∀ t ∈ l, t < 2 ^ p) :
    (l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum ≤ l.length * (p + 2) := by
  have h1 : ∀ t ∈ l, HvdH.isz (t : ℤ) ≤ p + 2 := by
    intro t ht
    have h2 : t.size ≤ p := Nat.size_le.mpr (hit t ht)
    have h3 : HvdH.isz (t : ℤ) = t.size + 2 := by simp [HvdH.isz, Int.natAbs_natCast]
    omega
  calc (l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum
      ≤ (l.map (fun _ => p + 2)).sum := List.sum_le_sum h1
    _ = l.length * (p + 2) := by simp

/-- The running product bound `X = (ts.take j).prod * (ss.drop (j + 1)).prod *
(ss.getD j 0 + ts.getD j 0 + 1)` is at least `6` in a `ResParams` setting. -/
theorem paXge6 {p α j : ℕ} {ss ts : List ℕ} (hRes : HvdH.ResParams p α ss ts) (hj : j < HvdH.D) :
    6 ≤ (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) := by
  have hA : 1 ≤ (ts.take j).prod :=
    paOneLeProd (fun x hx => paOneLeTs hRes x ((List.take_sublist j ts).subset hx))
  have hB : 1 ≤ (ss.drop (j + 1)).prod := by
    refine paOneLeProd (fun x hx => ?_)
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    have hidx : i + (j + 1) < HvdH.D := by
      have hlen : i < (ss.drop (j + 1)).length := hi
      rw [List.length_drop, hRes.1] at hlen
      omega
    have h1 : 2 ≤ ss.getD (i + (j + 1)) 0 := (hRes.2.2.2.2.2 (i + (j + 1)) hidx).1
    rw [← hix, ← List.getD_eq_getElem (ss.drop (j + 1)) 0 hi, pa_getD_drop ss (j + 1) i hi]
    omega
  have hC : 6 ≤ ss.getD j 0 + ts.getD j 0 + 1 := by
    have h1 := (hRes.2.2.2.2.2 j hj).1
    have h2 := (hRes.2.2.2.2.2 j hj).2.1
    omega
  calc (6 : ℕ) = 1 * 1 * 6 := by norm_num
    _ ≤ (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hA hB) hC

/-! ## The budget `PABr` contains its "size" summand -/

/-- The third summand of `PABr` is a lower bound for the whole budget. -/
theorem paPABrThird (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) :
    64 * (((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ts.take j).prod * (ss.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size + 1))
    ≤ Work.Resample.PABr Kb Cm p α ss ts j := by
  unfold Work.Resample.PABr
  have h : ∀ a b c d e f g h i : ℕ, c ≤ a + b + c + d + e + f + g + h + i := by
    intro a b c d e f g h i; omega
  exact h _ _ _ _ _ _ _ _ _

/-! ## The size arithmetic -/

/-- The quadratic size term is absorbed by the third summand of `PABr` (up to the constant factor
`448 = 7 * 64`): for `X ≥ 6`,
`(D(p+2) + X.size + 2) * (X.size + 2) ≤ 448 * (X+1) * (2p + 8 + X.size + 1) * (X.size + 1)`. -/
theorem paWordCostArith {D p X : ℕ} (hD : D ≤ 1729) (hX : 6 ≤ X) :
    (D * (p + 2) + X.size + 2) * (X.size + 2)
      ≤ 448 * (X + 1) * (2 * p + 8 + X.size + 1) * (X.size + 1) := by
  have hxs1 : 1 ≤ X.size := by
    have h0 : 0 < X := by omega
    have h1 := Nat.size_pos.mpr h0
    omega
  have hstep : 2 * (D * (p + 2) + X.size + 2) ≤ 448 * (X + 1) * (2 * p + 8 + X.size + 1) := by
    nlinarith [hD, hX, hxs1]
  calc (D * (p + 2) + X.size + 2) * (X.size + 2)
      ≤ (D * (p + 2) + X.size + 2) * (2 * (X.size + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (D * (p + 2) + X.size + 2) * (X.size + 1) := by ring
    _ ≤ 448 * (X + 1) * (2 * p + 8 + X.size + 1) * (X.size + 1) := Nat.mul_le_mul_right _ hstep

/-! ## The cost estimate -/

/-- The cost estimate with the running-product bound `X` as an explicit parameter. -/
theorem paWordCostAux {Kb Kw p α j X : ℕ} {Cm : ℕ → ℕ} {ss ts : List ℕ}
    (hXdef : X = (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1))
    (hX : 6 ≤ X) (l : List ℕ) (B : ℕ) (hlen : l.length ≤ HvdH.D)
    (hit : ∀ t ∈ l, t < 2 ^ p) (hB : B ≤ X) :
    Kw * (l.length + 1) * (((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum) + B.size + 2) * (B.size + 2)
      ≤ 7 * Kw * (HvdH.D + 1) * Work.Resample.PABr Kb Cm p α ss ts j := by
  set S : ℕ := (l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum with hSdef
  have hsum : S ≤ HvdH.D * (p + 2) := by
    rw [hSdef]
    exact le_trans (paSumIszLe l p hit) (Nat.mul_le_mul_right _ hlen)
  have hsz : B.size ≤ X.size := Nat.size_le_size hB
  have harith := paWordCostArith (D := HvdH.D) (p := p) (X := X) (by rw [HvdH.D]) hX
  have hthird : 64 * ((X + 1) * ((2 * p + 8) + X.size + 1) * (X.size + 1))
      ≤ Work.Resample.PABr Kb Cm p α ss ts j := by
    rw [hXdef]
    exact paPABrThird Kb Cm p α ss ts j
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
    _ ≤ Kw * (7 * (HvdH.D + 1) * (Work.Resample.PABr Kb Cm p α ss ts j)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hthird)
    _ = 7 * Kw * (HvdH.D + 1) * (Work.Resample.PABr Kb Cm p α ss ts j) := by ring

theorem paProdWordCost {Kb Kw p α j : ℕ} {Cm : ℕ → ℕ} {ss ts : List ℕ}
    (hRes : HvdH.ResParams p α ss ts) (hj : j < HvdH.D) (l : List ℕ) (B : ℕ)
    (hlen : l.length ≤ HvdH.D) (hit : ∀ t ∈ l, t < 2 ^ p)
    (hB : B ≤ (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)) :
    Kw * (l.length + 1) * (((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum) + B.size + 2) * (B.size + 2)
      ≤ 7 * Kw * (HvdH.D + 1) * Work.Resample.PABr Kb Cm p α ss ts j :=
  paWordCostAux (Kb := Kb) (Kw := Kw) (p := p) (α := α) (j := j)
    (X := (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1))
    rfl (paXge6 hRes hj) l B hlen hit hB

end Work.Resample
