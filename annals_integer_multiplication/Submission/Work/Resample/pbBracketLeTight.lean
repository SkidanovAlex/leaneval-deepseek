import Mathlib
import Submission.Work.Resample.pbIterDefs
import Submission.Work.Resample.pbRoundDefs
import Submission.Work.Resample.axisDefs

/-!
# `Work.Resample.pbBracketLeTight`: the bracket arithmetic of Theorem 4.1 (`B̃` half)

`PBTight` is the *tight* cost bracket of the D-fold iteration `pbIterTight`, i.e. `D` times the
budget of a single round in which every global quantity is replaced by `ts` alone:

* `ts.getD j 0 + 1 ≤ ts.sum + 1`,
* `(ss.take j).prod * (ts.drop (j+1)).prod * (ts.getD j 0 + 1) ≤ 4 * ts.prod`,
* `(ss.take j).prod * (ts.drop (j+1)).prod * (ts.getD j 0 + ss.getD j 0 + 1) ≤ ts.prod * 2^(p+1)`.

This file proves that the *actual* round brackets `PBBracket` sum to at most `PBTight`, using only
`HvdH.ResParams p α ss ts` (in particular `ss.length = ts.length = D` and `2 ≤ ssᵢ < tsᵢ`): the
list-facts `ssᵢ < tsᵢ` and `i < D` turn every factor `(ss.take j).prod * (ts.drop (j+1)).prod * tⱼ`
into at most `2 * ts.prod`, which the constant `4` of `PBTight` absorbs.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Elementary list facts (self-contained, so that this file has no extra dependencies) -/

/-- Splitting a list at an index: `(l.take i).prod * lᵢ * (l.drop (i+1)).prod = l.prod`. -/
theorem pbTight_prod_split (l : List ℕ) {i : ℕ} (hi : i < l.length) :
    (l.take i).prod * l.getD i 0 * (l.drop (i + 1)).prod = l.prod := by
  have h := List.prod_take_mul_prod_drop l i
  rw [List.drop_eq_getElem_cons hi, List.prod_cons] at h
  rw [List.getD_eq_getElem l 0 hi, mul_assoc]
  exact h

/-- An entry of a list of naturals is at most its sum. -/
theorem pbTight_getD_le_sum {l : List ℕ} {i : ℕ} (hi : i < l.length) : l.getD i 0 ≤ l.sum := by
  rw [List.getD_eq_getElem l 0 hi]
  exact List.le_sum_of_mem (List.getElem_mem hi)

/-- Products of equally long lists whose entries compare pointwise (`getD`) compare: applied to
the prefixes this gives `(l₁.take i).prod ≤ (l₂.take i).prod`. -/
theorem pbTight_take_prod_le {l₁ l₂ : List ℕ} (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i 0 ≤ l₂.getD i 0) {i : ℕ} (hi : i ≤ l₁.length) :
    (l₁.take i).prod ≤ (l₂.take i).prod := by
  rw [prod_take_range_getD l₁ hi, prod_take_range_getD l₂ (by omega)]
  refine List.prod_le_prod (fun j hj => ?_)
  simp only [List.mem_range] at hj
  exact h j (by omega)

/-- A list of naturals whose entries are `≥ 1` (read off with `getD`) has product `≥ 1`. -/
theorem pbTight_one_le_prod {l : List ℕ} (h : ∀ i, i < l.length → 1 ≤ l.getD i 0) :
    1 ≤ l.prod := by
  refine List.one_le_prod (fun x hx => ?_)
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [← List.getD_eq_getElem l 0 hk]
  exact h k hk

/-! ## The per-round budget of `PBTight` -/

/-- The budget `PBTight` allows for a single round: `PBTight = D * pbTight_perRound`. -/
def pbTight_perRound (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ts : List ℕ) : ℕ :=
    Kb * (ts.sum + 1) * (p + 1) ^ Kb
  + 4 * ts.prod * (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) + Kb * (p + 1) ^ 2)
  + 4 * ts.prod * (((2 * p + 8) + (ts.prod * 2 ^ (p + 1)).size + 1)
      * ((ts.prod * 2 ^ (p + 1)).size + 1))
  + 32 * (ts.prod * (2 * p + 8) + 2)
  + 800 * (HvdH.D * (p + 1))
  + (2 * PBTab Kb p ts + 5) * (2 * PBTab Kb p ts + 5)
  + 100

/-- `PBTight` is `D` times the per-round budget. -/
theorem pbTight_eq (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) :
    PBTight Kb Cm p α ss ts = HvdH.D * pbTight_perRound Kb Cm p α ts := by
  unfold PBTight pbTight_perRound
  ring

/-- **The per-round bound.**  Under `ResParams`, the round bracket `PBBracket i` fits into the
per-round budget `pbTight_perRound`: the tight bracket replaces
`(ss.take i).prod * (ts.drop (i+1)).prod * (ts.getD i 0 + 1)` by `4 * ts.prod` and
`(ss.take i).prod * (ts.drop (i+1)).prod * (ts.getD i 0 + ss.getD i 0 + 1)` by
`ts.prod * 2 ^ (p + 1)`. -/
theorem pbTight_bracket_le (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ)
    (h : HvdH.ResParams p α ss ts) {i : ℕ} (hi : i < HvdH.D) :
    PBBracket Kb Cm p α ss ts i ≤ pbTight_perRound Kb Cm p α ts := by
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hpt⟩ := h
  have hilt : i < ts.length := by rw [htslen]; exact hi
  have h2s : 2 ≤ ss.getD i 0 := (hpt i hi).1
  have hst : ss.getD i 0 < ts.getD i 0 := (hpt i hi).2.1
  -- the product of the `ss`-prefix is at most the product of the `ts`-prefix
  have hA : (ss.take i).prod ≤ (ts.take i).prod := by
    refine pbTight_take_prod_le (by rw [hsslen, htslen]) (fun j hj => ?_)
      (by rw [hsslen]; omega)
    have hj' : j < HvdH.D := by rw [hsslen] at hj; exact hj
    exact le_of_lt (hpt j hj').2.1
  -- the split identity for `ts.prod`
  have hT : (ts.take i).prod * ts.getD i 0 * (ts.drop (i + 1)).prod = ts.prod :=
    pbTight_prod_split ts hilt
  have hT1 : 1 ≤ ts.prod := by
    refine pbTight_one_le_prod (fun j hj => ?_)
    have hj' : j < HvdH.D := by rw [htslen] at hj; exact hj
    have := (hpt j hj').2.1
    omega
  -- bound 1: `(ss.take i).prod * (ts.drop (i+1)).prod * (tᵢ + 1) ≤ 4 * ts.prod`
  have hAB : (ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + 1) ≤ 4 * ts.prod := by
    have hstep : (ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + 1)
        ≤ (ts.take i).prod * (ts.drop (i + 1)).prod * (2 * ts.getD i 0) :=
      Nat.mul_le_mul (Nat.mul_le_mul hA (le_refl _)) (by omega)
    calc (ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + 1)
        ≤ (ts.take i).prod * (ts.drop (i + 1)).prod * (2 * ts.getD i 0) := hstep
      _ = 2 * ((ts.take i).prod * ts.getD i 0 * (ts.drop (i + 1)).prod) := by ring
      _ = 2 * ts.prod := by rw [hT]
      _ ≤ 4 * ts.prod := by omega
  -- term 1 of the bracket
  have h1 : Kb * (ts.getD i 0 + 1) * (p + 1) ^ Kb ≤ Kb * (ts.sum + 1) * (p + 1) ^ Kb := by
    have hle : ts.getD i 0 ≤ ts.sum := pbTight_getD_le_sum hilt
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  -- term 2 of the bracket
  have h2 : (ss.take i).prod * (ts.drop (i + 1)).prod *
        (Kb * (ts.getD i 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
          + Kb * (ts.getD i 0 + 1) * (p + 1) ^ 2)
      ≤ 4 * ts.prod * (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
          + Kb * (p + 1) ^ 2) := by
    have hfac : (ss.take i).prod * (ts.drop (i + 1)).prod *
          (Kb * (ts.getD i 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
            + Kb * (ts.getD i 0 + 1) * (p + 1) ^ 2)
        = ((ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + 1)) *
          (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) + Kb * (p + 1) ^ 2) := by
      ring
    rw [hfac]
    exact Nat.mul_le_mul_right _ hAB
  -- bound 2: `(ss.take i).prod * (ts.drop (i+1)).prod * (tᵢ + sᵢ + 1) ≤ 2 * ts.prod`
  have hZ : (ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + ss.getD i 0 + 1)
      ≤ 2 * ts.prod := by
    have hstep : (ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + ss.getD i 0 + 1)
        ≤ (ts.take i).prod * (ts.drop (i + 1)).prod * (2 * ts.getD i 0) :=
      Nat.mul_le_mul (Nat.mul_le_mul hA (le_refl _)) (by omega)
    calc (ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + ss.getD i 0 + 1)
        ≤ (ts.take i).prod * (ts.drop (i + 1)).prod * (2 * ts.getD i 0) := hstep
      _ = 2 * ((ts.take i).prod * ts.getD i 0 * (ts.drop (i + 1)).prod) := by ring
      _ = 2 * ts.prod := by rw [hT]
  -- term 3 of the bracket
  have h3 : ((ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + ss.getD i 0 + 1) + 1)
        * ((2 * p + 8) + ((ss.take i).prod * (ts.drop (i + 1)).prod
            * (ts.getD i 0 + ss.getD i 0 + 1)).size + 1)
        * (((ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + ss.getD i 0 + 1)).size + 1)
      ≤ 4 * ts.prod * (((2 * p + 8) + (ts.prod * 2 ^ (p + 1)).size + 1)
          * ((ts.prod * 2 ^ (p + 1)).size + 1)) := by
    have hW : (ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + ss.getD i 0 + 1)
        ≤ ts.prod * 2 ^ (p + 1) := by
      have hpw : 2 ≤ 2 ^ (p + 1) := by
        simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ p + 1 by omega)
      calc (ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + ss.getD i 0 + 1)
          ≤ 2 * ts.prod := hZ
        _ = ts.prod * 2 := by ring
        _ ≤ ts.prod * 2 ^ (p + 1) := Nat.mul_le_mul_left _ hpw
    have hZ4 : (ss.take i).prod * (ts.drop (i + 1)).prod * (ts.getD i 0 + ss.getD i 0 + 1) + 1
        ≤ 4 * ts.prod := by omega
    have hAb : (2 * p + 8) + ((ss.take i).prod * (ts.drop (i + 1)).prod
          * (ts.getD i 0 + ss.getD i 0 + 1)).size + 1
        ≤ (2 * p + 8) + (ts.prod * 2 ^ (p + 1)).size + 1 := by
      have hsize : ((ss.take i).prod * (ts.drop (i + 1)).prod
          * (ts.getD i 0 + ss.getD i 0 + 1)).size ≤ (ts.prod * 2 ^ (p + 1)).size :=
        Nat.size_le_size hW
      omega
    have hBb : ((ss.take i).prod * (ts.drop (i + 1)).prod
          * (ts.getD i 0 + ss.getD i 0 + 1)).size + 1 ≤ (ts.prod * 2 ^ (p + 1)).size + 1 := by
      have hsize : ((ss.take i).prod * (ts.drop (i + 1)).prod
          * (ts.getD i 0 + ss.getD i 0 + 1)).size ≤ (ts.prod * 2 ^ (p + 1)).size :=
        Nat.size_le_size hW
      omega
    have := Nat.mul_le_mul (Nat.mul_le_mul hZ4 hAb) hBb
    simpa only [mul_assoc] using this
  -- assemble the seven summands
  unfold PBBracket pbTight_perRound
  omega

/-- **The bracket arithmetic of Theorem 4.1 (`B̃` half)**: the sum of the `D` round brackets of
`pbIterTight` is at most `PBTight = D *` (per-round budget). -/
theorem pbBracketLeTight (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ)
    (h : HvdH.ResParams p α ss ts) :
    Work.Resample.PBSum Kb Cm p α ss ts 0 HvdH.D ≤ Work.Resample.PBTight Kb Cm p α ss ts := by
  rw [pbTight_eq, PBSum_zero_sum]
  calc (Finset.range HvdH.D).sum (fun i => PBBracket Kb Cm p α ss ts i)
      ≤ (Finset.range HvdH.D).sum (fun _ => pbTight_perRound Kb Cm p α ts) :=
        Finset.sum_le_sum (fun i hi =>
          pbTight_bracket_le Kb Cm p α ss ts h (Finset.mem_range.mp hi))
    _ = HvdH.D * pbTight_perRound Kb Cm p α ts := by
        rw [Finset.sum_const, Finset.card_range]
        simp

end Work.Resample
