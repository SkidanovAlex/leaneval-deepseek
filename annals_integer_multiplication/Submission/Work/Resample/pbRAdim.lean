import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.pbRoundFacts
import Submission.Work.Resample.axisDefs

/-!
# Dimension facts of one round of `progTensorB`

Local (sorry-free) version of the few arithmetic facts about `HvdH.ResParams` that the round of
`Submission/Work/Resample/pbRoundApply.lean` needs.  (`Submission/Work/Resample/pbDimFacts.lean`
states the same facts; this file is used by `pbRoundApply.lean` so that the round does not depend on
that file while it is in flight.)
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- Monotonicity of the product of a `range`-mapped list of naturals. -/
theorem pbRA_range_prod_mono {j : ℕ} {f g : ℕ → ℕ} (h : ∀ i < j, f i ≤ g i) :
    ((List.range j).map f).prod ≤ ((List.range j).map g).prod := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact Nat.mul_le_mul (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h n (Nat.lt_succ_self n))

/-- The product of a prefix is monotone in the entries. -/
theorem pbRA_take_prod_le (l l' : List ℕ) (j : ℕ) (hl : j ≤ l.length) (hl' : j ≤ l'.length)
    (h : ∀ i, i < j → l.getD i 0 ≤ l'.getD i 0) :
    (l.take j).prod ≤ (l'.take j).prod := by
  rw [prod_take_range_getD l hl, prod_take_range_getD l' hl']
  exact pbRA_range_prod_mono h

/-- The `D`-th entry of `ss`/`ts` bounds and the two product bounds needed by the round. -/
theorem pbRA_dimFacts (p α : ℕ) (ss ts : List ℕ) (j : ℕ) (h : HvdH.ResParams p α ss ts)
    (hj : j < HvdH.D) :
    1 ≤ (ss.take j).prod ∧ 2 ≤ ts.getD j 0 ∧ 2 ≤ ss.getD j 0 ∧
    1 ≤ (ts.drop (j + 1)).prod ∧
    (ss.take j).prod * ss.getD j 0 * (ts.drop (j + 1)).prod ≤ ts.prod := by
  obtain ⟨hsslen, htslen, h100, hα2, hαp, hdim⟩ := h
  have hjts : j < ts.length := by rw [htslen]; exact hj
  have hssj : 2 ≤ ss.getD j 0 := (hdim j hj).1
  have htsj : 2 ≤ ts.getD j 0 :=
    le_trans (hdim j hj).1 (le_of_lt (hdim j hj).2.1)
  have hsle : ss.getD j 0 ≤ ts.getD j 0 := le_of_lt (hdim j hj).2.1
  have hss_ge : ∀ i, i < ss.length → 2 ≤ ss.getD i 0 := by
    intro i hi
    exact (hdim i (by rw [← hsslen]; exact hi)).1
  have hts_ge : ∀ i, i < ts.length → 2 ≤ ts.getD i 0 := by
    intro i hi
    have hiD : i < HvdH.D := by rw [← htslen]; exact hi
    exact le_trans (hdim i hiD).1 (le_of_lt (hdim i hiD).2.1)
  have hge : ∀ (l : List ℕ), (∀ i, i < l.length → 2 ≤ l.getD i 0) → ∀ x ∈ l, 1 ≤ x := by
    intro l hl x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have h2 := hl i hi
    rw [List.getD_eq_getElem l 0 hi, hix] at h2
    omega
  have htake : 1 ≤ (ss.take j).prod :=
    pbRoundFacts.2.2.2.2.2.2.1 _ (fun x hx => hge ss hss_ge x (List.mem_of_mem_take hx))
  have hdrop : 1 ≤ (ts.drop (j + 1)).prod :=
    pbRoundFacts.2.2.2.2.2.2.1 _ (fun x hx => hge ts hts_ge x (List.mem_of_mem_drop hx))
  refine ⟨htake, htsj, hssj, hdrop, ?_⟩
  -- the product bound
  have hAle : (ss.take j).prod ≤ (ts.take j).prod :=
    pbRA_take_prod_le ss ts j (by rw [hsslen]; omega) (by rw [htslen]; omega)
      (fun i hi => le_of_lt (hdim i (by omega)).2.1)
  have hsplit : ts.prod = (ts.take j).prod * (ts.drop j).prod :=
    (pbRoundFacts.2.2.2.2.2.1 ts j hjts).2.2.1
  have hsplit' : (ts.drop j).prod = ts.getD j 0 * (ts.drop (j + 1)).prod :=
    (pbRoundFacts.2.2.2.2.2.1 ts j hjts).2.1
  calc (ss.take j).prod * ss.getD j 0 * (ts.drop (j + 1)).prod
      ≤ (ts.take j).prod * ts.getD j 0 * (ts.drop (j + 1)).prod :=
        Nat.mul_le_mul (Nat.mul_le_mul hAle hsle) le_rfl
    _ = (ts.take j).prod * (ts.getD j 0 * (ts.drop (j + 1)).prod) := by ring
    _ = (ts.take j).prod * (ts.drop j).prod := by rw [hsplit']
    _ = ts.prod := hsplit.symm

end Work.Resample
