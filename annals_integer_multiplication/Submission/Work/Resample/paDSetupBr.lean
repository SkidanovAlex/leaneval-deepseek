import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.pbCostArithKit
import Submission.Work.Params.listSizesBig

namespace Work.Resample

/-- A list of naturals all of whose entries are `≥ 2` has product at least `2 ^ length`. -/
theorem pa_two_pow_length_le_prod : ∀ (l : List ℕ), (∀ m ∈ l, 2 ≤ m) → 2 ^ l.length ≤ l.prod
  | [], _ => by simp
  | a :: t, h => by
    have ha : 2 ≤ a := h a (by simp)
    have ht : 2 ^ t.length ≤ t.prod :=
      pa_two_pow_length_le_prod t (fun m hm => h m (by simp [hm]))
    rw [List.prod_cons, List.length_cons, pow_succ]
    calc 2 ^ t.length * 2 ≤ t.prod * a := Nat.mul_le_mul ht ha
      _ = a * t.prod := Nat.mul_comm _ _

/-- Prologue plus epilogue budget of the `Ã` program is absorbed by the `ts.prod * p^2` term of
`HvdH.resCost` with the constant `4096`. -/
theorem paDSetupBr {p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts) :
    PASetupBr p ss ts + PAFinalBr p ss ts ≤ 4096 * (ts.prod * p ^ 2) := by
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hper⟩ := h
  -- every entry of `ss` and `ts` is `< 2^p`, hence has `size ≤ p`
  have hszs : ∀ m ∈ ss, m.size ≤ p := by
    intro m hm
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hm
    have him : i < HvdH.D := by rw [← hsslen]; exact hi
    have h1 : ss.getD i 0 < 2 ^ p :=
      lt_trans (hper i him).2.1 (hper i him).2.2.1
    rw [List.getD_eq_getElem ss 0 hi] at h1
    rw [hix] at h1
    exact Nat.size_le.mpr h1
  have hszts : ∀ m ∈ ts, m.size ≤ p := by
    intro m hm
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hm
    have him : i < HvdH.D := by rw [← htslen]; exact hi
    have h1 : ts.getD i 0 < 2 ^ p := (hper i him).2.2.1
    rw [List.getD_eq_getElem ts 0 hi] at h1
    rw [hix] at h1
    exact Nat.size_le.mpr h1
  -- sizes of the `intList`s and of `Val.int p`
  have hv1 : HvdH.vsz (HvdH.intList ss) ≤ (HvdH.D + 1) * (p + 3) := by
    have h1 := Work.Params.vsz_intList_le ss p hszs
    rwa [hsslen] at h1
  have hv2 : HvdH.vsz (HvdH.intList ts) ≤ (HvdH.D + 1) * (p + 3) := by
    have h1 := Work.Params.vsz_intList_le ts p hszts
    rwa [htslen] at h1
  have hv3 : HvdH.vsz (HvdH.Val.int p) ≤ p + 2 := by
    have h1 := Work.Params.vsz_int_natCast p
    have h2 : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
    omega
  -- `ts.prod ≥ 2^D ≥ D`, so `ts.prod` absorbs all the `D`-dependent terms
  have h2 : ∀ m ∈ ts, 2 ≤ m := by
    intro m hm
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hm
    have him : i < HvdH.D := by rw [← htslen]; exact hi
    have h1 : 2 ≤ ts.getD i 0 :=
      le_trans (hper i him).1 (le_of_lt (hper i him).2.1)
    rw [List.getD_eq_getElem ts 0 hi] at h1
    rw [hix] at h1
    exact h1
  have hT2 : 2 ^ HvdH.D ≤ ts.prod := by
    have h1 := pa_two_pow_length_le_prod ts h2
    rwa [htslen] at h1
  have hDleT : HvdH.D ≤ ts.prod := le_trans (le_of_lt Nat.lt_two_pow_self) hT2
  have h1T : 1 ≤ ts.prod := le_trans Nat.one_le_two_pow hT2
  have hTsz : ts.prod.size ≤ ts.prod := Nat.size_le.mpr (Nat.lt_two_pow_self (n := ts.prod))
  rw [PASetupBr, PAFinalBr]
  have hP768 : (768:ℕ) ≤ p ^ 2 := by nlinarith
  have hP64 : 64 * p ≤ p ^ 2 := by nlinarith
  have hP256 : 256 * p ≤ 3 * p ^ 2 := by nlinarith
  have hD2 : 768 * HvdH.D ≤ ts.prod * p ^ 2 := by nlinarith
  have hc : (1616:ℕ) ≤ ts.prod * p ^ 2 := by nlinarith
  have hDP : HvdH.D * p ≤ ts.prod * p ^ 2 := by nlinarith
  nlinarith

end Work.Resample
