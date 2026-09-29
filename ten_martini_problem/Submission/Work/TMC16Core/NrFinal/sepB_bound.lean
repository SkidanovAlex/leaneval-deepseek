import Mathlib
import Submission.Work.Basic.UniNonres.Defs
import Submission.Work.TMC16Core.Core.uni_nonres3_support
import Submission.Work.TMC16Core.NrFinal.sepBdefs
import Submission.Work.TMC16Core.NrFinal.factorial_central
import Submission.Work.TMC16Core.NrFinal.cls_add_le_sepB

/-!
# The separation bound `sepB c δ M` (AJ §9, non-resonant uniformity)

Given a finite family of phases `z i = ξ + k i · α` whose distances to `ℤ` are bounded below by
`c > 0` and whose "signed representatives" `ρ i = z i - round (z i)` are `δ`-separated inside
each sign class, the total logarithmic weight `∑ -log |sin (π z i)|` is at most `sepB c δ M`,
`M` the number of phases.

The signed representatives split the index set into `S⁺ = {i : ρ i > 0}` and
`S⁻ = {i : ρ i < 0}`.  Inside a sign class the values `|ρ i| = fracDist (z i)` lie in `[c, 1/2]`
and are pairwise `δ`-separated, so the single-cluster estimate applies to each class; the two
classes are then combined with `a! b! ≥ (⌊(a+b)/2⌋!)²` (see `cls_add_le_sepB`), which is exactly
the factorial factor appearing in `sepB`.
-/

namespace Work.TMC16Core.NrFinal

open Work.TMC16Core

theorem sepB_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ι → ℤ} {α ξ c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (hlow : ∀ i : ι, c ≤ Work.TMC16Core.fracDist (ξ + (k i : ℝ) * α))
    (hsep : ∀ i j : ι, i ≠ j → δ ≤ Work.TMC16Core.fracDist (((k i - k j : ℤ) : ℝ) * α)) :
    ∑ i : ι, -Real.log |Real.sin (Real.pi * (ξ + (k i : ℝ) * α))|
      ≤ Work.Basic.UniNonres.sepB c δ (Fintype.card ι) := by
  classical
  let z : ι → ℝ := fun i => ξ + (k i : ℝ) * α
  let ρ : ι → ℝ := fun i => z i - ((round (z i) : ℤ) : ℝ)
  let v : ι → ℝ := fun i => Work.TMC16Core.fracDist (z i)
  have hvρ : ∀ i, v i = |ρ i| := fun i => rfl
  have hlow' : ∀ i, c ≤ v i := fun i => hlow i
  have hle : ∀ i, v i ≤ 1 / 2 := fun i => abs_sub_round (z i)
  have habs : ∀ i, |ρ i| ≤ 1 / 2 := fun i => by rw [← hvρ i]; exact hle i
  have hρne : ∀ i, ρ i ≠ 0 := by
    intro i h
    have h0 : v i = 0 := by rw [hvρ i, h, abs_zero]
    have h1 := hlow' i
    rw [h0] at h1
    linarith
  let Spos : Finset ι := Finset.univ.filter (fun i => 0 < ρ i)
  let Sneg : Finset ι := Finset.univ.filter (fun i => ρ i < 0)
  have memSpos : ∀ i, i ∈ Spos ↔ 0 < ρ i := by intro i; simp [Spos]
  have memSneg : ∀ i, i ∈ Sneg ↔ ρ i < 0 := by intro i; simp [Sneg]
  -- the two summands agree with the `sin (π · fracDist)` form
  have hsin : ∀ i, -Real.log |Real.sin (Real.pi * z i)|
      = -Real.log (Real.sin (Real.pi * v i)) := by
    intro i
    have h1 : |Real.sin (Real.pi * z i)| = Real.sin (Real.pi * v i) :=
      Work.TMC16Core.Core.abs_sin_eq_sin_fracDist (z i)
    rw [h1]
  -- separation inside a sign class
  have hsep_core : ∀ p q : ι, 0 < ρ p * ρ q → p ≠ q → δ ≤ |v p - v q| := by
    intro p q hpq hne
    have hzpq : z p - z q = ((k p - k q : ℤ) : ℝ) * α := by simp only [z]; push_cast; ring
    have hδp : δ ≤ Work.TMC16Core.fracDist (z p - z q) := by
      have h1 := hsep p q hne
      rw [← hzpq] at h1
      exact h1
    have hshift : Work.TMC16Core.fracDist (z p - z q)
        = Work.TMC16Core.fracDist (ρ p - ρ q) := by
      have hdec : z p - z q = (ρ p - ρ q) + (((round (z p) - round (z q) : ℤ)) : ℝ) := by
        simp only [ρ]; push_cast; ring
      rw [hdec]
      exact Work.TMC16Core.Basic.nn_add_intCast (ρ p - ρ q) (round (z p) - round (z q))
    have hsub := fracDist_sub_eq_abs_sub_abs hpq (habs p) (habs q)
    calc δ ≤ Work.TMC16Core.fracDist (z p - z q) := hδp
      _ = Work.TMC16Core.fracDist (ρ p - ρ q) := hshift
      _ = |(|ρ p| - |ρ q|)| := hsub
      _ = |v p - v q| := by rw [hvρ p, hvρ q]
  have hsepP : ∀ p ∈ Spos, ∀ q ∈ Spos, p ≠ q → δ ≤ |v p - v q| := by
    intro p hp q hq hpq
    exact hsep_core p q (mul_pos ((memSpos p).mp hp) ((memSpos q).mp hq)) hpq
  have hsepN : ∀ p ∈ Sneg, ∀ q ∈ Sneg, p ≠ q → δ ≤ |v p - v q| := by
    intro p hp q hq hpq
    exact hsep_core p q (mul_pos_of_neg_of_neg ((memSneg p).mp hp) ((memSneg q).mp hq)) hpq
  -- the single-cluster estimate on each class
  have hclsP : ∑ i ∈ Spos, -Real.log (Real.sin (Real.pi * v i)) ≤ cls c δ Spos.card :=
    cluster_le_cls hc hδ (fun p _ => ⟨hlow' p, hle p⟩) hsepP
  have hclsN : ∑ i ∈ Sneg, -Real.log (Real.sin (Real.pi * v i)) ≤ cls c δ Sneg.card :=
    cluster_le_cls hc hδ (fun p _ => ⟨hlow' p, hle p⟩) hsepN
  -- the index set is the disjoint union of the two sign classes
  have hSneg_eq : Sneg = Finset.univ.filter (fun i => ¬ 0 < ρ i) := by
    ext i
    rw [memSneg i, Finset.mem_filter]
    constructor
    · intro h; exact ⟨Finset.mem_univ i, not_lt.mpr h.le⟩
    · rintro ⟨-, h⟩
      exact lt_of_le_of_ne (le_of_not_gt h) (hρne i)
  have hsum_eq : ∑ i : ι, -Real.log |Real.sin (Real.pi * z i)|
      = ∑ i ∈ Spos, -Real.log |Real.sin (Real.pi * z i)|
        + ∑ i ∈ Sneg, -Real.log |Real.sin (Real.pi * z i)| := by
    have h := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset ι))
      (p := fun i => 0 < ρ i) (f := fun i => -Real.log |Real.sin (Real.pi * z i)|)
    have hSpos_eq : Spos = Finset.univ.filter (fun i => 0 < ρ i) := rfl
    rw [← hSpos_eq, ← hSneg_eq] at h
    exact h.symm
  have hSP : ∑ i ∈ Spos, -Real.log |Real.sin (Real.pi * z i)|
      = ∑ i ∈ Spos, -Real.log (Real.sin (Real.pi * v i)) :=
    Finset.sum_congr rfl (fun i _ => hsin i)
  have hSN : ∑ i ∈ Sneg, -Real.log |Real.sin (Real.pi * z i)|
      = ∑ i ∈ Sneg, -Real.log (Real.sin (Real.pi * v i)) :=
    Finset.sum_congr rfl (fun i _ => hsin i)
  have hcard : Spos.card + Sneg.card = Fintype.card ι := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
      (fun i => 0 < ρ i)
    have hSpos_eq : Spos = Finset.univ.filter (fun i => 0 < ρ i) := rfl
    rw [hSpos_eq, hSneg_eq, h1, Finset.card_univ]
  have key : ∑ i : ι, -Real.log |Real.sin (Real.pi * z i)|
      ≤ cls c δ Spos.card + cls c δ Sneg.card := by
    rw [hsum_eq, hSP, hSN]
    exact add_le_add hclsP hclsN
  calc ∑ i : ι, -Real.log |Real.sin (Real.pi * (ξ + (k i : ℝ) * α))|
      = ∑ i : ι, -Real.log |Real.sin (Real.pi * z i)| := rfl
    _ ≤ cls c δ Spos.card + cls c δ Sneg.card := key
    _ ≤ Work.Basic.UniNonres.sepB c δ (Spos.card + Sneg.card) :=
        cls_add_le_sepB hc hδ Spos.card Sneg.card
    _ = Work.Basic.UniNonres.sepB c δ (Fintype.card ι) := by rw [hcard]

end Work.TMC16Core.NrFinal
