import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.glue_three_LZ

/-!
# A14D: gluing three `LZ`-solutions along an arbitrary open cover of the slit plane

Given open sets `A`, `B`, `C` with `A ∩ B = ∅` covering `Om1 = ℂ ∖ (−∞,1]`, and functions
`gA`, `gB`, `gC` solving `LZ f = 0` on `A`, `B`, `C` respectively, mutually consistent on the
overlaps `A ∩ C` and `B ∩ C`, there is a single function `F` on `Om1` which solves `LZ F = 0`
and restricts to each of `gA`, `gB`, `gC` on `A`, `B`, `C`.

The construction is the evident one: define `F z = gA z` when `z ∈ A`, `F z = gB z` when
`z ∉ A` and `z ∈ B`, and `F z = gC z` otherwise.  Since `A ∩ B = ∅`, this agrees with `gA` on
`A` and with `gB` on `B` definitionally, and the consistency hypotheses make it agree with `gC`
on `C`.  Each point `z ∈ Om1` lies in one of the three *open* sets, so a whole neighbourhood of
`z` is contained in it; there `F` coincides with the corresponding `g`, which gives both
differentiability and `LZ F z = 0` (`LZ` only involves `F`, `F'`, `F''` at `z`).
-/

namespace Work.A14D

open Work.A14D
open Classical

noncomputable section

/-- The function glued out of `gA`, `gB`, `gC` along the triple `(A, B, C)`, with `A` having
priority, then `B`, then `C`. -/
def glueFunABC (A B C : Set ℂ) (gA gB gC : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if z ∈ A then gA z else if z ∈ B then gB z else gC z

lemma glueFunABC_eqOn_A (A B C : Set ℂ) (gA gB gC : ℂ → ℂ) :
    Set.EqOn (glueFunABC A B C gA gB gC) gA A := by
  intro z hz
  simp only [glueFunABC, if_pos hz]

lemma glueFunABC_eqOn_B {A B C : Set ℂ} (hAB : A ∩ B = ∅) (gA gB gC : ℂ → ℂ) :
    Set.EqOn (glueFunABC A B C gA gB gC) gB B := by
  intro z hz
  have hzA : z ∉ A := by
    intro hA
    have hmem : z ∈ A ∩ B := ⟨hA, hz⟩
    rw [hAB] at hmem
    exact hmem
  simp only [glueFunABC, if_neg hzA, if_pos hz]

lemma glueFunABC_eqOn_C {A B C : Set ℂ} {gA gB gC : ℂ → ℂ}
    (hAC : Set.EqOn gA gC (A ∩ C)) (hBC : Set.EqOn gB gC (B ∩ C)) :
    Set.EqOn (glueFunABC A B C gA gB gC) gC C := by
  intro z hz
  by_cases hA : z ∈ A
  · simp only [glueFunABC, if_pos hA]
    exact hAC ⟨hA, hz⟩
  · simp only [glueFunABC, if_neg hA]
    by_cases hB : z ∈ B
    · simp only [if_pos hB]
      exact hBC ⟨hB, hz⟩
    · simp only [if_neg hB]

theorem glue_three_LZ_Om1 {A B C : Set ℂ}
    (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C) (hAB : A ∩ B = ∅)
    (hcover : ∀ z : ℂ, z ∈ Om1 → z ∈ A ∨ z ∈ B ∨ z ∈ C)
    {gA gB gC : ℂ → ℂ}
    (hAd : DifferentiableOn ℂ gA A) (hBd : DifferentiableOn ℂ gB B) (hCd : DifferentiableOn ℂ gC C)
    (hLA : ∀ z ∈ A, LZ gA z = 0) (hLB : ∀ z ∈ B, LZ gB z = 0) (hLC : ∀ z ∈ C, LZ gC z = 0)
    (hAC : Set.EqOn gA gC (A ∩ C)) (hBC : Set.EqOn gB gC (B ∩ C)) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Om1 ∧ (∀ z ∈ Om1, LZ F z = 0) ∧
      Set.EqOn F gA A ∧ Set.EqOn F gB B ∧ Set.EqOn F gC C := by
  have hFA := glueFunABC_eqOn_A A B C gA gB gC
  have hFB := glueFunABC_eqOn_B (A := A) (B := B) (C := C) hAB gA gB gC
  have hFC := glueFunABC_eqOn_C (A := A) (B := B) (C := C) hAC hBC
  refine ⟨glueFunABC A B C gA gB gC, ?_, ?_, hFA, hFB, hFC⟩
  · intro z hz
    rcases hcover z hz with hA | hB | hC
    · exact (differentiableAt_of_eqOn_open hAo hFA hAd hA).differentiableWithinAt
    · exact (differentiableAt_of_eqOn_open hBo hFB hBd hB).differentiableWithinAt
    · exact (differentiableAt_of_eqOn_open hCo hFC hCd hC).differentiableWithinAt
  · intro z hz
    rcases hcover z hz with hA | hB | hC
    · rw [LZ_congr_eventuallyEq (Filter.eventuallyEq_of_mem (hAo.mem_nhds hA) hFA)]
      exact hLA z hA
    · rw [LZ_congr_eventuallyEq (Filter.eventuallyEq_of_mem (hBo.mem_nhds hB) hFB)]
      exact hLB z hB
    · rw [LZ_congr_eventuallyEq (Filter.eventuallyEq_of_mem (hCo.mem_nhds hC) hFC)]
      exact hLC z hC

end

end Work.A14D
