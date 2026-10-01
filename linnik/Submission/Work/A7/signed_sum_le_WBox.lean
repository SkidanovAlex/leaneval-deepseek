import Mathlib
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.LinnikAreas.A7.Basic7

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- `WBox` vanishes for a character none of whose box points is a zero (with multiplicity). -/
private lemma WBox_eq_zero_of_no_box_zero {q : ℕ} [NeZero q] (K R : ℝ)
    (χ : DirichletCharacter ℂ q)
    (h : ∀ ρ : ℂ, Work.LinnikContract.InBox q R ρ → Work.LinnikContract.zeroMult χ ρ = 0) :
    Work.LinnikAreas.A7.WBox q K R χ = 0 := by
  rw [Work.LinnikAreas.A7.WBox]
  refine finsum_eq_zero_of_forall_eq_zero (fun ρ => ?_)
  by_cases hb : Work.LinnikContract.InBox q R ρ
  · rw [if_pos hb, h ρ hb]; simp
  · rw [if_neg hb]

/-- Pointwise bound: the signed contribution `Re(χ(a)‾ · boxSum χ)` of one character is at most
its `WBox`.  Indeed `Re z ≤ ‖z‖`, `‖χ a‖ ≤ 1`, and `‖boxSum χ‖ ≤ WBox χ`. -/
private lemma re_conj_mul_boxSum_le_WBox {q : ℕ} [NeZero q] (R : ℝ) (a : ℕ)
    (χ : DirichletCharacter ℂ q) :
    ((starRingEnd ℂ) (χ a) * Work.LinnikContract.boxSum q (11/2) (3/10) R χ).re
      ≤ Work.LinnikAreas.A7.WBox q (3/10) R χ := by
  have hnorm : ‖(starRingEnd ℂ) (χ a) * Work.LinnikContract.boxSum q (11/2) (3/10) R χ‖
      ≤ ‖Work.LinnikContract.boxSum q (11/2) (3/10) R χ‖ := by
    rw [norm_mul]
    have h : ‖(starRingEnd ℂ) (χ a)‖ ≤ 1 := by
      simpa using DirichletCharacter.norm_le_one χ (a : ZMod q)
    exact mul_le_of_le_one_left (norm_nonneg _) h
  have hbox := Work.LinnikAreas.A7.norm_boxSum_le_WBox (q := q) (L := 11/2) (K := 3/10)
    (R := R) (by norm_num [Work.LinnikAreas.A7.ac]) χ
  calc ((starRingEnd ℂ) (χ a) * Work.LinnikContract.boxSum q (11/2) (3/10) R χ).re
      ≤ ‖(starRingEnd ℂ) (χ a) * Work.LinnikContract.boxSum q (11/2) (3/10) R χ‖ :=
        Complex.re_le_norm _
    _ ≤ ‖Work.LinnikContract.boxSum q (11/2) (3/10) R χ‖ := hnorm
    _ ≤ Work.LinnikAreas.A7.WBox q (3/10) R χ := hbox

theorem signed_sum_le_WBox {q : ℕ} [NeZero q] {R : ℝ} (a : ℕ) :
    (∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
        ((starRingEnd ℂ) (χ a) * Work.LinnikContract.boxSum q (11/2) (3/10) R χ).re)
      ≤ ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ := by
  classical
  set S : Finset (DirichletCharacter ℂ q) := Finset.univ.erase 1 with hS
  set T : Finset (DirichletCharacter ℂ q) := Work.LinnikAreas.A7.Aset q R with hT
  have hsub : T ⊆ S := by
    rw [hT, hS]
    exact Finset.filter_subset _ _
  have hzero : ∀ χ ∈ S, χ ∉ T → Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ = 0 := by
    intro χ hχS hχT
    refine WBox_eq_zero_of_no_box_zero (3/10) R χ (fun ρ hρ => ?_)
    by_contra hne
    apply hχT
    rw [hT]
    refine Work.LinnikAreas.A7.mem_Aset.mpr ⟨?_, ⟨ρ, hρ, hne⟩⟩
    exact (Finset.mem_erase.mp (hS ▸ hχS)).1
  refine le_trans (Finset.sum_le_sum (fun χ _ => re_conj_mul_boxSum_le_WBox R a χ)) ?_
  exact le_of_eq (Finset.sum_subset hsub hzero).symm

end Work.A7
