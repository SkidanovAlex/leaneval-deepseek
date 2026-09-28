import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.box_card

namespace Work.HP.FM4

open Work.HP Finset

/-- Every coordinate of an integer vector is bounded in absolute value by its
Euclidean norm. -/
lemma coord_abs_le_eNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    |(v i : ℝ)| ≤ eNorm v := by
  have h1 : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((v j : ℝ))) (Finset.mem_univ i)
  calc |(v i : ℝ)| = Real.sqrt (((v i : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, ((v j : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm v := rfl

/-- A finset of integer vectors whose Euclidean norm is at most `R ≥ 0` has at most
`(2R+1)^{card ι}` elements: every coordinate satisfies `|v i| ≤ ‖v‖ ≤ R`, so the set is
contained in the box `∏ i, [-⌊R⌋, ⌊R⌋]` of cardinality `∏ i, (2⌊R⌋+1) ≤ (2R+1)^{card ι}`.
(`Work.HP.box_card` gives the exact cardinality of such a box.) -/
theorem card_le_ball {ι : Type*} [Fintype ι] [DecidableEq ι] (R : ℝ) (hR : 0 ≤ R)
    (s : Finset (ι → ℤ)) (hs : ∀ v ∈ s, eNorm v ≤ R) :
    (s.card : ℝ) ≤ (2 * R + 1) ^ (Fintype.card ι) := by
  set B : ℕ := Nat.floor R with hB
  have hBZ : (B : ℤ) = Int.floor R := by
    rw [hB, ← Int.floor_toNat R]
    exact Int.toNat_of_nonneg (Int.floor_nonneg.2 hR)
  have hsub : s ⊆ Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ)) := by
    intro v hv
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h := coord_abs_le_eNorm v i
    have h2 : |(v i : ℝ)| ≤ R := le_trans h (hs v hv)
    obtain ⟨hlo, hhi⟩ := abs_le.mp h2
    refine ⟨?_, ?_⟩
    · rw [hBZ]
      have h3 : ((-(v i) : ℤ) : ℝ) ≤ R := by push_cast; linarith
      have h4 := Int.le_floor.mpr h3
      omega
    · rw [hBZ]
      exact Int.le_floor.mpr hhi
  calc (s.card : ℝ)
      ≤ ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (2 * (B : ℝ) + 1) ^ Fintype.card ι := (box_card B).1
    _ ≤ (2 * R + 1) ^ Fintype.card ι := by
        have hle : (B : ℝ) ≤ R := by
          have h1 : (B : ℝ) = ((Int.floor R : ℤ) : ℝ) := by exact_mod_cast hBZ
          rw [h1]; exact Int.floor_le R
        exact pow_le_pow_left₀ (by positivity) (by linarith) _

end Work.HP.FM4
