import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace Commons.Analysis.Walsh

open Finset BigOperators

/-- `ZMod 2` has exactly the elements `0` and `1`. -/
private lemma zmod2_univ : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

/-- Every element of `ZMod 2` is `0` or `1`. -/
private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a ∈ ({(0 : ZMod 2), 1} : Finset (ZMod 2)) := by
    rw [← zmod2_univ]; exact Finset.mem_univ a
  simpa using h

/-- The standard additive character on `𝔽₂` at `0`. -/
private lemma stdAddChar_two_zero : ZMod.stdAddChar (0 : ZMod 2) = (1 : ℂ) :=
  AddChar.map_zero_eq_one _

/-- The standard additive character on `𝔽₂` at `1` is `-1`. -/
private lemma stdAddChar_two_one : ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by simp]
  rw [ZMod.stdAddChar_coe (1 : ℤ)]
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (1 : ℤ) / (2 : ℕ) = Real.pi * Complex.I by
    push_cast; ring]
  rw [Complex.exp_pi_mul_I]

/-- Sum over `𝔽₂` of the level function interpolated between `(1+ρ)/2` and `(1-ρ)/2`. -/
private lemma sum_ite_char (ρ : ℝ) (a : ZMod 2) :
    (∑ j : ZMod 2,
        (if j = a then (((1 + ρ) / 2 : ℝ) : ℂ) else (((1 - ρ) / 2 : ℝ) : ℂ))) = 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from zmod2_univ,
      Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
  rcases zmod2_eq_zero_or_one a with h | h
  · subst h
    rw [if_pos rfl, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
    push_cast; ring
  · subst h
    rw [if_neg (by decide : (0 : ZMod 2) ≠ 1), if_pos rfl]
    push_cast; ring

/-- Sum over `𝔽₂` of the level function interpolated between `(1+ρ)/2` and `(1-ρ)/2`,
weighted by the character `χ`. -/
private lemma sum_ite_mul_char (ρ : ℝ) (a : ZMod 2) :
    (∑ j : ZMod 2,
        (if j = a then (((1 + ρ) / 2 : ℝ) : ℂ) else (((1 - ρ) / 2 : ℝ) : ℂ)) *
          ZMod.stdAddChar j)
      = (ρ : ℂ) * ZMod.stdAddChar a := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from zmod2_univ,
      Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
  rcases zmod2_eq_zero_or_one a with h | h
  · subst h
    simp only [stdAddChar_two_zero, stdAddChar_two_one]
    norm_num
    ring
  · subst h
    simp only [stdAddChar_two_zero, stdAddChar_two_one]
    norm_num
    ring

/-- The noise operator on the hypercube `{0,1}^n = (Fin n → ZMod 2)` at the Walsh character
`∏_{i ∈ S} χ (· i)` has eigenvalue `ρ^{|S|}`: `T_ρ χ_S = ρ^{|S|} χ_S`. -/
theorem noise_char_complex {n : ℕ} (ρ : ℝ) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    (∑ y : Fin n → ZMod 2,
        (∏ i : Fin n, (if y i = x i then (((1 + ρ) / 2 : ℝ) : ℂ) else (((1 - ρ) / 2 : ℝ) : ℂ))) *
        ∏ i ∈ S, ZMod.stdAddChar (y i))
      = (ρ : ℂ) ^ S.card * ∏ i ∈ S, ZMod.stdAddChar (x i) := by
  classical
  set g : (i : Fin n) → ZMod 2 → ℂ :=
    fun i a => (if a = x i then (((1 + ρ) / 2 : ℝ) : ℂ) else (((1 - ρ) / 2 : ℝ) : ℂ)) *
      (if i ∈ S then ZMod.stdAddChar a else 1) with hg
  have step1 : ∀ y : Fin n → ZMod 2,
      (∏ i : Fin n, (if y i = x i then (((1 + ρ) / 2 : ℝ) : ℂ) else (((1 - ρ) / 2 : ℝ) : ℂ))) *
        (∏ i ∈ S, ZMod.stdAddChar (y i)) = ∏ i : Fin n, g i (y i) := by
    intro y
    rw [← Finset.prod_ite_mem_eq S (fun i : Fin n => ZMod.stdAddChar (y i)),
      ← Finset.prod_mul_distrib]
  simp only [step1]
  have h2 : (∑ y : Fin n → ZMod 2, ∏ i : Fin n, g i (y i))
      = ∏ i : Fin n, ∑ j : ZMod 2, g i j := by
    rw [show (∑ y : Fin n → ZMod 2, ∏ i : Fin n, g i (y i))
        = ∑ y ∈ (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))),
            ∏ i : Fin n, g i (y i) from by
      rw [Fintype.piFinset_univ]]
    rw [Finset.sum_prod_piFinset]
  rw [h2]
  have hcoord : ∀ i : Fin n, (∑ j : ZMod 2, g i j)
      = if i ∈ S then (ρ : ℂ) * ZMod.stdAddChar (x i) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · rw [hg]
      simp only [hi, if_true]
      exact sum_ite_mul_char ρ (x i)
    · rw [hg]
      simp only [hi, if_false, mul_one]
      exact sum_ite_char ρ (x i)
  rw [Finset.prod_congr rfl (fun i _ => hcoord i)]
  rw [Finset.prod_ite_mem_eq S (fun i : Fin n => (ρ : ℂ) * ZMod.stdAddChar (x i))]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

end Commons.Analysis.Walsh