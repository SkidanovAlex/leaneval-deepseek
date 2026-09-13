import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Inequalities

/-- `ZMod 2` has exactly the two elements `0` and `1`. -/
private lemma zmod2_univ : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

/-- Every element of `ZMod 2` is `0` or `1`. -/
private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a ∈ ({0,1} : Finset (ZMod 2)) := by
    rw [← zmod2_univ]
    exact Finset.mem_univ a
  simpa using h

/-- Sum over `ZMod 2` of the level function `1_{a = ·}` interpolated between `(1+ρ)/2` and
`(1-ρ)/2`. -/
private lemma sum_zmod2_ite_const (ρ : ℝ) (a : ZMod 2) :
    (∑ j : ZMod 2, (if j = a then (1 + ρ) / 2 else (1 - ρ) / 2)) = 1 := by
  rw [zmod2_univ, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
  rcases zmod2_eq_zero_or_one a with h | h <;> subst h <;> simp <;> ring

/-- Sum over `ZMod 2` of the level function interpolated between `(1+ρ)/2` and `(1-ρ)/2`,
weighted by the character `(-1)^{j}`. -/
private lemma sum_zmod2_ite_sign (ρ : ℝ) (a : ZMod 2) :
    (∑ j : ZMod 2, (if j = a then (1 + ρ) / 2 else (1 - ρ) / 2) * (-1 : ℝ) ^ j.val)
      = ρ * (-1 : ℝ) ^ a.val := by
  rw [zmod2_univ, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
  rcases zmod2_eq_zero_or_one a with h | h <;>
    subst h <;> simp [ZMod.val_zero, ZMod.val_one] <;> ring

/-- The noise operator on the hypercube `{0,1}^n = (Fin n → ZMod 2)` has Fourier
character `S ↦ ρ^{|S|}`: the Fourier coefficient at the character
`y ↦ ∏_{i ∈ S} (-1)^{y_i}` of the noisy function is `ρ^{|S|}` times that character
evaluated at `x`. -/
theorem noise_op_char (n : ℕ) (ρ : ℝ) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    (∑ y : Fin n → ZMod 2,
        (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2)) *
          (∏ i ∈ S, (-1 : ℝ) ^ (y i).val))
      = ρ ^ S.card * (∏ i ∈ S, (-1 : ℝ) ^ (x i).val) := by
  classical
  set g : (i : Fin n) → ZMod 2 → ℝ :=
    fun i a => (if a = x i then (1 + ρ) / 2 else (1 - ρ) / 2) *
      (if i ∈ S then (-1 : ℝ) ^ a.val else 1) with hg
  -- Absorb the `S`-product into the full product over all coordinates.
  have step1 : ∀ y : Fin n → ZMod 2,
      (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2)) *
        (∏ i ∈ S, (-1 : ℝ) ^ (y i).val) = ∏ i : Fin n, g i (y i) := by
    intro y
    rw [← Finset.prod_ite_mem_eq S (fun i : Fin n => (-1 : ℝ) ^ (y i).val),
      ← Finset.prod_mul_distrib]
  simp only [step1]
  -- Factor the sum over functions as a product of sums over coordinates.
  have h2 : (∑ y : Fin n → ZMod 2, ∏ i : Fin n, g i (y i))
      = ∏ i : Fin n, ∑ j : ZMod 2, g i j := by
    rw [show (∑ y : Fin n → ZMod 2, ∏ i : Fin n, g i (y i))
        = ∑ y ∈ (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))),
            ∏ i : Fin n, g i (y i) from by
      rw [Fintype.piFinset_univ]]
    rw [Finset.sum_prod_piFinset]
  rw [h2]
  -- Evaluate the one-dimensional sums.
  have hcoord : ∀ i : Fin n, (∑ j : ZMod 2, g i j)
      = if i ∈ S then ρ * (-1 : ℝ) ^ (x i).val else 1 := by
    intro i
    by_cases hi : i ∈ S
    · rw [hg]
      simp only [hi, if_true]
      exact sum_zmod2_ite_sign ρ (x i)
    · rw [hg]
      simp only [hi, if_false, mul_one]
      exact sum_zmod2_ite_const ρ (x i)
  rw [Finset.prod_congr rfl (fun i _ => hcoord i)]
  rw [Finset.prod_ite_mem_eq S (fun i : Fin n => ρ * (-1 : ℝ) ^ (x i).val)]
  rw [Finset.prod_mul_distrib, Finset.prod_const ρ]

end Commons.Analysis.Inequalities