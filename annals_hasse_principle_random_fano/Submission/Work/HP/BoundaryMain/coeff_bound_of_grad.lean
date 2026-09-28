import Mathlib
import Submission.Work.HP.BoundaryMain.grad_bound_def

set_option autoImplicit false

noncomputable section

namespace Work.HP.BoundaryMain

/-- Elementary consequence of the triangle inequality: from `|B + z| ≤ C` we deduce
`|z| ≤ C + |B|`. -/
lemma abs_le_add_abs_of_abs_add_le {B z C : ℝ} (h : |B + z| ≤ C) : |z| ≤ C + |B| := by
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2, neg_le_abs B, le_abs_self B]

/-- For `i ≠ j` the coefficient `c i` is pinned by the single gradient inequality
`|B i + c i · y_j^{d-1}| ≤ C`: dividing by `|y_j|^{d-1} > 0` gives the explicit bound. -/
theorem coeff_ne_bound (d n : ℕ) (C : ℝ) (y : Fin (n + 1) → ℝ)
    (j i : Fin (n + 1)) (hyj : y j ≠ 0) (B : Fin (n + 1) → ℝ) (c : Fin (n + 1) → ℤ)
    (h : |B i + (c i : ℝ) * y j ^ (d - 1)| ≤ C) :
    |(c i : ℝ)| ≤ (C + |B i|) / |y j| ^ (d - 1) := by
  have hKpos : 0 < |y j| ^ (d - 1) := pow_pos (abs_pos.mpr hyj) _
  rw [le_div_iff₀ hKpos]
  have h2 : |(c i : ℝ) * y j ^ (d - 1)| ≤ C + |B i| :=
    abs_le_add_abs_of_abs_add_le h
  have heq : |(c i : ℝ) * y j ^ (d - 1)| = |(c i : ℝ)| * |y j| ^ (d - 1) := by
    rw [abs_mul, abs_pow]
  rwa [heq] at h2

/-- For `i = j` the coefficient `c j` is pinned by the `j`-th gradient inequality
`|B j + y_j^{d-2} (d c_j y_j + (d-1) ∑_{i ≠ j} c_i y_i)| ≤ C`, using the bounds on the other
coefficients. -/
theorem coeff_j_bound (d n : ℕ) (hd2 : 2 ≤ d) (C : ℝ) (y : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) (hyj : y j ≠ 0) (B : Fin (n + 1) → ℝ) (c : Fin (n + 1) → ℤ)
    (hci : ∀ i : Fin (n + 1), i ≠ j → |(c i : ℝ)| ≤ (C + |B i|) / |y j| ^ (d - 1))
    (hj : |B j + y j ^ (d - 2) * ((d : ℝ) * (c j : ℝ) * y j
            + ((d : ℝ) - 1) * ∑ i ∈ Finset.univ.erase j, (c i : ℝ) * y i)| ≤ C) :
    |(c j : ℝ)| ≤ (C + |B j| + |y j| ^ (d - 2) * ((d : ℝ) - 1)
        * ∑ i ∈ Finset.univ.erase j, |(C + |B i|) / |y j| ^ (d - 1)| * |y i|)
      / ((d : ℝ) * |y j| ^ (d - 1)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hd1nn : (0 : ℝ) ≤ (d : ℝ) - 1 := by linarith
  have hKpos : 0 < |y j| ^ (d - 1) := pow_pos (abs_pos.mpr hyj) _
  have hLpos : 0 < |y j| ^ (d - 2) := pow_pos (abs_pos.mpr hyj) _
  set S : ℝ := ∑ i ∈ Finset.univ.erase j, (c i : ℝ) * y i with hS
  set T : ℝ := (d : ℝ) * (c j : ℝ) * y j + ((d : ℝ) - 1) * S with hT
  set Sig : ℝ := ∑ i ∈ Finset.univ.erase j, |(c i : ℝ)| * |y i| with hSig
  set Sig' : ℝ := ∑ i ∈ Finset.univ.erase j,
    |(C + |B i|) / |y j| ^ (d - 1)| * |y i| with hSig'
  have hjT : |B j + y j ^ (d - 2) * T| ≤ C := by rw [hT]; exact hj
  have h1 : |y j| ^ (d - 2) * |T| ≤ C + |B j| := by
    have hz : |y j ^ (d - 2) * T| ≤ C + |B j| :=
      abs_le_add_abs_of_abs_add_le hjT
    rwa [abs_mul, abs_pow] at hz
  have hSabs : |S| ≤ Sig := by
    rw [hS, hSig]
    calc |∑ i ∈ Finset.univ.erase j, (c i : ℝ) * y i|
        ≤ ∑ i ∈ Finset.univ.erase j, |(c i : ℝ) * y i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.univ.erase j, |(c i : ℝ)| * |y i| := by simp_rw [abs_mul]
  have hTsplit : |(d : ℝ) * (c j : ℝ) * y j| ≤ |T| + |((d : ℝ) - 1) * S| := by
    have heq : (d : ℝ) * (c j : ℝ) * y j = T + (-(((d : ℝ) - 1) * S)) := by
      rw [hT]; ring
    rw [heq]
    calc |T + (-(((d : ℝ) - 1) * S))| ≤ |T| + |(-(((d : ℝ) - 1) * S))| := abs_add_le _ _
      _ = |T| + |((d : ℝ) - 1) * S| := by rw [abs_neg]
  have he1 : |(d : ℝ) * (c j : ℝ) * y j| = (d : ℝ) * |(c j : ℝ)| * |y j| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (d : ℝ) by linarith)]
  have he2 : |((d : ℝ) - 1) * S| = ((d : ℝ) - 1) * |S| := by
    rw [abs_mul, abs_of_nonneg hd1nn]
  have h2 : (d : ℝ) * |(c j : ℝ)| * |y j| ≤ |T| + ((d : ℝ) - 1) * Sig := by
    rw [he1, he2] at hTsplit
    have h := mul_le_mul_of_nonneg_left hSabs hd1nn
    linarith
  have hSigle : Sig ≤ Sig' := by
    rw [hSig, hSig']
    apply Finset.sum_le_sum
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    exact mul_le_mul_of_nonneg_right (le_trans (hci i hij) (le_abs_self _)) (abs_nonneg _)
  have h3 : (d : ℝ) * |(c j : ℝ)| * |y j| * |y j| ^ (d - 2) ≤
      (|T| + ((d : ℝ) - 1) * Sig) * |y j| ^ (d - 2) :=
    mul_le_mul_of_nonneg_right h2 (le_of_lt hLpos)
  have hA : |T| * |y j| ^ (d - 2) ≤ C + |B j| := by
    rw [mul_comm]; exact h1
  have hB : ((d : ℝ) - 1) * Sig * |y j| ^ (d - 2) ≤
      ((d : ℝ) - 1) * Sig' * |y j| ^ (d - 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSigle hd1nn) (le_of_lt hLpos)
  have h4 : (|T| + ((d : ℝ) - 1) * Sig) * |y j| ^ (d - 2) ≤
      (C + |B j|) + ((d : ℝ) - 1) * Sig' * |y j| ^ (d - 2) := by
    nlinarith [hA, hB]
  have hLpow : |y j| * |y j| ^ (d - 2) = |y j| ^ (d - 1) := by
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]; ring
  have hLHS : (d : ℝ) * |(c j : ℝ)| * |y j| * |y j| ^ (d - 2) =
      (d : ℝ) * |(c j : ℝ)| * |y j| ^ (d - 1) := by rw [← hLpow]; ring
  have h5 : (d : ℝ) * |(c j : ℝ)| * |y j| ^ (d - 1) ≤
      (C + |B j|) + ((d : ℝ) - 1) * Sig' * |y j| ^ (d - 2) := by
    rw [hLHS] at h3; linarith [h3, h4]
  rw [le_div_iff₀ (by positivity : 0 < (d : ℝ) * |y j| ^ (d - 1))]
  nlinarith [h5]

theorem coeff_bound_of_grad (d n : ℕ) (hd2 : 2 ≤ d) (C : ℝ) (y : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) (hyj : y j ≠ 0) (B : Fin (n + 1) → ℝ) (c : Fin (n + 1) → ℤ)
    (hne : ∀ k : Fin (n + 1), k ≠ j → |B k + (c k : ℝ) * y j ^ (d - 1)| ≤ C)
    (hj : |B j + y j ^ (d - 2) * ((d : ℝ) * (c j : ℝ) * y j
            + ((d : ℝ) - 1) * ∑ i ∈ Finset.univ.erase j, (c i : ℝ) * y i)| ≤ C) :
    ∀ i : Fin (n + 1), |(c i : ℝ)| ≤ Work.HP.BoundaryMain.gradBound d n C y j B := by
  intro i
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) hj
  have hd1nn : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    linarith
  have hci : ∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ)| ≤ (C + |B k|) / |y j| ^ (d - 1) :=
    fun k hk => coeff_ne_bound d n C y j k hyj B c (hne k hk)
  have hQ := coeff_j_bound d n hd2 C y j hyj B c hci hj
  unfold gradBound
  rcases eq_or_ne i j with h | hij
  · rw [h]
    have hQnn : 0 ≤ (C + |B j| + |y j| ^ (d - 2) * ((d : ℝ) - 1)
        * ∑ i ∈ Finset.univ.erase j, |(C + |B i|) / |y j| ^ (d - 1)| * |y i|)
        / ((d : ℝ) * |y j| ^ (d - 1)) := by
      apply div_nonneg
      · have h1 : 0 ≤ |y j| ^ (d - 2) := pow_nonneg (abs_nonneg _) _
        have h3 : 0 ≤ ∑ i ∈ Finset.univ.erase j,
            |(C + |B i|) / |y j| ^ (d - 1)| * |y i| :=
          Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        have hp : 0 ≤ (|y j| ^ (d - 2) * ((d : ℝ) - 1))
            * ∑ i ∈ Finset.univ.erase j, |(C + |B i|) / |y j| ^ (d - 1)| * |y i| :=
          mul_nonneg (mul_nonneg h1 hd1nn) h3
        linarith [abs_nonneg (B j)]
      · positivity
    have hQabs : |(c j : ℝ)| ≤ |(C + |B j| + |y j| ^ (d - 2) * ((d : ℝ) - 1)
        * ∑ i ∈ Finset.univ.erase j, |(C + |B i|) / |y j| ^ (d - 1)| * |y i|)
        / ((d : ℝ) * |y j| ^ (d - 1))| := by
      rw [abs_of_nonneg hQnn]; exact hQ
    exact le_trans hQabs (le_max_right _ _)
  · have hci' : |(c i : ℝ)| ≤ (C + |B i|) / |y j| ^ (d - 1) := hci i hij
    calc |(c i : ℝ)| ≤ (C + |B i|) / |y j| ^ (d - 1) := hci'
      _ ≤ |(C + |B i|) / |y j| ^ (d - 1)| := le_abs_self _
      _ ≤ ∑ k : Fin (n + 1), |(C + |B k|) / |y j| ^ (d - 1)| :=
          Finset.single_le_sum
            (f := fun k : Fin (n + 1) => |(C + |B k|) / |y j| ^ (d - 1)|)
            (fun k _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ max (∑ k : Fin (n + 1), |(C + |B k|) / |y j| ^ (d - 1)|)
          |(C + |B j| + |y j| ^ (d - 2) * ((d : ℝ) - 1)
            * (∑ i ∈ Finset.univ.erase j, |(C + |B i|) / |y j| ^ (d - 1)| * |y i|))
            / ((d : ℝ) * |y j| ^ (d - 1))| := le_max_left _ _

end Work.HP.BoundaryMain
