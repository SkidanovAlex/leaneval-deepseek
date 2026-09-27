import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLC6Core.adjugate_entry_close

namespace Work.EKLC6Core

/-- Linear algebra of the entrywise box: if `w` lies in the box `B = {|g - 1| ≤ 1}` around the
identity and `g` is entrywise within `η` of `w`, then the displacement `g * w⁻¹` lies in the
displacement neighbourhood `V (24 η)`.  Indeed `↑(w⁻¹) = (↑w).adjugate` (det `w = 1`), the
adjugate of a matrix with entries in `[-1,2]` has entries of absolute value at most `8`
(`Matrix.adjugate_fin_three`), and
`↑(g * w⁻¹) - 1 = (↑g - ↑w) * (↑w).adjugate`, whose entries are sums of three terms of size
`< η * 8`. -/
theorem mul_inv_mem_V_of_entrywise_close (g w : Work.EKLContract.SL3)
    (hw : ∀ i j : Fin 3,
      |(w : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1)
    {η : ℝ} (hη : 0 < η)
    (h : ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (w : Matrix (Fin 3) (Fin 3) ℝ) i j| < η) :
    g * w⁻¹ ∈ Work.EKLContract.V (24 * η) := by
  -- The identity matrix has entries of absolute value at most `1`.
  have hone : ∀ i j : Fin 3, |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs <;> simp
  -- `w` lies in the closed box `{|g - 1| ≤ 1}`, hence `|w i j| ≤ 2` and `|(↑w).adjugate i j| ≤ 4`.
  have hwinv : ∀ k j : Fin 3,
      |((w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j| ≤ 5 := by
    intro k j
    have hadj := adjugate_entry_close (ε := 1) (by norm_num) (le_refl (1 : ℝ)) hw k j
    rw [Matrix.SpecialLinearGroup.coe_inv]
    calc |(w : Matrix (Fin 3) (Fin 3) ℝ).adjugate k j|
        = |((w : Matrix (Fin 3) (Fin 3) ℝ).adjugate k j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j) + (1 : Matrix (Fin 3) (Fin 3) ℝ) k j| := by
          rw [sub_add_cancel]
      _ ≤ |(w : Matrix (Fin 3) (Fin 3) ℝ).adjugate k j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) k j| :=
          abs_add_le _ _
      _ ≤ (2 * 1 + 2 * 1 ^ 2) + 1 := add_le_add hadj (hone k j)
      _ = 5 := by norm_num
  -- The displacement identity `↑(g * w⁻¹) - 1 = (↑g - ↑w) * ↑(w⁻¹)`.
  have hcoe : ((g * w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = (g : Matrix (Fin 3) (Fin 3) ℝ)
        * ((w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) :=
    Matrix.SpecialLinearGroup.coe_mul g w⁻¹
  have hmul : (w : Matrix (Fin 3) (Fin 3) ℝ)
      * ((w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hkey : ((g * w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1
      = ((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ))
        * ((w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [hcoe, Matrix.sub_mul, hmul]
  intro i j
  -- Each of the three summands is `< η * 5`.
  have hentry : ∀ k : Fin 3,
      |((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ)) i k
        * ((w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j| < η * 5 := by
    intro k
    rw [abs_mul, Matrix.sub_apply]
    calc |(g : Matrix (Fin 3) (Fin 3) ℝ) i k - (w : Matrix (Fin 3) (Fin 3) ℝ) i k|
          * |((w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j|
        ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ) i k - (w : Matrix (Fin 3) (Fin 3) ℝ) i k| * 5 :=
          mul_le_mul_of_nonneg_left (hwinv k j) (abs_nonneg _)
      _ < η * 5 := mul_lt_mul_of_pos_right (h i k) (by norm_num)
  calc |((g * w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      = |(((g * w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| := by
        rw [Matrix.sub_apply]
    _ = |(((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ))
            * ((w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j| := by rw [hkey]
    _ = |∑ k, ((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ)) i k
            * ((w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j| := by
        rw [Matrix.mul_apply]
    _ ≤ ∑ k, |((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ)) i k
            * ((w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ < ∑ _k : Fin 3, (η * 5) := by
        refine Finset.sum_lt_sum (f := fun k : Fin 3 =>
          |((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ)) i k
            * ((w⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j|)
          (fun k _ => le_of_lt (hentry k)) ⟨0, Finset.mem_univ 0, hentry 0⟩
    _ = 15 * η := by rw [Fin.sum_univ_three]; ring
    _ < 24 * η := by linarith

end Work.EKLC6Core
