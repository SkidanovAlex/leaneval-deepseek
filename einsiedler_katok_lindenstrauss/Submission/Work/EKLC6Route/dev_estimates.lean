import Mathlib
import Submission.Work.EKLC6Route.Defs

namespace Work.EKLC6Route

open Work.EKLContract

/-- Every entry of `g` is within `dev g` of the corresponding entry of the identity matrix. -/
theorem abs_dev_entry (g : SL3) (i j : Fin 3) :
    |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ dev g :=
  Finset.le_sup' (fun p : Fin 3 × Fin 3 =>
    |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2 -
      (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (i, j))

/-- Entrywise estimate for the product: the displacement matrix of `g * h` is
`(g-1)(h-1) + (g-1) + (h-1)`, and each summand is controlled by `dev`. -/
theorem dev_mul_entry_le (g h : SL3) (i j : Fin 3) :
    |((g * h : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j -
        (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ dev g + dev h + 3 * dev g * dev h := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  set a : Matrix (Fin 3) (Fin 3) ℝ := (g : Matrix (Fin 3) (Fin 3) ℝ) - 1 with ha_def
  set b : Matrix (Fin 3) (Fin 3) ℝ := (h : Matrix (Fin 3) (Fin 3) ℝ) - 1 with hb_def
  have ha : a + 1 = (g : Matrix (Fin 3) (Fin 3) ℝ) := sub_add_cancel _ _
  have hb : b + 1 = (h : Matrix (Fin 3) (Fin 3) ℝ) := sub_add_cancel _ _
  have hAB : (g : Matrix (Fin 3) (Fin 3) ℝ) * (h : Matrix (Fin 3) (Fin 3) ℝ) - 1 =
      a * b + a + b := by
    rw [← ha, ← hb]; noncomm_ring
  have hg : ∀ p : Fin 3, |a i p| ≤ dev g := by
    intro p; rw [ha_def, Matrix.sub_apply]; exact abs_dev_entry g i p
  have hh : ∀ p : Fin 3, |b p j| ≤ dev h := by
    intro p; rw [hb_def, Matrix.sub_apply]; exact abs_dev_entry h p j
  rw [← Matrix.sub_apply, hAB, Matrix.add_apply, Matrix.add_apply]
  have h1 : |(a * b) i j| ≤ 3 * (dev g * dev h) := by
    rw [Matrix.mul_apply]
    calc |∑ k, a i k * b k j| ≤ ∑ k, |a i k * b k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |a i k| * |b k j| := by simp only [abs_mul]
      _ ≤ ∑ k, dev g * dev h := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul (hg k) (hh k) (abs_nonneg _)
              (le_trans (abs_nonneg _) (hg k))
      _ = 3 * (dev g * dev h) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
  have h2 : |a i j| ≤ dev g := hg j
  have h3 : |b i j| ≤ dev h := hh i
  calc |(a * b) i j + a i j + b i j| ≤ |(a * b) i j + a i j| + |b i j| := abs_add_le _ _
    _ ≤ (|(a * b) i j| + |a i j|) + |b i j| := by
          have := abs_add_le ((a * b) i j) (a i j); linarith
    _ ≤ 3 * (dev g * dev h) + dev g + dev h := by linarith
    _ = dev g + dev h + 3 * dev g * dev h := by ring

/-- `dev (g * h) ≤ dev g + dev h + 3 dev g dev h`. -/
theorem dev_mul_le (g h : SL3) :
    dev (g * h) ≤ dev g + dev h + 3 * dev g * dev h := by
  apply Finset.sup'_le
  intro p _
  obtain ⟨i, j⟩ := p
  exact dev_mul_entry_le g h i j

/-- `dev (1) = 0`. -/
theorem dev_one : dev (1 : SL3) = 0 := by
  refine le_antisymm ?_ (le_trans (abs_nonneg _)
    (Finset.le_sup' (fun p : Fin 3 × Fin 3 =>
      |((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2 -
        (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (0, 0))))
  apply Finset.sup'_le
  intro p _
  simp [Matrix.SpecialLinearGroup.coe_one]

/-- `g ∈ V s ↔ dev g < s`: `V s` is the "sup-entry" ball of radius `s`. -/
theorem mem_V_iff_dev_lt (g : SL3) (s : ℝ) : (g ∈ V s ↔ dev g < s) := by
  simp only [V, Set.mem_ofPred_eq, dev]
  rw [Finset.sup'_lt_iff Finset.univ_nonempty]
  constructor
  · rintro h ⟨i, j⟩ _
    exact h i j
  · intro h i j
    exact h (i, j) (Finset.mem_univ _)

theorem dev_estimates (g h : Work.EKLContract.SL3) (i j : Fin 3) (s : ℝ) :
    (0 ≤ Work.EKLC6Route.dev g) ∧
    |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤
      Work.EKLC6Route.dev g ∧
    Work.EKLC6Route.dev (1 : Work.EKLContract.SL3) = 0 ∧
    Work.EKLC6Route.dev (g * h) ≤ Work.EKLC6Route.dev g + Work.EKLC6Route.dev h +
      3 * Work.EKLC6Route.dev g * Work.EKLC6Route.dev h ∧
    (g ∈ Work.EKLContract.V s ↔ Work.EKLC6Route.dev g < s) := by
  refine ⟨le_trans (abs_nonneg _) (Finset.le_sup' (fun p : Fin 3 × Fin 3 =>
      |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2 -
        (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (0, 0))),
    abs_dev_entry g i j, dev_one, dev_mul_le g h, mem_V_iff_dev_lt g s⟩

end Work.EKLC6Route
