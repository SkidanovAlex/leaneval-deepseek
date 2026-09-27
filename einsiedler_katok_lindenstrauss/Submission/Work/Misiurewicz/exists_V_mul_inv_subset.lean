import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLProd.inv_entries_bound

/-!
# `Work.Misiurewicz.exists_V_mul_inv_subset`

For every `ε > 0` there is `η > 0` with

    V η · (V η)⁻¹ ⊆ V ε,

where `V δ = {g ∈ SL₃(ℝ) | ∀ i j, |g i j - 1 i j| < δ}` is the max-entry displacement
neighbourhood of the identity used throughout the EKL development.

In other words, the two-sided "closeness" relation on the space of lattices that is measured by
`V` is transitive with a controlled modulus: if `y = u • x` and `z = v • y` with `u, v ∈ V η`,
then `z = v u⁻¹ • x` with `v u⁻¹ ∈ V ε` (this is what `Work.EKLComp.fine_Vball` consumes).

## The argument

For `u, v ∈ V η` we write, with all differences taken entrywise,

    v * u⁻¹ - 1 = (v - u) * u⁻¹ = ((v - 1) - (u - 1)) * u⁻¹,

using `u * u⁻¹ = 1`.  Every entry of `v - u` is bounded by `2η` (both `u` and `v` are `η`-close
to the identity), and every entry of `u⁻¹` is bounded by `2 (1+η)²`:  indeed `det u = 1`, so
`u⁻¹` is the adjugate of `u`, whose entries are `2 × 2` minors of a matrix whose entries are
bounded by `1 + η`.  Hence every entry of `v * u⁻¹ - 1` is bounded by `3 · 2η · 2(1+η)²`, which
is `< ε` as soon as `η ≤ 1/2` and `48η < ε`.  Taking `η = min (1/2) (ε/100)` closes the
argument.
-/

open Matrix

namespace Work.Misiurewicz

open Work.EKLContract

/-- Every entry of the inverse of `u ∈ V η` is bounded by `2 (1 + η)²`.

`det u = 1`, so `u⁻¹` is the adjugate of `u` (`Matrix.SpecialLinearGroup.coe_inv`), and the
entries of the adjugate are `2 × 2` minors of `u`, whose entries are all bounded by `1 + η`
(`Work.EKLProd.abs_adjugate_entry_le`). -/
private lemma abs_inv_entry_le {η : ℝ} (hη : 0 < η) {u : SL3} (hu : u ∈ V η) (k l : Fin 3) :
    |((u⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ 2 * (1 + η) ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  refine Work.EKLProd.abs_adjugate_entry_le (by linarith) (fun p q => ?_) k l
  have h1 : |(u : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < η :=
    hu p q
  have h2 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) p q| ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  calc |(u : Matrix (Fin 3) (Fin 3) ℝ) p q|
      = |((u : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q)
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| := by rw [sub_add_cancel]
    _ ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) p q| := abs_add_le _ _
    _ ≤ η + 1 := add_le_add (le_of_lt h1) h2
    _ = 1 + η := by ring

/-- The entrywise core of the proof: if `A` and `B` are `η`-close to the identity, `A * W = 1`
and every entry of `W` is bounded by `2 (1 + η)²`, then `B * W` is `ε`-close to the identity,
provided `η ≤ 1/2` and `48 η < ε`. -/
private lemma matrix_close {ε η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hηε : 48 * η < ε)
    {A B W : Matrix (Fin 3) (Fin 3) ℝ} (hA : A * W = 1)
    (hAε : ∀ p q, |A p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < η)
    (hBε : ∀ p q, |B p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < η)
    (hW : ∀ k l, |W k l| ≤ 2 * (1 + η) ^ 2) :
    ∀ i j, |(B * W) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε := by
  -- `B * W - 1 = (B - A) * W`, using `A * W = 1`
  have hkey : B * W - 1 = (B - A) * W := by
    rw [Matrix.sub_mul, hA]
  -- each entry of `B - A` is bounded by `2 η`
  have hBA : ∀ p k, |(B - A) p k| ≤ 2 * η := by
    intro p k
    have h3 : (B - A) p k
        = (B p k - (1 : Matrix (Fin 3) (Fin 3) ℝ) p k)
          - (A p k - (1 : Matrix (Fin 3) (Fin 3) ℝ) p k) := by
      rw [Matrix.sub_apply]; ring
    rw [h3]
    have h4 : |(B p k - (1 : Matrix (Fin 3) (Fin 3) ℝ) p k)
            - (A p k - (1 : Matrix (Fin 3) (Fin 3) ℝ) p k)| < 2 * η := by
      calc |(B p k - (1 : Matrix (Fin 3) (Fin 3) ℝ) p k)
              - (A p k - (1 : Matrix (Fin 3) (Fin 3) ℝ) p k)|
          ≤ |B p k - (1 : Matrix (Fin 3) (Fin 3) ℝ) p k|
            + |A p k - (1 : Matrix (Fin 3) (Fin 3) ℝ) p k| := abs_sub _ _
        _ < η + η := add_lt_add (hBε p k) (hAε p k)
        _ = 2 * η := by ring
    exact le_of_lt h4
  intro i j
  have hentry : (B * W) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = ∑ k : Fin 3, (B - A) i k * W k j := by
    rw [← Matrix.mul_apply, ← hkey, Matrix.sub_apply]
  rw [hentry]
  have hbd : |∑ k : Fin 3, (B - A) i k * W k j| ≤ 12 * η * (1 + η) ^ 2 := by
    calc |∑ k : Fin 3, (B - A) i k * W k j|
        ≤ ∑ k : Fin 3, |(B - A) i k * W k j| :=
          Finset.abs_sum_le_sum_abs (fun k : Fin 3 => (B - A) i k * W k j) Finset.univ
      _ ≤ ∑ _k : Fin 3, (2 * η) * (2 * (1 + η) ^ 2) := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul (hBA i k) (hW k j) (abs_nonneg _) (by linarith)
      _ = 12 * η * (1 + η) ^ 2 := by
          rw [Fin.sum_univ_three]; ring
  have hfin : 12 * η * (1 + η) ^ 2 < ε := by
    have h4 : (1 + η) ^ 2 ≤ 4 := by
      have h41 : 1 + η ≤ 2 := by linarith
      have h40 : (0 : ℝ) ≤ 1 + η := by linarith
      have h := pow_le_pow_left₀ h40 h41 2
      norm_num at h
      exact h
    have h5 : 12 * η * (1 + η) ^ 2 ≤ 12 * η * 4 :=
      mul_le_mul_of_nonneg_left h4 (by linarith)
    linarith
  linarith

theorem exists_V_mul_inv_subset (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ u v : Work.EKLContract.SL3, u ∈ Work.EKLContract.V η → v ∈ Work.EKLContract.V η → v * u⁻¹ ∈ Work.EKLContract.V ε := by
  have hηε : 48 * min (1 / 2) (ε / 100) < ε := by
    have h := min_le_right (1 / 2 : ℝ) (ε / 100)
    linarith
  refine ⟨min (1 / 2) (ε / 100), lt_min (by norm_num) (by linarith), ?_⟩
  have hη : 0 < min (1 / 2) (ε / 100) := lt_min (by norm_num) (by linarith)
  have hη1 : min (1 / 2) (ε / 100) ≤ 1 / 2 := min_le_left _ _
  intro u v hu hv
  refine fun i j => ?_
  have hA : (u : Matrix (Fin 3) (Fin 3) ℝ) * ((u⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact matrix_close hη hη1 hηε hA (fun p q => hu p q) (fun p q => hv p q)
    (fun k l => abs_inv_entry_le hη hu k l) i j

end Work.Misiurewicz
