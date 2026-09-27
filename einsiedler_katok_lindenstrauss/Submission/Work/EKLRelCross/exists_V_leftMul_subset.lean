import Mathlib
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLRelCross.exists_V_leftMul_subset` — left multiplication by a fixed `u` preserves
a `V`-neighbourhood of the identity (with a possibly larger radius)

`V δ = {g : SL₃(ℝ) | |g i j - 1 i j| < δ}` is the max-entry displacement neighbourhood of the
identity.  Since `V δ` is entrywise bounded and `SL₃(ℝ)` is a subgroup of the `3 × 3` matrices,
the image `u * (V δ)` of the *fixed* factor `u` is again contained in an entrywise box: for every
`u : SL₃(ℝ)` and every `δ > 0` there is `δ' > 0` with `u * V δ ⊆ V δ'` (`δ'` is the entrywise
radius of the image, which may of course be much larger than `δ`).

Proof (an explicit entrywise estimate, no compactness): `|u i j| ≤ M := ∑ i ∑ j |u i j|` for all
`i j`; for `g ∈ V δ` the decomposition
`(u * g) i j - 1 i j = ∑ k u i k (g k j - 1 k j) + (u i j - 1 i j)`
together with `|g k j - 1 k j| < δ`, `|1 i j| ≤ 1` and the triangle inequality gives
`|(u * g) i j - 1 i j| ≤ 3 M δ + (M + 1) < 3 M δ + M + 2`.
-/

namespace Work.EKLRelCross

open Work.EKLContract

/-- Left multiplication by a fixed `u : SL₃(ℝ)` maps the bounded box `V δ` into a box `V δ'`
(an entrywise estimate; no compactness needed). -/
theorem exists_V_leftMul_subset (u : Work.EKLContract.SL3) {δ : ℝ} (hδ : 0 < δ) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ g : Work.EKLContract.SL3, g ∈ Work.EKLContract.V δ →
      u * g ∈ Work.EKLContract.V δ' := by
  classical
  set M : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| with hMdef
  have hM : ∀ i j, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ M := by
    intro i j
    rw [hMdef]
    calc |(u : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ ∑ j' : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j'| := by
          exact Finset.single_le_sum (s := Finset.univ)
            (f := fun j' : Fin 3 => |(u : Matrix (Fin 3) (Fin 3) ℝ) i j'|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i' j'| := by
          exact Finset.single_le_sum (s := Finset.univ)
            (f := fun i' : Fin 3 => ∑ j' : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i' j'|)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 0)
  refine ⟨3 * M * δ + M + 2, ?_, ?_⟩
  · have h3M : 0 ≤ 3 * M := by linarith
    have h := mul_nonneg h3M (le_of_lt hδ)
    linarith
  · intro g hg i j
    have hsplit : (((u : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ)) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
        = (∑ k : Fin 3, (u : Matrix (Fin 3) (Fin 3) ℝ) i k
            * ((g : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j))
          + ((u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
      rw [Matrix.mul_apply]
      have h1 : ∑ k : Fin 3, (u : Matrix (Fin 3) (Fin 3) ℝ) i k
            * (1 : Matrix (Fin 3) (Fin 3) ℝ) k j = (u : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        simp [Matrix.one_apply]
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, h1]
      ring
    have hsum : |∑ k : Fin 3, (u : Matrix (Fin 3) (Fin 3) ℝ) i k
        * ((g : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)|
        ≤ 3 * M * δ := by
      calc |∑ k : Fin 3, (u : Matrix (Fin 3) (Fin 3) ℝ) i k
            * ((g : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)|
          ≤ ∑ k : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i k
            * ((g : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i k|
            * |(g : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j| := by
            simp only [abs_mul]
        _ ≤ ∑ _k : Fin 3, M * δ := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            exact mul_le_mul (hM i k) (le_of_lt (hg k j)) (abs_nonneg _) hM0
        _ = 3 * M * δ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hlast : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ M + 1 := by
      calc |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
            simpa using abs_sub_le ((u : Matrix (Fin 3) (Fin 3) ℝ) i j) 0
              ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
        _ ≤ M + 1 := by
            refine add_le_add (hM i j) ?_
            rw [Matrix.one_apply]; split <;> simp
    rw [show (((u * g : SL3)) : Matrix (Fin 3) (Fin 3) ℝ)
        = (u : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ) from
          Matrix.SpecialLinearGroup.coe_mul u g, hsplit]
    calc |(∑ k : Fin 3, (u : Matrix (Fin 3) (Fin 3) ℝ) i k
          * ((g : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j))
        + ((u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)|
        ≤ |∑ k : Fin 3, (u : Matrix (Fin 3) (Fin 3) ℝ) i k
          * ((g : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)|
          + |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
          abs_add_le _ _
      _ ≤ 3 * M * δ + (M + 1) := add_le_add hsum hlast
      _ < 3 * M * δ + M + 2 := by linarith

end Work.EKLRelCross
