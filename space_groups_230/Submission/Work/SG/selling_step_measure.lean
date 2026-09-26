import Mathlib
import Submission.Work.SG.SellingStep

/-! ## The Selling step lowers the energy `∑ m, qf Q (v m)` by exactly `2 * bf Q (v i) (v j)`

For a superbase `v : Fin 4 → IVec` (four vectors summing to zero) and a symmetric integer form
`Q`, the `(i,j)`-Selling step `sellStep v i j` (negate `v i`, keep `v j`, add `v i` to the two
remaining vectors) changes the energy by `- 2 * bf Q (v i) (v j)`:

`selling_step_measure`.

The proof writes the step as a "shift" of the sum `∑ m, qf Q (v m + v i)` plus a correction
supported on `{i,j}`:

* `∑ m, qf Q (v m + v i) = ∑ m, qf Q (v m) + 2 * ∑ m, bf Q (v m) (v i) + 4 * qf Q (v i)`
  (bilinearity of `bf`, and `Fintype.card (Fin 4) = 4`);
* `∑ m, bf Q (v m) (v i) = 0` (linearity in the first argument, `∑ m, v m = 0`, `bf Q 0 _ = 0`);
* the pointwise difference `qf Q (sellStep v i j m) - qf Q (v m + v i)` vanishes unless `m ∈ {i,j}`
  (`sum_eq_of_eq_zero_off`), where it equals `-3 * qf Q (v i)` and `-2 * bf Q (v j) (v i) -
  qf Q (v i)` respectively.

Adding up gives `∑ m, qf Q (sellStep v i j m) = ∑ m, qf Q (v m) - 2 * bf Q (v j) (v i)`, and
symmetry of `bf` (`bf_comm`) yields the stated form.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

/-! ### Elementary bilinearity of `bf`, in the form needed below -/

private theorem bf_zero_left (Q : IMat) (v : IVec) : bf Q (0 : IVec) v = 0 := by simp [bf]

private theorem bf_add_left (Q : IMat) (u u' v : IVec) :
    bf Q (u + u') v = bf Q u v + bf Q u' v := by
  simp only [bf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem bf_sum_left (Q : IMat) (s : Finset (Fin 4)) (u : Fin 4 → IVec) (y : IVec) :
    bf Q (∑ m ∈ s, u m) y = ∑ m ∈ s, bf Q (u m) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [bf_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bf_add_left, ih]

/-- Expansion of the quadratic form of a sum for a symmetric form. -/
private theorem qf_add (Q : IMat) (hsym : Q.transpose = Q) (u w : IVec) :
    qf Q (u + w) = qf Q u + qf Q w + 2 * bf Q u w := by
  rw [qf, bf_add_right, bf_add_left Q u w u, bf_add_left Q u w w, bf_comm Q hsym w u]
  simp only [qf]
  ring

/-- A function `Fin 4 → ℤ` vanishing off the two (distinct) indices `i`, `j` has sum
`f i + f j`. -/
private theorem sum_eq_of_eq_zero_off (f : Fin 4 → ℤ) (i j : Fin 4) (hij : i ≠ j)
    (h : ∀ m, m ≠ i → m ≠ j → f m = 0) : ∑ m, f m = f i + f j := by
  classical
  have h1 : ∑ m ∈ Finset.univ.erase i, f m + f i = ∑ m, f m :=
    Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have h2 : ∑ m ∈ (Finset.univ.erase i).erase j, f m + f j
      = ∑ m ∈ Finset.univ.erase i, f m :=
    Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  have h3 : ∑ m ∈ (Finset.univ.erase i).erase j, f m = 0 :=
    Finset.sum_eq_zero fun m hm => h m (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
      (Finset.mem_erase.mp hm).1
  linarith

theorem selling_step_measure (Q : IMat) (hsym : Q.transpose = Q) (v : Fin 4 → IVec)
    (hsum : ∑ m, v m = 0) (i j : Fin 4) (hij : i ≠ j) :
    ∑ m, qf Q (sellStep v i j m) = ∑ m, qf Q (v m) - 2 * bf Q (v i) (v j) := by
  classical
  -- `∑ m, bf Q (v m) (v i) = 0`, because `∑ m, v m = 0` and `bf` is linear in its first slot.
  have hS : ∑ m, bf Q (v m) (v i) = 0 := by
    rw [← bf_sum_left Q Finset.univ v (v i), hsum, bf_zero_left]
  -- The "shifted" energy `∑ m, qf Q (v m + v i)`.
  have hU : ∑ m, qf Q (v m + v i)
      = (∑ m, qf Q (v m)) + 2 * (∑ m, bf Q (v m) (v i)) + 4 * qf Q (v i) := by
    have hpt : ∀ m, qf Q (v m + v i) = qf Q (v m) + 2 * bf Q (v m) (v i) + qf Q (v i) := by
      intro m
      rw [qf_add Q hsym (v m) (v i)]
      ring
    calc ∑ m, qf Q (v m + v i)
        = ∑ m, (qf Q (v m) + 2 * bf Q (v m) (v i) + qf Q (v i)) :=
          Finset.sum_congr rfl fun m _ => hpt m
      _ = (∑ m, qf Q (v m)) + (∑ m, 2 * bf Q (v m) (v i)) + (∑ m, qf Q (v i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ m, qf Q (v m)) + 2 * (∑ m, bf Q (v m) (v i)) + 4 * qf Q (v i) := by
          rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num
  -- The pointwise correction is supported on `{i,j}`.
  have hD : ∑ m, (qf Q (sellStep v i j m) - qf Q (v m + v i))
      = -4 * qf Q (v i) - 2 * bf Q (v j) (v i) := by
    have hfz : ∀ m, m ≠ i → m ≠ j →
        (qf Q (sellStep v i j m) - qf Q (v m + v i)) = 0 := by
      intro m hmi hmj
      simp [sellStep, hmi, hmj]
    rw [sum_eq_of_eq_zero_off _ i j hij hfz]
    have hsi : sellStep v i j i = - v i := by simp [sellStep]
    have hsj : sellStep v i j j = v j := by simp [sellStep, hij.symm]
    have h1 : qf Q (sellStep v i j i) - qf Q (v i + v i) = -3 * qf Q (v i) := by
      rw [hsi, qf_neg, qf_add Q hsym (v i) (v i)]
      simp only [qf]
      ring
    have h2 : qf Q (sellStep v i j j) - qf Q (v j + v i)
        = -2 * bf Q (v j) (v i) - qf Q (v i) := by
      rw [hsj, qf_add Q hsym (v j) (v i)]
      ring
    rw [h1, h2]
    ring
  -- Split the energy of the step into the shifted energy plus the correction.
  have hT : ∑ m, qf Q (sellStep v i j m)
      = (∑ m, qf Q (v m + v i))
        + ∑ m, (qf Q (sellStep v i j m) - qf Q (v m + v i)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hT, hU, hS, hD, bf_comm Q hsym (v j) (v i)]
  ring

end Work.SG
