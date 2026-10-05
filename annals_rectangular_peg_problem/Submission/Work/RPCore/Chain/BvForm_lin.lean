import Mathlib
import Submission.Work.RPCore.Chain.C4Defs

/-!
# C4: `BvForm` is a symmetric bilinear form vanishing on the diagonal

`BvForm n N δ` (see `Submission.Work.RPCore.Chain.C4Defs`) is the explicit polar bilinear form of
the quadratic part of the reference chain action.  Here we record the elementary structural
properties used everywhere downstream:

* it is **symmetric**, `BvForm n N δ z z' = BvForm n N δ z' z`;
* it is **additive** and **homogeneous** in its second argument;
* the diagonal direction `diagVec n` (shifting every angular coordinate `q₂` simultaneously) lies
  in its kernel, `BvForm n N δ z (diagVec n) = 0`.

The proof splits `BvForm` into its three summands `Q1`, `Q2`, `Q3` (linearised chain action of the
identity steps, middle-block cross term, middle-block quadratic term), each of which is checked
summand-wise.
-/

namespace Work.RPCore.Chain

open Work.RPV
open scoped BigOperators

noncomputable section

/-- First summand of `BvForm`: the linearised chain action of the identity steps. -/
private def Q1 (n : ℕ) (z z' : ChainSp n) : ℝ :=
  ∑ j : Fin n,
    ((z.2 j).1 * ((z'.1 j.succ).1 - (z'.1 j.castSucc).1) +
     (z'.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
     (z.2 j).2 * ((z'.1 j.succ).2 - (z'.1 j.castSucc).2) +
     (z'.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2))

/-- Second summand of `BvForm`: the middle-block cross term in `q₁` and `p₁`. -/
private def Q2 (n N : ℕ) (z z' : ChainSp n) : ℝ :=
  ∑ j : Fin n,
    (if midBlock N (j : ℕ) then
       ((z.1 j.castSucc).1 * (z'.2 j).1 + (z'.1 j.castSucc).1 * (z.2 j).1) else 0)

/-- Third summand of `BvForm`: the middle-block quadratic term in `q₁` and `p₁`. -/
private def Q3 (n N : ℕ) (z z' : ChainSp n) : ℝ :=
  ∑ j : Fin n,
    (if midBlock N (j : ℕ) then
       ((z.1 j.castSucc).1 * (z'.1 j.castSucc).1 + (z.2 j).1 * (z'.2 j).1) else 0)

private lemma BvForm_eq_Q (n N : ℕ) (δ : ℝ) (z z' : ChainSp n) :
    BvForm n N δ z z' = Q1 n z z' - (1 / Real.cos δ - 1) * Q2 n N z z'
      + Real.tan δ * Q3 n N z z' := rfl

/-! ### Symmetry -/

private lemma Q1_sym (n : ℕ) (z z' : ChainSp n) : Q1 n z z' = Q1 n z' z := by
  unfold Q1
  exact Finset.sum_congr rfl (fun j _ => by ring)

private lemma Q2_sym (n N : ℕ) (z z' : ChainSp n) : Q2 n N z z' = Q2 n N z' z := by
  unfold Q2
  exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring)

private lemma Q3_sym (n N : ℕ) (z z' : ChainSp n) : Q3 n N z z' = Q3 n N z' z := by
  unfold Q3
  exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring)

/-! ### Additivity in the second argument -/

private lemma Q1_add (n : ℕ) (z z' z'' : ChainSp n) :
    Q1 n z (z' + z'') = Q1 n z z' + Q1 n z z'' := by
  unfold Q1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)

private lemma Q2_add (n N : ℕ) (z z' z'' : ChainSp n) :
    Q2 n N z (z' + z'') = Q2 n N z z' + Q2 n N z z'' := by
  unfold Q2
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; split_ifs <;> ring)

private lemma Q3_add (n N : ℕ) (z z' z'' : ChainSp n) :
    Q3 n N z (z' + z'') = Q3 n N z z' + Q3 n N z z'' := by
  unfold Q3
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; split_ifs <;> ring)

/-! ### Homogeneity in the second argument -/

private lemma Q1_smul (n : ℕ) (c : ℝ) (z z' : ChainSp n) :
    Q1 n z (c • z') = c * Q1 n z z' := by
  unfold Q1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring)

private lemma Q2_smul (n N : ℕ) (c : ℝ) (z z' : ChainSp n) :
    Q2 n N z (c • z') = c * Q2 n N z z' := by
  unfold Q2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring)

private lemma Q3_smul (n N : ℕ) (c : ℝ) (z z' : ChainSp n) :
    Q3 n N z (c • z') = c * Q3 n N z z' := by
  unfold Q3
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring)

/-! ### Vanishing on the diagonal -/

private lemma Q1_diag (n : ℕ) (z : ChainSp n) : Q1 n z (diagVec n) = 0 := by
  unfold Q1; simp

private lemma Q2_diag (n N : ℕ) (z : ChainSp n) : Q2 n N z (diagVec n) = 0 := by
  unfold Q2; simp

private lemma Q3_diag (n N : ℕ) (z : ChainSp n) : Q3 n N z (diagVec n) = 0 := by
  unfold Q3; simp

/-! ### The bilinearity package -/

theorem BvForm_lin (n N : ℕ) (δ : ℝ) :
    (∀ z z' : ChainSp n, BvForm n N δ z z' = BvForm n N δ z' z) ∧
    (∀ z z' z'' : ChainSp n,
      BvForm n N δ z (z' + z'') = BvForm n N δ z z' + BvForm n N δ z z'') ∧
    (∀ (c : ℝ) (z z' : ChainSp n), BvForm n N δ z (c • z') = c * BvForm n N δ z z') ∧
    (∀ z : ChainSp n, BvForm n N δ z (diagVec n) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z z'
    rw [BvForm_eq_Q, BvForm_eq_Q, Q1_sym n z z', Q2_sym n N z z', Q3_sym n N z z']
  · intro z z' z''
    rw [BvForm_eq_Q, BvForm_eq_Q, BvForm_eq_Q, Q1_add n z z' z'', Q2_add n N z z' z'',
        Q3_add n N z z' z'']
    ring
  · intro c z z'
    rw [BvForm_eq_Q, BvForm_eq_Q, Q1_smul n c z z', Q2_smul n N c z z', Q3_smul n N c z z']
    ring
  · intro z
    rw [BvForm_eq_Q, Q1_diag n z, Q2_diag n N z, Q3_diag n N z]
    ring

end

end Work.RPCore.Chain
