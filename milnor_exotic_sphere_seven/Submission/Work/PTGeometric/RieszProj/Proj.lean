import Submission.Work.PTGeometric.RieszProj.Eigen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Phi S` is the orthogonal projection onto the top cluster
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped ContDiff
open Set Function MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n : ℕ}

/-- The indicator of the top cluster. -/
def chi (lam : ℝ) : ℝ := if |lam - 1| < 1/2 then 1 else 0

lemma chi_mul_self (lam : ℝ) : chi lam * chi lam = chi lam := by
  unfold chi; split <;> norm_num

lemma chi_eq_zero_or_one (lam : ℝ) : chi lam = 0 ∨ chi lam = 1 := by
  unfold chi; split <;> simp

/-- The expansion of a vector in the eigenbasis, in terms of inner products. -/
lemma sum_repr_inner {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hn : Module.finrank ℝ (Amb n) = n) (x : Amb n) :
    ∑ i, inner ℝ (hSsym.eigenvectorBasis hn i) x • hSsym.eigenvectorBasis hn i = x := by
  simpa only [OrthonormalBasis.repr_apply_apply] using (hSsym.eigenvectorBasis hn).sum_repr x

/-- On an eigenvector of the eigenbasis, `Phi S` acts as the top-cluster indicator. -/
lemma Phi_apply_eigenbasis {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (hn : Module.finrank ℝ (Amb n) = n) (i : Fin n) :
    Phi S (hSsym.eigenvectorBasis hn i)
      = chi (hSsym.eigenvalues hn i) • hSsym.eigenvectorBasis hn i := by
  have hne : hSsym.eigenvectorBasis hn i ≠ 0 :=
    (hSsym.eigenvectorBasis hn).orthonormal.ne_zero i
  have h := Phi_apply_eigen S hSsym hS hne (hSsym.eigenvalues hn i)
    (hSsym.hasEigenvalue_eigenvalues hn i) (hSsym.apply_eigenvectorBasis hn i)
  simpa only [chi] using h

/-- `Phi S` applied to any vector, in the eigenbasis. -/
lemma Phi_apply_eq {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (hn : Module.finrank ℝ (Amb n) = n) (x : Amb n) :
    Phi S x = ∑ i, (chi (hSsym.eigenvalues hn i)
      * inner ℝ (hSsym.eigenvectorBasis hn i) x) • hSsym.eigenvectorBasis hn i := by
  conv_lhs => rw [← sum_repr_inner hSsym hn x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Phi_apply_eigenbasis hSsym hS hn i, smul_smul, mul_comm]

/-- `Phi S` is idempotent. -/
lemma Phi_mul_self {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (hn : Module.finrank ℝ (Amb n) = n) : Phi S * Phi S = Phi S := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.mul_apply]
  have hx := Phi_apply_eq hSsym hS hn x
  have h1 : Phi S (Phi S x)
      = ∑ i, (chi (hSsym.eigenvalues hn i)
          * inner ℝ (hSsym.eigenvectorBasis hn i) x) • Phi S (hSsym.eigenvectorBasis hn i) := by
    rw [hx, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  rw [h1, hx]
  apply Finset.sum_congr rfl
  intro i _
  rw [Phi_apply_eigenbasis hSsym hS hn i, smul_smul]
  congr 1
  rw [mul_assoc, mul_comm (inner ℝ (hSsym.eigenvectorBasis hn i) x), ← mul_assoc, chi_mul_self]

/-- `Phi S` is self-adjoint. -/
lemma Phi_isSymmetric {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (hn : Module.finrank ℝ (Amb n) = n) :
    (Phi S : Amb n →ₗ[ℝ] Amb n).IsSymmetric := by
  intro x y
  change inner ℝ (Phi S x) y = inner ℝ x (Phi S y)
  rw [Phi_apply_eq hSsym hS hn x, Phi_apply_eq hSsym hS hn y]
  have h1 : inner ℝ (∑ i, (chi (hSsym.eigenvalues hn i)
        * inner ℝ (hSsym.eigenvectorBasis hn i) x) • hSsym.eigenvectorBasis hn i) y
      = ∑ i, (chi (hSsym.eigenvalues hn i) * inner ℝ (hSsym.eigenvectorBasis hn i) x)
        * inner ℝ (hSsym.eigenvectorBasis hn i) y := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_smul_left]
  have h2 : inner ℝ x (∑ i, (chi (hSsym.eigenvalues hn i)
        * inner ℝ (hSsym.eigenvectorBasis hn i) y) • hSsym.eigenvectorBasis hn i)
      = ∑ i, (chi (hSsym.eigenvalues hn i) * inner ℝ (hSsym.eigenvectorBasis hn i) y)
        * inner ℝ (hSsym.eigenvectorBasis hn i) x := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hcomm : inner ℝ x (hSsym.eigenvectorBasis hn i)
        = inner ℝ (hSsym.eigenvectorBasis hn i) x := (real_inner_comm x _).symm
    rw [real_inner_smul_right, hcomm]
  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro i _
  ring

end

end Work.PTGeometric
