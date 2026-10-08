import Mathlib
import Submission.Work.PSU3.StageB.Omega.Seq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.Omega

open Work.PSU3

/-- The closed form of `uSeq` as a ratio of the "denominator sequence"
`S_i = β^i + (β^i)⁻¹`:  `u_{i+1} = S_i / S_{i+1}`.  This is the shape in which the
product of §2 (13) telescopes. -/
private lemma uSeq_succ_div {n : ℕ} (β : E n) (hβ : β ≠ 0) (i : ℕ) :
    uSeq β (i+1) = (β^i + (β^i)⁻¹)/(β^(i+1) + (β^(i+1))⁻¹) := by
  rw [uSeq]
  have h1 : β^(i+1)/β = β^i := by rw [pow_succ]; field_simp
  have h2 : β/β^(i+1) = (β^i)⁻¹ := by rw [pow_succ]; field_simp
  rw [h1, h2]

/-- `∏_{j=2}^{k} u_j = S_1 / S_k`: the product telescopes, the numerator `S_1 = β + β⁻¹ = α`
surviving at the bottom and `S_k = β^k + (β^k)⁻¹` at the top. -/
private lemma prod_uSeq {n : ℕ} (α β : E n) (hα : β + β⁻¹ = α) (hβ : β ≠ 0) :
    ∀ k, 2 ≤ k → (∀ j, 2 ≤ j → j ≤ k → β^j + (β^j)⁻¹ ≠ 0) →
      ∏ j ∈ Finset.Icc 2 k, uSeq β j = α/(β^k + (β^k)⁻¹) := by
  intro k
  refine Nat.le_induction ?base ?step k
  · intro _
    rw [Finset.Icc_self, Finset.prod_singleton]
    rw [uSeq_succ_div β hβ 1]
    rw [pow_one, hα]
  · intro m hm ih h
    rw [Finset.prod_Icc_succ_top (show 2 ≤ m+1 by omega) (fun j => uSeq β j)]
    rw [ih (fun j hj hjm => h j hj (le_trans hjm (Nat.le_succ m)))]
    have hSm : β^m + (β^m)⁻¹ ≠ 0 := h m (by omega) (by omega)
    rw [uSeq_succ_div β hβ m, div_mul_div_comm, mul_comm α (β^m + (β^m)⁻¹)]
    exact mul_div_mul_left α (β^(m+1) + (β^(m+1))⁻¹) hSm

theorem uSeq_telescope {n : ℕ} (α β : Work.PSU3.E n) (hα : β + β⁻¹ = α) (hβ : β ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) (h : ∀ j, 2 ≤ j → j ≤ k → β ^ j + (β ^ j)⁻¹ ≠ 0) :
    (Finset.Icc 2 k).prod (fun j => Work.PSU3.StageB.Omega.uSeq β j) =
      α / (β ^ k + (β ^ k)⁻¹) :=
  prod_uSeq α β hα hβ k hk h

end Work.PSU3.StageB.Omega
