import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.Defs

namespace Work.HP.EulerGrad

/-- Monomial-wise form of Euler's identity: for a single monomial `m` of degree `d`,
`∑_j (m_j) · y_j^{m_j} · ∏_{l ≠ j} y_l^{m_l} = d · ∏_i y_i^{m_i}`.
(Here `y_j^{m_j}` is written as `y j * y j ^ (m j - 1)`, which is the form in which the
monomial factor `y_j^{m_j - 1}` appears in `gradF`.) -/
private lemma mono_euler (d n : ℕ) (m : Mon d n) (y : Fin (n + 1) → ℝ) :
    ∑ j : Fin (n + 1), ((m.1 j : ℕ) : ℝ) * (y j * y j ^ ((m.1 j : ℕ) - 1)) *
        ∏ l ∈ Finset.univ.erase j, y l ^ ((m.1 l : ℕ)) =
      (d : ℝ) * ∏ i : Fin (n + 1), y i ^ ((m.1 i : ℕ)) := by
  have hterm : ∀ j : Fin (n + 1),
      ((m.1 j : ℕ) : ℝ) * (y j * y j ^ ((m.1 j : ℕ) - 1)) *
          ∏ l ∈ Finset.univ.erase j, y l ^ ((m.1 l : ℕ))
        = ((m.1 j : ℕ) : ℝ) * ∏ i : Fin (n + 1), y i ^ ((m.1 i : ℕ)) := by
    intro j
    by_cases h : (m.1 j : ℕ) = 0
    · rw [h]; simp
    · have h1 : 1 ≤ (m.1 j : ℕ) := Nat.one_le_iff_ne_zero.mpr h
      have hp : y j * y j ^ ((m.1 j : ℕ) - 1) = y j ^ (m.1 j : ℕ) := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel h1]
      rw [hp, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [← Finset.sum_mul]
  congr 1
  rw [← Nat.cast_sum, m.2]

/-- Euler's identity for the gradient of a degree-`d` form: `∑ j, y_j ∂_j f(y) = d · f(y)`. -/
theorem euler_grad (d n : ℕ) (b : Mon d n → ℝ) (y : Fin (n + 1) → ℝ) :
    ∑ j : Fin (n + 1), y j * gradF d n b y j = (d : ℝ) * formEvalR d n b y := by
  have hmain : ∀ m : Mon d n,
      (∑ j : Fin (n + 1), y j * (b m * ((m.1 j : ℕ) : ℝ) * y j ^ ((m.1 j : ℕ) - 1) *
          ∏ l ∈ Finset.univ.erase j, y l ^ ((m.1 l : ℕ))))
        = b m * ((d : ℝ) * ∏ i : Fin (n + 1), y i ^ ((m.1 i : ℕ))) := by
    intro m
    have h1 : (∑ j : Fin (n + 1), y j * (b m * ((m.1 j : ℕ) : ℝ) * y j ^ ((m.1 j : ℕ) - 1) *
          ∏ l ∈ Finset.univ.erase j, y l ^ ((m.1 l : ℕ))))
        = ∑ j : Fin (n + 1), b m * (((m.1 j : ℕ) : ℝ) * (y j * y j ^ ((m.1 j : ℕ) - 1)) *
            ∏ l ∈ Finset.univ.erase j, y l ^ ((m.1 l : ℕ))) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1, ← Finset.mul_sum, mono_euler]
  simp only [gradF, formEvalR, veronese]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun m _ => hmain m)]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

end Work.HP.EulerGrad
