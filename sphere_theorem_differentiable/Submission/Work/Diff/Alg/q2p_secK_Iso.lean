import Mathlib
import Submission.Diff.Alg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `secK (Iso n) u v = 1` on an orthonormal pair

`Iso n` is the curvature tensor of the unit round sphere, `δᵢₖ δⱼₗ - δᵢₗ δⱼₖ`.  Its sectional
curvature on every orthonormal plane is `1`; this is the normalization under which Hamilton's
reaction term satisfies `Q (Iso n) = 2 (n - 1) • Iso n`, and it is the constant that fixes the
pinching scale in the quarter-pinching algebra (`Work.Diff.Alg.quarter_to_pic2`).

The proof is the elementary computation
`R4 (Iso n) a b c d = ⟪a, c⟫ ⟪b, d⟫ - ⟪a, d⟫ ⟪b, c⟫`,
obtained by collapsing the Kronecker deltas in the four-fold sum defining `R4`; specializing to
`a = c = u`, `b = d = v` and using orthonormality gives `1 * 1 - 0 * 0 = 1`.
-/

namespace Work.Diff.Alg

open Submission.Diff.Alg Finset

/-- Summation against a Kronecker delta: `∑ k, (if i = k then 1 else 0) * g k = g i`. -/
theorem sum_ite_one_mul {n : ℕ} (i : Fin n) (g : Fin n → ℝ) :
    (∑ k, (if i = k then (1 : ℝ) else 0) * g k) = g i := by
  have h : ∀ k : Fin n, (if i = k then (1 : ℝ) else 0) * g k = (if k = i then g k else 0) := by
    intro k; split_ifs with hk <;> simp_all
  rw [Finset.sum_congr rfl (fun k _ => h k)]
  simp

/-- Collapsing two Kronecker deltas: `∑ k l, δᵢₖ δⱼₗ cₖ dₗ = cᵢ dⱼ`. -/
theorem kron_sum {n : ℕ} (i j : Fin n) (c d : Fin n → ℝ) :
    (∑ k, ∑ l, (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0) * c k * d l)
      = c i * d j := by
  have hl : ∀ k, (∑ l, (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        * c k * d l) = (if i = k then (1 : ℝ) else 0) * c k * d j := by
    intro k
    rw [show (∑ l, (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0) * c k * d l)
        = (if i = k then (1 : ℝ) else 0) * c k * (∑ l, (if j = l then (1 : ℝ) else 0) * d l)
        from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _; ring]
    rw [sum_ite_one_mul j d]
  rw [Finset.sum_congr rfl (fun k _ => hl k), ← Finset.sum_mul, sum_ite_one_mul i c]

/-- The full four-fold double-delta sum: `∑ i j k l, δᵢₖ δⱼₗ aᵢ bⱼ cₖ dₗ = ⟪a,c⟫ ⟪b,d⟫`. -/
theorem kron_full {n : ℕ} (a b c d : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        * a i * b j * c k * d l) = dot a c * dot b d := by
  have step : ∀ i j, (∑ k, ∑ l, (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        * a i * b j * c k * d l) = a i * b j * (c i * d j) := by
    intro i j
    rw [show (∑ k, ∑ l, (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          * a i * b j * c k * d l)
        = a i * b j * (∑ k, ∑ l, (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          * c k * d l) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      ring]
    rw [kron_sum i j c d]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => step i j))]
  rw [show (∑ i, ∑ j, a i * b j * (c i * d j)) = (∑ i, a i * c i) * (∑ j, b j * d j) from by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring]
  rfl

/-- Swap the last two summation indices of a four-fold sum. -/
theorem sum4_swap34' {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F i j l k := by
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]

/-- `dot` is symmetric. -/
theorem dot_comm'' {n : ℕ} (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `R4 (Iso n) a b c d = ⟪a, c⟫ ⟪b, d⟫ - ⟪a, d⟫ ⟪b, c⟫`. -/
theorem R4_Iso {n : ℕ} (a b c d : Fin n → ℝ) :
    R4 (Iso n) a b c d = dot a c * dot b d - dot a d * dot b c := by
  have key : ∀ (i j k l : Fin n),
      (((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))
        * a i * b j * c k * d l)
      = (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0) * a i * b j * c k * d l
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0) * a i * b j * c k * d l
    := by intro i j k l; ring
  have hmain : R4 (Iso n) a b c d =
      (∑ i, ∑ j, ∑ k, ∑ l, (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        * a i * b j * c k * d l)
      - (∑ i, ∑ j, ∑ k, ∑ l, (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)
        * a i * b j * c k * d l) := by
    simp only [R4, Iso]
    simp only [key, Finset.sum_sub_distrib]
  rw [hmain, kron_full a b c d, sub_right_inj, sum4_swap34']
  simpa [mul_comm, mul_left_comm, mul_assoc] using kron_full a b d c

theorem q2p_secK_Iso {n : ℕ} {u v : Fin n → ℝ} (h : Submission.Diff.Alg.IsONPair u v) :
    Submission.Diff.Alg.secK (Submission.Diff.Alg.Iso n) u v = 1 := by
  simp only [secK]
  rw [R4_Iso]
  obtain ⟨huu, hvv, huv⟩ := h
  have hvu : dot v u = 0 := by rw [dot_comm'', huv]
  rw [huu, hvv, huv, hvu]
  norm_num

end Work.Diff.Alg
