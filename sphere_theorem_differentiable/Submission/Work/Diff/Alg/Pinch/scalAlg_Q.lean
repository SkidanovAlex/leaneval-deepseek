import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar curvature of Hamilton's reaction term: `scal (Q R) = 2 |Ric|²`

For an algebraic curvature tensor `R` (components `R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫` in an
orthonormal frame) the trace of Hamilton's quadratic term
`Q(R)ᵢⱼₖₗ = ∑_{p,q} (Rᵢⱼₚq Rₖₗₚq + 2 Rᵢₚₖq Rⱼₚₗq − 2 Rᵢₚₗq Rⱼₚₖq)`
is twice the squared norm of the Ricci tensor.  This is the "scalar curvature equation" of the
Ricci flow, `∂ₜ scal = Δ scal + 2|Ric|²`.

## Proof

Write `T₁ = ∑_{i,j,p,q} Rᵢⱼₚq²`, `T₂ = ∑_{i,j,p,q} Rᵢₚᵢq Rⱼₚⱼq` and
`T₃ = ∑_{i,j,p,q} Rᵢₚⱼq Rⱼₚᵢq`.  Expanding the trace gives `scal (Q R) = T₁ + 2 T₂ − 2 T₃`.

* `T₂ = ∑_{i,j} ricᵢⱼ ricᵢⱼ`: group the sum over `(p,q)` and use `∑ᵢ Rᵢₚᵢq = ricₚq`
  (`ric R p q = ∑ k, R k p k q`) together with `Finset.sum_mul_sum`.
* `T₁ = 2 T₃`: the first Bianchi identity, in the antisymmetrised form
  `Rᵢⱼₚq = Rᵢₚⱼq − Rᵢqⱼₚ` (equivalently `Rⱼₚᵢq = Rᵢₚⱼq − Rᵢⱼₚq`), writes
  `T₃ = T₁ − U` with `U = ∑ Rᵢₚⱼq Rᵢⱼₚq`; and `U = T₃` by exchanging the summation variables
  `i ↔ p` (a permutation of the summation indices) together with the antisymmetry of `R`.

Both of the last two steps are pure index gymnastics; the two reindexings
(`∑ Rᵢₚⱼq² = ∑ Rᵢⱼₚq²` and `∑ Rᵢₚⱼq Rᵢⱼₚq = ∑ Rᵢₚⱼq Rⱼₚᵢq`) are isolated in `private` lemmas so
that the main proof only has to multiply out the definition of `Q`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- Splitting a fourfold sum of `f + 2 g - 2 h` into three fourfold sums. -/
private lemma scalQ_sum4_split (n : ℕ) (f g h : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, (f a b c d + 2 * g a b c d - 2 * h a b c d))
      = (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) + 2 * (∑ a, ∑ b, ∑ c, ∑ d, g a b c d)
        - 2 * (∑ a, ∑ b, ∑ c, ∑ d, h a b c d) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The block exchange `∑_{i,j,p,q} = ∑_{p,q,i,j}` of a fourfold sum. -/
private lemma scalQ_sum4_block (n : ℕ) (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ p, ∑ q, F i j p q) = ∑ p, ∑ q, ∑ i, ∑ j, F i j p q := by
  rw [show (∑ i, ∑ j, ∑ p, ∑ q, F i j p q) = ∑ i, ∑ p, ∑ j, ∑ q, F i j p q from
    Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [show (∑ i, ∑ p, ∑ j, ∑ q, F i j p q) = ∑ i, ∑ p, ∑ q, ∑ j, F i j p q from
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p _ => Finset.sum_comm))]
  rw [show (∑ i, ∑ p, ∑ q, ∑ j, F i j p q) = ∑ p, ∑ i, ∑ q, ∑ j, F i j p q from
    Finset.sum_comm]
  rw [show (∑ p, ∑ i, ∑ q, ∑ j, F i j p q) = ∑ p, ∑ q, ∑ i, ∑ j, F i j p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_comm)]

/-- The index permutation `(i,j,p,q) ↦ (p,j,i,q)` of a fourfold sum. -/
private lemma scalQ_sum4_swap13 (n : ℕ) (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ p, ∑ q, F p j i q) = ∑ i, ∑ j, ∑ p, ∑ q, F i j p q := by
  rw [show (∑ i, ∑ j, ∑ p, ∑ q, F p j i q) = ∑ j, ∑ i, ∑ p, ∑ q, F p j i q from
    Finset.sum_comm]
  rw [show (∑ j, ∑ i, ∑ p, ∑ q, F p j i q) = ∑ j, ∑ p, ∑ i, ∑ q, F p j i q from
    Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  rw [show (∑ j, ∑ p, ∑ i, ∑ q, F p j i q) = ∑ p, ∑ j, ∑ i, ∑ q, F p j i q from
    Finset.sum_comm]

/-- The index permutation `(i,j,p,q) ↦ (i,p,j,q)` of a fourfold sum. -/
private lemma scalQ_sum4_swap23 (n : ℕ) (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ p, ∑ q, F i p j q) = ∑ i, ∑ j, ∑ p, ∑ q, F i j p q := by
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]

/-- **The scalar curvature of Hamilton's reaction term.**  For an algebraic curvature tensor `R`,
`scalAlg (Q R) = 2 ∑ᵢⱼ (ric R)ᵢⱼ (ric R)ᵢⱼ`. -/
theorem scalAlg_Q (n : ℕ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) :
    Submission.Diff.Alg.scalAlg (Submission.Diff.Alg.Q R) =
      2 * (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric R i j * Work.Diff.Alg.Pinch.ric R i j) := by
  have hanti := hR.1
  have hbian := hR.2.2
  -- Expand `scal (Q R)` into the double sums `T₁`, `T₂`, `T₃`.
  have hQ : scalAlg (Q R)
      = (∑ i, ∑ j, ∑ p, ∑ q, R i j p q * R i j p q)
        + 2 * (∑ i, ∑ j, ∑ p, ∑ q, R i p i q * R j p j q)
        - 2 * (∑ i, ∑ j, ∑ p, ∑ q, R i p j q * R j p i q) := by
    simp only [scalAlg, Q]
    rw [show (∑ i, ∑ j, ∑ p, ∑ q,
          (R i j p q * R i j p q + 2 * R i p i q * R j p j q - 2 * R i p j q * R j p i q))
        = ∑ i, ∑ j, ∑ p, ∑ q,
          ((R i j p q * R i j p q) + 2 * (R i p i q * R j p j q)
            - 2 * (R i p j q * R j p i q)) from by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro q _
      ring]
    exact scalQ_sum4_split n _ _ _
  -- The middle contraction is the squared norm of the Ricci tensor.
  have hT2 : (∑ i, ∑ j, ∑ p, ∑ q, R i p i q * R j p j q)
      = ∑ i, ∑ j, ric R i j * ric R i j := by
    rw [scalQ_sum4_block n (fun i j p q => R i p i q * R j p j q)]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    simp only [ric]
    rw [Finset.sum_mul_sum]
  -- The first contraction is twice the third one, by the first Bianchi identity.
  have hT3 : (∑ i, ∑ j, ∑ p, ∑ q, R i j p q * R i j p q)
      = 2 * (∑ i, ∑ j, ∑ p, ∑ q, R i p j q * R j p i q) := by
    have hpoint : ∀ i j p q : Fin n, R j p i q = R i p j q - R i j p q := by
      intro i j p q
      have h1 := hbian i p j q
      have h2 := hanti j p i q
      have h3 := hanti i j p q
      linarith
    have hstep : (∑ i, ∑ j, ∑ p, ∑ q, R i p j q * R j p i q)
        = (∑ i, ∑ j, ∑ p, ∑ q, (R i p j q * R i p j q - R i p j q * R i j p q)) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro q _
      rw [hpoint i j p q]; ring
    have hsum : (∑ i, ∑ j, ∑ p, ∑ q, (R i p j q * R i p j q - R i p j q * R i j p q))
        = (∑ i, ∑ j, ∑ p, ∑ q, R i p j q * R i p j q)
          - (∑ i, ∑ j, ∑ p, ∑ q, R i p j q * R i j p q) := by
      simp only [Finset.sum_sub_distrib]
    have hA : (∑ i, ∑ j, ∑ p, ∑ q, R i p j q * R i p j q)
        = ∑ i, ∑ j, ∑ p, ∑ q, R i j p q * R i j p q :=
      (scalQ_sum4_swap23 n (fun a b c d => R a c b d * R a c b d)).symm
    have hU : (∑ i, ∑ j, ∑ p, ∑ q, R i p j q * R i j p q)
        = ∑ i, ∑ j, ∑ p, ∑ q, R i p j q * R j p i q := by
      have h := scalQ_sum4_swap13 n (fun a b c d => R a c b d * R a b c d)
      rw [← h]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro q _
      rw [hanti i p j q, hanti j p i q]; ring
    rw [hsum, hA, hU] at hstep
    linarith
  rw [hQ, hT2, hT3]
  ring

end Work.Diff.Alg.Pinch
