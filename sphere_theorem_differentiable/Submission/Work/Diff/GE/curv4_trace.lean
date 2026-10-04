import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.GE.bianchi_kato_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Trace identities for an algebraic curvature tensor (`Work.Diff.GE.curv4_trace`)

Fix a 4-index array `R : Curv4 n` (the curvature components in an orthonormal frame) and let
`Iso n i j k l = δᵢₖ δⱼₗ - δᵢₗ δⱼₖ` be the round-sphere tensor. Writing
`S = scalAlg R = ∑ᵢⱼ R i j i j` for the scalar curvature, this file proves three identities.

* `⟪R, Iso⟫ = ∑ᵢⱼₖₗ R i j k l · Iso i j k l = 2 S`, using only antisymmetry in the first pair
  (`δ`-contracting in the last two slots and swapping the two index pairs).
* `frobSqTF R = |R - (S/(n(n-1))) Iso|²`, where `frobSqTF R = |R|² - 2 S²/(n(n-1))`. This is
  bilinear expansion of the square together with the two elementary norms
  `⟪R, Iso⟫ = 2 S` and `|Iso|² = 2 n (n-1)` (the latter is a direct `δ`-contraction:
  `|Iso|² = 2 n² - 2 n`).
* hence `0 ≤ frobSqTF R` (a sum of squares).

The computation is elementary `δ`-contraction. The two primitive contraction lemmas are
`ite_delta_mul_sum` (one index) and `delta_contract₂` / `delta_contract₂'` (two indices, both
pairings of the `δ`s), from which the four-index contractions follow.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {n : ℕ}

/-! ## Kronecker-delta contractions -/

/-- `∑ k, δᵢₖ f k = f i`, with `δ` written as `if i = k then 1 else 0`. -/
theorem ite_delta_mul_sum (i : Fin n) (f : Fin n → ℝ) :
    (∑ k, (if i = k then (1 : ℝ) else 0) * f k) = f i := by
  have h : (∑ k, (if i = k then (1 : ℝ) else 0) * f k) = ∑ k, (if i = k then f k else 0) := by
    apply Finset.sum_congr rfl; intro k _
    by_cases hk : i = k <;> simp [hk]
  rw [h, Finset.sum_ite_eq]
  simp

/-- `∑ k l, δᵢₖ δⱼₗ X k l = X i j`. -/
theorem delta_contract₂ (i j : Fin n) (X : Fin n → Fin n → ℝ) :
    (∑ k, ∑ l, (if i = k then (1 : ℝ) else 0) * ((if j = l then (1 : ℝ) else 0) * X k l))
      = X i j := by
  calc (∑ k, ∑ l, (if i = k then (1 : ℝ) else 0) * ((if j = l then (1 : ℝ) else 0) * X k l))
      = ∑ k, (if i = k then (1 : ℝ) else 0)
          * (∑ l, (if j = l then (1 : ℝ) else 0) * X k l) := by
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum]
    _ = ∑ k, (if i = k then (1 : ℝ) else 0) * X k j := by
        apply Finset.sum_congr rfl; intro k _
        rw [ite_delta_mul_sum j (fun l => X k l)]
    _ = X i j := ite_delta_mul_sum i (fun k => X k j)

/-- `∑ k l, δᵢₗ δⱼₖ X k l = X j i`. -/
theorem delta_contract₂' (i j : Fin n) (X : Fin n → Fin n → ℝ) :
    (∑ k, ∑ l, (if i = l then (1 : ℝ) else 0) * ((if j = k then (1 : ℝ) else 0) * X k l))
      = X j i := by
  calc (∑ k, ∑ l, (if i = l then (1 : ℝ) else 0) * ((if j = k then (1 : ℝ) else 0) * X k l))
      = ∑ k, (if j = k then (1 : ℝ) else 0)
          * (∑ l, (if i = l then (1 : ℝ) else 0) * X k l) := by
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro l _
        ring
    _ = ∑ k, (if j = k then (1 : ℝ) else 0) * X k i := by
        apply Finset.sum_congr rfl; intro k _
        rw [ite_delta_mul_sum i (fun l => X k l)]
    _ = X j i := ite_delta_mul_sum j (fun k => X k i)

/-- Contraction of the round-sphere tensor against a rank-one pair:
`∑ k l, Iso i j k l (A k * B l) = A i B j - A j B i`. -/
theorem iso_contract_pair (i j : Fin n) (A B : Fin n → ℝ) :
    (∑ k, ∑ l, Iso n i j k l * (A k * B l)) = A i * B j - A j * B i := by
  have hexp : ∀ k l, Iso n i j k l * (A k * B l) =
      (if i = k then (1 : ℝ) else 0) * ((if j = l then (1 : ℝ) else 0) * (A k * B l))
      - (if i = l then (1 : ℝ) else 0) * ((if j = k then (1 : ℝ) else 0) * (A k * B l)) := by
    intro k l; simp only [Iso]; ring
  have h2 : (∑ k, ∑ l, Iso n i j k l * (A k * B l))
      = ∑ k, ∑ l,
        ((if i = k then (1 : ℝ) else 0) * ((if j = l then (1 : ℝ) else 0) * (A k * B l))
        - (if i = l then (1 : ℝ) else 0) * ((if j = k then (1 : ℝ) else 0) * (A k * B l))) := by
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    exact hexp k l
  rw [h2]
  simp only [Finset.sum_sub_distrib]
  rw [delta_contract₂ i j (fun k l => A k * B l), delta_contract₂' i j (fun k l => A k * B l)]

/-! ## The trace `⟪R, Iso⟫ = 2 S` -/

/-- Pointwise contraction: `∑ k l, R i j k l Iso i j k l = R i j i j - R i j j i`. -/
theorem iso_pairing_step (R : Curv4 n) (i j : Fin n) :
    (∑ k, ∑ l, R i j k l * Iso n i j k l) = R i j i j - R i j j i := by
  have hexp : ∀ k l, R i j k l * Iso n i j k l =
      (if i = k then (1 : ℝ) else 0) * ((if j = l then (1 : ℝ) else 0) * R i j k l)
      - (if i = l then (1 : ℝ) else 0) * ((if j = k then (1 : ℝ) else 0) * R i j k l) := by
    intro k l; simp only [Iso]; ring
  have h2 : (∑ k, ∑ l, R i j k l * Iso n i j k l)
      = ∑ k, ∑ l,
        ((if i = k then (1 : ℝ) else 0) * ((if j = l then (1 : ℝ) else 0) * R i j k l)
        - (if i = l then (1 : ℝ) else 0) * ((if j = k then (1 : ℝ) else 0) * R i j k l)) := by
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    exact hexp k l
  rw [h2]
  simp only [Finset.sum_sub_distrib]
  rw [delta_contract₂ i j (fun k l => R i j k l), delta_contract₂' i j (fun k l => R i j k l)]

/-- **Trace identity.** `⟪R, Iso⟫ = 2 · scalAlg R`, for any array antisymmetric in its first pair
(in particular for an algebraic curvature tensor). -/
theorem rm_iso_trace (R : Curv4 n) (hanti : ∀ i j k l, R j i k l = - R i j k l) :
    (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * Iso n i j k l) = 2 * scalAlg R := by
  have hsum : (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * Iso n i j k l)
      = ∑ i, ∑ j, (R i j i j - R i j j i) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    exact iso_pairing_step R i j
  rw [hsum]
  have hsplit : (∑ i, ∑ j, (R i j i j - R i j j i))
      = (∑ i, ∑ j, R i j i j) - (∑ i, ∑ j, R i j j i) := by
    simp only [Finset.sum_sub_distrib]
  rw [hsplit]
  have htranspose : (∑ i, ∑ j, R i j j i) = -(∑ i, ∑ j, R i j i j) := by
    have hren : (∑ i, ∑ j, R i j j i) = ∑ i, ∑ j, R j i i j := by
      rw [Finset.sum_comm]
    rw [hren]
    have hpt : ∀ i j, R j i i j = - R i j i j := by
      intro i j
      have h := hanti j i i j
      linarith
    calc (∑ i, ∑ j, R j i i j) = ∑ i, ∑ j, (- R i j i j) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))
      _ = -(∑ i, ∑ j, R i j i j) := by simp only [Finset.sum_neg_distrib]
  rw [htranspose, scalAlg]
  ring

/-! ## The squared norm of `Iso`: `|Iso|² = 2 n (n-1)` -/

/-- `∑ k l, Iso i j k l · Iso i j k l = 2 (1 - δᵢⱼ)`. -/
theorem iso_self_sq_inner (i j : Fin n) :
    (∑ k, ∑ l, Iso n i j k l * Iso n i j k l) = 2 - 2 * (if i = j then (1 : ℝ) else 0) := by
  have hexp : ∀ k l, Iso n i j k l * Iso n i j k l =
      Iso n i j k l * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0))
      - Iso n i j k l * ((if j = k then (1 : ℝ) else 0) * (if i = l then (1 : ℝ) else 0)) := by
    intro k l; simp only [Iso]; ring
  have h2 : (∑ k, ∑ l, Iso n i j k l * Iso n i j k l)
      = ∑ k, ∑ l,
        (Iso n i j k l * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0))
        - Iso n i j k l * ((if j = k then (1 : ℝ) else 0) * (if i = l then (1 : ℝ) else 0))) := by
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    exact hexp k l
  rw [h2]
  simp only [Finset.sum_sub_distrib]
  rw [iso_contract_pair i j (fun k => (if i = k then (1 : ℝ) else 0))
        (fun l => (if j = l then (1 : ℝ) else 0)),
      iso_contract_pair i j (fun k => (if j = k then (1 : ℝ) else 0))
        (fun l => (if i = l then (1 : ℝ) else 0))]
  by_cases h : i = j
  · simp only [h, ite_true]
    norm_num
  · have h' : ¬ (j = i) := fun hh => h hh.symm
    simp only [h, h', ite_true, ite_false]
    norm_num

/-- **Norm of the round sphere tensor.** `|Iso|² = ∑ᵢⱼₖₗ Iso i j k l ² = 2 n (n-1)`. -/
theorem iso_norm_sq (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, Iso n i j k l * Iso n i j k l)
      = 2 * ((n : ℝ) * ((n : ℝ) - 1)) := by
  have h1 : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, Iso n i j k l * Iso n i j k l)
      = ∑ i : Fin n, ∑ j : Fin n, ((2 : ℝ) - 2 * (if i = j then (1 : ℝ) else 0)) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    exact iso_self_sq_inner i j
  rw [h1]
  have h2 : (∑ i : Fin n, ∑ j : Fin n, ((2 : ℝ) - 2 * (if i = j then (1 : ℝ) else 0)))
      = (∑ i : Fin n, ∑ j : Fin n, (2 : ℝ))
        - 2 * (∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0)) := by
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [h2]
  have h3 : (∑ i : Fin n, ∑ j : Fin n, (2 : ℝ)) = 2 * (n : ℝ) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have h4 : (∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0)) = (n : ℝ) := by simp
  rw [h3, h4]
  ring

/-! ## Expansion of the squared distance to the constant-curvature line -/

/-- Bilinear expansion: `|R - c Iso|² = |R|² - 2c⟪R, Iso⟫ + c²|Iso|²`. -/
theorem frobSq_sub_smul (R : Curv4 n) (c : ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, (R i j k l - c * Iso n i j k l) ^ 2)
      = frobSq R - 2 * c * (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * Iso n i j k l)
        + c ^ 2 * (∑ i, ∑ j, ∑ k, ∑ l, Iso n i j k l * Iso n i j k l) := by
  have hp : ∀ i j k l, (R i j k l - c * Iso n i j k l) ^ 2
      = R i j k l ^ 2 - 2 * c * (R i j k l * Iso n i j k l)
        + c ^ 2 * (Iso n i j k l * Iso n i j k l) := by
    intro i j k l; ring
  have h2 : (∑ i, ∑ j, ∑ k, ∑ l, (R i j k l - c * Iso n i j k l) ^ 2)
      = ∑ i, ∑ j, ∑ k, ∑ l, (R i j k l ^ 2 - 2 * c * (R i j k l * Iso n i j k l)
          + c ^ 2 * (Iso n i j k l * Iso n i j k l)) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    exact hp i j k l
  rw [h2]
  simp only [frobSq, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The elementary identity `2s²/d = 2 (s/d) (2s) - (s/d)² (2d)`, the key step in expanding
`|R - (S/(n(n-1))) Iso|²` (valid for `d = 0` too, since then both sides vanish). -/
theorem div_sq_algebra (s d : ℝ) :
    2 * s ^ 2 / d = 2 * (s / d) * (2 * s) - (s / d) ^ 2 * (2 * d) := by
  have h3 : (s / d) * s = s ^ 2 / d := by rw [div_mul_eq_mul_div]; ring
  have h4 : (s / d) ^ 2 * d = s ^ 2 / d := by
    by_cases hd : d = 0
    · simp [hd]
    · field_simp
  linear_combination (-4) * h3 + 2 * h4

/-! ## The main statement -/

/-- Trace identities for an algebraic curvature tensor `R : Curv4 n`: pairing with the round-sphere
tensor `Iso n` gives twice the scalar curvature, the "trace-free norm" `frobSqTF` is the sum of
squares of the trace-free part `R - (scalAlg R/(n(n-1))) • Iso n`, and is nonnegative.
(`Iso n i j k l = δᵢₖδⱼₗ - δᵢₗδⱼₖ` is the unit round sphere tensor, `scalAlg R = ∑ᵢⱼ R i j i j`.) -/
theorem curv4_trace {n : ℕ} (R : Curv4 n) (hR : IsAlgCurv R) :
    (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * Iso n i j k l = 2 * scalAlg R) ∧
    (frobSqTF R = ∑ i, ∑ j, ∑ k, ∑ l,
      (R i j k l - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n i j k l) ^ 2) ∧
    (0 ≤ frobSqTF R) := by
  have hpair : (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * Iso n i j k l) = 2 * scalAlg R :=
    rm_iso_trace R hR.1
  have hexpand := frobSq_sub_smul R (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1)))
  rw [hpair, iso_norm_sq n] at hexpand
  have hTF : frobSqTF R = ∑ i, ∑ j, ∑ k, ∑ l,
      (R i j k l - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n i j k l) ^ 2 := by
    rw [hexpand,
      show frobSqTF R = frobSq R - 2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) from rfl,
      div_sq_algebra (scalAlg R) ((n : ℝ) * ((n : ℝ) - 1))]
    ring
  refine ⟨hpair, hTF, ?_⟩
  rw [hTF]
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  apply Finset.sum_nonneg; intro k _
  apply Finset.sum_nonneg; intro l _
  exact sq_nonneg _

end Work.Diff.GE
