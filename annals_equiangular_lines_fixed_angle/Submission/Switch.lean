import Submission.Ramsey
import Submission.Correspondence
import Submission.MatrixFacts
import Submission.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

open EquiangularLinesFixedAngle
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

open Finset

/-! # Switching to a bounded-degree associated graph -/

/-- number of neighbours of `u` in the set `S` -/
noncomputable def degWithin {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) (S : Finset (Fin n)) : ℕ :=
  (S.filter fun w => G.Adj u w).card

/-- the set `C_X(Y)`: vertices outside `X` adjacent to every vertex of `Y ⊆ X` and to none of `X∖Y`. -/
noncomputable def Cset {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ.filter fun w => w ∉ X ∧
      (∀ u, u ∈ Y → G.Adj u w) ∧
      (∀ u, u ∈ X → u ∉ Y → ¬ G.Adj u w))

/-- X is an independent set (pairwise non-adjacent) -/
def IsIndep {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : Prop :=
  ∀ ⦃a : Fin n⦄, a ∈ X → ∀ ⦃b : Fin n⦄, b ∈ X → a ≠ b → ¬ G.Adj a b

/-- weighted inner-product cross-sum over edges (ordered pairs), the `v^T A_G v` quantity -/
noncomputable def eord {n d : ℕ} (α : ℝ) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (w : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if (assocGraph α v).Adj i j then w i * w j else 0

/-- basic flip facts -/
lemma inner_flip_eq {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) (s t : ℝ) :
    ⟪s • x, t • y⟫ = s * t * ⟪x, y⟫ := by
  rw [inner_smul_left, inner_smul_right, conj_trivial]
  ring

lemma abs_inner_flip_eq {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) (s t : ℝ)
    (hs : |s| = 1) (ht : |t| = 1) : |⟪s • x, t • y⟫| = |⟪x, y⟫| := by
  rw [inner_flip_eq, abs_mul, abs_mul, hs, ht]
  norm_num

/-- a flipped family has the same angles -/
lemma flip_family_angle (α : ℝ) {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (F : Fin n → Prop) [DecidablePred F]
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) :
    ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪(if F i then -v i else v i), (if F j then -v j else v j)⟫| = α := by
  classical
  intro i j hij
  by_cases hi : F i <;> by_cases hj : F j <;> simp [hi, hj]
  · exact hvangle hij
  · simpa [abs_neg] using hvangle hij
  · simpa [abs_neg] using hvangle hij
  · exact hvangle hij

/-- a flipped family has unit norms -/
lemma flip_family_norm {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (F : Fin n → Prop) [DecidablePred F]
    (hvnorm : ∀ i, ‖v i‖ = 1) :
    ∀ i, ‖(if F i then -v i else v i)‖ = 1 := by
  intro i
  by_cases h : F i <;> simp [h, hvnorm i]

/-- inner product is `-α` iff the pair is an edge of the associated graph (for `i ≠ j`). -/
lemma assocGraph_adj_inner_neg (α : ℝ) {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    {i j : Fin n} (h : (assocGraph α v).Adj i j) : ⟪v i, v j⟫ = -α := h.2

/-- non-adjacent pairs have inner product `+α`. -/
lemma assocGraph_notAdj_inner_pos (α : ℝ) {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α)
    {i j : Fin n} (hij : i ≠ j) (h : ¬ (assocGraph α v).Adj i j) : ⟪v i, v j⟫ = α := by
  have hval : ⟪v i, v j⟫ = α ∨ ⟪v i, v j⟫ = -α := eq_or_eq_neg_of_abs_eq (hvangle hij)
  rcases hval with hp | hn
  · exact hp
  · exfalso
    apply h
    exact ⟨hij, hn⟩

lemma inner_eq_ite (α : ℝ) {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) (i j : Fin n) :
    ⟪v i, v j⟫ = if i = j then 1 else if (assocGraph α v).Adj i j then -α else α := by
  classical
  by_cases hij : i = j
  · subst j
    rw [real_inner_self_eq_norm_sq, hvnorm i]
    norm_num
  · by_cases hadj : (assocGraph α v).Adj i j
    · rw [assocGraph_adj_inner_neg α v hadj]
      simp [hij, hadj]
    · rw [assocGraph_notAdj_inner_pos α v hvangle hij hadj]
      simp [hij, hadj]



/-! ## vector-sum and double-sum engine -/

lemma diag_count {n : ℕ} (S : Finset (Fin n)) :
    (∑ i ∈ S, ∑ j ∈ S, if i = j then (1 : ℝ) else 0) = (S.card : ℝ) := by
  have hstep : ∀ i ∈ S, (∑ j ∈ S, if i = j then (1 : ℝ) else 0) = (1 : ℝ) := by
    intro i hi
    rw [Finset.sum_ite_eq S i (fun _ => (1 : ℝ))]
    simp [hi]
  calc
    (∑ i ∈ S, ∑ j ∈ S, if i = j then (1 : ℝ) else 0) = ∑ i ∈ S, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hstep i hi
    _ = (S.card : ℝ) := by simp [Finset.sum_const]

-- (∑ if i=j then a else b) = b|S||S| + (a-b)|S|
lemma double_sum_diag_else {n : ℕ} (S : Finset (Fin n)) (a b : ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, if i = j then a else b) =
      b * (S.card : ℝ) * (S.card : ℝ) + (a - b) * (S.card : ℝ) := by
  classical
  have hrew : ∀ i ∈ S, ∀ j ∈ S,
      (if i = j then a else b) = b + (a - b) * (if i = j then (1 : ℝ) else 0) := by
    intro i hi j hj
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  calc
    (∑ i ∈ S, ∑ j ∈ S, if i = j then a else b)
        = ∑ i ∈ S, ∑ j ∈ S, (b + (a - b) * (if i = j then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hrew i hi j hj
    _ = b * (S.card : ℝ) * (S.card : ℝ) + (a - b) * (S.card : ℝ) := by
      calc
        (∑ i ∈ S, ∑ j ∈ S, (b + (a - b) * (if i = j then (1 : ℝ) else 0)))
            = ∑ i ∈ S, ((∑ j ∈ S, b) + ∑ j ∈ S, ((a - b) * (if i = j then (1 : ℝ) else 0))) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_add_distrib]
        _ = ∑ i ∈ S, ((S.card : ℝ) * b + (a - b) * (if i ∈ S then (1 : ℝ) else 0)) := by
              apply Finset.sum_congr rfl
              intro i hi
              congr 1
              · rw [Finset.sum_const]
                simp [nsmul_eq_mul]
              · rw [← Finset.mul_sum]
                rw [Finset.sum_ite_eq S i (fun _ => (1 : ℝ))]
        _ = (S.card : ℝ) * ((S.card : ℝ) * b) + (a - b) * (S.card : ℝ) := by
              have hstep2 : ∀ i ∈ S, ((S.card : ℝ) * b + (a - b) * (if i ∈ S then (1 : ℝ) else 0))
                  = (S.card : ℝ) * b + (a - b) := by
                intro i hi
                simp [hi]
              rw [show (∑ i ∈ S, ((S.card : ℝ) * b + (a - b) * (if i ∈ S then (1 : ℝ) else 0)))
                      = ∑ i ∈ S, ((S.card : ℝ) * b + (a - b)) by
                    apply Finset.sum_congr rfl
                    intro i hi
                    exact hstep2 i hi]
              simp [Finset.sum_const, nsmul_eq_mul]
              ring
        _ = b * (S.card : ℝ) * (S.card : ℝ) + (a - b) * (S.card : ℝ) := by ring

/-- inner of vector sums over finsets -/
lemma inner_vsum_vsum {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) (S T : Finset (Fin n)) :
    ⟪∑ i ∈ S, v i, ∑ j ∈ T, v j⟫ = ∑ i ∈ S, ∑ j ∈ T, ⟪v i, v j⟫ := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]

lemma norm_vsum_sq {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) (S : Finset (Fin n)) :
    ‖∑ i ∈ S, v i‖ ^ 2 = ∑ i ∈ S, ∑ j ∈ S, ⟪v i, v j⟫ := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_vsum_vsum v S S

-- role inner product over sets all with common value c
lemma vsum_inner_const {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) (S T : Finset (Fin n)) (c : ℝ)
    (h : ∀ i ∈ S, ∀ j ∈ T, ⟪v i, v j⟫ = c) :
    ⟪∑ i ∈ S, v i, ∑ j ∈ T, v j⟫ = (c : ℝ) * S.card * T.card := by
  rw [inner_vsum_vsum]
  calc
    (∑ i ∈ S, ∑ j ∈ T, ⟪v i, v j⟫) = ∑ i ∈ S, ∑ j ∈ T, c := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact h i hi j hj
    _ = (c : ℝ) * S.card * T.card := by
      rw [Finset.sum_const, Finset.sum_const]
      simp [nsmul_eq_mul]
      ring

-- upper bound for ‖Σ_S v‖² when distinct inner products are ≤ α
lemma norm_vsum_le {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) (α : ℝ) (S : Finset (Fin n))
    (hvnorm : ∀ i ∈ S, ‖v i‖ = 1)
    (hα : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪v i, v j⟫ ≤ α) :
    ‖∑ i ∈ S, v i‖ ^ 2 ≤ (S.card : ℝ) + α * (S.card : ℝ) * ((S.card : ℝ) - 1) := by
  classical
  rw [norm_vsum_sq]
  have hle : ∀ i ∈ S, ∀ j ∈ S, ⟪v i, v j⟫ ≤ (if i = j then (1 : ℝ) else α) := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      rw [real_inner_self_eq_norm_sq, hvnorm i hi]
      norm_num
    · rw [if_neg hij]
      exact hα i hi j hj hij
  have hsum : (∑ i ∈ S, ∑ j ∈ S, ⟪v i, v j⟫) ≤ ∑ i ∈ S, ∑ j ∈ S, (if i = j then (1 : ℝ) else α) := by
    exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hle i hi j hj))
  calc
    (∑ i ∈ S, ∑ j ∈ S, ⟪v i, v j⟫) ≤ ∑ i ∈ S, ∑ j ∈ S, (if i = j then (1 : ℝ) else α) := hsum
    _ = α * (S.card : ℝ) * (S.card : ℝ) + (1 - α) * (S.card : ℝ) := double_sum_diag_else S 1 α
    _ = (S.card : ℝ) + α * (S.card : ℝ) * ((S.card : ℝ) - 1) := by ring

-- within an independent set (pairwise ≠ inner = α): exact
lemma norm_vsum_indep {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) (α : ℝ) (S : Finset (Fin n))
    (hvnorm : ∀ i ∈ S, ‖v i‖ = 1)
    (hα : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪v i, v j⟫ = α) :
    ‖∑ i ∈ S, v i‖ ^ 2 = (S.card : ℝ) + α * (S.card : ℝ) * ((S.card : ℝ) - 1) := by
  classical
  rw [norm_vsum_sq]
  have hinner : ∀ i ∈ S, ∀ j ∈ S, ⟪v i, v j⟫ = (if i = j then 1 else α) := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      rw [real_inner_self_eq_norm_sq, hvnorm i hi]
      norm_num
    · simp [hij, hα i hi j hj]
  calc
    (∑ i ∈ S, ∑ j ∈ S, ⟪v i, v j⟫) = ∑ i ∈ S, ∑ j ∈ S, (if i = j then (1 : ℝ) else α) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hinner i hi j hj
    _ = α * (S.card : ℝ) * (S.card : ℝ) + (1 - α) * (S.card : ℝ) := double_sum_diag_else S 1 α
    _ = (S.card : ℝ) + α * (S.card : ℝ) * ((S.card : ℝ) - 1) := by ring

lemma norm_smul_sq {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    ‖r • x‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (r • x)]
  rw [inner_smul_left, inner_smul_right, conj_trivial]
  rw [real_inner_self_eq_norm_sq]
  ring

-- norm² of a three-term combination expands
lemma norm3_sq {d : ℕ} (A B C : EuclideanSpace ℝ (Fin d)) (x y z : ℝ) :
    ‖x • A + y • B + z • C‖ ^ 2 =
      x^2 * ‖A‖^2 + y^2 * ‖B‖^2 + z^2 * ‖C‖^2
        + 2*x*y*⟪A,B⟫ + 2*x*z*⟪A,C⟫ + 2*y*z*⟪B,C⟫ := by
  have h1 := norm_add_mul_self_real (x • A) (y • B + z • C)
  have h2 := norm_add_mul_self_real (y • B) (z • C)
  rw [add_assoc]
  rw [pow_two, h1]
  rw [show ‖y • B + z • C‖ * ‖y • B + z • C‖ = ‖y • B + z • C‖ ^ 2 by ring]
  rw [pow_two, h2]
  rw [show ‖x • A‖ * ‖x • A‖ = ‖x • A‖ ^ 2 by ring]
  rw [show ‖y • B‖ * ‖y • B‖ = ‖y • B‖ ^ 2 by ring]
  rw [show ‖z • C‖ * ‖z • C‖ = ‖z • C‖ ^ 2 by ring]
  rw [norm_smul_sq, norm_smul_sq, norm_smul_sq]
  simp only [inner_smul_left, inner_add_right, inner_smul_right, conj_trivial]
  ring



/-! ## structural facts about the associated graph and inner products -/

lemma Cset_mem {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) (w : Fin n) :
    w ∈ Cset G X Y ↔ w ∉ X ∧
      (∀ u, u ∈ Y → G.Adj u w) ∧
      (∀ u, u ∈ X → u ∉ Y → ¬ G.Adj u w) := by
  classical
  simp [Cset]

lemma Cset_not_mem_X {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) {w : Fin n}
    (hw : w ∈ Cset G X Y) : w ∉ X := (Cset_mem G X Y w).mp hw |>.1

lemma Cset_adj_Y {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) {w u : Fin n}
    (hw : w ∈ Cset G X Y) (hu : u ∈ Y) : G.Adj u w :=
  (Cset_mem G X Y w).mp hw |>.2.1 u hu

lemma Cset_notAdj_XmY {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) {w u : Fin n}
    (hw : w ∈ Cset G X Y) (hu : u ∈ X) (huY : u ∉ Y) : ¬ G.Adj u w :=
  (Cset_mem G X Y w).mp hw |>.2.2 u hu huY

/-- pairs from an independent set have inner product +α -/
lemma indep_inner_pos (α : ℝ) {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α)
    {X : Finset (Fin n)} (hX : IsIndep (assocGraph α v) X)
    {i j : Fin n} (hi : i ∈ X) (hj : j ∈ X) (hij : i ≠ j) : ⟪v i, v j⟫ = α := by
  classical
  apply assocGraph_notAdj_inner_pos α v hvangle hij
  intro hadj
  exact hX hi hj hij hadj

/-- any distinct pair has inner product ≤ α -/
lemma inner_le_alpha (α : ℝ) {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α)
    {i j : Fin n} (hij : i ≠ j) : ⟪v i, v j⟫ ≤ α := by
  have h : |⟪v i, v j⟫| = α := hvangle hij
  have hle : ⟪v i, v j⟫ ≤ |⟪v i, v j⟫| := le_abs_self _
  linarith

/-- set difference union lemma -/
lemma sdiff_union_self {α : Type*} [DecidableEq α] (X Y : Finset α) (hY : Y ⊆ X) :
    Y ∪ (X \ Y) = X := by
  ext x
  constructor
  · intro hx
    rw [mem_union] at hx
    rcases hx with hxY | hxXY
    · exact hY hxY
    · exact (mem_sdiff.mp hxXY).1
  · intro hx
    by_cases hxY : x ∈ Y
    · exact mem_union_left _ hxY
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hx, hxY⟩)


/-- The quadratic-form estimate (Pb ≥ 0) for the sets Y ⊆ X with C = C_X(Y). -/
lemma quad_b_nonneg (α : ℝ) (hα0 : 0 < α)
    {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α)
    (X Y : Finset (Fin n)) (hYsub : Y ⊆ X) (hXind : IsIndep (assocGraph α v) X) :
    ∀ (x y z : ℝ),
      0 ≤ lam α * ((Y.card : ℝ) * x^2 + ((X \ Y).card : ℝ) * y^2 + (Cset (assocGraph α v) X Y).card * z^2)
        + (1/2) * (((Y.card : ℝ) * x + ((X \ Y).card : ℝ) * y + (Cset (assocGraph α v) X Y).card * z)^2)
        - 2 * (Y.card : ℝ) * (Cset (assocGraph α v) X Y).card * x * z := by
  classical
  let G := assocGraph α v
  let p : ℝ := Y.card
  let q : ℝ := (X \ Y).card
  let r : ℝ := (Cset G X Y).card
  let Yv : EuclideanSpace ℝ (Fin d) := ∑ i ∈ Y, v i
  let Bv : EuclideanSpace ℝ (Fin d) := ∑ i ∈ X \ Y, v i
  let Cv : EuclideanSpace ℝ (Fin d) := ∑ i ∈ Cset G X Y, v i
  have hY : ‖Yv‖^2 = p + α * p * (p - 1) := by
    have h0 : ‖∑ i ∈ Y, v i‖ ^ 2 = (Y.card : ℝ) + α * (Y.card : ℝ) * ((Y.card : ℝ) - 1) :=
      norm_vsum_indep v α Y (fun i hi => hvnorm i)
        (fun i hi j hj hij => indep_inner_pos α v hvangle hXind (hYsub hi) (hYsub hj) hij)
    simpa [Yv, p] using h0
  have hB : ‖Bv‖^2 = q + α * q * (q - 1) := by
    have h0 : ‖∑ i ∈ X \ Y, v i‖ ^ 2 = ((X \ Y).card : ℝ) + α * ((X \ Y).card : ℝ) * (((X \ Y).card : ℝ) - 1) :=
      norm_vsum_indep v α (X \ Y) (fun i hi => hvnorm i)
        (fun i hi j hj hij => indep_inner_pos α v hvangle hXind (mem_sdiff.mp hi).1 (mem_sdiff.mp hj).1 hij)
    simpa [Bv, q] using h0
  have hC : ‖Cv‖^2 ≤ r + α * r * (r - 1) := by
    have h0 : ‖∑ i ∈ Cset G X Y, v i‖ ^ 2 ≤ (Cset G X Y).card + α * (Cset G X Y).card * ((Cset G X Y).card - 1) :=
      norm_vsum_le v α (Cset G X Y) (fun i hi => hvnorm i) (fun i hi j hj hij => inner_le_alpha α v hvangle hij)
    simpa [Cv, r] using h0
  have hYB : ⟪Yv, Bv⟫ = α * p * q := by
    have h0 : ⟪∑ i ∈ Y, v i, ∑ j ∈ X \ Y, v j⟫ = α * (Y.card : ℝ) * ((X \ Y).card : ℝ) :=
      vsum_inner_const v Y (X \ Y) α (fun i hi j hj => by
        have hjX : j ∈ X := (mem_sdiff.mp hj).1
        have hjY : j ∉ Y := (mem_sdiff.mp hj).2
        have hij : i ≠ j := by
          intro hij'
          subst j
          exact hjY hi
        exact indep_inner_pos α v hvangle hXind (hYsub hi) hjX hij)
    simpa [Yv, Bv, p, q] using h0
  have hYC : ⟪Yv, Cv⟫ = -α * p * r := by
    have h0 : ⟪∑ i ∈ Y, v i, ∑ j ∈ Cset G X Y, v j⟫ = -α * (Y.card : ℝ) * (Cset G X Y).card :=
      vsum_inner_const v Y (Cset G X Y) (-α) (fun i hi c hc => by
        exact assocGraph_adj_inner_neg α v (Cset_adj_Y G X Y hc hi))
    simpa [Yv, Cv, p, r] using h0
  have hBC : ⟪Bv, Cv⟫ = α * q * r := by
    have h0 : ⟪∑ i ∈ X \ Y, v i, ∑ j ∈ Cset G X Y, v j⟫ = α * ((X \ Y).card : ℝ) * (Cset G X Y).card :=
      vsum_inner_const v (X \ Y) (Cset G X Y) α (fun b hb c hc => by
        have hnon : ¬ G.Adj b c := by
          intro hadj
          exact Cset_notAdj_XmY G X Y hc (mem_sdiff.mp hb).1 (mem_sdiff.mp hb).2 (by simpa [G.adj_comm] using hadj)
        exact assocGraph_notAdj_inner_pos α v hvangle (by
          intro hbc'
          subst c
          exact (Cset_not_mem_X G X Y hc) (mem_sdiff.mp hb).1) hnon)
    simpa [Bv, Cv, q, r] using h0
  intro x y z
  have hW0 : 0 ≤ ‖x • Yv + y • Bv + z • Cv‖ ^ 2 := sq_nonneg _
  have hExp := norm3_sq Yv Bv Cv x y z
  have hzsq : 0 ≤ z^2 := sq_nonneg z
  have hz2 : z^2 * ‖Cv‖^2 ≤ z^2 * (r + α * r * (r - 1)) := mul_le_mul_of_nonneg_left hC hzsq
  have hWle : ‖x • Yv + y • Bv + z • Cv‖ ^ 2 ≤
      x^2 * (p + α * p * (p - 1)) + y^2 * (q + α * q * (q - 1)) + z^2 * (r + α * r * (r - 1))
        + 2*x*y*(α * p * q) + 2*x*z*(-α * p * r) + 2*y*z*(α * q * r) := by
    rw [hExp, hYB, hYC, hBC]
    rw [hY, hB]
    nlinarith [hz2]
  have hPge : 0 ≤
      x^2 * (p + α * p * (p - 1)) + y^2 * (q + α * q * (q - 1)) + z^2 * (r + α * r * (r - 1))
        + 2*x*y*(α * p * q) + 2*x*z*(-α * p * r) + 2*y*z*(α * q * r) := by
    linarith [hWle, hW0]
  have hlam : 2 * α * lam α = 1 - α := two_mul_lam (ne_of_gt hα0)
  have hT : (2 * α) * (lam α * (p * x^2 + q * y^2 + r * z^2)
        + (1/2) * (p * x + q * y + r * z)^2 - 2 * p * r * x * z)
      = x^2 * (p + α * p * (p - 1)) + y^2 * (q + α * q * (q - 1)) + z^2 * (r + α * r * (r - 1))
        + 2*x*y*(α * p * q) + 2*x*z*(-α * p * r) + 2*y*z*(α * q * r) := by
    calc
      (2 * α) * (lam α * (p * x^2 + q * y^2 + r * z^2)
            + (1/2) * (p * x + q * y + r * z)^2 - 2 * p * r * x * z)
          = (2 * α * lam α) * (p * x^2 + q * y^2 + r * z^2) + α * (p*x + q*y + r*z)^2
            - 4 * α * p * r * x * z := by ring
      _ = (1 - α) * (p * x^2 + q * y^2 + r * z^2) + α * (p*x + q*y + r*z)^2
            - 4 * α * p * r * x * z := by rw [hlam]
      _ = x^2 * (p + α * p * (p - 1)) + y^2 * (q + α * q * (q - 1)) + z^2 * (r + α * r * (r - 1))
            + 2*x*y*(α * p * q) + 2*x*z*(-α * p * r) + 2*y*z*(α * q * r) := by ring
  have h2a : 0 < 2 * α := by positivity
  have hTm : 0 ≤ (2 * α) * (lam α * (p * x^2 + q * y^2 + r * z^2)
        + (1/2) * (p * x + q * y + r * z)^2 - 2 * p * r * x * z) := by
    rw [hT]
    exact hPge
  have hTge : 0 ≤ lam α * (p * x^2 + q * y^2 + r * z^2)
        + (1/2) * (p * x + q * y + r * z)^2 - 2 * p * r * x * z :=
    (mul_nonneg_iff_of_pos_left h2a).mp hTm
  simpa [p, q, r] using hTge


/-- discriminant bound for quadratics everywhere nonnegative -/
lemma discr_of_quad (A B C : ℝ) (hA : 0 < A)
    (h : ∀ t : ℝ, A * t^2 + B * t + C ≥ 0) : B^2 ≤ 4 * A * C := by
  have ht : A * (-B / (2 * A))^2 + B * (-B / (2 * A)) + C ≥ 0 := h (-B / (2 * A))
  have hA2 : 2 * A ≠ 0 := by positivity
  have hneq : A * (-B / (2 * A))^2 + B * (-B / (2 * A)) + C = C - B^2 / (4 * A) := by
    field_simp [hA2]
    ring
  rw [hneq] at ht
  have hpos4 : 0 < 4 * A := by positivity
  have hmul : 0 ≤ (4 * A) * (C - B^2 / (4 * A)) := mul_nonneg (le_of_lt hpos4) ht
  have hc : (4 * A) * (C - B^2 / (4 * A)) = 4*A*C - B^2 := by
    field_simp [hA.ne']
  rw [hc] at hmul
  linarith

/-- from the (b)-quadratic form bound (≥ 0 for all x,y,z) derive the cleared star inequality -/
lemma quad_to_cleared_star (p q r l : ℝ) (hl : 0 < l) (hq : 0 < q)
    (h : ∀ x y z : ℝ, 0 ≤ l * (p*x^2 + q*y^2 + r*z^2) + (1/2)*(p*x + q*y + r*z)^2 - 2*p*r*x*z) :
    ∀ x z : ℝ, 0 ≤ (q + 2*l) * (l*p*x^2 + l*r*z^2 - 2*p*r*x*z) + l*(p*x + r*z)^2 := by
  intro x z
  let Cv : ℝ := l * (p*x^2 + r*z^2) - 2*p*r*x*z + (1/2) * (p*x + r*z)^2
  have hA : 0 < l * q + q^2 / 2 := by positivity
  have hq2 : ∀ y : ℝ,
      0 ≤ (l * q + q^2 / 2) * y^2 + (q * (p*x + r*z)) * y + Cv := by
    intro y
    have hy := h x y z
    have hrew : l * (p*x^2 + q*y^2 + r*z^2) + (1/2)*(p*x + q*y + r*z)^2 - 2*p*r*x*z
        = (l * q + q^2 / 2) * y^2 + (q * (p*x + r*z)) * y + Cv := by
      dsimp [Cv]
      ring
    rw [hrew] at hy
    exact hy
  have hd := discr_of_quad (l * q + q^2 / 2) (q * (p*x + r*z)) Cv hA hq2
  have hdiff : 0 ≤ 4 * (l * q + q^2 / 2) * Cv - (q * (p*x + r*z))^2 := by linarith
  have hident : 4 * (l * q + q^2 / 2) * Cv - (q * (p*x + r*z))^2
      = 2*q*((q + 2*l) * (l*p*x^2 + l*r*z^2 - 2*p*r*x*z) + l*(p*x + r*z)^2) := by
    dsimp [Cv]
    ring
  rw [hident] at hdiff
  have h2q : 0 < 2 * q := by positivity
  exact (mul_nonneg_iff_of_pos_left h2q).mp hdiff

/-- the determinant inequality obtained from the cleared star inequality -/
lemma det_bound (p q r l : ℝ) (hl : 0 < l) (hp : 0 < p) (hr : 0 < r) (hq0 : 0 ≤ q)
    (h : ∀ x z : ℝ, 0 ≤ (q + 2*l) * (l*p*x^2 + l*r*z^2 - 2*p*r*x*z) + l*(p*x + r*z)^2) :
    p * r * (q + l)^2 ≤ l^2 * (p + q + 2*l) * (q + r + 2*l) := by
  have hq2lr : 0 < q + 2*l + r := by nlinarith [hl, hq0, hr]
  have hpoly : ∀ t : ℝ,
      0 ≤ (l * r * (q + 2*l + r)) * t^2 + (-2 * p * r * (q + l)) * t + (l * p * (p + q + 2*l)) := by
    intro t
    have ht := h 1 t
    have hrew : (q + 2*l) * (l*p*1^2 + l*r*t^2 - 2*p*r*1*t) + l*(p*1 + r*t)^2
        = (l * r * (q + 2*l + r)) * t^2 + (-2 * p * r * (q + l)) * t + (l * p * (p + q + 2*l)) := by
      ring
    rw [hrew] at ht
    exact ht
  have hA : 0 < l * r * (q + 2*l + r) := by
    exact mul_pos (mul_pos hl hr) hq2lr
  have hd := discr_of_quad (l * r * (q + 2*l + r)) (-2 * p * r * (q + l)) (l * p * (p + q + 2*l)) hA hpoly
  have hd4 : 4 * p^2 * r^2 * (q + l)^2 ≤ 4 * l^2 * p * r * (p + q + 2*l) * (q + 2*l + r) := by nlinarith [hd]
  have hpr4 : 0 < 4 * p * r := by
    exact mul_pos (by nlinarith [hp]) hr
  have hgoal4 : 4 * p * r * (p * r * (q + l)^2) ≤ 4 * p * r * (l^2 * (p + q + 2*l) * (q + r + 2*l)) := by
    nlinarith [hd4]
  exact (mul_le_mul_iff_of_pos_left hpr4).mp hgoal4

/-- the final cardinal bound: |C| ≤ 4 λ² -/
lemma r_bound_of_det (p q r l : ℝ) (hl : 0 < l)
    (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) (hr0 : 0 ≤ r)
    (hM : (2 * l^2 + 2) ≤ p + q)
    (hd : p * r * (q + l)^2 ≤ l^2 * (p + q + 2*l) * (q + r + 2*l)) :
    r ≤ 4 * l^2 := by
  have hstep1 : r * (p * q - l^2) ≤ l^2 * (p + q + 2*l) := by
    have hd' : r * (p * (q + l)^2 - l^2 * (p + q + 2*l)) ≤ l^2 * (p + q + 2*l) * (q + 2*l) := by
      nlinarith [hd]
    nlinarith [hd']
  have hpq : p * q ≥ p + q - 1 := by nlinarith [sq_nonneg (p - 1), sq_nonneg (q - 1)]
  have hs2 : p + q - 1 - l^2 ≥ (p + q) / 2 := by nlinarith [hM]
  have hs : 0 < p + q := by nlinarith [hM, hl]
  have hs2l : 2 * l ≤ p + q := by
    nlinarith [sq_nonneg (l - 1/2), hM]
  have hstep2 : r * (p + q) ≤ 2 * l^2 * (p + q) + 4 * l^3 := by
    have hmid : r * ((p + q) / 2) ≤ l^2 * (p + q + 2*l) := by
      have hle : r * (p * q - l^2) ≥ r * ((p + q) - 1 - l^2) := by
        nlinarith [hr0, hpq]
      have hle2 : r * ((p + q) - 1 - l^2) ≥ r * ((p + q) / 2) := by
        nlinarith [hr0, hs2]
      nlinarith [hstep1, hle, hle2]
    nlinarith
  have hstep3 : r * (p + q) ≤ 4 * l^2 * (p + q) := by
    nlinarith [hstep2, hs2l]
  have hmul : (p + q) * r ≤ (p + q) * (4 * l^2) := by nlinarith [hstep3]
  exact (mul_le_mul_iff_of_pos_left hs).mp hmul


/-- Proposition (independent) (b): for an independent set X with |X| ≥ M1 and any nonempty
proper subset Y of X, |C_X(Y)| is bounded by M2 (constants depend only on α). -/
lemma prop_b (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (M1 : ℕ)
    (hM1 : (2 * lam α^2 + 2 : ℝ) ≤ (M1 : ℝ)) :
    ∃ M2 : ℕ, 0 < M2 ∧
      ∀ {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)),
        (∀ i, ‖v i‖ = 1) →
        (∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) →
        ∀ (X : Finset (Fin n)), IsIndep (assocGraph α v) X → M1 ≤ X.card →
        ∀ (Y : Finset (Fin n)), Y ⊆ X → 0 < Y.card → Y.card < X.card →
          (Cset (assocGraph α v) X Y).card ≤
            Nat.ceil (4 * lam α^2) + 1 := by
  classical
  let l : ℝ := lam α
  have hl : 0 < l := lam_pos hα0 hα1
  refine ⟨Nat.ceil (4 * l^2) + 1, by positivity, ?_⟩
  intro n d v hvnorm hvangle X hXind hXcard Y hYsub hYpos hYprop
  let G := assocGraph α v
  let C := Cset G X Y
  let p : ℝ := Y.card
  let q : ℝ := (X \ Y).card
  let r : ℝ := C.card
  have hp1 : 1 ≤ p := by
    dsimp [p]
    exact_mod_cast Nat.succ_le_of_lt hYpos
  have hq1n : 1 ≤ (X \ Y).card := by
    have hcd : (X \ Y).card = X.card - Y.card := by
      rw [Finset.card_sdiff]
      have hint : Y ∩ X = Y := by simp [hYsub]
      rw [hint]
    rw [hcd]
    exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt hYprop)
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast hq1n
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hYdisjX : Disjoint Y (X \ Y) := by
    rw [disjoint_left]
    intro a haY haXY
    exact (mem_sdiff.mp haXY).2 haY
  have hXeqNat : Y.card + (X \ Y).card = X.card := by
    rw [← Finset.card_union_of_disjoint hYdisjX]
    congr 1
    exact sdiff_union_self X Y hYsub
  have hXeq : p + q = (X.card : ℝ) := by
    dsimp [p, q]
    exact_mod_cast hXeqNat
  have hM : (2 * l^2 + 2) ≤ p + q := by
    have h1 : (2 * l^2 + 2 : ℝ) ≤ (M1 : ℝ) := hM1
    have h2 : (M1 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hXcard
    rw [hXeq]
    linarith
  have hquad := quad_b_nonneg α hα0 v hvnorm hvangle X Y hYsub hXind
  have hquad' : ∀ x y z : ℝ, 0 ≤ l * (p * x^2 + q * y^2 + r * z^2)
      + (1/2) * (p * x + q * y + r * z)^2 - 2 * p * r * x * z := by
    intro x y z
    have hq := hquad x y z
    simpa [l, p, q, r, C] using hq
  have hstar := quad_to_cleared_star p q r l hl (by linarith [hq1]) hquad'
  by_cases hCempty : C.card = 0
  · have hC0 : (Cset G X Y).card = 0 := by simpa [C] using hCempty
    rw [hC0]
    omega
  · have hCpos : 0 < C.card := Nat.pos_of_ne_zero hCempty
    have hrpos : 0 < r := by dsimp [r]; exact_mod_cast hCpos
    have hdet := det_bound p q r l hl (by linarith [hp1]) hrpos (by linarith [hq1]) hstar
    have hbnd := r_bound_of_det p q r l hl (by linarith [hp1]) (by linarith [hq1]) hr0 hM hdet
    have hceil : (4 * l^2) ≤ (Nat.ceil (4 * l^2) : ℝ) := Nat.le_ceil (4 * l^2)
    have hbndR : (C.card : ℝ) ≤ (Nat.ceil (4 * l^2) : ℝ) := by
      have h1 := hbnd
      dsimp [r] at h1
      linarith [h1, hceil]
    have hstep : (C.card : ℝ) ≤ (Nat.ceil (4 * l^2) : ℝ) + 1 := by
      linarith [hbndR]
    have hfin : C.card ≤ Nat.ceil (4 * l^2) + 1 := by
      exact_mod_cast hstep
    change (Cset (assocGraph α v) X Y).card ≤ Nat.ceil (4 * lam α^2) + 1
    simpa [C, l] using hfin

/-- geometric core of the star estimate. With a star of D leaves `L` around `u`, all of {u}∪L
non-adjacent to the independent set X, the geometry forces for all weights t,s:
`0 ≤ l·(t² + D s² + (t+Ds)²/|X|) − 2Dts`. -/
lemma star_core (α : ℝ) (hα0 : 0 < α)
    {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α)
    (D : ℕ) (hDpos : 0 < D)
    (X L : Finset (Fin n)) (u : Fin n)
    (hXind : IsIndep (assocGraph α v) X)
    (huX : u ∉ X)
    (hLX : ∀ ℓ ∈ L, ℓ ∉ X)
    (hLstar : ∀ ℓ ∈ L, (assocGraph α v).Adj u ℓ)
    (hXstar : ∀ x ∈ X, ¬ (assocGraph α v).Adj u x)
    (hLXstar : ∀ ℓ ∈ L, ∀ x ∈ X, ¬ (assocGraph α v).Adj ℓ x)
    (hLcard : L.card = D) (hXne : (X.card : ℝ) ≠ 0) :
    ∀ (t s : ℝ),
      0 ≤ lam α * (t^2 + (D : ℝ) * s^2 + (t + (D : ℝ)*s)^2 / (X.card : ℝ))
        - 2 * (D : ℝ) * t * s := by
  classical
  let G := assocGraph α v
  let aR : ℝ := X.card
  let Uv : EuclideanSpace ℝ (Fin d) := v u
  let Lv : EuclideanSpace ℝ (Fin d) := ∑ ℓ ∈ L, v ℓ
  let Xv : EuclideanSpace ℝ (Fin d) := ∑ x ∈ X, v x
  have hAne : aR ≠ 0 := by simpa [aR] using hXne
  intro t s
  let w0 : ℝ := -(t + (D : ℝ) * s) / aR
  have hXsq : ‖Xv‖^2 = aR + α * aR * (aR - 1) := by
    dsimp [Xv, aR]
    have h0 : ‖∑ i ∈ X, v i‖ ^ 2 = (X.card : ℝ) + α * (X.card : ℝ) * ((X.card : ℝ) - 1) :=
      norm_vsum_indep v α X (fun i hi => hvnorm i)
        (fun i hi j hj hij => indep_inner_pos α v hvangle hXind hi hj hij)
    simpa using h0
  have hLle : ‖Lv‖^2 ≤ (D : ℝ) + α * (D : ℝ) * ((D : ℝ) - 1) := by
    dsimp [Lv]
    have h0 : ‖∑ ℓ ∈ L, v ℓ‖ ^ 2 ≤ (L.card : ℝ) + α * (L.card : ℝ) * ((L.card : ℝ) - 1) :=
      norm_vsum_le v α L (fun ℓ hℓ => hvnorm ℓ) (fun ℓ hℓ ℓ' hℓ' hne => inner_le_alpha α v hvangle hne)
    rw [hLcard] at h0
    simpa using h0
  have hU : ‖Uv‖^2 = 1 := by
    dsimp [Uv]
    have h := hvnorm u
    nlinarith
  have hUL : ⟪Uv, Lv⟫ = -α * (D : ℝ) := by
    dsimp [Uv, Lv]
    have h0 : ⟪v u, ∑ ℓ ∈ L, v ℓ⟫ = -α * (L.card : ℝ) := by
      rw [inner_sum]
      calc
        (∑ ℓ ∈ L, ⟪v u, v ℓ⟫) = ∑ ℓ ∈ L, -α := by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          exact assocGraph_adj_inner_neg α v (hLstar ℓ hℓ)
        _ = -α * (L.card : ℝ) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
          ring
    rw [hLcard] at h0
    simpa using h0
  have hUX : ⟪Uv, Xv⟫ = α * aR := by
    dsimp [Uv, Xv, aR]
    have h0 : ⟪v u, ∑ x ∈ X, v x⟫ = α * (X.card : ℝ) := by
      rw [inner_sum]
      calc
        (∑ x ∈ X, ⟪v u, v x⟫) = ∑ x ∈ X, α := by
          apply Finset.sum_congr rfl
          intro x hx
          apply assocGraph_notAdj_inner_pos α v hvangle
          · intro hxu
            subst u
            exact huX hx
          · exact hXstar x hx
        _ = α * (X.card : ℝ) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
          ring
    simpa using h0
  have hLX : ⟪Lv, Xv⟫ = α * (D : ℝ) * aR := by
    dsimp [Lv, Xv, aR]
    have h0 : ⟪∑ ℓ ∈ L, v ℓ, ∑ x ∈ X, v x⟫ = α * (L.card : ℝ) * (X.card : ℝ) :=
      vsum_inner_const v L X α (fun ℓ hℓ x hx => by
        apply assocGraph_notAdj_inner_pos α v hvangle
        · intro hℓx
          subst x
          exact hLX ℓ hℓ hx
        · exact hLXstar ℓ hℓ x hx)
    rw [hLcard] at h0
    simpa using h0
  -- W := t•Uv + s•Lv + w0•Xv
  have hW0 : 0 ≤ ‖t • Uv + s • Lv + w0 • Xv‖ ^ 2 := sq_nonneg _
  have hExp := norm3_sq Uv Lv Xv t s w0
  have hWle : ‖t • Uv + s • Lv + w0 • Xv‖ ^ 2 ≤
      t^2 + s^2 * ((D : ℝ) + α * (D : ℝ) * ((D : ℝ) - 1))
        + w0^2 * (aR + α * aR * (aR - 1))
        + 2*t*s*(-α * (D : ℝ)) + 2*t*w0*(α * aR) + 2*s*w0*(α * (D : ℝ) * aR) := by
    rw [hExp, hUL, hUX, hLX, hU, hXsq]
    -- s²‖Lv‖² ≤ s²·UB, w0²‖Xv‖² exact, others exact
    have hsq1 : s^2 * ‖Lv‖^2 ≤ s^2 * ((D : ℝ) + α * (D : ℝ) * ((D : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hLle (sq_nonneg s)
    nlinarith [hsq1]
  -- poly ≥ 0 and total weight zero, giving (1-α)S1 - 4αDts ≥ 0 where S1 := t²+Ds²+aR w0²
  have htot : t + (D : ℝ) * s + aR * w0 = 0 := by
    dsimp [w0]
    field_simp [hAne]
    ring
  have hPge : 0 ≤ (1 - α) * (t^2 + (D : ℝ) * s^2 + aR * w0^2) - 4 * α * (D : ℝ) * t * s := by
    have hpoly : (t^2 + s^2 * ((D : ℝ) + α * (D : ℝ) * ((D : ℝ) - 1))
          + w0^2 * (aR + α * aR * (aR - 1))
          + 2*t*s*(-α * (D : ℝ)) + 2*t*w0*(α * aR) + 2*s*w0*(α * (D : ℝ) * aR))
        = (1 - α) * (t^2 + (D : ℝ) * s^2 + aR * w0^2) - 4 * α * (D : ℝ) * t * s := by
          have hdiff : (t^2 + s^2 * ((D : ℝ) + α * (D : ℝ) * ((D : ℝ) - 1))
                + w0^2 * (aR + α * aR * (aR - 1))
                + 2*t*s*(-α * (D : ℝ)) + 2*t*w0*(α * aR) + 2*s*w0*(α * (D : ℝ) * aR))
              = (1 - α) * (t^2 + (D : ℝ) * s^2 + aR * w0^2) - 4 * α * (D : ℝ) * t * s
                + α * (t + (D : ℝ) * s + aR * w0)^2 := by ring
          rw [hdiff]
          rw [htot]
          ring
    have h1 : 0 ≤ (t^2 + s^2 * ((D : ℝ) + α * (D : ℝ) * ((D : ℝ) - 1))
          + w0^2 * (aR + α * aR * (aR - 1))
          + 2*t*s*(-α * (D : ℝ)) + 2*t*w0*(α * aR) + 2*s*w0*(α * (D : ℝ) * aR)) := by
      linarith [hWle, hW0]
    rw [hpoly] at h1
    exact h1
  -- substitute w0's value: aR w0 = -(t+Ds)
  have hRaw : aR * w0 = -(t + (D : ℝ) * s) := by
    dsimp [w0]
    field_simp [hAne]
  have hS1 : aR * w0^2 = (t + (D : ℝ) * s)^2 / aR := by
    have htmp : aR * w0^2 = (aR * w0)^2 / aR := by
      field_simp [hAne]
    calc
      aR * w0^2 = (aR * w0)^2 / aR := htmp
      _ = (t + (D : ℝ) * s)^2 / aR := by
        rw [hRaw]
        ring
  -- target: 0 ≤ l·(t²+Ds²+(t+Ds)²/aR) − 2Dts
  have hlam : 2 * α * lam α = 1 - α := two_mul_lam (ne_of_gt hα0)
  have hfin : 0 ≤ lam α * (t^2 + (D : ℝ) * s^2 + (t + (D : ℝ)*s)^2 / aR)
        - 2 * (D : ℝ) * t * s := by
    have h2 : 0 ≤ (2 * α) * (lam α * (t^2 + (D : ℝ) * s^2 + (t + (D : ℝ)*s)^2 / aR)
        - 2 * (D : ℝ) * t * s) := by
      -- (2α)·target = (1-α)S1 - 4αDts (via hS1)
      have hEq : (2 * α) * (lam α * (t^2 + (D : ℝ) * s^2 + (t + (D : ℝ)*s)^2 / aR)
            - 2 * (D : ℝ) * t * s)
          = (1 - α) * (t^2 + (D : ℝ) * s^2 + aR * w0^2) - 4 * α * (D : ℝ) * t * s := by
            rw [hS1]
            rw [← hlam]
            ring
      rw [hEq]
      exact hPge
    have h2a : 0 < 2 * α := by positivity
    exact (mul_nonneg_iff_of_pos_left h2a).mp h2
  -- unfold aR
  simpa [aR] using hfin


/-- number of neighbours of `u` inside `C_X(∅)` -/
noncomputable def nbrCX {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (u : Fin n) : ℕ := by
  classical
  exact ((Cset G X ∅).filter (fun w => G.Adj u w)).card

/-- the numeric contradiction behind part (a): for the weight t=D, s=l the bound of
`star_core` would be strictly negative when |X| is large. -/
lemma star_neg (l : ℝ) (D aR : ℝ) (hl : 0 < l) (ha : 0 < aR) (hD : 0 < D)
    (hD1 : 1 ≤ D - l^2) (hbig : D * (1 + l)^2 < aR) :
    l * (D^2 + D * l^2 + (D + D * l)^2 / aR) - 2 * D * D * l < 0 := by
  have hge : aR * (D - l^2) ≥ aR := by
    have hmul : aR * 1 ≤ aR * (D - l^2) := mul_le_mul_of_nonneg_left hD1 (le_of_lt ha)
    simpa using hmul
  have hlt : aR * (D - l^2) > D * (1 + l)^2 := by linarith
  have hEc : aR * (l * (D^2 + D * l^2 + (D + D * l)^2 / aR) - 2 * D * D * l)
      = l * D * (D * (1 + l)^2 - aR * (D - l^2)) := by
    field_simp [ne_of_gt ha]
    ring
  have hEcneg : aR * (l * (D^2 + D * l^2 + (D + D * l)^2 / aR) - 2 * D * D * l) < 0 := by
    rw [hEc]
    have h1 : D * (1 + l)^2 - aR * (D - l^2) < 0 := by linarith
    exact mul_neg_of_pos_of_neg (mul_pos hl hD) h1
  by_contra hE
  have hEge : 0 ≤ l * (D^2 + D * l^2 + (D + D * l)^2 / aR) - 2 * D * D * l := le_of_not_gt hE
  have hprod : 0 ≤ aR * (l * (D^2 + D * l^2 + (D + D * l)^2 / aR) - 2 * D * D * l) :=
    mul_nonneg (le_of_lt ha) hEge
  linarith

/-- Proposition (independent) (a): with `D = ⌈λ²⌉+1` (satisfying 1 ≤ D−λ²) and an `M1` with
`M1 > D(1+λ)²`, any vertex u ∉ X non-adjacent to an independent set X of size ≥ M1 has fewer
than D neighbours inside C_X(∅). -/
lemma prop_a (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (D M1 : ℕ)
    (hDpos : 0 < D) (hD1 : 1 ≤ (D : ℝ) - lam α ^ 2)
    (hM1rel : (D : ℝ) * (1 + lam α)^2 < (M1 : ℝ)) :
    ∀ {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖v i‖ = 1) →
      (∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) →
      ∀ (X : Finset (Fin n)), IsIndep (assocGraph α v) X → M1 ≤ X.card →
      ∀ (u : Fin n), u ∉ X → (∀ x ∈ X, ¬ (assocGraph α v).Adj u x) →
        nbrCX (assocGraph α v) X u < D := by
  classical
  let l : ℝ := lam α
  have hl : 0 < l := lam_pos hα0 hα1
  have hDposR : 0 < (D : ℝ) := by exact_mod_cast hDpos
  intro n d v hvnorm hvangle X hXind hXcard u huX hNX
  let G := assocGraph α v
  by_contra hc
  have hc' : D ≤ nbrCX G X u := Nat.le_of_not_gt hc
  have hcF : D ≤ ((Cset G X ∅).filter (fun w => G.Adj u w)).card := by
    simpa [nbrCX, G] using hc'
  have hXpos : 0 < X.card := by
    have hM1ge : 1 ≤ M1 := by
      by_contra h
      have hM1z : M1 = 0 := by omega
      rw [hM1z] at hM1rel
      have hDge : 0 < (D : ℝ) * (1 + lam α)^2 := by
        have hDp : 0 < (D : ℝ) := by exact_mod_cast hDpos
        have h1l : 0 < 1 + lam α := by linarith
        exact mul_pos hDp (sq_pos_of_pos h1l)
      have hM1rel' : (D : ℝ) * (1 + lam α)^2 < (0 : ℝ) := by simpa using hM1rel
      exact (lt_asymm hDge hM1rel')
    omega
  have hXne : (X.card : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hXpos)
  rcases (Finset.exists_subset_card_eq (s := ((Cset G X ∅).filter (fun w => G.Adj u w))) hcF) with ⟨L, hLsub, hLcard⟩
  have hLc : ∀ ℓ ∈ L, ℓ ∈ ((Cset G X ∅).filter (fun w => G.Adj u w)) := fun ℓ hℓ => hLsub hℓ
  have hLX : ∀ ℓ ∈ L, ℓ ∉ X := fun ℓ hℓ => (Cset_mem G X ∅ ℓ).mp (mem_filter.mp (hLc ℓ hℓ)).1 |>.1
  have hLstar : ∀ ℓ ∈ L, G.Adj u ℓ := fun ℓ hℓ => (mem_filter.mp (hLc ℓ hℓ)).2
  have hLXstar : ∀ ℓ ∈ L, ∀ x ∈ X, ¬ G.Adj ℓ x := by
    intro ℓ hℓ x hx
    intro hadj
    have hnon := (Cset_mem G X ∅ ℓ).mp (mem_filter.mp (hLc ℓ hℓ)).1 |>.2.2 x hx (by simp)
    exact hnon (by simpa [G.adj_comm] using hadj)
  have hb := star_core α hα0 v hvnorm hvangle D hDpos X L u hXind huX hLX hLstar hNX hLXstar hLcard hXne
    (D : ℝ) l
  have hb' : 0 ≤ l * ((D : ℝ)^2 + (D : ℝ) * l^2 + ((D : ℝ) + (D : ℝ)*l)^2 / (X.card : ℝ))
      - 2 * (D : ℝ) * (D : ℝ) * l := by
    simpa [l] using hb
  have hbig : (D : ℝ) * (1 + l)^2 < (X.card : ℝ) := by
    have h1 : (D : ℝ) * (1 + l)^2 < (M1 : ℝ) := by
      dsimp [l]
      exact hM1rel
    have h2 : (M1 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hXcard
    linarith
  have hneg := star_neg l (D : ℝ) (X.card : ℝ) hl (by exact_mod_cast hXpos) hDposR
    (by dsimp [l]; exact hD1) hbig
  have hneg' : l * ((D : ℝ)^2 + (D : ℝ) * l^2 + ((D : ℝ) + (D : ℝ)*l)^2 / (X.card : ℝ))
      - 2 * (D : ℝ) * (D : ℝ) * l < 0 := by
    simpa using hneg
  linarith

lemma no_clique_M0 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) :
    ¬ ∃ s : Finset (Fin n), Nat.ceil (α⁻¹) + 2 ≤ s.card ∧
        ∀ ⦃a : Fin n⦄, a ∈ s → ∀ ⦃b : Fin n⦄, b ∈ s → a ≠ b → (assocGraph α v).Adj a b := by
  classical
  rintro ⟨s, hcard, hcl⟩
  let m : ℕ := Nat.ceil (α⁻¹) + 2
  rcases (Finset.exists_subset_card_eq (s := s) (n := m) (by dsimp [m]; omega)) with ⟨t, htsub, htcard⟩
  have hclt : ∀ ⦃a : Fin n⦄, a ∈ t → ∀ ⦃b : Fin n⦄, b ∈ t → a ≠ b → (assocGraph α v).Adj a b := by
    intro a ha b hb hab
    exact hcl (htsub ha) (htsub hb) hab
  have hmpos : 0 < m := by dsimp [m]; omega
  have hmposR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hgram : 0 ≤ ‖∑ i ∈ t, v i‖ ^ 2 := sq_nonneg _
  have hinner : ∀ i ∈ t, ∀ j ∈ t, ⟪v i, v j⟫ = (if i = j then (1 : ℝ) else -α) := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      rw [real_inner_self_eq_norm_sq, hvnorm i]
      norm_num
    · have hadj : (assocGraph α v).Adj i j := hclt hi hj hij
      rw [assocGraph_adj_inner_neg α v hadj]
      simp [hij]
  have hsq : ‖∑ i ∈ t, v i‖ ^ 2 = (m : ℝ) - α * (m : ℝ) * ((m : ℝ) - 1) := by
    rw [norm_vsum_sq]
    calc
      (∑ i ∈ t, ∑ j ∈ t, ⟪v i, v j⟫) = ∑ i ∈ t, ∑ j ∈ t, (if i = j then (1 : ℝ) else -α) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hinner i hi j hj
      _ = (-α) * (m : ℝ) * (m : ℝ) + (1 - (-α)) * (m : ℝ) := by
        have hd := double_sum_diag_else t 1 (-α)
        rw [htcard] at hd
        simpa using hd
      _ = (m : ℝ) - α * (m : ℝ) * ((m : ℝ) - 1) := by ring
  have hpos : 0 ≤ (m : ℝ) - α * (m : ℝ) * ((m : ℝ) - 1) := by
    rw [← hsq]
    exact hgram
  have hbnd : (m : ℝ) ≤ (α : ℝ)⁻¹ + 1 := by
    have hfac : (m : ℝ) - α * (m : ℝ) * ((m : ℝ) - 1) = (m : ℝ) * (1 - α * ((m : ℝ) - 1)) := by ring
    have hposf : 0 ≤ (m : ℝ) * (1 - α * ((m : ℝ) - 1)) := by
      rw [← hfac]
      exact hpos
    have h2 : 0 ≤ 1 - α * ((m : ℝ) - 1) := (mul_nonneg_iff_of_pos_left hmposR).mp hposf
    have h2' : ((m : ℝ) - 1) * α ≤ 1 := by nlinarith [h2]
    have hd0 : (m : ℝ) - 1 ≤ 1 / α := (le_div_iff₀ hα0).mpr h2'
    have hd : (m : ℝ) - 1 ≤ (α : ℝ)⁻¹ := by simpa using hd0
    linarith
  have hgt : (α : ℝ)⁻¹ + 1 < (m : ℝ) := by
    dsimp [m]
    have hc := Nat.le_ceil (α⁻¹)
    have hc' : (α : ℝ)⁻¹ < (Nat.ceil (α⁻¹) : ℝ) + 1 := by linarith
    have hmc : ((Nat.ceil (α⁻¹) + 2 : ℕ) : ℝ) = (Nat.ceil (α⁻¹) : ℝ) + 2 := by norm_num [Nat.cast_add]
    rw [hmc]
    linarith
  linarith


/-- number of neighbours of `i` inside the set `V1` in the graph `G` -/
noncomputable def nbrCount {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)) (i : Fin n) : ℕ := by
  classical
  exact (V1.filter (fun u => G.Adj i u)).card

/-- flip the vectors on the set `Sf` -/
noncomputable def flipVec {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (Sf : Finset (Fin n)) (i : Fin n) : EuclideanSpace ℝ (Fin d) :=
  if i ∈ Sf then -v i else v i

lemma inner_neg_left_eq {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  have h := inner_smul_left x y (-1 : ℝ)
  simpa [neg_one_smul] using h

lemma inner_neg_right_eq {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  have h := inner_smul_right x y (-1 : ℝ)
  simpa [neg_one_smul] using h

/-- after the switching operation each vertex outside V1 is adjacent to at most M1 vertices of V1 -/
lemma switching_count (α : ℝ) (hα0 : 0 < α)
    {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α)
    (V1 : Finset (Fin n)) (M1 : ℕ) (hV1c : V1.card = 2 * M1)
    (Sf : Finset (Fin n)) (hSf : ∀ i, i ∈ Sf ↔ i ∉ V1 ∧ M1 < nbrCount (assocGraph α v) V1 i) :
    ∀ i : Fin n, i ∉ V1 → nbrCount (assocGraph α (flipVec v Sf)) V1 i ≤ M1 := by
  classical
  intro i hiV1
  let vF := flipVec v Sf
  let G := assocGraph α v
  let G' := assocGraph α vF
  have huSf : ∀ u ∈ V1, u ∉ Sf := by
    intro u huV1
    intro huS
    have huV1' : u ∉ V1 := (hSf u).mp huS |>.1
    exact huV1' huV1
  by_cases hiS : i ∈ Sf
  · have hS : M1 < nbrCount G V1 i := (hSf i).mp hiS |>.2
    have hmain : ∀ u ∈ V1, G'.Adj i u ↔ ¬ G.Adj i u := by
      intro u huV1
      have huV1S : u ∉ Sf := huSf u huV1
      have hiu : i ≠ u := by
        intro hiu'
        exact hiV1 (by simpa [hiu'] using huV1)
      have hvu : ⟪vF i, vF u⟫ = -⟪v i, v u⟫ := by
        dsimp [vF, flipVec]
        rw [if_pos hiS, if_neg huV1S]
        exact inner_neg_left_eq (v i) (v u)
      have hin : ⟪v i, v u⟫ = α ∨ ⟪v i, v u⟫ = -α := eq_or_eq_neg_of_abs_eq (hvangle hiu)
      constructor
      · intro hadj
        have hval : ⟪v i, v u⟫ = α := by
          have hnegv : -⟪v i, v u⟫ = -α := by
            rw [← hvu]
            exact hadj.2
          linarith
        intro hadjG
        have hvalG : ⟪v i, v u⟫ = -α := hadjG.2
        linarith
      · intro hnot
        refine ⟨hiu, ?_⟩
        have hval : ⟪v i, v u⟫ = α := by
          rcases hin with hpos | hnega
          · exact hpos
          · exfalso
            apply hnot
            exact ⟨hiu, hnega⟩
        rw [hvu, hval]
    have hfeq : V1.filter (fun u => G'.Adj i u) = V1.filter (fun u => ¬ G.Adj i u) := by
      ext u
      constructor
      · intro hu
        rw [mem_filter] at hu
        rcases hu with ⟨huV1, hadj⟩
        rw [mem_filter]
        exact ⟨huV1, (hmain u huV1).mp hadj⟩
      · intro hu
        rw [mem_filter] at hu
        rcases hu with ⟨huV1, hnot⟩
        rw [mem_filter]
        exact ⟨huV1, (hmain u huV1).mpr hnot⟩
    have hsum' : nbrCount G V1 i + (V1.filter (fun u => ¬ G.Adj i u)).card = V1.card := by
      dsimp [nbrCount, G]
      exact Finset.card_filter_add_card_filter_not (s := V1) (fun u : Fin n => (assocGraph α v).Adj i u)
    rw [hV1c] at hsum'
    have ha : nbrCount G V1 i ≥ M1 + 1 := by omega
    have hfin : (V1.filter (fun u => ¬ G.Adj i u)).card ≤ M1 := by omega
    have hcount : (V1.filter (fun u => G'.Adj i u)).card = (V1.filter (fun u => ¬ G.Adj i u)).card := by
      rw [hfeq]
    have hg : nbrCount (assocGraph α (flipVec v Sf)) V1 i = (V1.filter (fun u => G'.Adj i u)).card := by
      dsimp [nbrCount, G', vF, flipVec]
    rw [hg, hcount]
    simpa [G] using hfin
  · have hS : ¬ M1 < nbrCount G V1 i := by
      intro h
      apply hiS
      exact (hSf i).mpr ⟨hiV1, h⟩
    have hle : nbrCount G V1 i ≤ M1 := by omega
    have hmain : ∀ u ∈ V1, G'.Adj i u ↔ G.Adj i u := by
      intro u huV1
      have huV1S : u ∉ Sf := huSf u huV1
      have hiu : i ≠ u := by
        intro hiu'
        exact hiV1 (by simpa [hiu'] using huV1)
      have hvu : ⟪vF i, vF u⟫ = ⟪v i, v u⟫ := by
        dsimp [vF, flipVec]
        rw [if_neg hiS, if_neg huV1S]
      constructor <;> intro hadj
      · exact ⟨hadj.1, by rw [← hvu]; exact hadj.2⟩
      · exact ⟨hadj.1, by rw [hvu]; exact hadj.2⟩
    have hfeq : V1.filter (fun u => G'.Adj i u) = V1.filter (fun u => G.Adj i u) := by
      ext u
      constructor
      · intro hu
        rw [mem_filter] at hu
        rcases hu with ⟨huV1, hadj⟩
        rw [mem_filter]
        exact ⟨huV1, (hmain u huV1).mp hadj⟩
      · intro hu
        rw [mem_filter] at hu
        rcases hu with ⟨huV1, hadj⟩
        rw [mem_filter]
        exact ⟨huV1, (hmain u huV1).mpr hadj⟩
    have hg : nbrCount (assocGraph α (flipVec v Sf)) V1 i = (V1.filter (fun u => G'.Adj i u)).card := by
      dsimp [nbrCount, G', vF, flipVec]
    rw [hg, hfeq]
    dsimp [nbrCount, G] at hle
    simpa using hle


/-- the large-part bound: |V∖V2| ≤ 2M1 + 2^(2M1) M2, where V2 = C_{V1}(∅). -/
lemma partition_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (V1 : Finset (Fin n)) (M1 M2 : ℕ) (hV1c : V1.card = 2 * M1) (hM1pos : 0 < M1)
    (hswitch : ∀ i, i ∉ V1 → nbrCount G V1 i ≤ M1)
    (hb : ∀ (Y : Finset (Fin n)), Y ⊆ V1 → 0 < Y.card → Y.card ≤ M1 →
      (Cset G V1 Y).card ≤ M2) :
    ((Finset.univ : Finset (Fin n)) \ Cset G V1 ∅).card ≤ 2 * M1 + 2 ^ (2 * M1) * M2 := by
  classical
  let V2 := Cset G V1 ∅
  let Ps : Finset (Finset (Fin n)) := (V1.powerset.filter (fun Y => 0 < Y.card ∧ Y.card ≤ M1))
  have hcover : ((Finset.univ : Finset (Fin n)) \ V2) ⊆ V1 ∪ (Ps.biUnion (fun Y => Cset G V1 Y)) := by
    intro w hw
    rw [mem_sdiff] at hw
    have hwV2 : w ∉ V2 := hw.2
    by_cases hwV1 : w ∈ V1
    · exact mem_union_left _ hwV1
    · apply mem_union_right
      let Yw : Finset (Fin n) := V1.filter (fun x => G.Adj w x)
      have hwC : w ∈ Cset G V1 Yw := by
        rw [Cset_mem]
        refine ⟨hwV1, ?_, ?_⟩
        · intro u hu
          exact (G.adj_comm w u).mp (mem_filter.mp hu).2
        · intro u huV1 huY
          intro hadj
          apply huY
          rw [mem_filter]
          exact ⟨huV1, (G.adj_comm w u).mpr hadj⟩
      have hY1 : 0 < Yw.card := by
        -- w ∉ V2 means not all non-adjacent: exists x ∈ V1 adjacent to w
        have hnot : ¬ (∀ u ∈ V1, ¬ G.Adj u w) := by
          intro hall
          apply hwV2
          rw [Cset_mem]
          exact ⟨hwV1, (by intro u hu; simp at hu), (fun u huV1 huE => hall u huV1)⟩
        by_contra hle
        have hnone : ∀ u ∈ V1, ¬ G.Adj u w := by
          intro u huV1
          intro hadj
          have huY : u ∈ Yw := by
            rw [mem_filter]
            exact ⟨huV1, (G.adj_comm w u).mpr hadj⟩
          have hcard1 : 1 ≤ Yw.card := Finset.card_pos.mpr ⟨u, huY⟩
          omega
        exact hnot hnone
      have hY2 : Yw.card ≤ M1 := by
        dsimp [Yw]
        simpa [nbrCount] using hswitch w hwV1
      have hYsub : Yw ⊆ V1 := Finset.filter_subset _ _
      have hYwPs : Yw ∈ Ps := by
        dsimp [Ps]
        rw [mem_filter]
        exact ⟨Finset.mem_powerset.mpr hYsub, hY1, hY2⟩
      exact Finset.mem_biUnion.mpr ⟨Yw, hYwPs, hwC⟩
  have hcard1 : ((Finset.univ : Finset (Fin n)) \ V2).card ≤ (V1 ∪ (Ps.biUnion (fun Y => Cset G V1 Y))).card :=
    Finset.card_le_card hcover
  have hcard2 : (V1 ∪ (Ps.biUnion (fun Y => Cset G V1 Y))).card
      ≤ V1.card + (Ps.biUnion (fun Y => Cset G V1 Y)).card := Finset.card_union_le _ _
  have hcard3 : (Ps.biUnion (fun Y => Cset G V1 Y)).card
      ≤ ∑ Y ∈ Ps, (Cset G V1 Y).card := Finset.card_biUnion_le
  have hb' : ∀ Y ∈ Ps, (Cset G V1 Y).card ≤ M2 := by
    intro Y hY
    have hYm := (mem_filter.mp hY).2
    have hYs : Y ⊆ V1 := (Finset.mem_powerset.mp (mem_filter.mp hY).1)
    exact hb Y hYs hYm.1 hYm.2
  have hcard4 : (∑ Y ∈ Ps, (Cset G V1 Y).card) ≤ Ps.card * M2 := by
    have h := Finset.sum_le_card_nsmul Ps (fun Y => (Cset G V1 Y).card) M2 hb'
    simpa [nsmul_eq_mul] using h
  have hcard5 : Ps.card ≤ V1.powerset.card := Finset.card_le_card (by
    intro Y hY
    exact (mem_filter.mp hY).1)
  have hcard6 : V1.powerset.card = 2 ^ V1.card := Finset.card_powerset V1
  have hcard7 : Ps.card * M2 ≤ 2 ^ (2 * M1) * M2 := by
    rw [hV1c] at hcard6
    exact Nat.mul_le_mul_right M2 (by omega)
  rw [← show V2 = Cset G V1 ∅ by rfl]
  calc
    ((Finset.univ : Finset (Fin n)) \ V2).card ≤ (V1 ∪ (Ps.biUnion (fun Y => Cset G V1 Y))).card := hcard1
    _ ≤ V1.card + (Ps.biUnion (fun Y => Cset G V1 Y)).card := hcard2
    _ ≤ V1.card + (∑ Y ∈ Ps, (Cset G V1 Y).card) := by
      exact Nat.add_le_add_left hcard3 _
    _ ≤ V1.card + Ps.card * M2 := by
      exact Nat.add_le_add_left hcard4 _
    _ ≤ 2 * M1 + 2 ^ (2 * M1) * M2 := by
      rw [hV1c]
      exact Nat.add_le_add_left hcard7 (2 * M1)

/-- the main theorem: switching -/

theorem switch_bounded (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Δ : ℕ, ∀ {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖v i‖ = 1) →
      (∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) →
      ∃ v' : Fin n → EuclideanSpace ℝ (Fin d),
        (∀ i, v' i = v i ∨ v' i = -v i) ∧
        (∀ i : Fin n, (assocGraph α v').degree i ≤ Δ) := by
  classical
  let l : ℝ := lam α
  have hl : 0 < l := lam_pos hα0 hα1
  let Dn : ℕ := Nat.ceil (l^2) + 1
  let M1a : ℕ := Nat.ceil ((Dn : ℝ) * (1 + l)^2) + 1
  let M1b : ℕ := Nat.ceil (2 * l^2 + 2) + 1
  let M1 := max M1a M1b
  let M0 : ℕ := Nat.ceil (α⁻¹) + 2
  let R := Classical.choose (Submission.Ramsey.ramsey_clique_indep M0 (2 * M1))
  have hRam : ∀ (V : Type) [Fintype V], R ≤ Fintype.card V →
      ∀ G : SimpleGraph V,
        (∃ s : Finset V, M0 ≤ s.card ∧ ∀ ⦃a : V⦄, a ∈ s → ∀ ⦃b : V⦄, b ∈ s → a ≠ b → G.Adj a b) ∨
        (∃ s : Finset V, (2 * M1) ≤ s.card ∧ ∀ ⦃a : V⦄, a ∈ s → ∀ ⦃b : V⦄, b ∈ s → a ≠ b → ¬ G.Adj a b) := by
    dsimp [R]
    exact Classical.choose_spec (Submission.Ramsey.ramsey_clique_indep M0 (2 * M1))
  have hDpos : 0 < Dn := by dsimp [Dn]; omega
  have hD1l : 1 ≤ (Dn : ℝ) - l^2 := by
    have hceil : l^2 ≤ (Nat.ceil (l^2) : ℝ) := Nat.le_ceil (l^2)
    have hc : ((Nat.ceil (l^2) + 1 : ℕ) : ℝ) = (Nat.ceil (l^2) : ℝ) + 1 := by norm_num [Nat.cast_add]
    dsimp [Dn]
    rw [hc]
    linarith
  have hM1rel : (Dn : ℝ) * (1 + l)^2 < (M1a : ℝ) := by
    have hc : ((Nat.ceil ((Dn : ℝ) * (1 + l)^2) + 1 : ℕ) : ℝ) = (Nat.ceil ((Dn : ℝ) * (1 + l)^2) : ℝ) + 1 := by
      norm_num [Nat.cast_add]
    dsimp [M1a]
    rw [hc]
    have h1 : (Dn : ℝ) * (1 + l)^2 ≤ (Nat.ceil ((Dn : ℝ) * (1 + l)^2) : ℝ) := Nat.le_ceil _
    linarith
  have hM1b : (2 * l^2 + 2 : ℝ) ≤ (M1b : ℝ) := by
    have hc : ((Nat.ceil (2 * l^2 + 2) + 1 : ℕ) : ℝ) = (Nat.ceil (2 * l^2 + 2) : ℝ) + 1 := by
      norm_num [Nat.cast_add]
    dsimp [M1b]
    rw [hc]
    have h1 : (2 * l^2 + 2 : ℝ) ≤ (Nat.ceil (2 * l^2 + 2) : ℝ) := Nat.le_ceil _
    linarith
  have hM1pos : 0 < M1 := by dsimp [M1]; omega
  have hM1a_le : M1a ≤ M1 := by dsimp [M1]; omega
  rcases prop_b α hα0 hα1 M1b hM1b with ⟨M2op, hM2pos, hpropB⟩
  let M2v : ℕ := Nat.ceil (4 * l^2) + 1
  let Mbig : ℕ := 2 * M1 + 2 ^ (2 * M1) * M2v
  let Dl : ℕ := Nat.ceil (l^2)
  let Δ : ℕ := max R (Dl + Mbig)
  refine ⟨Δ, ?_⟩
  intro n d v hvnorm hvangle
  by_cases hsmall : n < R
  · -- small case: no flipping needed
    refine ⟨v, ?_, ?_⟩
    · intro i
      exact Or.inl rfl
    · intro i
      have hdeg : (assocGraph α v).degree i ≤ n - 1 := by
        by_cases hn0 : n = 0
        · subst n
          exfalso
          exact (Nat.not_lt_zero i.1 i.2)
        · have hlt : (assocGraph α v).degree i < n := by
            simpa using (SimpleGraph.degree_lt_card_verts (G := assocGraph α v) i)
          omega
      have hRΔ : R ≤ Δ := by dsimp [Δ]; exact le_max_left _ _
      omega
  · -- big case: Ramsey applies
    have hnR : R ≤ n := by omega
    let G := assocGraph α v
    rcases hRam (Fin n) (by simpa using hnR) G with hclq | hind
    · exfalso
      exact no_clique_M0 α hα0 hα1 v hvnorm hvangle hclq
    · rcases hind with ⟨S, hScard, hSind⟩
      rcases (Finset.exists_subset_card_eq (s := S) (n := 2 * M1) hScard) with ⟨V1, hV1sub, hV1card⟩
      have hV1ind : IsIndep G V1 := by
        intro a ha b hb hab
        exact hSind (hV1sub ha) (hV1sub hb) hab
      let Sf : Finset (Fin n) := Finset.univ.filter (fun i => i ∉ V1 ∧ M1 < nbrCount G V1 i)
      have hSf : ∀ i, i ∈ Sf ↔ i ∉ V1 ∧ M1 < nbrCount G V1 i := by
        intro i
        simp [Sf]
      let vF : Fin n → EuclideanSpace ℝ (Fin d) := flipVec v Sf
      have hflip : ∀ i, vF i = v i ∨ vF i = -v i := by
        intro i
        by_cases hi : i ∈ Sf
        · right
          dsimp [vF, flipVec]
          rw [if_pos hi]
        · left
          dsimp [vF, flipVec]
          rw [if_neg hi]
      have hvnormF : ∀ i, ‖vF i‖ = 1 := by
        intro i
        by_cases hi : i ∈ Sf
        · dsimp [vF, flipVec]
          rw [if_pos hi]
          simp [hvnorm i]
        · dsimp [vF, flipVec]
          rw [if_neg hi]
          exact hvnorm i
      have hvangleF : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪vF i, vF j⟫| = α := by
        intro i j hij
        by_cases hi : i ∈ Sf <;> by_cases hj : j ∈ Sf <;>
          dsimp [vF, flipVec] <;> simp [hi, hj]
        · exact hvangle hij
        · simpa [abs_neg] using hvangle hij
        · simpa [abs_neg] using hvangle hij
        · exact hvangle hij
      let G' := assocGraph α vF
      have hSfV1 : ∀ i, i ∈ Sf → i ∉ V1 := by
        intro i hi
        exact (hSf i).mp hi |>.1
      have hV1ind' : IsIndep G' V1 := by
        intro a ha b hb hab
        have hFa : a ∉ Sf := by
          intro h
          exact hSfV1 a h ha
        have hFb : b ∉ Sf := by
          intro h
          exact hSfV1 b h hb
        intro hadj
        have hinner : ⟪vF a, vF b⟫ = ⟪v a, v b⟫ := by
          dsimp [vF, flipVec]
          rw [if_neg hFa, if_neg hFb]
        have hin_neg : ⟪v a, v b⟫ = -α := by
          rw [← hinner]
          exact hadj.2
        have hin_pos : ⟪v a, v b⟫ = α := by
          have hGnon : ¬ G.Adj a b := hV1ind ha hb hab
          exact assocGraph_notAdj_inner_pos α v hvangle hab hGnon
        linarith
      have hswitch := switching_count α hα0 v hvnorm hvangle V1 M1 (by simpa [G] using hV1card) Sf hSf
      have hswitchG' : ∀ i, i ∉ V1 → nbrCount G' V1 i ≤ M1 := by
        intro i hi
        dsimp [G']
        exact hswitch i hi
      have hV1cardB : M1b ≤ V1.card := by
        rw [hV1card]
        omega
      have hbC : ∀ (Y : Finset (Fin n)), Y ⊆ V1 → 0 < Y.card → Y.card ≤ M1 →
          (Cset G' V1 Y).card ≤ M2v := by
        intro Y hYsub hYpos hYleM1
        have hYprop : Y.card < V1.card := by
          rw [hV1card]
          omega
        have hres : (Cset (assocGraph α vF) V1 Y).card ≤ M2v := by
          have hrr := hpropB vF hvnormF hvangleF V1 hV1ind' hV1cardB Y hYsub hYpos hYprop
          -- hrr ≤ ⌈4 lam²⌉+1 and M2v := ⌈4 l²⌉+1
          simpa [M2v] using hrr
        simpa [G'] using hres
      let V2 := Cset G' V1 ∅
      have hMbig : ((Finset.univ : Finset (Fin n)) \ V2).card ≤ Mbig := by
        have hpb := partition_bound G' V1 M1 M2v (by simpa [G'] using hV1card) hM1pos hswitchG' hbC
        simpa [V2, Mbig, G'] using hpb
      have hV1nb : ∀ i ∈ V1, ∀ u, G'.Adj i u → u ∉ V2 := by
        intro i hiV1 u hadj
        intro huV2
        have hmem := (Cset_mem G' V1 ∅ u).mp huV2
        have hnot := hmem.2.2 i hiV1 (by simp)
        exact hnot hadj
      refine ⟨vF, ?_, ?_⟩
      · exact hflip
      · -- degree bound
        intro i
        by_cases hiV1 : i ∈ V1
        · have hsub : G'.neighborFinset i ⊆ ((Finset.univ : Finset (Fin n)) \ V2) := by
            intro u hu
            have huAdj : G'.Adj i u := (SimpleGraph.mem_neighborFinset G' i u).mp hu
            rw [mem_sdiff]
            exact ⟨Finset.mem_univ u, fun hv2 => hV1nb i hiV1 u huAdj hv2⟩
          have hdeg1 : G'.degree i ≤ ((Finset.univ : Finset (Fin n)) \ V2).card := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree (G := G') i]
            exact Finset.card_le_card hsub
          have hMbigle : ((Finset.univ : Finset (Fin n)) \ V2).card ≤ Mbig := hMbig
          have hΔ : Dl + Mbig ≤ Δ := by dsimp [Δ]; exact le_max_right _ _
          have h1 : G'.degree i ≤ Mbig := le_trans hdeg1 hMbigle
          have h2 : Mbig ≤ Dl + Mbig := by omega
          exact le_trans (le_trans h1 h2) hΔ
        · -- i ∉ V1
          let Y' : Finset (Fin n) := V1.filter (fun x => ¬ G'.Adj x i)
          have hY'sub : Y' ⊆ V1 := Finset.filter_subset _ _
          have hY'ind : IsIndep G' Y' := by
            intro a ha b hb hab
            exact hV1ind' (hY'sub ha) (hY'sub hb) hab
          have hY'card : M1a ≤ Y'.card := by
            have hcount := hswitchG' i hiV1
            have hsum' : nbrCount G' V1 i + Y'.card = V1.card := by
              have hY'eq : V1.filter (fun x => ¬ G'.Adj x i) = V1.filter (fun x => ¬ G'.Adj i x) := by
                apply Finset.filter_congr
                intro x hx
                simp [G'.adj_comm x i]
              dsimp [Y', nbrCount]
              rw [hY'eq]
              exact Finset.card_filter_add_card_filter_not (s := V1) (fun x : Fin n => G'.Adj i x)
            have hV1c' : V1.card = 2 * M1 := by simpa [G'] using hV1card
            rw [hV1c'] at hsum'
            have hge : M1 ≤ Y'.card := by omega
            exact le_trans hM1a_le hge
          have hiuY' : i ∉ Y' := by
            intro hiY'
            exact hiV1 (hY'sub hiY')
          have hnonY' : ∀ x ∈ Y', ¬ (assocGraph α vF).Adj i x := by
            intro x hx
            intro hadj
            exact (mem_filter.mp hx).2 (by simpa [G'.adj_comm] using hadj)
          have hpropAres := prop_a α hα0 hα1 Dn M1a hDpos hD1l hM1rel vF hvnormF hvangleF Y' hY'ind hY'card i hiuY' hnonY'
          have hcnt : nbrCX G' Y' i < Dn := by
            simpa [G'] using hpropAres
          have hDleq : nbrCX G' Y' i ≤ Dl := by
            dsimp [Dn, Dl] at hcnt ⊢
            have hc : Nat.ceil (l^2) + 1 = Nat.ceil (l^2) + 1 := rfl
            omega
          let C := Cset G' Y' ∅
          have hV2subC : V2 ⊆ C := by
            intro w hw
            have hmem := (Cset_mem G' V1 ∅ w).mp hw
            rw [Cset_mem]
            refine ⟨fun hwY => hmem.1 (hY'sub hwY), (by intro u hu; simp at hu), ?_⟩
            intro u huY' huE
            have huV1 : u ∈ V1 := hY'sub huY'
            exact hmem.2.2 u huV1 (by simp)
          have hdegA : (C.filter (fun w => G'.Adj i w)).card ≤ Dl := by
            have hc : (C.filter (fun w => G'.Adj i w)).card = nbrCX G' Y' i := by
              dsimp [C, nbrCX]
            rw [hc]
            exact hDleq
          have hdegB : ((Finset.univ : Finset (Fin n)) \ C).card ≤ Mbig := by
            have hsubC : (Finset.univ : Finset (Fin n)) \ C ⊆ (Finset.univ : Finset (Fin n)) \ V2 := by
              intro w hw
              rw [mem_sdiff] at hw ⊢
              exact ⟨hw.1, fun hwV2 => hw.2 (hV2subC hwV2)⟩
            have hc1 := Finset.card_le_card hsubC
            omega
          have hdegC : G'.degree i ≤ Dl + Mbig := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree (G := G') i]
            have hpart2 : G'.neighborFinset i ⊆ (C.filter (fun w => G'.Adj i w)) ∪ ((Finset.univ : Finset (Fin n)) \ C) := by
              intro u hu
              have huAdj : G'.Adj i u := (SimpleGraph.mem_neighborFinset G' i u).mp hu
              by_cases huC : u ∈ C
              · exact mem_union_left _ (by rw [mem_filter]; exact ⟨huC, huAdj⟩)
              · exact mem_union_right _ (by rw [mem_sdiff]; exact ⟨Finset.mem_univ u, huC⟩)
            have hc3 := Finset.card_le_card hpart2
            have hc4 := Finset.card_union_le (C.filter (fun w => G'.Adj i w)) ((Finset.univ : Finset (Fin n)) \ C)
            omega
          have hΔ2 : Dl + Mbig ≤ Δ := by dsimp [Δ]; exact le_max_right _ _
          exact le_trans hdegC hΔ2



end
end Submission
