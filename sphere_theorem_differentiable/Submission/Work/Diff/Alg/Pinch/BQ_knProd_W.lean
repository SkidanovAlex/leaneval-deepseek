import Mathlib
import Submission.Work.Diff.Alg.Pinch.BQDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `BQ (knProd A id2) W` for a Ricci-flat algebraic curvature tensor `W`

For a symmetric `2`-tensor `A` and an algebraic curvature tensor `W` with vanishing Ricci tensor,
the polarization `BQ` of Hamilton's quadratic term against the Kulkarni–Nomizu product
`knProd A (id2 n)` is again a Kulkarni–Nomizu product against the metric:

`BQ (A ∧ id) W = B ∧ id`,  `B_{ab} = ∑_{p q} A_{pq} W_{a p b q}`.

The proof expands `BQ` into its six double sums; each one is evaluated by contracting the
Kronecker deltas of `knProd A (id2 n)`, which produces the "mixed" contractions
`∑_{p} W_{x p y p}` (equal to `ric W x y`, hence zero) together with the four index identities

* `W_{k l p j} - W_{j k l p} + W_{j l k p} = 0`,
* `W_{k l p i} + W_{i l k p} - W_{i k l p} = 0`,
* `W_{i j p l} + W_{j p i l} - W_{i p j l} = 0`,
* `W_{i j p k} - W_{i p j k} + W_{j p i k} = 0`,

which are consequences of the Bianchi identity together with the antisymmetries of `W`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary facts about `id2`, `knProd` and algebraic curvature tensors -/

/-- `id2 n` is symmetric. -/
lemma knProdW_id2_comm (a b : Fin n) : id2 n a b = id2 n b a := by
  rw [id2, id2]
  exact if_congr eq_comm rfl rfl

/-- Summation against a Kronecker delta. -/
lemma knProdW_sum_mul_id2 (f : Fin n → ℝ) (a : Fin n) : (∑ p, f p * id2 n a p) = f a := by
  rw [Finset.sum_eq_single a]
  · simp [id2]
  · intro p _ hp
    have h : ¬ (a = p) := Ne.symm hp
    simp only [id2, h, ite_false, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- An algebraic curvature tensor is antisymmetric in its last two indices. -/
lemma knProdW_anti2 {W : Curv4 n} (hW : IsAlgCurv W) (a b c d : Fin n) :
    W a b c d = - W a b d c := by
  obtain ⟨hanti, hpair, hbian⟩ := hW
  have h1 : W a b c d = W c d a b := (hpair a b c d).symm
  have h2 : W a b d c = W d c a b := (hpair a b d c).symm
  have h3 : W d c a b = - W c d a b := hanti c d a b
  linarith

/-- The mixed contraction `∑_p W x p y p` is the Ricci tensor. -/
lemma knProdW_sum_W_diag {W : Curv4 n} (hW : IsAlgCurv W) (x y : Fin n) :
    (∑ p, W x p y p) = ric W x y := by
  obtain ⟨hanti, hpair, hbian⟩ := hW
  have h2 := knProdW_anti2 ⟨hanti, hpair, hbian⟩
  have hpt : ∀ p, W x p y p = W p x p y := by
    intro p
    have e1 : W p x y p = - W x p y p := hanti x p y p
    have e2 : W p x y p = - W p x p y := h2 p x y p
    linarith
  rw [show (∑ p, W x p y p) = ∑ p, W p x p y from Finset.sum_congr rfl (fun p _ => hpt p)]
  rfl

/-! ## The six contractions -/

/-- `∑_{p q} (A ∧ id)ᵢⱼₚq W_{k l p q} = 2 ∑_p A_{i p} W_{k l p j} - 2 ∑_p A_{j p} W_{k l p i}`. -/
lemma knProdW_contract_a (A : Fin n → Fin n → ℝ) (W : Curv4 n) (hW : IsAlgCurv W)
    (i j k l : Fin n) :
    (∑ p, ∑ q, knProd A (id2 n) i j p q * W k l p q)
      = 2 * (∑ p, A i p * W k l p j) - 2 * (∑ p, A j p * W k l p i) := by
  have h2 := knProdW_anti2 hW
  have expand : ∀ p q, knProd A (id2 n) i j p q * W k l p q
      = (A i p * W k l p q) * id2 n j q - (A i q * W k l p q) * id2 n j p
        - (A j p * W k l p q) * id2 n i q + (A j q * W k l p q) * id2 n i p := by
    intro p q; rw [knProd]; ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    knProdW_sum_mul_id2]
  have h1 : (∑ q, A i q * W k l j q) = - (∑ q, A i q * W k l q j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro q _; rw [h2 k l j q]; ring
  have h3 : (∑ q, A j q * W k l i q) = - (∑ q, A j q * W k l q i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro q _; rw [h2 k l i q]; ring
  rw [h1, h3]; ring

/-- `∑_{p q} W_{i j p q} (A ∧ id)_{k l p q} = 2 ∑_p A_{k p} W_{i j p l} - 2 ∑_p A_{l p} W_{i j p k}`. -/
lemma knProdW_contract_b (A : Fin n → Fin n → ℝ) (W : Curv4 n) (hW : IsAlgCurv W)
    (i j k l : Fin n) :
    (∑ p, ∑ q, W i j p q * knProd A (id2 n) k l p q)
      = 2 * (∑ p, A k p * W i j p l) - 2 * (∑ p, A l p * W i j p k) := by
  have h2 := knProdW_anti2 hW
  have expand : ∀ p q, W i j p q * knProd A (id2 n) k l p q
      = (A k p * W i j p q) * id2 n l q - (A k q * W i j p q) * id2 n l p
        - (A l p * W i j p q) * id2 n k q + (A l q * W i j p q) * id2 n k p := by
    intro p q; rw [knProd]; ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    knProdW_sum_mul_id2]
  have h1 : (∑ q, A k q * W i j l q) = - (∑ q, A k q * W i j q l) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro q _; rw [h2 i j l q]; ring
  have h3 : (∑ q, A l q * W i j k q) = - (∑ q, A l q * W i j q k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro q _; rw [h2 i j k q]; ring
  rw [h1, h3]; ring

/-- `∑_{p q} (A ∧ id)_{i p k q} W_{j p l q}`. -/
lemma knProdW_contract_c (A : Fin n → Fin n → ℝ) (W : Curv4 n) (hW : IsAlgCurv W)
    (hA : ∀ a b, A a b = A b a) (i j k l : Fin n) :
    (∑ p, ∑ q, knProd A (id2 n) i p k q * W j p l q)
      = A i k * (∑ p, W j p l p) - (∑ p, A i p * W j k l p) + (∑ p, A k p * W j p i l)
        + (∑ p, ∑ q, A p q * W j p l q) * id2 n i k := by
  have h2 := knProdW_anti2 hW
  have expand : ∀ p q, knProd A (id2 n) i p k q * W j p l q
      = A i k * W j p l q * id2 n p q - (A i q * W j p l q) * id2 n k p
        - (A p k * W j p l q) * id2 n i q + (A p q * W j p l q) * id2 n i k := by
    intro p q; rw [knProd, knProdW_id2_comm p k]; ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, knProdW_sum_mul_id2]
  have h3 : (∑ p, A p k * W j p l i) = - (∑ p, A k p * W j p i l) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [hA p k, h2 j p l i]; ring
  rw [h3]; ring

/-- `∑_{p q} W_{i p k q} (A ∧ id)_{j p l q}`. -/
lemma knProdW_contract_d (A : Fin n → Fin n → ℝ) (W : Curv4 n) (hW : IsAlgCurv W)
    (hA : ∀ a b, A a b = A b a) (i j k l : Fin n) :
    (∑ p, ∑ q, W i p k q * knProd A (id2 n) j p l q)
      = A j l * (∑ p, W i p k p) - (∑ p, A j p * W i l k p) + (∑ p, A l p * W i p j k)
        + (∑ p, ∑ q, A p q * W i p k q) * id2 n j l := by
  have h2 := knProdW_anti2 hW
  have expand : ∀ p q, W i p k q * knProd A (id2 n) j p l q
      = A j l * W i p k q * id2 n p q - (A j q * W i p k q) * id2 n l p
        - (A p l * W i p k q) * id2 n j q + (A p q * W i p k q) * id2 n j l := by
    intro p q; rw [knProd, knProdW_id2_comm p l]; ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, knProdW_sum_mul_id2]
  have h3 : (∑ p, A p l * W i p k j) = - (∑ p, A l p * W i p j k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [hA p l, h2 i p k j]; ring
  rw [h3]; ring

/-- `∑_{p q} (A ∧ id)_{i p l q} W_{j p k q}`. -/
lemma knProdW_contract_e (A : Fin n → Fin n → ℝ) (W : Curv4 n) (hW : IsAlgCurv W)
    (hA : ∀ a b, A a b = A b a) (i j k l : Fin n) :
    (∑ p, ∑ q, knProd A (id2 n) i p l q * W j p k q)
      = A i l * (∑ p, W j p k p) - (∑ p, A i p * W j l k p) + (∑ p, A l p * W j p i k)
        + (∑ p, ∑ q, A p q * W j p k q) * id2 n i l := by
  have h2 := knProdW_anti2 hW
  have expand : ∀ p q, knProd A (id2 n) i p l q * W j p k q
      = A i l * W j p k q * id2 n p q - (A i q * W j p k q) * id2 n l p
        - (A p l * W j p k q) * id2 n i q + (A p q * W j p k q) * id2 n i l := by
    intro p q; rw [knProd, knProdW_id2_comm p l]; ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, knProdW_sum_mul_id2]
  have h3 : (∑ p, A p l * W j p k i) = - (∑ p, A l p * W j p i k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [hA p l, h2 j p k i]; ring
  rw [h3]; ring

/-- `∑_{p q} W_{i p l q} (A ∧ id)_{j p k q}`. -/
lemma knProdW_contract_f (A : Fin n → Fin n → ℝ) (W : Curv4 n) (hW : IsAlgCurv W)
    (hA : ∀ a b, A a b = A b a) (i j k l : Fin n) :
    (∑ p, ∑ q, W i p l q * knProd A (id2 n) j p k q)
      = A j k * (∑ p, W i p l p) - (∑ p, A j p * W i k l p) + (∑ p, A k p * W i p j l)
        + (∑ p, ∑ q, A p q * W i p l q) * id2 n j k := by
  have h2 := knProdW_anti2 hW
  have expand : ∀ p q, W i p l q * knProd A (id2 n) j p k q
      = A j k * W i p l q * id2 n p q - (A j q * W i p l q) * id2 n k p
        - (A p k * W i p l q) * id2 n j q + (A p q * W i p l q) * id2 n j k := by
    intro p q; rw [knProd, knProdW_id2_comm p k]; ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, knProdW_sum_mul_id2]
  have h3 : (∑ p, A p k * W i p l j) = - (∑ p, A k p * W i p j l) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [hA p k, h2 i p l j]; ring
  rw [h3]; ring

/-! ## The four index identities (consequences of Bianchi + antisymmetry) -/

/-- `W_{k l p j} - W_{j k l p} + W_{j l k p} = 0`. -/
lemma knProdW_bracket1 (A : Fin n → Fin n → ℝ) (W : Curv4 n) (hW : IsAlgCurv W)
    (i j k l : Fin n) :
    (∑ p, A i p * W k l p j) - (∑ p, A i p * W j k l p) + (∑ p, A i p * W j l k p) = 0 := by
  have hpt : ∀ p, W k l p j - W j k l p + W j l k p = 0 := by
    intro p
    obtain ⟨hanti, hpair, hbian⟩ := hW
    have hb := hbian j k l p
    have e1 : W k l p j = - W k l j p := knProdW_anti2 ⟨hanti, hpair, hbian⟩ k l p j
    have e2 : W j l k p = - W l j k p := hanti l j k p
    linarith
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro p _
  have hp := hpt p
  calc A i p * W k l p j - A i p * W j k l p + A i p * W j l k p
      = A i p * (W k l p j - W j k l p + W j l k p) := by ring
    _ = 0 := by rw [hp, mul_zero]

/-- `W_{k l p i} + W_{i l k p} - W_{i k l p} = 0`. -/
lemma knProdW_bracket2 (A : Fin n → Fin n → ℝ) (W : Curv4 n) (hW : IsAlgCurv W)
    (i j k l : Fin n) :
    (∑ p, A j p * W k l p i) + (∑ p, A j p * W i l k p) - (∑ p, A j p * W i k l p) = 0 := by
  have hpt : ∀ p, W k l p i + W i l k p - W i k l p = 0 := by
    intro p
    obtain ⟨hanti, hpair, hbian⟩ := hW
    have hb := hbian i k l p
    have e1 : W k l p i = - W k l i p := knProdW_anti2 ⟨hanti, hpair, hbian⟩ k l p i
    have e2 : W i l k p = - W l i k p := hanti l i k p
    linarith
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro p _
  have hp := hpt p
  calc A j p * W k l p i + A j p * W i l k p - A j p * W i k l p
      = A j p * (W k l p i + W i l k p - W i k l p) := by ring
    _ = 0 := by rw [hp, mul_zero]

/-- `W_{i j p l} + W_{j p i l} - W_{i p j l} = 0`. -/
lemma knProdW_bracket3 (A : Fin n → Fin n → ℝ) (W : Curv4 n) (hW : IsAlgCurv W)
    (i j k l : Fin n) :
    (∑ p, A k p * W i j p l) + (∑ p, A k p * W j p i l) - (∑ p, A k p * W i p j l) = 0 := by
  have hpt : ∀ p, W i j p l + W j p i l - W i p j l = 0 := by
    intro p
    obtain ⟨hanti, hpair, hbian⟩ := hW
    have hb := hbian i j p l
    have e1 : W i p j l = - W p i j l := hanti p i j l
    linarith
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro p _
  have hp := hpt p
  calc A k p * W i j p l + A k p * W j p i l - A k p * W i p j l
      = A k p * (W i j p l + W j p i l - W i p j l) := by ring
    _ = 0 := by rw [hp, mul_zero]

/-- `W_{i j p k} - W_{i p j k} + W_{j p i k} = 0`. -/
lemma knProdW_bracket4 (A : Fin n → Fin n → ℝ) (W : Curv4 n) (hW : IsAlgCurv W)
    (i j k l : Fin n) :
    (∑ p, A l p * W i j p k) - (∑ p, A l p * W i p j k) + (∑ p, A l p * W j p i k) = 0 := by
  have hpt : ∀ p, W i j p k - W i p j k + W j p i k = 0 := by
    intro p
    obtain ⟨hanti, hpair, hbian⟩ := hW
    have hb := hbian i j p k
    have e1 : W i p j k = - W p i j k := hanti p i j k
    linarith
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro p _
  have hp := hpt p
  calc A l p * W i j p k - A l p * W i p j k + A l p * W j p i k
      = A l p * (W i j p k - W i p j k + W j p i k) := by ring
    _ = 0 := by rw [hp, mul_zero]

/-! ## The main identity -/

theorem BQ_knProd_W (n : ℕ) {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i)
    {W : Submission.Diff.Alg.Curv4 n} (hW : Submission.Diff.Alg.IsAlgCurv W)
    (hric : ∀ i j, Work.Diff.Alg.Pinch.ric W i j = 0) (i j k l : Fin n) :
    Work.Diff.Alg.Pinch.BQ (Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n)) W i j k l
      = Work.Diff.Alg.Pinch.knProd (fun a b => ∑ p, ∑ q, A p q * W a p b q)
          (Work.Diff.Alg.Pinch.id2 n) i j k l := by
  have hSa := knProdW_contract_a A W hW i j k l
  have hSb := knProdW_contract_b A W hW i j k l
  have hSc := knProdW_contract_c A W hW hA i j k l
  have hSd := knProdW_contract_d A W hW hA i j k l
  have hSe := knProdW_contract_e A W hW hA i j k l
  have hSf := knProdW_contract_f A W hW hA i j k l
  have hUik : (∑ p, W i p k p) = 0 := by rw [knProdW_sum_W_diag hW i k]; exact hric i k
  have hUjl : (∑ p, W j p l p) = 0 := by rw [knProdW_sum_W_diag hW j l]; exact hric j l
  have hUil : (∑ p, W i p l p) = 0 := by rw [knProdW_sum_W_diag hW i l]; exact hric i l
  have hUjk : (∑ p, W j p k p) = 0 := by rw [knProdW_sum_W_diag hW j k]; exact hric j k
  have hbr1 := knProdW_bracket1 A W hW i j k l
  have hbr2 := knProdW_bracket2 A W hW i j k l
  have hbr3 := knProdW_bracket3 A W hW i j k l
  have hbr4 := knProdW_bracket4 A W hW i j k l
  rw [BQ_apply]
  rw [show (∑ p, ∑ q, ((knProd A (id2 n) i j p q * W k l p q
          + W i j p q * knProd A (id2 n) k l p q) / 2
        + (knProd A (id2 n) i p k q * W j p l q + W i p k q * knProd A (id2 n) j p l q)
        - (knProd A (id2 n) i p l q * W j p k q + W i p l q * knProd A (id2 n) j p k q)))
      = ((∑ p, ∑ q, knProd A (id2 n) i j p q * W k l p q)
          + (∑ p, ∑ q, W i j p q * knProd A (id2 n) k l p q)) / 2
        + ((∑ p, ∑ q, knProd A (id2 n) i p k q * W j p l q)
          + (∑ p, ∑ q, W i p k q * knProd A (id2 n) j p l q))
        - ((∑ p, ∑ q, knProd A (id2 n) i p l q * W j p k q)
          + (∑ p, ∑ q, W i p l q * knProd A (id2 n) j p k q)) from by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]]
  rw [hSa, hSb, hSc, hSd, hSe, hSf]
  simp only [hUik, hUjl, hUil, hUjk, mul_zero]
  rw [knProd]
  linear_combination hbr1 - hbr2 + hbr3 - hbr4

end Work.Diff.Alg.Pinch
