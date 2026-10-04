import Mathlib
import Submission.Work.Diff.Alg.Pinch.Q_knProd_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ricci and scalar curvature of `Q (C ∧ id)`

Consequences of `Q_knProd_apply`: the Ricci tensor, the scalar curvature, and the traceless Ricci
tensor of Hamilton's reaction term evaluated on a "Ricci-type" curvature tensor `C ∧ id`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## The `(0,2)`-companions of `knProd C id` -/

lemma trM_id2 : trM (id2 n) = (n : ℝ) := by
  simp only [trM, id2]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

lemma scalAlg_knProd_id (C : Fin n → Fin n → ℝ) :
    scalAlg (knProd C (id2 n)) = (2 * (n : ℝ) - 2) * trM C := by
  rw [scalAlg_knProd]
  have h1 : (∑ j, id2 n j j) = (n : ℝ) := by
    simp only [id2]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : (∑ i, ∑ j, C i j * id2 n j i) = trM C := by
    simp only [trM]
    apply Finset.sum_congr rfl; intro i _
    exact sum_mul_id2 (fun j => C i j) i
  rw [h1, h2, ← trM_eq]
  ring

lemma ric_knProd_id (C : Fin n → Fin n → ℝ) (i j : Fin n) :
    ric (knProd C (id2 n)) i j = trM C * id2 n i j + ((n : ℝ) - 2) * C i j := by
  rw [ric_knProd_id2]
  rfl

lemma ric_knProd_idd (i j : Fin n) :
    ric (knProd (id2 n) (id2 n)) i j = (2 * (n : ℝ) - 2) * id2 n i j := by
  rw [ric_knProd_id, trM_id2]
  ring

lemma ric_knProd_self {C : Fin n → Fin n → ℝ} (hC : ∀ i j, C i j = C j i) (i j : Fin n) :
    ric (knProd C C) i j = 2 * trM C * C i j - 2 * s2m C i j := by
  have hpt : ∀ k : Fin n, knProd C C k i k j = 2 * (C k k * C i j) - 2 * (C i k * C k j) := by
    intro k; simp only [knProd]; ring
  have h1 : (∑ k, 2 * (C k k * C i j)) = 2 * trM C * C i j := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← trM_eq]
    ring
  have h2 : (∑ k, 2 * (C i k * C k j)) = 2 * s2m C i j := by
    rw [← Finset.mul_sum, ← s2m_rows hC i j]
  simp only [ric, hpt, Finset.sum_sub_distrib, h1, h2]

/-! ## The Ricci tensor of `Q (C ∧ id)` -/

theorem ric_Q_knProd_apply (n : ℕ) {C : Fin n → Fin n → ℝ} (hC : ∀ i j, C i j = C j i)
    (i j : Fin n) :
    ric (Submission.Diff.Alg.Q (knProd C (id2 n))) i j
      = 4 * ((n : ℝ) - 2) * trM C * C i j - 4 * ((n : ℝ) - 2) * s2m C i j
        + 2 * id2 n i j * ((trM C) ^ 2 + ((n : ℝ) - 2) * frb C) := by
  have h1 : ric (knProd (s2m C) (id2 n)) i j
      = frb C * id2 n i j + ((n : ℝ) - 2) * s2m C i j := by
    rw [ric_knProd_id, trM_eq, sum_s2m_diag]
  have h3 : ric (knProd C (id2 n)) i j = trM C * id2 n i j + ((n : ℝ) - 2) * C i j :=
    ric_knProd_id C i j
  have h4 : ric (knProd (id2 n) (id2 n)) i j = (2 * (n : ℝ) - 2) * id2 n i j :=
    ric_knProd_idd i j
  have h2 : ric (knProd C C) i j = 2 * trM C * C i j - 2 * s2m C i j := ric_knProd_self hC i j
  rw [Q_knProd_apply n hC]
  simp only [ric_add_linv, ric_smul_linv]
  rw [h1, h2, h3, h4]
  ring

/-! ## The scalar curvature of `Q (C ∧ id)` -/

theorem scalAlg_Q_knProd_apply (n : ℕ) {C : Fin n → Fin n → ℝ} (hC : ∀ i j, C i j = C j i) :
    scalAlg (Submission.Diff.Alg.Q (knProd C (id2 n)))
      = 2 * ((3 * (n : ℝ) - 4) * (trM C) ^ 2 + ((n : ℝ) - 2) ^ 2 * frb C) := by
  have hA : IsAlgCurv (knProd C (id2 n)) :=
    knProd_isAlgCurv hC (fun i j => id2_symm i j)
  rw [scalAlg_Q n hA]
  have hpt : ∀ i j : Fin n, ric (knProd C (id2 n)) i j * ric (knProd C (id2 n)) i j
      = (trM C) ^ 2 * (id2 n i j * id2 n i j)
        + 2 * (trM C * ((n : ℝ) - 2)) * (id2 n i j * C i j)
        + ((n : ℝ) - 2) ^ 2 * (C i j * C i j) := by
    intro i j; rw [ric_knProd_id]; ring
  have hinner : (∑ i, ∑ j, ric (knProd C (id2 n)) i j * ric (knProd C (id2 n)) i j)
      = (3 * (n : ℝ) - 4) * (trM C) ^ 2 + ((n : ℝ) - 2) ^ 2 * frb C := by
    simp only [hpt, Finset.sum_add_distrib]
    rw [sum_sum_const, sum_sum_const, sum_sum_const, sum_sum_id2_id2, sum_sum_id2_C]
    simp only [frb]
    ring
  rw [hinner]

/-! ## The traceless Ricci tensor of `C ∧ id` -/

lemma ric0_knProd {C : Fin n → Fin n → ℝ} (hn : (n : ℝ) ≠ 0) (i j : Fin n) :
    ric0 (knProd C (id2 n)) i j
      = ((n : ℝ) - 2) * (C i j - (trM C / (n : ℝ)) * id2 n i j) := by
  rw [ric0, ric_knProd_id, scalAlg_knProd_id]
  field_simp
  ring

lemma ric0sq_knProd {C : Fin n → Fin n → ℝ} (hC : ∀ i j, C i j = C j i) (hn : (n : ℝ) ≠ 0)
    (i j : Fin n) :
    ric0sq (knProd C (id2 n)) i j
      = ((n : ℝ) - 2) ^ 2 * (s2m C i j - 2 * (trM C / (n : ℝ)) * C i j
          + (trM C / (n : ℝ)) ^ 2 * id2 n i j) := by
  have hpt : ∀ k : Fin n, ((n : ℝ) - 2) * (C i k - (trM C / (n : ℝ)) * id2 n i k)
        * (((n : ℝ) - 2) * (C k j - (trM C / (n : ℝ)) * id2 n k j))
      = ((n : ℝ) - 2) ^ 2 * ((C i k - (trM C / (n : ℝ)) * id2 n i k)
          * (C k j - (trM C / (n : ℝ)) * id2 n k j)) := by
    intro k; ring
  have h2 : ∀ k : Fin n, (C i k - (trM C / (n : ℝ)) * id2 n i k)
        * (C k j - (trM C / (n : ℝ)) * id2 n k j)
      = (C i k * C k j) - (trM C / (n : ℝ)) * (C i k * id2 n k j)
        - (trM C / (n : ℝ)) * (id2 n i k * C k j)
        + (trM C / (n : ℝ)) ^ 2 * (id2 n i k * id2 n k j) := by
    intro k; ring
  simp only [ric0sq, ric0_knProd hn, hpt, h2]
  simp only [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← s2m_rows hC i j]
  simp only [← Finset.mul_sum]
  rw [sum_mul_id2 (fun k => C i k) j, sum_id2_mul (fun k => C k j) i, sum_id2_id2'' i j]
  ring

lemma ric0Frob2_knProd {C : Fin n → Fin n → ℝ} (hn : (n : ℝ) ≠ 0) :
    ric0Frob2 (knProd C (id2 n))
      = ((n : ℝ) - 2) ^ 2 * (frb C - (trM C) ^ 2 / (n : ℝ)) := by
  have hpt : ∀ i j : Fin n, ((n : ℝ) - 2) * (C i j - (trM C / (n : ℝ)) * id2 n i j)
        * (((n : ℝ) - 2) * (C i j - (trM C / (n : ℝ)) * id2 n i j))
      = ((n : ℝ) - 2) ^ 2 * ((C i j - (trM C / (n : ℝ)) * id2 n i j)
          * (C i j - (trM C / (n : ℝ)) * id2 n i j)) := by
    intro i j; ring
  have h2 : ∀ i j : Fin n, (C i j - (trM C / (n : ℝ)) * id2 n i j)
        * (C i j - (trM C / (n : ℝ)) * id2 n i j)
      = (C i j * C i j) - 2 * (trM C / (n : ℝ)) * (C i j * id2 n i j)
        + (trM C / (n : ℝ)) ^ 2 * (id2 n i j * id2 n i j) := by
    intro i j; ring
  simp only [ric0Frob2, ric0_knProd hn, hpt, h2]
  simp only [← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← frb_eq]
  simp only [← Finset.mul_sum]
  rw [sum_sum_C_id2 C, sum_sum_id2_id2]
  field_simp
  ring

end Work.Diff.Alg.Pinch
