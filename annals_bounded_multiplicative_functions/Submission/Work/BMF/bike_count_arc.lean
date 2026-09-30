import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.bike_count
import Submission.Work.BMF.sum_adj_le_edges

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset Matrix

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-! ## Auxiliary lemmas -/

/-- Matrix powers transport along a reindexing. -/
lemma pow_reindex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Matrix α α ℝ) (e : α ≃ β) (m : ℕ) (i j : β) :
    ((Matrix.reindex e e M) ^ m) i j = (M ^ m) (e.symm i) (e.symm j) := by
  induction m generalizing i j with
  | zero =>
      rw [pow_zero, pow_zero, Matrix.one_apply, Matrix.one_apply]
      by_cases h : i = j
      · rw [ite_eq_left h, ite_eq_left (by rw [h])]
      · rw [ite_eq_right h, ite_eq_right (fun hh => h (e.symm.injective hh))]
  | succ m ih =>
      calc ((Matrix.reindex e e M) ^ (m + 1)) i j
          = ∑ k : β, ((Matrix.reindex e e M) ^ m) i k * (Matrix.reindex e e M) k j := by
            rw [pow_succ, Matrix.mul_apply]
        _ = ∑ k : β, (M ^ m) (e.symm i) (e.symm k) * M (e.symm k) (e.symm j) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [ih i k]
            simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
        _ = ∑ k : α, (M ^ m) (e.symm i) k * M k (e.symm j) :=
            Equiv.sum_comp e.symm (fun k => (M ^ m) (e.symm i) k * M k (e.symm j))
        _ = (M ^ (m + 1)) (e.symm i) (e.symm j) := by
            rw [pow_succ, Matrix.mul_apply]

/-- A double sum is invariant under reindexing both variables. -/
lemma sum_sum_reindex {α β : Type*} [Fintype α] [Fintype β]
    (F : α → α → ℝ) (e : α ≃ β) :
    (∑ i : β, ∑ j : β, F (e.symm i) (e.symm j)) = ∑ i : α, ∑ j : α, F i j := by
  rw [Equiv.sum_comp e.symm (fun i : α => ∑ j : β, F i (e.symm j))]
  exact Finset.sum_congr rfl (fun i _ => Equiv.sum_comp e.symm (fun j : α => F i j))

/-- **Bicycle count in terms of the bicycle set.**  For a graph of `q`-arcs with `2ℓ+1`-th power
sum `S` over `n` vertices, the number of bicycles (a `q`-arc with a closed `q`-walk of length
`ℓ` through each of its endpoints) is at least `S^(2ℓ+1)/(2 n^(2ℓ+2))`. -/
theorem bike_count_arc {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : Work.BMF.QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) (hℓ : Even ℓ) :
    ((∑ i, ∑ j, (Matrix.of (fun i j : Work.BMF.GVert D =>
          if Work.BMF.GAdjQ D q i j then (1 : ℝ) else 0)) i j) ^ (2 * ℓ + 1) /
        (Fintype.card (Work.BMF.GVert D) : ℝ) ^ (2 * ℓ + 2)) / 2
      ≤ ((Work.BMF.bikeSet D q ℓ).card : ℝ) := by
  classical
  set A : Matrix (GVert D) (GVert D) ℝ :=
    Matrix.of (fun i j : GVert D => if GAdjQ D q i j then (1 : ℝ) else 0) with hA
  set g : ℝ → ℝ := fun x => ((closedWalkVal D q ℓ x).card : ℝ) with hg
  have hgnn : ∀ x, 0 ≤ g x := by
    intro x; rw [hg]; exact Nat.cast_nonneg _
  have hAent : ∀ i j : GVert D, A i j = if GAdjQ D q i j then (1 : ℝ) else 0 := by
    intro i j; rw [hA, Matrix.of_apply]
  have hpow : ∀ i : GVert D, (A ^ ℓ) i i = g i.1 := by
    intro i
    rw [hA, hg]
    exact (card_closedWalkVal D q ℓ i.2).symm
  rcases Nat.eq_zero_or_pos (Fintype.card (GVert D)) with hn | hn
  · -- degenerate case: no vertices
    rw [hn, Nat.cast_zero, zero_pow (by omega : 2 * ℓ + 2 ≠ 0)]
    simp only [div_zero, zero_div]
    exact Nat.cast_nonneg _
  · -- main case
    set e : GVert D ≃ Fin (Fintype.card (GVert D)) := Fintype.equivFin (GVert D) with he
    set B : Matrix (Fin (Fintype.card (GVert D))) (Fin (Fintype.card (GVert D))) ℝ :=
      Matrix.reindex e e A with hB
    have hAsymm : ∀ i j : GVert D, A i j = A j i := by
      intro i j
      rw [hAent i j, hAent j i]
      by_cases h : GAdjQ D q i j
      · rw [ite_eq_left h, ite_eq_left ((GAdjQ_symm D q i j).mp h)]
      · rw [ite_eq_right h, ite_eq_right (fun hh => h ((GAdjQ_symm D q i j).mpr hh))]
    have hBent : ∀ i j : Fin (Fintype.card (GVert D)), B i j = A (e.symm i) (e.symm j) := by
      intro i j
      rw [hB, Matrix.reindex_apply, Matrix.submatrix_apply]
    have hBpow : ∀ i : Fin (Fintype.card (GVert D)),
        (B ^ ℓ) i i = (A ^ ℓ) (e.symm i) (e.symm i) := by
      intro i
      rw [hB]
      exact pow_reindex A e ℓ i i
    have hBsymm : B.transpose = B := by
      ext i j
      rw [Matrix.transpose_apply, hBent j i, hBent i j]
      exact hAsymm (e.symm j) (e.symm i)
    have hBnn : ∀ i j, 0 ≤ B i j := by
      intro i j
      rw [hBent i j, hAent (e.symm i) (e.symm j)]
      split <;> norm_num
    have hbc := bike_count (A := B) hn hBsymm hBnn hℓ
    have hSB : (∑ i : Fin (Fintype.card (GVert D)), ∑ j : Fin (Fintype.card (GVert D)), B i j)
        = ∑ i : GVert D, ∑ j : GVert D, A i j := by
      have h : (∑ i : Fin (Fintype.card (GVert D)), ∑ j : Fin (Fintype.card (GVert D)), B i j)
          = ∑ i : Fin (Fintype.card (GVert D)), ∑ j : Fin (Fintype.card (GVert D)),
              A (e.symm i) (e.symm j) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hBent i j]
      rw [h]
      exact sum_sum_reindex (fun i j : GVert D => A i j) e
    have hMB : (∑ i : Fin (Fintype.card (GVert D)), ∑ j : Fin (Fintype.card (GVert D)),
          B i j * (B ^ ℓ) i i * (B ^ ℓ) j j)
        = ∑ i : GVert D, ∑ j : GVert D, A i j * (A ^ ℓ) i i * (A ^ ℓ) j j := by
      have h : (∑ i : Fin (Fintype.card (GVert D)), ∑ j : Fin (Fintype.card (GVert D)),
            B i j * (B ^ ℓ) i i * (B ^ ℓ) j j)
          = ∑ i : Fin (Fintype.card (GVert D)), ∑ j : Fin (Fintype.card (GVert D)),
              A (e.symm i) (e.symm j) * (A ^ ℓ) (e.symm i) (e.symm i)
                * (A ^ ℓ) (e.symm j) (e.symm j) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hBent i j, hBpow i, hBpow j]
      rw [h]
      exact sum_sum_reindex (fun i j : GVert D => A i j * (A ^ ℓ) i i * (A ^ ℓ) j j) e
    have h1 : (∑ i : GVert D, ∑ j : GVert D, A i j) ^ (2 * ℓ + 1) /
          (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2)
        ≤ ∑ i : GVert D, ∑ j : GVert D, A i j * (A ^ ℓ) i i * (A ^ ℓ) j j := by
      rw [hSB, hMB] at hbc
      exact hbc
    have h2 : (∑ i : GVert D, ∑ j : GVert D, A i j * (A ^ ℓ) i i * (A ^ ℓ) j j) / 2
        ≤ ((bikeSet D q ℓ).card : ℝ) := by
      have h3 : (∑ i : GVert D, ∑ j : GVert D, A i j * (A ^ ℓ) i i * (A ^ ℓ) j j)
          = ∑ i : GVert D, ∑ j : GVert D,
              (if GAdjQ D q i j then (1 : ℝ) else 0) * g i.1 * g j.1 := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hpow i, hpow j, hAent i j]
      have h4 := sum_adj_le_edges D q g hgnn
      have h5 : (∑ e ∈ D.edges.filter (fun e => q ∈ edgeS D e), g e.x₁ * g e.x₂)
          = ((bikeSet D q ℓ).card : ℝ) := by
        rw [card_bikeSet, hg]
        push_cast
        rfl
      rw [h3]
      linarith
    have hdiv : ((∑ i : GVert D, ∑ j : GVert D, A i j) ^ (2 * ℓ + 1) /
          (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2)) / 2
        ≤ (∑ i : GVert D, ∑ j : GVert D, A i j * (A ^ ℓ) i i * (A ^ ℓ) j j) / 2 := by
      linarith
    exact le_trans hdiv h2

end Work.BMF
