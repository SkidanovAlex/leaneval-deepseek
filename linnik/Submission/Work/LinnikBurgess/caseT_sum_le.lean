import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_aux.caseT_defs
import Submission.Work.LinnikBurgess.frame_count_prov_helpers
import Submission.Work.LinnikBurgess.caseT_aux_defs
import Submission.Work.LinnikBurgess.exists_fin3_decomp
import Submission.Work.LinnikBurgess.frame_count_prov_aux.bsum_expansion
import Submission.Work.LinnikBurgess.frame_count_prov_aux.sum_box3_eq_iterate

/-!
# The Case-T divisor-expansion inequality (`caseT_sum_le`)

The statement bounds the Case-T part of the frame count.  For each pivot `x0` the two pinned
values `x1, x2` (both `≠ x0`) contribute the squared weights `(wg m x0 x1)^2 (wg m x0 x2)^2`,
the free slot value `γ` contributes `wg m x0 γ`, and the three distances `del x0 x1, del x0 x2,
del x0 γ` must have product divisible by `g`.  The right-hand side is the standard divisor
expansion: sum over the ordered factorisations `a : Fin 3 → ℕ` of `g = a 0 * a 1 * a 2` of the
product of the single-coordinate sums `Asum` (squares of the weight over `a 0 ∣ del x0 x1`),
`Asum` (over `a 1 ∣ del x0 x2`) and `Bsum` (the weight over `a 2 ∣ del x0 γ`).

The proof is the divisor expansion `bsum_expansion`: every admissible triple `(x1,x2,γ)` admits
*some* factorisation `g = a 0 * a 1 * a 2` with `a k ∣ del x0 (b k)`, so the indicator of
`g ∣ ∏_k del x0 (b k)` is bounded by the sum over factorisations of the indicators
`a k ∣ del x0 (b k)`; expanding the product of the resulting sums and reindexing gives the
right-hand side.  The left-hand side is first rewritten as the box sum appearing in
`bsum_expansion` (`sum_box3_eq_iterate` + `Finset.mul_sum`).
-/

namespace Work.LinnikBurgess

open scoped BigOperators
open Classical

/-- The Case-T coordinate weights: the two pinned coordinates carry the square
`(wg m x0 ·)^2`, the free coordinate carries `wg m x0 ·`. -/
private noncomputable def caseT_F (m x0 : ℕ) : Fin 3 → ℕ → ℝ :=
  fun k y => if k = 0 ∨ k = 1 then (wg m x0 y) ^ 2 else wg m x0 y

private lemma caseT_F_nonneg (m x0 : ℕ) : ∀ k y, 0 ≤ caseT_F m x0 k y := by
  intro k y
  simp only [caseT_F]
  split_ifs with h
  · exact sq_nonneg _
  · exact wg_nonneg m x0 y

private lemma caseT_F_zero (m x0 y : ℕ) : caseT_F m x0 0 y = (wg m x0 y) ^ 2 := by
  simp [caseT_F]

private lemma caseT_F_one (m x0 y : ℕ) : caseT_F m x0 1 y = (wg m x0 y) ^ 2 := by
  simp [caseT_F]

private lemma caseT_F_two (m x0 y : ℕ) : caseT_F m x0 2 y = wg m x0 y := by
  simp [caseT_F]

private lemma prod_del_vec (x0 x1 x2 γ : ℕ) :
    (∏ k : Fin 3, del x0 (![x1, x2, γ] k))
      = del x0 x1 * del x0 x2 * del x0 γ := by
  rw [Fin.prod_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

private lemma prod_if_vec (m x0 x1 x2 γ : ℕ) :
    (∏ k : Fin 3, (if ![x1, x2, γ] k ≠ x0 then caseT_F m x0 k (![x1, x2, γ] k) else 0))
      = (if x1 ≠ x0 then (wg m x0 x1) ^ 2 else 0)
        * (if x2 ≠ x0 then (wg m x0 x2) ^ 2 else 0)
        * (if γ ≠ x0 then wg m x0 γ else 0) := by
  rw [Fin.prod_univ_three]
  simp [caseT_F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

/-- Pointwise identity: the Case-T product of indicators/weights equals the box-weight form. -/
private lemma ite_mul_ite_caseT (g m x0 x1 x2 γ : ℕ) :
    (if x1 ≠ x0 ∧ x2 ≠ x0 then (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2 else 0)
      * (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)
    = (if g ∣ del x0 x1 * del x0 x2 * del x0 γ
        then (if x1 ≠ x0 then (wg m x0 x1) ^ 2 else 0)
              * (if x2 ≠ x0 then (wg m x0 x2) ^ 2 else 0)
              * (if γ ≠ x0 then wg m x0 γ else 0)
        else 0) := by
  by_cases h1 : x1 = x0 <;> by_cases h2 : x2 = x0 <;> by_cases h3 : γ = x0 <;>
    by_cases h4 : g ∣ del x0 x1 * del x0 x2 * del x0 γ <;> simp_all

/-- Each factor of the `bsum_expansion` right-hand side is the corresponding `Asum`/`Bsum`. -/
private lemma prod_filter_eq (H m x0 : ℕ) (a : Fin 3 → ℕ) :
    (∏ k : Fin 3,
        ∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x0 ∧ a k ∣ del x0 y),
          caseT_F m x0 k y)
      = frame_count_prov_aux.Asum H m (a 0) x0 * frame_count_prov_aux.Asum H m (a 1) x0
          * frame_count_prov_aux.Bsum H m (a 2) x0 := by
  rw [Fin.prod_univ_three]
  have h0 : (∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x0 ∧ a 0 ∣ del x0 y),
        caseT_F m x0 0 y) = frame_count_prov_aux.Asum H m (a 0) x0 := by
    rw [Finset.sum_filter, frame_count_prov_aux.Asum]
    exact Finset.sum_congr rfl (fun y _ => by rw [caseT_F_zero])
  have h1 : (∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x0 ∧ a 1 ∣ del x0 y),
        caseT_F m x0 1 y) = frame_count_prov_aux.Asum H m (a 1) x0 := by
    rw [Finset.sum_filter, frame_count_prov_aux.Asum]
    exact Finset.sum_congr rfl (fun y _ => by rw [caseT_F_one])
  have h2 : (∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x0 ∧ a 2 ∣ del x0 y),
        caseT_F m x0 2 y) = frame_count_prov_aux.Bsum H m (a 2) x0 := by
    rw [Finset.sum_filter, frame_count_prov_aux.Bsum]
    exact Finset.sum_congr rfl (fun y _ => by rw [caseT_F_two])
  rw [h0, h1, h2]

/-- The Case-T sum for a fixed pivot `x0`, bounded by the divisor expansion. -/
private lemma caseT_x0_le {H m g : ℕ} (hg : 0 < g) (x0 : ℕ) :
    (∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
        (if x1 ≠ x0 ∧ x2 ≠ x0 then (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2 else 0)
        * ∑ γ ∈ Finset.Icc 1 H,
            (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0))
      ≤ ∑ a ∈ Afact g, frame_count_prov_aux.Asum H m (a 0) x0
          * frame_count_prov_aux.Asum H m (a 1) x0 * frame_count_prov_aux.Bsum H m (a 2) x0 := by
  classical
  calc (∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
        (if x1 ≠ x0 ∧ x2 ≠ x0 then (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2 else 0)
        * ∑ γ ∈ Finset.Icc 1 H,
            (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0))
      = ∑ b ∈ box3 H, (if g ∣ ∏ k : Fin 3, del x0 (b k) then
            ∏ k : Fin 3, (if b k ≠ x0 then caseT_F m x0 k (b k) else 0) else 0) := by
        rw [frame_count_prov_aux.sum_box3_eq_iterate H]
        refine Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => ?_))
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun γ _ => ?_)
        rw [ite_mul_ite_caseT g m x0 x1 x2 γ, prod_del_vec, prod_if_vec]
    _ ≤ ∑ a ∈ (Fintype.piFinset (fun _ : Fin 3 => g.divisors)).filter
            (fun a : Fin 3 → ℕ => ∏ k : Fin 3, a k = g),
          ∏ k : Fin 3,
            ∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x0 ∧ a k ∣ del x0 y),
              caseT_F m x0 k y :=
        frame_count_prov_aux.bsum_expansion (g := g) (α := x0) (H := H) hg
          (caseT_F m x0) (caseT_F_nonneg m x0)
    _ = ∑ a ∈ Afact g, frame_count_prov_aux.Asum H m (a 0) x0
          * frame_count_prov_aux.Asum H m (a 1) x0 * frame_count_prov_aux.Bsum H m (a 2) x0 := by
        refine Finset.sum_congr rfl (fun a _ => prod_filter_eq H m x0 a)

theorem caseT_sum_le {H m g : ℕ} (hg : 0 < g) :
    (∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
        (if x1 ≠ x0 ∧ x2 ≠ x0
          then (Work.LinnikBurgess.wg m x0 x1) ^ 2 * (Work.LinnikBurgess.wg m x0 x2) ^ 2
          else 0)
          * ∑ γ ∈ Finset.Icc 1 H,
              (if γ ≠ x0 ∧ g ∣ Work.LinnikBurgess.del x0 x1 * Work.LinnikBurgess.del x0 x2
                  * Work.LinnikBurgess.del x0 γ
                then Work.LinnikBurgess.wg m x0 γ else 0))
      ≤ ∑ x0 ∈ Finset.Icc 1 H, ∑ a ∈ Work.LinnikBurgess.Afact g,
          Work.LinnikBurgess.frame_count_prov_aux.Asum H m (a 0) x0
            * Work.LinnikBurgess.frame_count_prov_aux.Asum H m (a 1) x0
            * Work.LinnikBurgess.frame_count_prov_aux.Bsum H m (a 2) x0 := by
  classical
  refine Finset.sum_le_sum (fun x0 _ => ?_)
  exact caseT_x0_le hg x0

end Work.LinnikBurgess
