import Mathlib
import Submission.Commons.Analysis.Inequalities.bonami_lemma_cube

namespace Commons.Analysis.Inequalities

open Finset BigOperators

theorem bonami_lemma_cube_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (f : (ι → ZMod 2) → ℂ)
    (h : ∀ S : Finset ι, d < S.card →
      (∑ x : ι → ZMod 2, f x * ∏ i ∈ S, ((-1 : ℂ) ^ (x i).val)) = 0) :
    (2 : ℝ) ^ Fintype.card ι * ∑ x : ι → ZMod 2, ‖f x‖ ^ 4 ≤
      (9 : ℝ) ^ d * (∑ x : ι → ZMod 2, ‖f x‖ ^ 2) ^ 2 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Φ : (Fin (Fintype.card ι) → ZMod 2) ≃ (ι → ZMod 2) :=
    Equiv.arrowCongr e.symm (Equiv.refl (ZMod 2))
  let f' : (Fin (Fintype.card ι) → ZMod 2) → ℂ := fun y => f (Φ y)
  have hΦ : ∀ y : Fin (Fintype.card ι) → ZMod 2, Φ y = fun i => y (e i) := by
    intro y; funext i; rfl
  have h' : ∀ S : Finset (Fin (Fintype.card ι)), d < S.card →
      (∑ y : Fin (Fintype.card ι) → ZMod 2,
        f' y * ∏ j ∈ S, ((-1 : ℂ) ^ (y j).val)) = 0 := by
    intro S hS
    have hcard : d < (S.map e.symm.toEmbedding).card := by
      rw [Finset.card_map]; exact hS
    have hkey := h (S.map e.symm.toEmbedding) hcard
    have hprod : ∀ y : Fin (Fintype.card ι) → ZMod 2,
        (∏ j ∈ S, ((-1 : ℂ) ^ (y j).val))
          = ∏ i ∈ S.map e.symm.toEmbedding, ((-1 : ℂ) ^ ((Φ y) i).val) := by
      intro y
      rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro j hj
      congr 1
      rw [hΦ]
      simp
    have hsplit : (∑ y, f' y * ∏ j ∈ S, ((-1 : ℂ) ^ (y j).val))
        = ∑ x, f x * ∏ i ∈ S.map e.symm.toEmbedding, ((-1 : ℂ) ^ (x i).val) := by
      refine Fintype.sum_equiv Φ (fun y => f' y * ∏ j ∈ S, ((-1 : ℂ) ^ (y j).val))
        (fun x => f x * ∏ i ∈ S.map e.symm.toEmbedding, ((-1 : ℂ) ^ (x i).val)) ?_
      intro y
      simp only [f']
      rw [hprod y]
    rw [hsplit]
    exact hkey
  have hb := bonami_lemma_cube (Fintype.card ι) d f' h'
  have hs4 : (∑ y : Fin (Fintype.card ι) → ZMod 2, ‖f' y‖ ^ 4)
      = ∑ x : ι → ZMod 2, ‖f x‖ ^ 4 := by
    refine Fintype.sum_equiv Φ (fun y => ‖f' y‖ ^ 4) (fun x => ‖f x‖ ^ 4) ?_
    intro y; simp only [f']
  have hs2 : (∑ y : Fin (Fintype.card ι) → ZMod 2, ‖f' y‖ ^ 2)
      = ∑ x : ι → ZMod 2, ‖f x‖ ^ 2 := by
    refine Fintype.sum_equiv Φ (fun y => ‖f' y‖ ^ 2) (fun x => ‖f x‖ ^ 2) ?_
    intro y; simp only [f']
  rw [hs4, hs2] at hb
  exact hb

end Commons.Analysis.Inequalities
