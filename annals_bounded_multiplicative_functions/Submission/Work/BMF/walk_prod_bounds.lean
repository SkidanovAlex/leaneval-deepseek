import Mathlib
import Submission.Work.BMF.adi_all_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- Bounds for a product of naturals over `Fin ℓ`: if every factor lies between `a` and `b`,
then so does the product (with `a ≥ 0` needed only for the lower bound). -/
private lemma fin_prod_cast_bounds {ℓ : ℕ} {g : Fin ℓ → ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hlo : ∀ j, a ≤ (g j : ℝ)) (hhi : ∀ j, (g j : ℝ) ≤ b) :
    a ^ ℓ ≤ ((∏ j : Fin ℓ, g j : ℕ) : ℝ) ∧
      ((∏ j : Fin ℓ, g j : ℕ) : ℝ) ≤ b ^ ℓ := by
  have hcast : ((∏ j : Fin ℓ, g j : ℕ) : ℝ) = ∏ j : Fin ℓ, (g j : ℝ) := by
    rw [Nat.cast_prod]
  constructor
  · rw [hcast]
    calc a ^ ℓ = ∏ _j : Fin ℓ, a := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j : Fin ℓ, (g j : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro j _; exact ha
          · intro j _; exact hlo j
  · rw [hcast]
    calc ∏ j : Fin ℓ, (g j : ℝ) ≤ ∏ _j : Fin ℓ, b := by
          apply Finset.prod_le_prod₀
          · intro j _; positivity
          · intro j _; exact hhi j
      _ = b ^ ℓ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem walk_prod_bounds {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : Work.BMF.QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) {q ℓ : ℕ} {x : ℝ}
    {W : Fin (ℓ + 1) → Work.BMF.GVert D}
    (hW : W ∈ Work.BMF.closedWalkVal D q ℓ x) :
    P₁ ^ ℓ ≤ ((Work.BMF.walkProdV D ℓ W : ℕ) : ℝ) ∧
      ((Work.BMF.walkProdV D ℓ W : ℕ) : ℝ) ≤ (2 * P₁) ^ ℓ ∧
      P₁ ^ ℓ ≤ ((Work.BMF.walkProdU D ℓ W : ℕ) : ℝ) ∧
      ((Work.BMF.walkProdU D ℓ W : ℕ) : ℝ) ≤ (2 * P₁) ^ ℓ ∧
      0 < Work.BMF.walkProdV D ℓ W ∧ 0 < Work.BMF.walkProdU D ℓ W := by
  classical
  -- Extract the adjacency of consecutive vertices from the `closedWalkVal` membership.
  have hadj : ∀ j : Fin ℓ, GAdjQ D q (W j.castSucc) (W j.succ) := by
    have h1 : W ∈ walkSet D q ℓ := by
      have h2 := hW
      rw [closedWalkVal, Finset.mem_filter] at h2
      exact h2.1
    simp only [walkSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    exact h1
  -- Each step prime lies in `[P₁, 2 P₁]`.
  have hV := fin_prod_cast_bounds (ℓ := ℓ) (g := fun j => stepV D (W j.castSucc) (W j.succ))
    (a := P₁) (b := 2 * P₁) hP.le (fun j => (stepV_prime D (hadj j)).2.1)
    (fun j => (stepV_prime D (hadj j)).2.2)
  have hU := fin_prod_cast_bounds (ℓ := ℓ) (g := fun j => stepU D (W j.castSucc) (W j.succ))
    (a := P₁) (b := 2 * P₁) hP.le (fun j => (stepU_prime D (hadj j)).2.1)
    (fun j => (stepU_prime D (hadj j)).2.2)
  have hVpos : 0 < walkProdV D ℓ W := by
    rw [walkProdV]
    apply Finset.prod_pos
    intro j _
    have h : (0:ℝ) < (stepV D (W j.castSucc) (W j.succ) : ℕ) := by
      have := (stepV_prime D (hadj j)).2.1; linarith
    exact Nat.cast_pos.mp h
  have hUpos : 0 < walkProdU D ℓ W := by
    rw [walkProdU]
    apply Finset.prod_pos
    intro j _
    have h : (0:ℝ) < (stepU D (W j.castSucc) (W j.succ) : ℕ) := by
      have := (stepU_prime D (hadj j)).2.1; linarith
    exact Nat.cast_pos.mp h
  refine ⟨?_, ?_, ?_, ?_, hVpos, hUpos⟩
  · rw [walkProdV]; exact hV.1
  · rw [walkProdV]; exact hV.2
  · rw [walkProdU]; exact hU.1
  · rw [walkProdU]; exact hU.2

end Work.BMF
