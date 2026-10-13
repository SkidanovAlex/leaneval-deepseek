import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Reindexing along a coordinate equivalence

`SemiPf.reindex e` renames the coordinates of a semi-Pfaffian set along an
equivalence `e : Fin k ≃ Fin K`.  The lemmas below record that this is the
"pull back along `e`" operation: reindexed chain functions, `EA`-polynomials and
basic sets evaluate at `y` exactly as the original ones evaluate at
`fun i => y (e i)`. -/

/-- The chain functions of a reindexed chain are the old chain functions
precomposed with the coordinate change. -/
theorem EAChain.reindex_ell {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r)
    (j : Fin r) (y : Fin K → ℝ) :
    (EAChain.reindex e c).ell j y = c.ell j (fun i => y (e i)) := by
  unfold EAChain.ell EAChain.reindex
  rw [← Equiv.sum_comp e.symm (fun i : Fin k => c.a j i * y (e i))]
  simp

/-- Evaluating a reindexed `EA`-polynomial in the reindexed chain at `y` is the
same as evaluating the original polynomial in the original chain at the
reindexed point `fun i => y (e i)`. -/
theorem eaEval_reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r)
    (Q : EAPoly k r) (y : Fin K → ℝ) :
    eaEval (EAChain.reindex e c) (EAPoly.reindex e Q) y = eaEval c Q (fun i => y (e i)) := by
  have hpt : (Sum.elim y (fun j => Real.exp ((EAChain.reindex e c).ell j y)) ∘ Sum.map e id)
      = Sum.elim (fun i => y (e i)) (fun j => Real.exp (c.ell j (fun i => y (e i)))) := by
    funext s
    rcases s with i | j
    · rfl
    · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr, id_eq]
      rw [EAChain.reindex_ell]
  simp only [eaEval, EAPoly.reindex, MvPolynomial.eval_rename, hpt]

/-- Membership in the cube is invariant under reindexing the coordinates. -/
theorem cubeC_reindex {k K : ℕ} (e : Fin k ≃ Fin K) (y : Fin K → ℝ) :
    y ∈ cubeC K ↔ (fun i => y (e i)) ∈ cubeC k := by
  simp only [cubeC, Set.mem_setOf_eq]
  constructor
  · intro h i; exact h (e i)
  · intro h i; simpa using h (e.symm i)

/-- A reindexed basic set holds at `y` exactly when the original basic set holds
at the reindexed point. -/
theorem Basic.holds_reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r)
    (B : Basic k r) (y : Fin K → ℝ) :
    (Basic.reindex e B).holds (EAChain.reindex e c) y ↔ B.holds c (fun i => y (e i)) := by
  simp only [Basic.holds, Basic.reindex]
  constructor
  · intro h
    exact ⟨fun f hf => by
        have h' := h.1 (EAPoly.reindex e f) (List.mem_map_of_mem hf)
        rwa [eaEval_reindex e c f y] at h',
      fun g hg => by
        have h' := h.2 (EAPoly.reindex e g) (List.mem_map_of_mem hg)
        rwa [eaEval_reindex e c g y] at h'⟩
  · intro h
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
      rw [eaEval_reindex e c f₀ y]
      exact h.1 f₀ hf₀
    · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
      rw [eaEval_reindex e c g₀ y]
      exact h.2 g₀ hg₀

theorem reindex_eval :
    (∀ {k K r : ℕ} (e : Fin k ≃ Fin K) (c : WilkiesDesign.E.EAChain k r)
        (Q : WilkiesDesign.E.EAPoly k r) (y : Fin K → ℝ),
        WilkiesDesign.E.eaEval (Work.WilE7.EAChain.reindex e c) (Work.WilE7.EAPoly.reindex e Q) y =
          WilkiesDesign.E.eaEval c Q (fun i => y (e i))) ∧
    (∀ {k K : ℕ} (e : Fin k ≃ Fin K) (X : WilkiesDesign.E.SemiPf k),
        (Work.WilE7.SemiPf.reindex e X).set = {y | (fun i => y (e i)) ∈ X.set}) := by
  constructor
  · intro k K r e c Q y
    exact eaEval_reindex e c Q y
  · intro k K e X
    ext y
    simp only [SemiPf.set, SemiPf.reindex, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, B, hB, hB'⟩
      obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
      exact ⟨(cubeC_reindex e y).mp h1, B₀, hB₀, (Basic.holds_reindex e X.c B₀ y).mp hB'⟩
    · rintro ⟨h1, B, hB, hB'⟩
      exact ⟨(cubeC_reindex e y).mpr h1, Basic.reindex e B,
        List.mem_map.mpr ⟨B, hB, rfl⟩, (Basic.holds_reindex e X.c B y).mpr hB'⟩

end Work.WilE7
