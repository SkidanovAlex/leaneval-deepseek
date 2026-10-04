import Mathlib
import Submission.Work.Diff.EXT.chartData_step_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- **Value bound for determinants.** -/
theorem det_value_bound {N : ℕ} (B : ℝ) (hB : 0 ≤ B)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : ∀ r c, ‖A r c‖ ≤ B) :
    ‖A.det‖ ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * B ^ N := by
  rw [Matrix.det_apply']
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ σ : Equiv.Perm (Fin N),
      ‖((↑(↑(Equiv.Perm.sign σ) : ℤ)) : ℝ) * ∏ i : Fin N, A (σ i) i‖ ≤ 1 * B ^ N := by
    intro σ
    have hc : ‖((↑(↑(Equiv.Perm.sign σ) : ℤ)) : ℝ)‖ ≤ 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    rw [norm_mul]
    refine mul_le_mul hc ?_ (by positivity) (by norm_num)
    calc ‖∏ i : Fin N, A (σ i) i‖ = ∏ i : Fin N, ‖A (σ i) i‖ := norm_prod _ _
      _ ≤ ∏ _i : Fin N, B := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hA _ _)
      _ = B ^ N := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ∑ σ : Equiv.Perm (Fin N), ‖((↑(↑(Equiv.Perm.sign σ) : ℤ)) : ℝ) * ∏ i : Fin N, A (σ i) i‖
      ≤ ∑ _σ : Equiv.Perm (Fin N), 1 * B ^ N := Finset.sum_le_sum fun σ _ => hterm σ
    _ = (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * B ^ N := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **Jet bounds for the determinant of a smooth matrix family.** -/
theorem exists_det_jets_bound (k : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
      (x : E),
      (∀ (r c : Fin (Module.finrank ℝ E)), ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y r c) x) →
      (∀ (r c : Fin (Module.finrank ℝ E)), ∀ m ≤ k,
        ‖iteratedFDeriv ℝ m (fun y => A y r c) x‖ ≤ B) →
      ∀ m ≤ k, ‖iteratedFDeriv ℝ m (fun y => (A y).det) x‖ ≤ C := by
  classical
  set B' : ℝ := max 1 B with hB'def
  have hB'0 : 0 ≤ B' := le_trans zero_le_one (le_max_left _ _)
  have hBB' : B ≤ B' := le_max_right _ _
  obtain ⟨Cp, hCp0, hCp⟩ := exists_jets_finset_prod_bound (E := E) k
    (Finset.univ : Finset (Fin (Module.finrank ℝ E))) B' hB'0
  set B'' : ℝ := max B' Cp with hB''def
  have hB''0 : 0 ≤ B'' := le_trans hB'0 (le_max_left _ _)
  have hB'B'' : B' ≤ B'' := le_max_left _ _
  have hCpB'' : Cp ≤ B'' := le_max_right _ _
  refine ⟨(Fintype.card (Equiv.Perm (Fin (Module.finrank ℝ E))) : ℝ) * ((2 : ℝ) ^ k * B'' * B''),
    ?_, fun A x hA hb m hm => ?_⟩
  · positivity
  · have hsign : ∀ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        ‖((↑(↑(Equiv.Perm.sign σ) : ℤ)) : ℝ)‖ ≤ 1 := by
      intro σ
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    have hexp : (fun y : E => (A y).det) = fun y =>
        ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          ((↑(↑(Equiv.Perm.sign σ) : ℤ)) : ℝ) * ∏ i : Fin (Module.finrank ℝ E), A y (σ i) i := by
      funext y
      rw [Matrix.det_apply']
    rw [hexp]
    refine le_trans (norm_iteratedFDeriv_sum_le_at (E := E)
      (s := (Finset.univ : Finset (Equiv.Perm (Fin (Module.finrank ℝ E)))))
      (φ := fun σ y => ((↑(↑(Equiv.Perm.sign σ) : ℤ)) : ℝ)
        * ∏ i : Fin (Module.finrank ℝ E), A y (σ i) i)
      (x := x) (n := m) (C := (2 : ℝ) ^ k * B'' * B'') ?_ ?_) ?_
    · intro σ _
      refine ContDiffAt.mul contDiffAt_const ?_
      exact (hCp (fun i : Fin (Module.finrank ℝ E) => fun y => A y (σ i) i) x
        (fun i _ => hA (σ i) i) (fun i _ m' hm' => le_trans (hb (σ i) i m' hm') hBB')).1
    · intro σ _
      have hprod := hCp (fun i : Fin (Module.finrank ℝ E) => fun y => A y (σ i) i) x
        (fun i _ => hA (σ i) i) (fun i _ m' hm' => le_trans (hb (σ i) i m' hm') hBB')
      have hconst : ∀ m' ≤ k,
          ‖iteratedFDeriv ℝ m' (fun _ : E => ((↑(↑(Equiv.Perm.sign σ) : ℤ)) : ℝ)) x‖ ≤ B'' := by
        intro m' hm'
        by_cases hm0 : m' = 0
        · subst hm0
          rw [norm_iteratedFDeriv_zero]
          exact le_trans (hsign σ) (le_trans (le_max_left _ _) hB'B'')
        · rw [iteratedFDeriv_const_of_ne hm0]
          simpa using hB''0
      refine le_trans (norm_iteratedFDeriv_mul_le_at_le (k := k) (m := m) (B := B'') hm
        contDiffAt_const hprod.1 hB''0 hconst (fun m' hm' => le_trans (hprod.2 m' hm') hCpB'')) ?_
      exact le_rfl
    · simp only [Finset.card_univ, Fintype.card_perm]
      exact le_rfl

end Work.Diff.EXT
