import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

theorem inner_coeff_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (e : Fin (Module.finrank ℝ V) → V) {Cl : ℝ} (hCl : 0 ≤ Cl)
    (hdiag : ∀ i, inner ℝ (e i) (e i) ≤ Cl)
    (hInv : ∀ i j, |(Matrix.of (fun i j => inner ℝ (e i) (e j)))⁻¹ i j| ≤ Cl) :
    ∀ (q : V) (i : Fin (Module.finrank ℝ V)),
      |∑ j, (Matrix.of (fun i j => inner ℝ (e i) (e j)))⁻¹ i j * inner ℝ (e j) q|
        ≤ (Module.finrank ℝ V : ℝ) * Cl * Real.sqrt Cl * ‖q‖ := by
  intro q i
  set A := (Matrix.of (fun i j => inner ℝ (e i) (e j)))⁻¹ with hA
  -- Each frame vector has norm at most `√Cl`.
  have hnorm : ∀ j, ‖e j‖ ≤ Real.sqrt Cl := by
    intro j
    rw [norm_eq_sqrt_real_inner]
    exact Real.sqrt_le_sqrt (hdiag j)
  -- Termwise bound: `|A i j * ⟨e j, q⟩| ≤ Cl * (√Cl * ‖q‖)`.
  have hterm : ∀ j, |A i j * inner ℝ (e j) q| ≤ Cl * (Real.sqrt Cl * ‖q‖) := by
    intro j
    rw [abs_mul]
    refine mul_le_mul (hInv i j) ?_ (abs_nonneg _) hCl
    calc |inner ℝ (e j) q| ≤ ‖e j‖ * ‖q‖ := abs_real_inner_le_norm _ _
      _ ≤ Real.sqrt Cl * ‖q‖ := mul_le_mul_of_nonneg_right (hnorm j) (norm_nonneg q)
  calc |∑ j, A i j * inner ℝ (e j) q|
      ≤ ∑ j, |A i j * inner ℝ (e j) q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, Cl * (Real.sqrt Cl * ‖q‖) := Finset.sum_le_sum (fun j _ => hterm j)
    _ = (Module.finrank ℝ V : ℝ) * (Cl * (Real.sqrt Cl * ‖q‖)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (Module.finrank ℝ V : ℝ) * Cl * Real.sqrt Cl * ‖q‖ := by ring

end Work.Diff.EXT.ConnCov
