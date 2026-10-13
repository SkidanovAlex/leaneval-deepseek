import Mathlib

namespace Work.WilC4aP

/-- The map sending a point `q : ℂ × ℂ` to the family of distances `i ↦ ‖q.2 - η i q.1‖`. -/
noncomputable def sheetNormVec {m : ℕ} (η : Fin m → ℂ → ℂ) (q : ℂ × ℂ) : Fin m → ℝ :=
  fun i => ‖q.2 - η i q.1‖

lemma isOpen_sheet {m : ℕ} {η : Fin m → ℂ → ℂ} {z₀ : ℂ} {ρ ρ' : ℝ} {k : Fin m}
    (hcont : ∀ j, ContinuousOn (η j) (Metric.ball z₀ ρ)) (hρ' : ρ' ≤ ρ) :
    IsOpen {q : ℂ × ℂ | ‖q.1 - z₀‖ < ρ' ∧
      ∀ i, i ≠ k → ‖q.2 - η i q.1‖ > ‖q.2 - η k q.1‖} := by
  -- The open condition `‖q.1 - z₀‖ < ρ'`.
  have hAopen : IsOpen {q : ℂ × ℂ | ‖q.1 - z₀‖ < ρ'} :=
    isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_const)) continuous_const
  -- On that set, each `q ↦ η i q.1` is continuous, hence so is `sheetNormVec η`.
  have hΦcont : ContinuousOn (sheetNormVec η) {q : ℂ × ℂ | ‖q.1 - z₀‖ < ρ'} := by
    rw [continuousOn_pi]
    intro i
    have h1 : ContinuousOn (fun q : ℂ × ℂ => η i q.1) {q : ℂ × ℂ | ‖q.1 - z₀‖ < ρ'} := by
      have hmaps : Set.MapsTo (fun q : ℂ × ℂ => q.1) {q | ‖q.1 - z₀‖ < ρ'}
          (Metric.ball z₀ ρ) := by
        intro q hq
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_lt_of_le hq hρ'
      exact (hcont i).comp continuous_fst.continuousOn hmaps
    have h2 : ContinuousOn (fun q : ℂ × ℂ => q.2) {q : ℂ × ℂ | ‖q.1 - z₀‖ < ρ'} :=
      continuous_snd.continuousOn
    exact (h2.sub h1).norm
  -- The set of `f : Fin m → ℝ` whose `k`-th coordinate is strictly minimal is open.
  have hUopen : IsOpen {f : Fin m → ℝ | ∀ i, i ≠ k → f i > f k} := by
    have hEq : {f : Fin m → ℝ | ∀ i, i ≠ k → f i > f k}
        = ⋂ j : {i : Fin m // i ≠ k}, {f : Fin m → ℝ | f j.1 > f k} := by
      ext f; simp [Set.mem_iInter]
    rw [hEq]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (continuous_apply k) (continuous_apply j.1)
  have hmain : IsOpen ({q : ℂ × ℂ | ‖q.1 - z₀‖ < ρ'} ∩
      (sheetNormVec η) ⁻¹' {f : Fin m → ℝ | ∀ i, i ≠ k → f i > f k}) :=
    ContinuousOn.isOpen_inter_preimage hΦcont hAopen hUopen
  convert hmain using 1
  ext q
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, sheetNormVec]

end Work.WilC4aP
