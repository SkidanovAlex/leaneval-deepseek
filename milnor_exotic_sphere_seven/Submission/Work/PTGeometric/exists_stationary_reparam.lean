import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric

/-- The reparametrisation `φ(x) = min 1 (max 0 (4x - 2))` of the real line: it is `0` for
`x ≤ 1/2`, it is `1` for `x ≥ 3/4`, and it is continuous in between. -/
private def phiR (x : ℝ) : ℝ := min 1 (max 0 (4 * x - 2))

private theorem phiR_cont : Continuous phiR := by
  show Continuous fun x : ℝ => min 1 (max 0 (4 * x - 2))
  fun_prop

private theorem phiR_mem (t : ℝ) : phiR t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

private theorem phiR_eq_of_le (t : ℝ) (ht : t ≤ 1 / 2) : phiR t = 0 := by
  have hz : 4 * t - 2 ≤ 0 := by linarith
  show min 1 (max 0 (4 * t - 2)) = 0
  rw [max_eq_left hz, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

private theorem phiR_eq_of_ge (t : ℝ) (ht : 3 / 4 ≤ t) : phiR t = 1 := by
  have hz : (0 : ℝ) ≤ 4 * t - 2 := by linarith
  have h1 : (1 : ℝ) ≤ 4 * t - 2 := by linarith
  show min 1 (max 0 (4 * t - 2)) = 1
  rw [max_eq_right hz, min_eq_left h1]

/-- The reparametrisation of `[0,1]` induced by `phiR`. -/
private noncomputable def rho : C(Set.Icc (0 : ℝ) 1, Set.Icc (0 : ℝ) 1) where
  toFun t := ⟨phiR t, phiR_mem t⟩
  continuous_toFun :=
    Continuous.subtype_mk (f := fun t : Set.Icc (0 : ℝ) 1 => phiR (t : ℝ))
      (phiR_cont.comp continuous_subtype_val) (fun t => phiR_mem (t : ℝ))

private theorem rho_eq_zero (t : Set.Icc (0 : ℝ) 1) (ht : (t : ℝ) ≤ 1 / 2) : rho t = 0 :=
  Subtype.ext (phiR_eq_of_le (t : ℝ) ht)

private theorem rho_eq_one (t : Set.Icc (0 : ℝ) 1) (ht : 3 / 4 ≤ (t : ℝ)) : rho t = 1 :=
  Subtype.ext (phiR_eq_of_ge (t : ℝ) ht)

private theorem rho_one : rho 1 = 1 := by
  refine rho_eq_one 1 ?_
  show (3 : ℝ) / 4 ≤ (1 : ℝ)
  norm_num

theorem exists_stationary_reparam {n : ℕ} {T : Type} [TopologicalSpace T]
    (H : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (0 : ℝ) 1, T)) :
    ∃ H' : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (0 : ℝ) 1, T),
      (∀ (s : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (t : Set.Icc (0 : ℝ) 1),
        (t : ℝ) ≤ 1 / 2 → H' (s, t) = H (s, 0)) ∧
      (∀ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, H' (s, 1) = H (s, 1)) ∧
      (∀ (s : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (t : Set.Icc (0 : ℝ) 1),
        (3 / 4 : ℝ) ≤ (t : ℝ) → H' (s, t) = H (s, 1)) := by
  refine ⟨H.comp ((ContinuousMap.id _).prodMap rho), ?_, ?_, ?_⟩
  · intro s t ht
    show H (s, rho t) = H (s, 0)
    rw [rho_eq_zero t ht]
  · intro s
    show H (s, rho 1) = H (s, 1)
    rw [rho_one]
  · intro s t ht
    show H (s, rho t) = H (s, 1)
    rw [rho_eq_one t ht]

end Work.PTGeometric
