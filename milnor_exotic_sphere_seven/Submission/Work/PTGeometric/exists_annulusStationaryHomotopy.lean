import Mathlib
import Submission.Work.Stems.exists_collapsingMap
import Submission.Work.PTGeometric.exists_sphereHomotopy
import Submission.Work.PTGeometric.exists_stationary_reparam

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric

/-- Collapsing the boundary of the cube and then reparametrising in time so that the homotopy is
stationary on `[0, 1/2]`.

Given `H : I × Iⁿ → T` which is constant on the boundary `∂Iⁿ` of the cube for every time and
which is constant (equal to `y₀`) at time `1`, this produces the collapse `φ : Iⁿ → Sⁿ` of the cube
boundary to a point together with a homotopy `Hbar` out of `Sⁿ × I` such that

* `Hbar (φ y, 0) = H (0, y)`,
* `Hbar` is stationary in time for `t ≤ 1/2`, i.e. `Hbar (s, t) = Hbar (s, 0)`, and
* `Hbar (s, 1) = y₀`.

The construction is the composition of `exists_sphereHomotopy` (descent of `H` along the collapse
`φ` of `exists_collapsingMap`) with the time reparametrisation `exists_stationary_reparam`. -/
theorem exists_annulusStationaryHomotopy {n : ℕ} (hn : 1 ≤ n) {T : Type} [TopologicalSpace T] {y₀ : T}
    (H : C(Set.Icc (0 : ℝ) 1 × (Fin n → Set.Icc (0 : ℝ) 1), T))
    (hH : ∀ (t : Set.Icc (0 : ℝ) 1) (y : Fin n → Set.Icc (0 : ℝ) 1),
      y ∈ _root_.Cube.boundary (Fin n) → H (t, y) = y₀)
    (hH1 : ∀ y : Fin n → Set.Icc (0 : ℝ) 1, H (1, y) = y₀) :
    ∃ (φ : C(Fin n → Set.Icc (0 : ℝ) 1,
        _root_.Metric.sphere (0 : _root_.EuclideanSpace ℝ (Fin (n + 1))) 1))
      (Hbar : C(_root_.Metric.sphere (0 : _root_.EuclideanSpace ℝ (Fin (n + 1))) 1
        × Set.Icc (0 : ℝ) 1, T)),
      (∀ (y : Fin n → Set.Icc (0 : ℝ) 1)
        (s : _root_.Metric.sphere (0 : _root_.EuclideanSpace ℝ (Fin (n + 1))) 1),
        φ y = s → Hbar (s, 0) = H (0, y)) ∧
      (∀ (s : _root_.Metric.sphere (0 : _root_.EuclideanSpace ℝ (Fin (n + 1))) 1)
        (t : Set.Icc (0 : ℝ) 1), (t : ℝ) ≤ 1 / 2 → Hbar (s, t) = Hbar (s, 0)) ∧
      (∀ s : _root_.Metric.sphere (0 : _root_.EuclideanSpace ℝ (Fin (n + 1))) 1, Hbar (s, 1) = y₀) := by
  classical
  -- the collapse of the cube boundary to a point
  obtain ⟨φ, hφ, _hφ0, hφfib⟩ := Work.Stems.exists_collapsingMap n hn
  -- descend `H` along `φ` to a homotopy out of the sphere
  obtain ⟨Hbar₀, hHbar₀, hHbar₀_one⟩ := exists_sphereHomotopy hn φ hφ hφfib H hH hH1
  -- reparametrise in time so that the homotopy is stationary on `[0, 1/2]`
  obtain ⟨Hbar, hstat, hHbar_zero, _hHbar_late⟩ := exists_stationary_reparam Hbar₀
  refine ⟨φ, Hbar, ?_, ?_, ?_⟩
  · intro y s hys
    have h0 : Hbar (s, 0) = Hbar₀ (s, 0) := hstat s 0 (by norm_num)
    rw [h0, ← hys]
    exact hHbar₀ y 0
  · intro s t ht
    exact (hstat s t ht).trans (hstat s 0 (by norm_num)).symm
  · intro s
    rw [hHbar_zero s]
    exact hHbar₀_one s

end Work.PTGeometric
