import Mathlib
import Submission.Work.Geo.Radial.RadialDefs

namespace Work.Geo.Radial

open Finset

theorem radRho_facts {n : ℕ} [NeZero n] :
    (∀ x : PL.E n, 0 ≤ radRho x) ∧
    (∀ (x : PL.E n) (i : Fin n), |x i| ≤ radRho x) ∧
    (∀ x : PL.E n, radRho x = 0 ↔ x = 0) ∧
    (∀ (c : ℝ) (x : PL.E n), 0 ≤ c → radRho (c • x) = c * radRho x) ∧
    (∀ (x : PL.E n) (r : ℝ), radRho x < r ↔ x ∈ ocubeAround 0 r) ∧
    (∀ (x : PL.E n) (r : ℝ), radRho x ≤ r ↔ x ∈ ccubeAround 0 r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `radRho` is the supremum of the nonnegative numbers `|x i|`, hence nonnegative.
    intro x
    rw [radRho]
    have hn : 0 < n := NeZero.pos n
    exact le_trans (abs_nonneg (x ⟨0, hn⟩))
      (Finset.le_sup' (fun i => |x i|) (Finset.mem_univ ⟨0, hn⟩))
  · -- Each coordinate bound is a lower bound of the supremum.
    intro x i
    rw [radRho]
    exact Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)
  · -- The supremum vanishes exactly when every coordinate vanishes.
    intro x
    constructor
    · intro h
      ext i
      have hle : |x i| ≤ 0 := by
        rw [radRho] at h
        rw [← h]
        exact Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    · intro h
      rw [h, radRho]
      simp
  · -- Positive homogeneity of the supremum under `c ≥ 0`.
    intro c x hc
    rw [radRho, radRho]
    have h1 : (Finset.univ.sup' Finset.univ_nonempty fun i => |(c • x) i|)
        = Finset.univ.sup' Finset.univ_nonempty fun i => c * |x i| := by
      apply Finset.sup'_congr _ rfl
      intro i _
      simp [abs_mul, abs_of_nonneg hc]
    rw [h1]
    exact (Finset.mul₀_sup' hc (fun i => |x i|) Finset.univ Finset.univ_nonempty).symm
  · -- Strict sublevel set of `radRho`: the open sup-norm cube.
    intro x r
    rw [radRho, mem_ocubeAround]
    rw [Finset.sup'_lt_iff]
    constructor
    · intro h i
      simpa using h i (Finset.mem_univ i)
    · intro h i _
      simpa using h i
  · -- Sublevel set of `radRho`: the closed sup-norm cube.
    intro x r
    rw [radRho, mem_ccubeAround]
    rw [Finset.sup'_le_iff]
    constructor
    · intro h i
      simpa using h i (Finset.mem_univ i)
    · intro h i _
      simpa using h i

end Work.Geo.Radial
