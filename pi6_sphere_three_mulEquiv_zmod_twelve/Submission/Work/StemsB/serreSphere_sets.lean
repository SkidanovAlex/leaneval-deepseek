import Mathlib
import Submission.Work.StemsB.SerreSphereDefs

set_option synthInstance.maxHeartbeats 400000

/-!
# The two-piece decomposition of the sphere model `SphModel n`: elementary set theory

This file discharges the elementary topological bookkeeping of the decomposition

* `P = sphLoopThick n = {∞} ∪ {v | 1/2 < ‖v‖}` (the outer thickening of the outer disc),
* `Q = sphLoopBig n = {v | ∀ i, |v i| < 3/2}` (the thick inner cube),

of the model `SphModel n = OnePoint ℝⁿ` of `Sⁿ` (`Submission/Work/StemsB/SphLoopModel.lean`):
both are **open**, they **cover** the model, and the shell point `sphShellPt n` (`1` in the first
coordinate) lies in the shell `sphLoopMid n = P ∩ Q`, hence in both pieces.

Mathematically this is where the two pieces come from: `sphLoopBig n` is an open cube (open as the
preimage of an open box under the coordinate projections), while `sphLoopThick n` is a neighbourhood
of `∞` whose complement is the compact set `{‖v‖ ≤ 1/2}` (so that `sphLoopThick n` is open by the
characterisation `OnePoint.isOpen_iff_of_mem` of open sets containing the extra point: the preimage
of the set under `OnePoint.some` must be open and its complement compact).  The covering property
uses `|v i| ≤ ‖v‖` (`PiLp.norm_apply_le`): a vector that is *not* in the thickening has
`‖v‖ ≤ 1/2`, hence every coordinate is at most `1/2 < 3/2` in absolute value.

The vector `serreSphereShellVec n` underlying the shell point is exhibited explicitly; the point
`∞` is *not* in the shell, and the hypothesis `1 ≤ n` in the main theorem is exactly what makes
`‖sphShellPt n‖ = 1` (for `n = 0` the shell point is the origin and the statement is false).
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

/-! ## The vector of the shell point -/

/-- The explicit vector underlying the shell point `sphShellPt n`: the first coordinate is `1` and
all others are `0`.  (It is `sphShellPt n` with the `OnePoint.some` stripped off.) -/
def serreSphereShellVec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0)

/-- `sphShellPt n` is `OnePoint.some` applied to `serreSphereShellVec n` — definitionally. -/
theorem serreSphereShellPt_eq (n : ℕ) :
    sphShellPt n = OnePoint.some (serreSphereShellVec n) := rfl

/-- The coordinates of `serreSphereShellVec n`. -/
theorem serreSphereShellVec_apply (n : ℕ) (i : Fin n) :
    serreSphereShellVec n i = if (i : ℕ) = 0 then (1 : ℝ) else 0 := by
  simp only [serreSphereShellVec, WithLp.equiv_symm_apply, WithLp.ofLp_toLp]

/-- The coordinates of the shell point are `1` and `0`. -/
theorem serreSphereShellVec_coord_lt (n : ℕ) (i : Fin n) :
    |serreSphereShellVec n i| < (3 : ℝ) / 2 := by
  rw [serreSphereShellVec_apply]
  split_ifs <;> norm_num

/-- The shell vector has norm at least `1` (its first coordinate is `1`). -/
theorem one_le_norm_serreSphereShellVec (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) ≤ ‖serreSphereShellVec n‖ := by
  have hle := PiLp.norm_apply_le (serreSphereShellVec n) (⟨0, hn⟩ : Fin n)
  have happ : serreSphereShellVec n (⟨0, hn⟩ : Fin n) = 1 := by
    rw [serreSphereShellVec_apply]
    simp
  rw [happ] at hle
  simpa using hle

/-! ## The two pieces are open -/

/-- The thick inner cube, as the image of the open cube `{|v i| < 3/2}` under `OnePoint.some`. -/
theorem serreSphere_sphLoopBig_eq_image (n : ℕ) :
    sphLoopBig n =
      (OnePoint.some : EuclideanSpace ℝ (Fin n) → SphModel n) '' {v | ∀ i, |v i| < 3 / 2} := by
  ext x
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, rfl, hv⟩

/-- **The thick inner cube is open.** -/
theorem serreSphere_isOpen_big (n : ℕ) : IsOpen (sphLoopBig n) := by
  rw [serreSphere_sphLoopBig_eq_image, OnePoint.isOpen_image_coe]
  have hset : {v : EuclideanSpace ℝ (Fin n) | ∀ i, |v i| < 3 / 2}
      = ⋂ i : Fin n, {v : EuclideanSpace ℝ (Fin n) | |v i| < 3 / 2} := by
    ext v
    simp
  rw [hset]
  exact isOpen_iInter_of_finite fun _ => isOpen_lt (by fun_prop) continuous_const

/-- **The outer thickening is open**: it contains `∞`, the preimage of the finite part is the open
set `{1/2 < ‖v‖}`, and its complement is the compact ball `{‖v‖ ≤ 1/2}`. -/
theorem serreSphere_isOpen_thick (n : ℕ) : IsOpen (sphLoopThick n) := by
  rw [show sphLoopThick n = {x : SphModel n |
      x = OnePoint.infty ∨ ∃ v : EuclideanSpace ℝ (Fin n), x = ↑v ∧ (1 / 2 : ℝ) < ‖v‖}
      from rfl]
  rw [OnePoint.isOpen_iff_of_mem (Or.inl rfl)]
  have hpre : OnePoint.some ⁻¹' {x : SphModel n |
      x = OnePoint.infty ∨ ∃ v : EuclideanSpace ℝ (Fin n), x = ↑v ∧ (1 / 2 : ℝ) < ‖v‖}
      = {v : EuclideanSpace ℝ (Fin n) | (1 / 2 : ℝ) < ‖v‖} := by
    ext v
    simp
  rw [hpre]
  have hball : ({v : EuclideanSpace ℝ (Fin n) | (1 / 2 : ℝ) < ‖v‖})ᶜ
      = Metric.closedBall 0 (1 / 2) := by
    ext v
    simp [Metric.closedBall, not_lt]
  rw [hball]
  exact ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩

/-! ## The two pieces cover the model -/

/-- **The thickening and the inner cube cover the model** (for every `n`): a vector outside the
thickening has norm `≤ 1/2`, hence every coordinate is `< 3/2` in absolute value. -/
theorem serreSphere_thick_union_big (n : ℕ) :
    sphLoopThick n ∪ sphLoopBig n = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    rcases x with _ | v
    · exact Or.inl (Or.inl rfl)
    · by_cases h : (1 / 2 : ℝ) < ‖v‖
      · exact Or.inl (Or.inr ⟨v, rfl, h⟩)
      · push Not at h
        exact Or.inr ⟨v, rfl, fun i => by
          have h2 : |v i| ≤ ‖v‖ := by simpa using PiLp.norm_apply_le v i
          linarith⟩

/-! ## The shell point -/

/-- The shell point lies in the thick inner cube. -/
theorem serreSphere_shellPt_mem_big (n : ℕ) : sphShellPt n ∈ sphLoopBig n :=
  ⟨serreSphereShellVec n, serreSphereShellPt_eq n, serreSphereShellVec_coord_lt n⟩

/-- For `1 ≤ n`, the shell point lies in the outer thickening (its norm is `1 > 1/2`). -/
theorem serreSphere_shellPt_mem_thick (n : ℕ) (hn : 1 ≤ n) : sphShellPt n ∈ sphLoopThick n :=
  Or.inr ⟨serreSphereShellVec n, serreSphereShellPt_eq n, by
    have := one_le_norm_serreSphereShellVec n hn
    linarith⟩

/-- The shell point lies in the shell `sphLoopMid n = sphLoopThick n ∩ sphLoopBig n`. -/
theorem serreSphere_shellPt_mem_mid (n : ℕ) (hn : 1 ≤ n) : sphShellPt n ∈ sphLoopMid n :=
  ⟨serreSphere_shellPt_mem_thick n hn, serreSphere_shellPt_mem_big n⟩

/-! ## The main statement -/

/-- The two pieces of the sphere decomposition are open, cover the model, and the shell point lies
in the shell. -/
theorem serreSphere_sets (n : ℕ) (hn : 1 ≤ n) :
    IsOpen (sphLoopThick n) ∧ IsOpen (sphLoopBig n) ∧
    sphLoopThick n ∪ sphLoopBig n = Set.univ ∧
    sphShellPt n ∈ sphLoopMid n :=
  ⟨serreSphere_isOpen_thick n, serreSphere_isOpen_big n,
    serreSphere_thick_union_big n, serreSphere_shellPt_mem_mid n hn⟩

end

end Work.StemsB
