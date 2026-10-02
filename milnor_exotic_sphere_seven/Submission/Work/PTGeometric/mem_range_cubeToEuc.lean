import Mathlib
import Submission.Work.Tubular.Collapse

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped unitInterval

namespace Work.PTGeometric

/-- **The image of the cube parametrisation** `cubeToEuc N R : I^N → ℝ^N` (the parametrisation of
the box `[-R,R]^N` of radius `R ≥ 0`) is exactly the box: a point of `ℝ^N` is in the range of
`cubeToEuc N R` if and only if all of its coordinates have absolute value at most `R`. -/
theorem mem_range_cubeToEuc {N : ℕ} {R : ℝ} (hR : 0 ≤ R) (u : Work.Tubular.Euc N) :
    u ∈ Set.range (⇑(Work.Tubular.cubeToEuc N R)) ↔ ∀ j : Fin N, |u.ofLp j| ≤ R := by
  constructor
  · -- A point of the cube has coordinates `2R(t_j - 1/2)` with `t_j ∈ [0,1]`, hence `|·| ≤ R`.
    rintro ⟨t, rfl⟩ j
    have hcoe : (Work.Tubular.cubeToEuc N R t).ofLp j = 2 * R * ((t j : ℝ) - 1 / 2) :=
      congrFun (Work.Tubular.funToEuc_symm_cubeToEuc N R t) j
    rw [hcoe, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * R)]
    have ha : |(t j : ℝ) - 1 / 2| ≤ 1 / 2 :=
      abs_le.mpr ⟨by linarith [(t j).2.1], by linarith [(t j).2.2]⟩
    calc 2 * R * |(t j : ℝ) - 1 / 2| ≤ 2 * R * (1 / 2) :=
          mul_le_mul_of_nonneg_left ha (by linarith)
      _ = R := by ring
  · intro hu
    -- Conversely, a point of the box is the image of the cube point `t_j = u_j/(2R) + 1/2`.
    rcases lt_or_eq_of_le hR with hpos | h0
    · have h2R : (0:ℝ) < 2 * R := by linarith
      let t : Fin N → unitInterval := fun i => ⟨u.ofLp i / (2*R) + 1/2, by
          have h1 : -(1/2:ℝ) ≤ u.ofLp i / (2*R) := by
            rw [le_div_iff₀ h2R]; nlinarith [neg_le_of_abs_le (hu i)]
          linarith, by
          have h1 : u.ofLp i / (2*R) ≤ (1/2:ℝ) := by
            rw [div_le_iff₀ h2R]; nlinarith [le_of_abs_le (hu i)]
          linarith⟩
      refine ⟨t, ?_⟩
      have heq : (Work.Tubular.cubeToEuc N R t).ofLp = u.ofLp := by
        funext j
        have hcoe : (Work.Tubular.cubeToEuc N R t).ofLp j = 2 * R * ((t j : ℝ) - 1 / 2) :=
          congrFun (Work.Tubular.funToEuc_symm_cubeToEuc N R t) j
        rw [hcoe]
        have ht : ((t j : unitInterval) : ℝ) = u.ofLp j / (2*R) + 1/2 := rfl
        rw [ht]
        have hR0 : (2 * R) ≠ 0 := by positivity
        field_simp
        ring
      calc Work.Tubular.cubeToEuc N R t
          = WithLp.toLp 2 ((Work.Tubular.cubeToEuc N R t).ofLp) := (WithLp.toLp_ofLp 2 _).symm
        _ = WithLp.toLp 2 u.ofLp := by rw [heq]
        _ = u := WithLp.toLp_ofLp 2 u
    · -- The degenerate case `R = 0`: the box is the single point `0`, which is the image of `0`.
      refine ⟨fun _ => (0 : unitInterval), ?_⟩
      have heq : (Work.Tubular.cubeToEuc N R (fun _ => (0 : unitInterval))).ofLp = u.ofLp := by
        funext j
        have hcoe : (Work.Tubular.cubeToEuc N R (fun _ => (0 : unitInterval))).ofLp j
            = 2 * R * (((fun _ => (0 : unitInterval)) j : ℝ) - 1 / 2) :=
          congrFun (Work.Tubular.funToEuc_symm_cubeToEuc N R (fun _ => (0:unitInterval))) j
        have hz : u.ofLp j = 0 := by
          have hh := hu j
          rw [← h0] at hh
          exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
        rw [hcoe, ← h0]
        simp [hz]
      calc Work.Tubular.cubeToEuc N R (fun _ => (0 : unitInterval))
          = WithLp.toLp 2 ((Work.Tubular.cubeToEuc N R (fun _ => (0:unitInterval))).ofLp) := (WithLp.toLp_ofLp 2 _).symm
        _ = WithLp.toLp 2 u.ofLp := by rw [heq]
        _ = u := WithLp.toLp_ofLp 2 u

end Work.PTGeometric
