import Mathlib
import Submission.Work.Tubular.Gauss

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Auxiliary definitions for `Work.ThomBordism.tubeGenLoop_hurewiczChain_natural`

The lemma `Work.ThomBordism.tubeGenLoop_hurewiczChain_natural` compares the Hurewicz chain of the
Pontryagin–Thom cube loop `Work.Tubular.tubeGenLoopOnePoint` with the push-forward along the collapse
`g` of the Hurewicz chain of the *standard* collapse cube loop `Work.Stems.cubeToOnePoint`.

The two cube maps are

* `t ↦ g (OnePoint.some (cubeToEuc n R t))` (the loop used by `tubeGenLoopOnePoint`), and
* `t ↦ g (cubeToOnePoint n t)`,

i.e. the standard collapse `cubeToOnePoint` precomposed with the "coordinate" chart
`t ↦ cubeCoords n t = (y_i/√(1-y_i²))_i`, against the *linear* chart `t ↦ cubeToEuc n R t = (2R y_i)`
(with `y_i = 2 t_i - 1`).  The link between the two is the coordinatewise diffeomorphism of the
line `ℝ`, `y ↦ R y/√(1+y²)`, which this file records together with the interpolation

  `θ_s(y) = (1-s) · (R y/√(1+y²)) + s · y`

between it (`s = 0`) and the identity (`s = 1`).  The endpoints satisfy (for `|y_i| < 1`)

  `θ_0 (cubeCoords t) = cubeToEuc R t`   (`theta_zero_cubeCoords`)

which is what makes the homotopy below start at the tube loop and end at the standard collapse.

* `theta`, `theta_apply`, `theta_one`, `continuous_theta`, `theta_zero_cubeCoords`;
* `thresh` — the threshold from which the interpolation is guaranteed to leave the tube.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TubeGen

noncomputable section

/-- The interpolation `θ_s(y) = (1-s) · (R · y/√(1+y²)) + s · y`, coordinatewise.  At `s = 0` it is
the coordinatewise squashing `y ↦ R y/√(1+y²)`, at `s = 1` the identity. -/
def theta {n : ℕ} (R s : ℝ) (y : Work.Tubular.Euc n) : Work.Tubular.Euc n :=
  Work.Tubular.funToEuc n
    (fun j => (1 - s) * (R * y j / Real.sqrt (1 + y j ^ 2)) + s * y j)

@[simp] theorem theta_apply {n : ℕ} (R s : ℝ) (y : Work.Tubular.Euc n) (j : Fin n) :
    theta R s y j = (1 - s) * (R * y j / Real.sqrt (1 + y j ^ 2)) + s * y j := rfl

theorem theta_one {n : ℕ} (R : ℝ) (y : Work.Tubular.Euc n) : theta R 1 y = y := by
  ext j
  show (1 - 1) * (R * y j / Real.sqrt (1 + y j ^ 2)) + 1 * y j = y j
  ring

theorem continuous_theta {n : ℕ} (R : ℝ) :
    Continuous (fun p : ℝ × Work.Tubular.Euc n => theta R p.1 p.2) := by
  refine (Work.Tubular.funToEuc n).continuous.comp ?_
  refine continuous_pi (fun j => ?_)
  have hj : Continuous (fun p : ℝ × Work.Tubular.Euc n => p.2 j) :=
    (continuous_apply j).comp
      (((Work.Tubular.funToEuc n).symm.continuous).comp continuous_snd)
  have hden : Continuous (fun p : ℝ × Work.Tubular.Euc n => Real.sqrt (1 + p.2 j ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.add (hj.pow 2))
  have hden_ne : ∀ p : ℝ × Work.Tubular.Euc n, Real.sqrt (1 + p.2 j ^ 2) ≠ 0 := fun p =>
    ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
  have hquot : Continuous (fun p : ℝ × Work.Tubular.Euc n =>
      R * p.2 j / Real.sqrt (1 + p.2 j ^ 2)) :=
    (continuous_const.mul hj).div hden hden_ne
  have h1 : Continuous (fun p : ℝ × Work.Tubular.Euc n => 1 - p.1) :=
    continuous_const.sub continuous_fst
  exact (h1.mul hquot).add (continuous_fst.mul hj)

/-- **The coordinatewise cancellation** `u/√(1-u²) / √(1 + (u/√(1-u²))²) = u` for `u² < 1`. -/
theorem self_div_sqrt_one_add_sq {u : ℝ} (hu : u ^ 2 < 1) :
    u / Real.sqrt (1 - u ^ 2) / Real.sqrt (1 + (u / Real.sqrt (1 - u ^ 2)) ^ 2) = u := by
  have h1 : 0 < 1 - u ^ 2 := by linarith
  have hs : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos_of_pos h1
  have hsq : (Real.sqrt (1 - u ^ 2)) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt h1.le
  have h2 : 1 + (u / Real.sqrt (1 - u ^ 2)) ^ 2 = (Real.sqrt (1 - u ^ 2))⁻¹ ^ 2 := by
    field_simp
    nlinarith [hsq]
  rw [h2, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  field_simp

/-- **At `s = 0` the interpolation inverts the standard collapse**: for a cube point `t` in the
interior of the cube, `θ_0 (cubeCoords t) = cubeToEuc R t`. -/
theorem theta_zero_cubeCoords {n : ℕ} (R : ℝ) {t : Work.Stems.CubeI n}
    (ht : t ∉ Cube.boundary (Fin n)) :
    theta R 0 (Work.Stems.cubeCoords n t) = Work.Tubular.cubeToEuc n R t := by
  have ht' : ∀ i : Fin n, (t i : ℝ) ≠ 0 ∧ (t i : ℝ) ≠ 1 := by
    intro i
    refine ⟨fun h => ht ⟨i, Or.inl ?_⟩, fun h => ht ⟨i, Or.inr ?_⟩⟩
    · exact Subtype.ext h
    · exact Subtype.ext h
  ext j
  show (1 - 0) * (R * (Work.Stems.cubeCoords n t) j
      / Real.sqrt (1 + (Work.Stems.cubeCoords n t) j ^ 2)) + 0 * (Work.Stems.cubeCoords n t) j
    = (Work.Tubular.cubeToEuc n R t) j
  have h0 : (0 : ℝ) ≤ (t j : ℝ) := (t j).2.1
  have h1 : (t j : ℝ) ≤ 1 := (t j).2.2
  have hu : (2 * (t j : ℝ) - 1) ^ 2 < 1 := by
    have hlt : (t j : ℝ) < 1 := lt_of_le_of_ne h1 (ht' j).2
    have hgt : 0 < (t j : ℝ) := lt_of_le_of_ne h0 (Ne.symm (ht' j).1)
    nlinarith
  have hcoord : (Work.Stems.cubeCoords n t) j
      = (2 * (t j : ℝ) - 1) / Real.sqrt (1 - (2 * (t j : ℝ) - 1) ^ 2) := rfl
  have hRHS : (Work.Tubular.cubeToEuc n R t) j = 2 * R * ((t j : ℝ) - 1 / 2) := by
    show Work.Tubular.cubeToFun n R t j = 2 * R * ((t j : ℝ) - 1 / 2)
    rw [Work.Tubular.cubeToFun_apply]
  rw [hcoord, hRHS]
  rw [show R * ((2 * (t j : ℝ) - 1) / Real.sqrt (1 - (2 * (t j : ℝ) - 1) ^ 2))
        / Real.sqrt (1 + ((2 * (t j : ℝ) - 1) / Real.sqrt (1 - (2 * (t j : ℝ) - 1) ^ 2)) ^ 2)
      = R * ((2 * (t j : ℝ) - 1) / Real.sqrt (1 - (2 * (t j : ℝ) - 1) ^ 2)
        / Real.sqrt (1 + ((2 * (t j : ℝ) - 1)
          / Real.sqrt (1 - (2 * (t j : ℝ) - 1) ^ 2)) ^ 2)) from by ring]
  rw [self_div_sqrt_one_add_sq hu]
  ring

/-- The threshold beyond which the interpolation `θ_s` is guaranteed to leave the box of radius
`R`: `Y = max 1 (max (4R²/δ) (max (4R/δ) √(2R/δ)))`. -/
def thresh (R δ : ℝ) : ℝ :=
  max 1 (max (4 * R ^ 2 / δ) (max (4 * R / δ) (Real.sqrt (2 * R / δ))))

theorem one_le_thresh (R δ : ℝ) : 1 ≤ thresh R δ := le_max_left _ _

theorem four_R_sq_div_le_thresh (R δ : ℝ) : 4 * R ^ 2 / δ ≤ thresh R δ :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem four_R_div_le_thresh (R δ : ℝ) : 4 * R / δ ≤ thresh R δ :=
  le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

theorem sqrt_two_R_div_le_thresh (R δ : ℝ) : Real.sqrt (2 * R / δ) ≤ thresh R δ :=
  le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))


/-! ## The interpolating family between the two cube collapses

The homotopy between the Pontryagin–Thom cube loop `Work.Tubular.tubeGenLoopOnePoint` and the
standard collapse loop `Work.Stems.cubeToOnePoint`, pushed forward by a collapse map `g`: at time
`s` the cube point `t` of the boundary is mapped to the basepoint, and an interior cube point `t`
to `g (θ_s (cubeCoords t))`. -/

/-- The interpolating cube map: `∞` on the boundary of the cube and
`g (θ_s (cubeCoords t))` on the interior. -/
noncomputable def thetaHomotopyFun {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (R : ℝ) :
    unitInterval × (Fin (8 + k) → unitInterval) → OnePoint (Work.Tubular.NormalTotal E) := by
  classical
  exact fun p => if p.2 ∈ Cube.boundary (Fin (8 + k)) then OnePoint.infty
    else g (OnePoint.some (theta R (p.1 : ℝ)
      (Work.Stems.cubeCoords (8 + k) p.2)))

theorem thetaHomotopyFun_apply_of_mem {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (R : ℝ) (s : unitInterval) (t : Fin (8 + k) → unitInterval)
    (ht : t ∈ Cube.boundary (Fin (8 + k))) :
    thetaHomotopyFun C g R (s, t) = OnePoint.infty := by
  rw [thetaHomotopyFun]
  split
  · rfl
  · exact absurd ht ‹_›

theorem thetaHomotopyFun_apply_of_notMem {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (R : ℝ) (s : unitInterval) (t : Fin (8 + k) → unitInterval)
    (ht : t ∉ Cube.boundary (Fin (8 + k))) :
    thetaHomotopyFun C g R (s, t) =
      g (OnePoint.some (theta R (s : ℝ) (Work.Stems.cubeCoords (8 + k) t))) := by
  rw [thetaHomotopyFun]
  split
  · exact absurd ‹_› ht
  · rfl

end

end Work.ThomBordism.TubeGen
