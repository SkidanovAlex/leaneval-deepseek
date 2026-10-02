import Mathlib
import Submission.Work.Stems.Cubical.Kop3

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cone parametrisation of the square

`I^2` is the cone on its boundary `∂I^2 ≅ S^1`.  We make this explicit: the boundary is
parametrised by `bd : [0,1] → I^2` (piecewise linear, counterclockwise), and the cone map
`c (s, t) = centre + (1 - s) • (bd t - centre)` maps `[0,1] × [0,1]` onto `I^2`, folding the fibre
`{1} × [0,1]` onto the centre.  A null-homotopy `H` of a loop parametrised by `bd` is constant on
that fibre, hence descends along the (quotient) cone map to a square filling the loop.
-/

open scoped unitInterval Topology

namespace Work.Stems.Cubical

/-- The centre of `I^2`. -/
noncomputable def sqCentre : IC 2 := fun _ => ⟨1 / 2, by norm_num⟩

/-- First coordinate of the counterclockwise boundary parametrisation. -/
noncomputable def bd0 (t : unitInterval) : ℝ :=
  min 1 (min (4 * (t : ℝ)) (max 0 (3 - 4 * (t : ℝ))))

/-- Second coordinate of the counterclockwise boundary parametrisation. -/
noncomputable def bd1 (t : unitInterval) : ℝ :=
  max 0 (min 1 (min (4 * (t : ℝ) - 1) (4 - 4 * (t : ℝ))))

theorem bd0_mem (t : unitInterval) : bd0 t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min (by norm_num) (le_min (by nlinarith [t.2.1]) (le_max_left _ _)), min_le_left _ _⟩

theorem bd1_mem (t : unitInterval) : bd1 t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The counterclockwise piecewise-linear parametrisation of `∂I^2`, based at `(0,0)`. -/
noncomputable def bd (t : unitInterval) : IC 2 :=
  fun j => if j = 0 then ⟨bd0 t, bd0_mem t⟩ else ⟨bd1 t, bd1_mem t⟩

@[fun_prop] theorem continuous_bd0 : Continuous bd0 := by
  unfold bd0; fun_prop

@[fun_prop] theorem continuous_bd1 : Continuous bd1 := by
  unfold bd1; fun_prop

@[fun_prop] theorem continuous_bd : Continuous bd := by
  rw [continuous_pi_iff]
  intro j
  fin_cases j
  · show Continuous fun t : unitInterval => (⟨bd0 t, bd0_mem t⟩ : unitInterval)
    exact Continuous.subtype_mk continuous_bd0 _
  · show Continuous fun t : unitInterval => (⟨bd1 t, bd1_mem t⟩ : unitInterval)
    exact Continuous.subtype_mk continuous_bd1 _

end Work.Stems.Cubical

namespace Work.Stems.Cubical

/-- One coordinate of the cone map `[0,1] × [0,1] → I^2`; the value is the affine combination of
`1/2` (the centre) and `bd t` with parameter `1 - s`. -/
noncomputable def coneCoord (p : IC 1 × IC 1) (j : Fin 2) : unitInterval :=
  ⟨1 / 2 + (1 - (p.1 0 : ℝ)) * ((bd (p.2 0) j : ℝ) - 1 / 2), by
    have hs : 0 ≤ (p.1 0 : ℝ) := (p.1 0).2.1
    have hs1 : (p.1 0 : ℝ) ≤ 1 := (p.1 0).2.2
    have hx : 0 ≤ (bd (p.2 0) j : ℝ) := (bd (p.2 0) j).2.1
    have hx1 : (bd (p.2 0) j : ℝ) ≤ 1 := (bd (p.2 0) j).2.2
    constructor <;> nlinarith⟩

theorem continuous_coneCoord (j : Fin 2) : Continuous fun p : IC 1 × IC 1 => coneCoord p j := by
  apply Continuous.subtype_mk
  fun_prop

/-- The cone map `[0,1] × [0,1] → I^2`. -/
noncomputable def coneMap : C(IC 1 × IC 1, IC 2) where
  toFun := fun p j => coneCoord p j
  continuous_toFun := by
    rw [continuous_pi_iff]
    exact continuous_coneCoord

end Work.Stems.Cubical

namespace Work.Stems.Cubical

/-- The max-norm "radius" of a point of `I^2` from its centre: `1` on the boundary, `0` at the
centre. -/
noncomputable def rad (y : IC 2) : ℝ := max |2 * (y 0 : ℝ) - 1| |2 * (y 1 : ℝ) - 1|

theorem rad_nonneg (y : IC 2) : 0 ≤ rad y := le_max_of_le_left (abs_nonneg _)

theorem rad_le_one (y : IC 2) : rad y ≤ 1 := by
  have h0 : 0 ≤ (y 0 : ℝ) := (y 0).2.1
  have h0' : (y 0 : ℝ) ≤ 1 := (y 0).2.2
  have h1 : 0 ≤ (y 1 : ℝ) := (y 1).2.1
  have h1' : (y 1 : ℝ) ≤ 1 := (y 1).2.2
  refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;> linarith

theorem rad_sqCentre : rad sqCentre = 0 := by
  unfold rad sqCentre
  norm_num

theorem rad_eq_max (y : IC 2) : rad y = max |2 * (y 0 : ℝ) - 1| |2 * (y 1 : ℝ) - 1| := rfl

end Work.Stems.Cubical

namespace Work.Stems.Cubical

/-- `a ↦ a/4` as a point of `[0,1]`. -/
noncomputable def quarter (a : unitInterval) : unitInterval :=
  ⟨(a : ℝ) / 4, by constructor <;> [nlinarith [a.2.1]; nlinarith [a.2.2]]⟩

@[simp] theorem quarter_val (a : unitInterval) : (quarter a : ℝ) = (a : ℝ) / 4 := rfl

theorem bd0_quarter (a : unitInterval) : bd0 (quarter a) = a := by
  have ha1 : (a : ℝ) ≤ 1 := a.2.2
  have h4 : 4 * (quarter a : ℝ) = (a : ℝ) := by rw [quarter_val]; ring
  unfold bd0
  rw [h4]
  rw [show max 0 (3 - (a : ℝ)) = 3 - (a : ℝ) by
    rw [max_eq_right]; linarith [a.2.2]]
  rw [show min (a : ℝ) (3 - (a : ℝ)) = (a : ℝ) by
    rw [min_eq_left]; linarith [a.2.2]]
  rw [min_eq_right ha1]

theorem bd1_quarter (a : unitInterval) : bd1 (quarter a) = 0 := by
  have ha1 : (a : ℝ) ≤ 1 := a.2.2
  have h4 : 4 * (quarter a : ℝ) = (a : ℝ) := by rw [quarter_val]; ring
  unfold bd1
  rw [h4]
  rw [show min (1 : ℝ) (min ((a : ℝ) - 1) (4 - (a : ℝ))) = (a : ℝ) - 1 by
    rw [min_eq_right]
    · rw [min_eq_left]; linarith [a.2.2]
    · have h : min ((a : ℝ) - 1) (4 - (a : ℝ)) ≤ (a : ℝ) - 1 := min_le_left _ _
      linarith [a.2.2]]
  rw [max_eq_left]
  linarith [a.2.1]

end Work.Stems.Cubical
