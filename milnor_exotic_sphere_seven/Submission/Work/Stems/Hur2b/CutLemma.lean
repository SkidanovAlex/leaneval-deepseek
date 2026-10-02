import Mathlib
import Submission.Work.Stems.Hur2b.WedgeArr

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cutting a based cube along a straight line

Let `p : Ω²(X,x₀)` be a based `2`-cube and `a ∈ I`.  If `p` is `x₀` on the straight line
`{y₀ = a}`, then its class in `π₂(X,x₀)` is the product of the classes of the two *affine column
readings* `cutL a p h` and `cutR a p h` (the restrictions of `p` to the columns `[0,a] × I` and
`[a,1] × I`, read via the affine parametrisations `(a·y₀, y₁)` and `(a + (1-a)y₀, y₁)`).

Three ingredients, each with an explicit homotopy:

* `cl_reparam_coord` — replacing the coordinate `y₀` by `ψ y₀` for a continuous `ψ : I → I` with
  `ψ 0 = 0`, `ψ 1 = 1` does not change the class (homotopy `(y,t) ↦ c ((1-t)ψ y₀ + t y₀, y₁)`).
* `cl_reading_column` — if moreover `c` is `x₀` on the line `{y₀ = a}` and `ψ 0 = 0`, `ψ 1 = a`,
  then reading the column `[0,a] × I` with `ψ` gives the same class as reading it affinely
  (homotopy `(y,t) ↦ c ((1-t) ψ y₀ + t a y₀, y₁)`; every slice is based because `c` vanishes on
  `{y₀ = a}`).
* `cl_cut_vertical` — combines the two: move the line `{y₀ = a}` to the midline with the
  piecewise-linear stretch `stretch a` (satisfying `stretch a (1/2) = a`), which does not change
  the class, and split at the midline with `HomotopyGroup.mul_spec`.

The horizontal analogues are identical with the roles of the coordinates exchanged.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical
open Work.Stems.Hur2

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-! ## The piecewise-linear stretch moving the midline to the line `{a}` -/

/-- The piecewise-linear map `I → I` with `0 ↦ 0`, `1/2 ↦ a`, `1 ↦ 1`, written with `min`/`max`
inside a `clamp` so that continuity is automatic. -/
noncomputable def stretch (a : unitInterval) : C(unitInterval, unitInterval) :=
  ⟨fun s => clamp (min (1:ℝ) (2 * (s : ℝ)) * (a : ℝ)
      + max (0:ℝ) (2 * (s : ℝ) - 1) * (1 - (a : ℝ))),
    continuous_clamp.comp (by fun_prop)⟩

/-- The value of the stretch at the collar. -/
theorem stretch_zero_val (a : unitInterval) : stretch a 0 = 0 := by
  show clamp (min (1:ℝ) (2 * ((0 : unitInterval) : ℝ)) * (a : ℝ)
    + max (0:ℝ) (2 * ((0 : unitInterval) : ℝ) - 1) * (1 - (a : ℝ))) = 0
  simp

/-- The value of the stretch at the top. -/
theorem stretch_one_val (a : unitInterval) : stretch a 1 = 1 := by
  show clamp (min (1:ℝ) (2 * ((1 : unitInterval) : ℝ)) * (a : ℝ)
    + max (0:ℝ) (2 * ((1 : unitInterval) : ℝ) - 1) * (1 - (a : ℝ))) = 1
  have h : (a:ℝ) + (1 - (a:ℝ)) = 1 := by ring
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
  rw [show min (1:ℝ) (2 * (1:ℝ)) = 1 from by norm_num,
    show max (0:ℝ) (2 * (1:ℝ) - 1) = 1 from by norm_num, one_mul, one_mul, h, clamp_one]

/-! ## Reparametrising one coordinate -/

/-- Replacing the first coordinate `y₀` by `ψ y₀`. -/
noncomputable def coordMap (ψ : C(unitInterval, unitInterval)) : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (ψ (y 0)) (y 1),
    continuous_pair2 (ψ.continuous.comp (continuous_apply 0)) (continuous_apply 1)⟩

/-- The affine reading of the column `[0,a] × I`: `y ↦ (a · y₀, y₁)`. -/
noncomputable def colMap (a : unitInterval) : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (clamp ((a : ℝ) * (y 0 : ℝ))) (y 1),
    continuous_pair2 (continuous_clamp.comp (by fun_prop)) (continuous_apply 1)⟩

/-- The affine reading of the column `[a,1] × I`: `y ↦ (a + (1-a) · y₀, y₁)`. -/
noncomputable def colMapR (a : unitInterval) : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (clamp ((a : ℝ) + (1 - (a : ℝ)) * (y 0 : ℝ))) (y 1),
    continuous_pair2 (continuous_clamp.comp (by fun_prop)) (continuous_apply 1)⟩

theorem colMap_zero (a : unitInterval) (y : IC 2) (h : y 0 = 0) : colMap a y 0 = 0 := by
  show pair2 (clamp ((a : ℝ) * (y 0 : ℝ))) (y 1) 0 = 0
  rw [pair2_zero, h]; simp

theorem colMap_oneElt (a : unitInterval) (y : IC 2) (h : y 0 = 1) :
    colMap a y = pair2 a (y 1) := by
  ext j; fin_cases j <;> simp [colMap, h, clamp_coe]

theorem colMapR_left (a : unitInterval) (y : IC 2) (h : y 0 = 0) :
    colMapR a y = pair2 a (y 1) := by
  ext j; fin_cases j <;> simp [colMapR, h, clamp_coe]

theorem colMapR_right (a : unitInterval) (y : IC 2) (h : y 0 = 1) :
    colMapR a y = pair2 1 (y 1) := by
  ext j; fin_cases j <;> simp [colMapR, h, clamp_one]

theorem coordMap_zero {ψ : C(unitInterval, unitInterval)} (h0 : ψ 0 = 0) (y : IC 2)
    (h : y 0 = 0) : (coordMap ψ y) 0 = 0 := by
  show ψ (y 0) = 0
  rw [h, h0]

theorem coordMap_one {ψ : C(unitInterval, unitInterval)} (h1 : ψ 1 = 1) (y : IC 2)
    (h : y 0 = 1) : (coordMap ψ y) 0 = 1 := by
  show ψ (y 0) = 1
  rw [h, h1]

/-- The end value of `coordMap ψ` at `y₀ = 1` for a prescribed `ψ 1 = a`. -/
theorem coordMap_end {ψ : C(unitInterval, unitInterval)} {a : unitInterval} (h1 : ψ 1 = a)
    (y : IC 2) (h : y 0 = 1) : coordMap ψ y = pair2 a (y 1) := by
  ext j; fin_cases j <;> simp [coordMap, show y 0 = 1 from h, h1]

theorem coordMap_coord (ψ : C(unitInterval, unitInterval)) (y : IC 2) :
    (coordMap ψ y) 1 = y 1 := by simp [coordMap]

/-- `coordMap ψ` sends `∂I²` into `∂I²` when `ψ` fixes `0` and `1`. -/
theorem coordMap_mem_boundary {ψ : C(unitInterval, unitInterval)} (h0 : ψ 0 = 0) (h1 : ψ 1 = 1)
    {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) : coordMap ψ y ∈ Cube.boundary (Fin 2) := by
  rcases hy with ⟨i, hi | hi⟩ <;> fin_cases i
  · exact ⟨0, Or.inl (coordMap_zero h0 y hi)⟩
  · exact ⟨1, Or.inl (by rw [coordMap_coord]; exact hi)⟩
  · exact ⟨0, Or.inr (coordMap_one h1 y hi)⟩
  · exact ⟨1, Or.inr (by rw [coordMap_coord]; exact hi)⟩

/-- A composition `c ∘ φ` is a based cube as soon as `φ` maps `∂I²` into the zero set of `c`. -/
noncomputable def compGenLoop {c : GenLoop (Fin 2) X x₀} {φ : C(IC 2, IC 2)}
    (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 (φ y) = x₀) : GenLoop (Fin 2) X x₀ :=
  ⟨c.1.comp φ, h⟩

@[simp] theorem compGenLoop_apply {c : GenLoop (Fin 2) X x₀} {φ : C(IC 2, IC 2)}
    (h : ∀ y ∈ Cube.boundary (Fin 2), c.1 (φ y) = x₀) (y : IC 2) :
    (compGenLoop h : GenLoop (Fin 2) X x₀) y = c.1 (φ y) := rfl

/-- The left piece of the cut at `{y₀ = a}`: the affine reading of the column `[0,a] × I`. -/
noncomputable def cutL (a : unitInterval) (p : GenLoop (Fin 2) X x₀)
    (h : ∀ s : unitInterval, p.1 (pair2 a s) = x₀) : GenLoop (Fin 2) X x₀ :=
  compGenLoop fun y hy => by
    rcases hy with ⟨i, hi | hi⟩ <;> fin_cases i
    · exact p.2 _ ⟨0, Or.inl (colMap_zero a y hi)⟩
    · show p.1 (colMap a y) = x₀
      exact p.2 _ ⟨1, Or.inl (by rw [show (colMap a y) 1 = y 1 from by simp [colMap]]; exact hi)⟩
    · show p.1 (colMap a y) = x₀
      rw [colMap_oneElt a y hi]; exact h (y 1)
    · show p.1 (colMap a y) = x₀
      exact p.2 _ ⟨1, Or.inr (by rw [show (colMap a y) 1 = y 1 from by simp [colMap]]; exact hi)⟩

/-- The right piece of the cut at `{y₀ = a}`: the affine reading of the column `[a,1] × I`. -/
noncomputable def cutR (a : unitInterval) (p : GenLoop (Fin 2) X x₀)
    (h : ∀ s : unitInterval, p.1 (pair2 a s) = x₀) : GenLoop (Fin 2) X x₀ :=
  compGenLoop fun y hy => by
    rcases hy with ⟨i, hi | hi⟩ <;> fin_cases i
    · show p.1 (colMapR a y) = x₀
      rw [colMapR_left a y hi]; exact h (y 1)
    · show p.1 (colMapR a y) = x₀
      exact p.2 _ ⟨1, Or.inl (by rw [show (colMapR a y) 1 = y 1 from by simp [colMapR]]; exact hi)⟩
    · show p.1 (colMapR a y) = x₀
      rw [colMapR_right a y hi]; exact p.2 _ ⟨0, Or.inr rfl⟩
    · show p.1 (colMapR a y) = x₀
      exact p.2 _ ⟨1, Or.inr (by rw [show (colMapR a y) 1 = y 1 from by simp [colMapR]]; exact hi)⟩

/-- The column reading with `ψ` is a based cube when `ψ 0 = 0`, `ψ 1 = a` and `c` vanishes on the
line `{y₀ = a}`. -/
noncomputable def colRead (c : GenLoop (Fin 2) X x₀) (a : unitInterval)
    (h : ∀ s : unitInterval, c.1 (pair2 a s) = x₀) (ψ : C(unitInterval, unitInterval))
    (h0 : ψ 0 = 0) (h1 : ψ 1 = a) : GenLoop (Fin 2) X x₀ :=
  compGenLoop fun y hy => by
    rcases hy with ⟨i, hi | hi⟩ <;> fin_cases i
    · exact c.2 _ ⟨0, Or.inl (coordMap_zero h0 y hi)⟩
    · exact c.2 _ ⟨1, Or.inl (by rw [coordMap_coord]; exact hi)⟩
    · show c.1 (coordMap ψ y) = x₀
      rw [coordMap_end h1 y hi]
      exact h (y 1)
    · exact c.2 _ ⟨1, Or.inr (by rw [coordMap_coord]; exact hi)⟩

/-! ## The value of the stretch at `1/2` -/

theorem stretch_at_half (a : unitInterval) : stretch a (⟨1/2, by norm_num⟩ : unitInterval) = a := by
  show clamp (min (1:ℝ) (2 * ((⟨1/2, by norm_num⟩ : unitInterval) : ℝ)) * (a : ℝ)
    + max (0:ℝ) (2 * ((⟨1/2, by norm_num⟩ : unitInterval) : ℝ) - 1) * (1 - (a : ℝ))) = a
  have h : ((⟨1/2, by norm_num⟩ : unitInterval) : ℝ) = 1/2 := by norm_num
  rw [h, show min (1:ℝ) (2 * (1/2)) = 1 from by norm_num,
    show max (0:ℝ) (2 * (1/2) - 1) = 0 from by norm_num, one_mul, zero_mul, add_zero, clamp_coe]

/-! ## The right column reading -/

/-- The column reading of `[a,1] × I` with a parametrisation `ψ` (with `ψ 0 = a`, `ψ 1 = 1`). -/
noncomputable def colReadR (c : GenLoop (Fin 2) X x₀) (a : unitInterval)
    (h : ∀ s : unitInterval, c.1 (pair2 a s) = x₀) (ψ : C(unitInterval, unitInterval))
    (h0 : ψ 0 = a) (h1 : ψ 1 = 1) : GenLoop (Fin 2) X x₀ :=
  compGenLoop fun y hy => by
    rcases hy with ⟨i, hi | hi⟩ <;> fin_cases i
    · show c.1 (coordMap ψ y) = x₀
      rw [show coordMap ψ y = pair2 a (y 1) from by
        ext j; fin_cases j <;> simp [coordMap, show y 0 = 0 from hi, h0]]
      exact h (y 1)
    · exact c.2 _ ⟨1, Or.inl (by rw [coordMap_coord]; exact hi)⟩
    · exact c.2 _ ⟨0, Or.inr (coordMap_one h1 y hi)⟩
    · exact c.2 _ ⟨1, Or.inr (by rw [coordMap_coord]; exact hi)⟩

/-! ## The two reading lemmas and the cut lemma -/

/-- **Reading a column with any parametrisation gives the affine reading's class** (left column). -/
theorem cl_reading_column (c : GenLoop (Fin 2) X x₀) (a : unitInterval)
    (h : ∀ s : unitInterval, c.1 (pair2 a s) = x₀) (ψ : C(unitInterval, unitInterval))
    (h0 : ψ 0 = 0) (h1 : ψ 1 = a) :
    cl x₀ (colRead c a h ψ h0 h1) = cl x₀ (cutL a c h) := by
  refine Quotient.sound ⟨⟨⟨fun q : unitInterval × IC 2 => c.1 (pair2
      (clamp ((1 - (q.1 : ℝ)) * (ψ (q.2 0) : ℝ) + (q.1 : ℝ) * ((a : ℝ) * (q.2 0 : ℝ))))
      (q.2 1)), ?_⟩, ?_, ?_⟩, ?_⟩
  · refine c.1.continuous.comp (continuous_pair2 ?_ ?_)
    · refine continuous_clamp.comp ?_
      have h1 : Continuous fun q : unitInterval × IC 2 => (ψ (q.2 0) : unitInterval) :=
        ψ.continuous.comp ((continuous_apply 0).comp continuous_snd)
      fun_prop
    · exact (continuous_apply 1).comp continuous_snd
  · intro y
    have harg : pair2 (clamp ((1 - ((0 : unitInterval) : ℝ)) * (ψ (y 0) : ℝ)
        + ((0 : unitInterval) : ℝ) * ((a : ℝ) * (y 0 : ℝ)))) (y 1) = coordMap ψ y := by
      ext j; fin_cases j <;> simp [coordMap, clamp_coe]
    show c.1 (pair2 (clamp _) (y 1)) = c.1 (coordMap ψ y)
    rw [harg]
  · intro y
    have harg : pair2 (clamp ((1 - ((1 : unitInterval) : ℝ)) * (ψ (y 0) : ℝ)
        + ((1 : unitInterval) : ℝ) * ((a : ℝ) * (y 0 : ℝ)))) (y 1) = colMap a y := by
      ext j; fin_cases j <;> simp [colMap, clamp_coe]
    show c.1 (pair2 (clamp _) (y 1)) = c.1 (colMap a y)
    rw [harg]
  · intro t y hy
    rcases hy with ⟨i, hi | hi⟩ <;> fin_cases i
    · -- `y 0 = 0`: both sides are `c (0, y1)`
      have hval : (1 - (t : ℝ)) * (ψ (y 0) : ℝ) + (t : ℝ) * ((a : ℝ) * (y 0 : ℝ)) = 0 := by
        rw [show y 0 = 0 from hi, h0]
        simp only [show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero, add_zero]
      have hA : pair2 (clamp ((1 - (t : ℝ)) * (ψ (y 0) : ℝ)
          + (t : ℝ) * ((a : ℝ) * (y 0 : ℝ)))) (y 1) = pair2 0 (y 1) := by
        ext j; fin_cases j <;> simp [hval]
      have hB : coordMap ψ y = pair2 0 (y 1) := by
        ext j; fin_cases j <;> simp [coordMap, show y 0 = 0 from hi, h0]
      show c.1 (pair2 (clamp _) (y 1)) = c.1 (coordMap ψ y)
      rw [hA, hB]
    · -- `y 1 = 0`: both points are in `∂I²`
      show c.1 (pair2 (clamp _) (y 1)) = c.1 (coordMap ψ y)
      rw [show y 1 = 0 from hi]
      exact (c.2 _ ⟨1, Or.inl (by simp)⟩).trans (c.2 _ ⟨1, Or.inl (by rw [coordMap_coord, show y 1 = 0 from hi])⟩).symm
    · -- `y 0 = 1`: both sides are `c (a, y1)`
      have hval : (1 - (t : ℝ)) * (ψ (y 0) : ℝ) + (t : ℝ) * ((a : ℝ) * (y 0 : ℝ)) = (a:ℝ) := by
        rw [show y 0 = 1 from hi, h1]
        simp only [show ((1 : unitInterval) : ℝ) = 1 from rfl]
        ring
      have hA : pair2 (clamp ((1 - (t : ℝ)) * (ψ (y 0) : ℝ)
          + (t : ℝ) * ((a : ℝ) * (y 0 : ℝ)))) (y 1) = pair2 a (y 1) := by
        ext j; fin_cases j <;> simp [hval, clamp_coe]
      have hB : coordMap ψ y = pair2 a (y 1) := by
        ext j; fin_cases j <;> simp [coordMap, show y 0 = 1 from hi, h1]
      show c.1 (pair2 (clamp _) (y 1)) = c.1 (coordMap ψ y)
      rw [hA, hB]
    · -- `y 1 = 1`: both points are in `∂I²`
      show c.1 (pair2 (clamp _) (y 1)) = c.1 (coordMap ψ y)
      rw [show y 1 = 1 from hi]
      exact (c.2 _ ⟨1, Or.inr (by simp)⟩).trans (c.2 _ ⟨1, Or.inr (by rw [coordMap_coord, show y 1 = 1 from hi])⟩).symm

/-- **Reading a column with any parametrisation gives the affine reading's class** (right column). -/
theorem cl_reading_columnR (c : GenLoop (Fin 2) X x₀) (a : unitInterval)
    (h : ∀ s : unitInterval, c.1 (pair2 a s) = x₀) (ψ : C(unitInterval, unitInterval))
    (h0 : ψ 0 = a) (h1 : ψ 1 = 1) :
    cl x₀ (colReadR c a h ψ h0 h1) = cl x₀ (cutR a c h) := by
  refine Quotient.sound ⟨⟨⟨fun q : unitInterval × IC 2 => c.1 (pair2
      (clamp ((1 - (q.1 : ℝ)) * (ψ (q.2 0) : ℝ) + (q.1 : ℝ) * (a + (1 - (a : ℝ)) * (q.2 0 : ℝ))))
      (q.2 1)), ?_⟩, ?_, ?_⟩, ?_⟩
  · refine c.1.continuous.comp (continuous_pair2 ?_ ?_)
    · refine continuous_clamp.comp ?_
      have h1 : Continuous fun q : unitInterval × IC 2 => (ψ (q.2 0) : unitInterval) :=
        ψ.continuous.comp ((continuous_apply 0).comp continuous_snd)
      fun_prop
    · exact (continuous_apply 1).comp continuous_snd
  · intro y
    have harg : pair2 (clamp ((1 - ((0 : unitInterval) : ℝ)) * (ψ (y 0) : ℝ)
        + ((0 : unitInterval) : ℝ) * (a + (1 - (a : ℝ)) * (y 0 : ℝ)))) (y 1) = coordMap ψ y := by
      ext j; fin_cases j <;> simp [coordMap, clamp_coe]
    show c.1 (pair2 (clamp _) (y 1)) = c.1 (coordMap ψ y)
    rw [harg]
  · intro y
    have harg : pair2 (clamp ((1 - ((1 : unitInterval) : ℝ)) * (ψ (y 0) : ℝ)
        + ((1 : unitInterval) : ℝ) * (a + (1 - (a : ℝ)) * (y 0 : ℝ)))) (y 1)
        = colMapR a y := by
      ext j; fin_cases j <;> simp [colMapR, clamp_coe]
    show c.1 (pair2 (clamp _) (y 1)) = c.1 (colMapR a y)
    rw [harg]
  · intro t y hy
    rcases hy with ⟨i, hi | hi⟩ <;> fin_cases i
    · -- `y 0 = 0`: both sides are `c (a, y1)`
      have hval : (1 - (t : ℝ)) * (ψ (y 0) : ℝ) + (t : ℝ) * (a + (1 - (a : ℝ)) * (y 0 : ℝ))
          = (a:ℝ) := by
        rw [show y 0 = 0 from hi, h0]
        simp only [show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero, add_zero]
        ring
      have hA : pair2 (clamp ((1 - (t : ℝ)) * (ψ (y 0) : ℝ)
          + (t : ℝ) * (a + (1 - (a : ℝ)) * (y 0 : ℝ)))) (y 1) = pair2 a (y 1) := by
        ext j; fin_cases j <;> simp [hval, clamp_coe]
      have hB : coordMap ψ y = pair2 a (y 1) := by
        ext j; fin_cases j <;> simp [coordMap, show y 0 = 0 from hi, h0]
      show c.1 (pair2 (clamp _) (y 1)) = c.1 (coordMap ψ y)
      rw [hA, hB]
    · show c.1 (pair2 (clamp _) (y 1)) = c.1 (coordMap ψ y)
      rw [show y 1 = 0 from hi]
      exact (c.2 _ ⟨1, Or.inl (by simp)⟩).trans (c.2 _ ⟨1, Or.inl (by rw [coordMap_coord, show y 1 = 0 from hi])⟩).symm
    · -- `y 0 = 1`: both sides are `c (1, y1)`
      have hval : (1 - (t : ℝ)) * (ψ (y 0) : ℝ) + (t : ℝ) * (a + (1 - (a : ℝ)) * (y 0 : ℝ))
          = 1 := by
        rw [show y 0 = 1 from hi, h1]
        simp only [show ((1 : unitInterval) : ℝ) = 1 from rfl]
        ring
      have hA : pair2 (clamp ((1 - (t : ℝ)) * (ψ (y 0) : ℝ)
          + (t : ℝ) * (a + (1 - (a : ℝ)) * (y 0 : ℝ)))) (y 1) = pair2 1 (y 1) := by
        ext j; fin_cases j <;> simp [hval, clamp_one]
      have hB : coordMap ψ y = pair2 1 (y 1) := by
        ext j; fin_cases j <;> simp [coordMap, show y 0 = 1 from hi, h1]
      show c.1 (pair2 (clamp _) (y 1)) = c.1 (coordMap ψ y)
      rw [hA, hB]
    · show c.1 (pair2 (clamp _) (y 1)) = c.1 (coordMap ψ y)
      rw [show y 1 = 1 from hi]
      exact (c.2 _ ⟨1, Or.inr (by simp)⟩).trans (c.2 _ ⟨1, Or.inr (by rw [coordMap_coord, show y 1 = 1 from hi])⟩).symm


/-! ## Reparametrising a coordinate -/

/-- The coordinate homotopy `(t, y) ↦ ((1-t)·ψ y₀ + t·y₀, y₁)` interpolating `coordMap ψ` to the
identity. -/
noncomputable def coordHom (ψ : C(unitInterval, unitInterval)) : C(unitInterval × IC 2, IC 2) :=
  ⟨fun q => pair2 (clamp ((1 - (q.1 : ℝ)) * (ψ (q.2 0) : ℝ) + (q.1 : ℝ) * (q.2 0 : ℝ))) (q.2 1),
    continuous_pair2 (continuous_clamp.comp (by
      have h1 : Continuous fun q : unitInterval × IC 2 => (ψ (q.2 0) : unitInterval) :=
        ψ.continuous.comp ((continuous_apply 0).comp continuous_snd)
      fun_prop)) ((continuous_apply 1).comp continuous_snd)⟩

@[simp] theorem coordHom_zero {ψ : C(unitInterval, unitInterval)} (y : IC 2) :
    coordHom ψ ((0 : unitInterval), y) = coordMap ψ y := by
  have h : pair2 (clamp ((1 - ((0 : unitInterval) : ℝ)) * (ψ (y 0) : ℝ)
      + ((0 : unitInterval) : ℝ) * (y 0 : ℝ))) (y 1) = coordMap ψ y := by
    ext j; fin_cases j <;> simp [coordMap, clamp_coe]
  show pair2 (clamp _) (y 1) = coordMap ψ y
  rw [h]

@[simp] theorem coordHom_one {ψ : C(unitInterval, unitInterval)} (y : IC 2) :
    coordHom ψ ((1 : unitInterval), y) = y := by
  have h : pair2 (clamp ((1 - ((1 : unitInterval) : ℝ)) * (ψ (y 0) : ℝ)
      + ((1 : unitInterval) : ℝ) * (y 0 : ℝ))) (y 1) = y := by
    ext j; fin_cases j <;> simp [clamp_coe]
  show pair2 (clamp _) (y 1) = y
  rw [h]

theorem coordHom_apply (ψ : C(unitInterval, unitInterval)) (t : unitInterval) (y : IC 2) :
    coordHom ψ (t, y) = pair2 (clamp ((1 - (t : ℝ)) * (ψ (y 0) : ℝ) + (t : ℝ) * (y 0 : ℝ)))
      (y 1) := rfl

theorem coordHom_mem_boundary {ψ : C(unitInterval, unitInterval)} (h0 : ψ 0 = 0) (h1 : ψ 1 = 1)
    {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) (t : unitInterval) :
    coordHom ψ (t, y) ∈ Cube.boundary (Fin 2) := by
  rcases hy with ⟨i, hi | hi⟩ <;> fin_cases i
  · have hval : (1 - (t : ℝ)) * (ψ (y 0) : ℝ) + (t : ℝ) * (y 0 : ℝ) = 0 := by
      rw [show y 0 = 0 from hi, h0]
      simp only [show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero, add_zero]
    refine ⟨0, Or.inl ?_⟩
    rw [coordHom_apply, pair2_zero, hval, clamp_zero]
  · refine ⟨1, Or.inl ?_⟩
    rw [coordHom_apply, pair2_one]; exact hi
  · have hval : (1 - (t : ℝ)) * (ψ (y 0) : ℝ) + (t : ℝ) * (y 0 : ℝ) = 1 := by
      rw [show y 0 = 1 from hi, h1]
      simp only [show ((1 : unitInterval) : ℝ) = 1 from rfl]
      ring
    refine ⟨0, Or.inr ?_⟩
    rw [coordHom_apply, pair2_zero, hval, clamp_one]
  · refine ⟨1, Or.inr ?_⟩
    rw [coordHom_apply, pair2_one]; exact hi

/-- **Reparametrising the first coordinate does not change the class.** -/
theorem cl_reparam_coord (c : GenLoop (Fin 2) X x₀) (ψ : C(unitInterval, unitInterval))
    (h0 : ψ 0 = 0) (h1 : ψ 1 = 1) :
    cl x₀ (compGenLoop fun y hy => c.2 _ (coordMap_mem_boundary h0 h1 hy)) = cl x₀ c := by
  refine Quotient.sound ⟨⟨⟨fun q : unitInterval × IC 2 => c.1 (coordHom ψ q), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact c.1.continuous.comp (coordHom ψ).continuous
  · intro y
    show c.1 (coordHom ψ ((0 : unitInterval), y)) = c.1 (coordMap ψ y)
    rw [coordHom_zero]
  · intro y
    show c.1 (coordHom ψ ((1 : unitInterval), y)) = c.1 y
    rw [coordHom_one]
  · intro t y hy
    show c.1 (coordHom ψ (t, y)) = c.1 (coordMap ψ y)
    exact (c.2 _ (coordHom_mem_boundary h0 h1 hy t)).trans
      (c.2 _ (coordMap_mem_boundary h0 h1 hy)).symm

end Work.Stems.Hur2b
