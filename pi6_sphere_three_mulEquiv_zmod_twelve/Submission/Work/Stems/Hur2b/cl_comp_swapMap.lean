import Mathlib
import Submission.Work.Stems.Hur2b.NetLayout
import Submission.Work.Stems.Hur2b.CutLemma
import Submission.Work.Stems.Hur2b.NetData

namespace Work.Stems.Hur2b

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.Stems.Hur2

/-
# The class of a based `2`-cube reparametrised by the coordinate swap

`swapMap : I² → I²` is the transposition of the two coordinates.  It is a reflection of the square,
hence has boundary degree `-1`, so composing a based `2`-cube with it inverts the class:
`cl x₀ (q ∘ swapMap) = (cl x₀ q)⁻¹`.

Together with the already proved `cl_symmAt : cl (q ∘ (reversal of coordinate i)) = (cl q)⁻¹` this
covers *all four* coordinate-dihedral reparametrisations of the square.

## The route

`swapMap = rot90 ∘ flip` where `rot90 y = (σ y₁, y₀)` is the quarter turn of the square and
`flip y = (y₀, σ y₁)` is the reversal of the second coordinate (Mathlib's `symmAt 1`).  So

* `cl (q ∘ swapMap) = cl (symmAt 1 (q ∘ rot90)) = (cl (q ∘ rot90))⁻¹`
  (the first equality is `GenLoop.ext`, the second `HomotopyGroup.inv_spec`),
* it remains to see `cl (q ∘ rot90) = cl q`, i.e. that the two domain maps `rot90` and `id` are
  homotopic through self-maps of the square preserving `∂I²`.

The homotopy is the interpolation of the linear rotation between `0` and `π/2`, radially
renormalised so that the boundary of the square stays fixed; the renormalisation is clamped at
`1/4` so that no division by a vanishing quantity ever appears:

* `radHom (y,s)` — the "radial" family with parameter `s ∈ I`, denominator
  `2 · max (sqRad y) (radC s)`, with `radC 0 = 1/2`, `radC 1 = 1/4`.  Its slices fix `∂I²`
  pointwise, `radHom (·,0) = id` and `radHom (·,1) = radSqMap`.
* `rotHom (y,t)` — the rotated point `Rot_{tπ/2}(y - c)`, renormalised by the clamp
  `2 · max (rotN (y,t)) (1/4)`.  It maps `∂I²` into itself (for `y ∈ ∂I²` the rotated centred
  vector has `ℓ∞`-norm at least `1/2√2 > 1/4`), `rotHom (·,0) = radSqMap` and
  `rotHom (·,1) = radSqMap ∘ rot90`.

Composing: `rot90 ~ radSqMap ∘ rot90` (via `rotHom`), `radSqMap ∘ rot90 ~ radSqMap` (conjugating the
`radHom` family by `rot90`), `radSqMap ~ id` (via `radHom`).  Each step is a homotopy through
boundary-preserving maps, so the two-map reparametrisation lemma
`genLoop_homotopic_comp_of_homotopic` (below, an adaptation of
`Work.Stems.Hur2b.genLoop_homotopic_comp_of_homotopic_id`) gives the equality of classes.
-/

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-! ## A coordinate bound -/

/-- The coordinate `1/2 + u/(2 max r c)` lies in `[0,1]` when `|u| ≤ r` and `0 < c`.  This is the
only estimate needed to see that all the formulas below define points of the square. -/
theorem coord_mem {r u c : ℝ} (hc : 0 < c) (hu : |u| ≤ r) :
    (1/2 + u / (2 * max r c)) ∈ Set.Icc (0:ℝ) 1 := by
  have hM : 0 < max r c := lt_of_lt_of_le hc (le_max_right r c)
  have hr : r ≤ max r c := le_max_left r c
  have hD : (0:ℝ) < 2 * max r c := by linarith
  have h1 : u / (2 * max r c) ≤ 1/2 := by
    rw [div_le_iff₀ hD]; linarith [(abs_le.mp hu).2]
  have h2 : -(1/2:ℝ) ≤ u / (2 * max r c) := by
    rw [le_div_iff₀ hD]; linarith [(abs_le.mp hu).1]
  exact ⟨by linarith, by linarith⟩

/-! ## The `ℓ∞`-radius of the square about its centre -/

/-- The `ℓ∞`-radius `max (|y₀ - 1/2|) (|y₁ - 1/2|)` of a point of the square about its centre. -/
noncomputable def sqRad (y : IC 2) : ℝ := max |(y 0 : ℝ) - 1/2| |(y 1 : ℝ) - 1/2|

theorem continuous_sqRad : Continuous sqRad := by unfold sqRad; fun_prop

theorem sqRad_coord (y : IC 2) (j : Fin 2) : |((y j : unitInterval) : ℝ) - 1/2| ≤ sqRad y := by
  unfold sqRad
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem sqRad_nonneg (y : IC 2) : 0 ≤ sqRad y := le_trans (abs_nonneg _) (le_max_left _ _)

theorem sqRad_le_half (y : IC 2) : sqRad y ≤ 1/2 := by
  unfold sqRad
  refine max_le ?_ ?_
  · rw [abs_le]; constructor <;> [linarith [(y 0).2.1]; linarith [(y 0).2.2]]
  · rw [abs_le]; constructor <;> [linarith [(y 1).2.1]; linarith [(y 1).2.2]]

theorem sqRad_eq_half_of_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    sqRad y = 1/2 := by
  refine le_antisymm (sqRad_le_half y) ?_
  obtain ⟨i, hi⟩ := hy
  have hc : |((y i : unitInterval) : ℝ) - 1/2| = 1/2 := by
    rcases hi with h | h
    · rw [show ((y i : unitInterval) : ℝ) = 0 from by rw [h]; rfl]; norm_num
    · rw [show ((y i : unitInterval) : ℝ) = 1 from by rw [h]; rfl]; norm_num
  calc (1/2 : ℝ) = |((y i : unitInterval) : ℝ) - 1/2| := hc.symm
    _ ≤ sqRad y := sqRad_coord y i

/-! ## The radial family `radHom` -/

/-- The clamp constant of the radial family: `1/2` at `s = 0` (identity) and `1/4` at `s = 1`. -/
noncomputable def radC (s : unitInterval) : ℝ := 1/2 - (s : ℝ) / 4

theorem continuous_radC : Continuous radC := by unfold radC; fun_prop

theorem radC_pos (s : unitInterval) : 0 < radC s := by
  have h := s.2.2; unfold radC; linarith

theorem radC_le_half (s : unitInterval) : radC s ≤ 1/2 := by
  have h := s.2.1; unfold radC; linarith

@[simp] theorem radC_zero : radC 0 = 1/2 := by unfold radC; norm_num

@[simp] theorem radC_one : radC 1 = 1/4 := by unfold radC; norm_num

/-- The radial reparametrisation family of the square: `y ↦ c + (y - c)/(2 max (sqRad y) (radC s))`
in coordinates.  Every slice fixes `∂I²` pointwise; `s = 0` is the identity and `s = 1` is
`radSqMap`. -/
noncomputable def radHomFun (p : IC 2 × unitInterval) : IC 2 :=
  fun j => ⟨1/2 + ((p.1 j : ℝ) - 1/2) / (2 * max (sqRad p.1) (radC p.2)),
    Set.mem_Icc.mp (coord_mem (radC_pos p.2) (sqRad_coord p.1 j))⟩

theorem radHomFun_apply (p : IC 2 × unitInterval) (j : Fin 2) :
    ((radHomFun p j : unitInterval) : ℝ)
      = 1/2 + ((p.1 j : ℝ) - 1/2) / (2 * max (sqRad p.1) (radC p.2)) := rfl

theorem continuous_radHomFun : Continuous radHomFun := by
  unfold radHomFun
  apply continuous_pi
  intro j
  apply Continuous.subtype_mk
  have hnum : Continuous fun p : IC 2 × unitInterval => ((p.1 j : unitInterval) : ℝ) - 1/2 := by
    fun_prop
  have hden : Continuous fun p : IC 2 × unitInterval => 2 * max (sqRad p.1) (radC p.2) :=
    continuous_const.mul
      ((continuous_sqRad.comp continuous_fst).max (continuous_radC.comp continuous_snd))
  exact continuous_const.add (hnum.div hden (fun p => by
    have h := radC_pos p.2
    have := le_max_right (sqRad p.1) (radC p.2)
    have : (0:ℝ) < 2 * max (sqRad p.1) (radC p.2) := by linarith
    linarith))

/-- The radial family, as a continuous map. -/
noncomputable def radHom : C(IC 2 × unitInterval, IC 2) := ⟨radHomFun, continuous_radHomFun⟩

/-- The radial map of the square: the radial push of the outer half of the square onto the boundary
and the affine `2`-expansion of the inner quarter square. -/
noncomputable def radSqMap : C(IC 2, IC 2) := radHom.comp ⟨fun y => (y, 1), by fun_prop⟩

theorem radSqMap_apply (y : IC 2) (j : Fin 2) :
    ((radSqMap y j : unitInterval) : ℝ)
      = 1/2 + ((y j : ℝ) - 1/2) / (2 * max (sqRad y) (radC 1)) := by
  show ((radHomFun (y, 1) j : unitInterval) : ℝ) = _
  rw [radHomFun_apply]

theorem radHom_zero (y : IC 2) : radHom (y, 0) = y := by
  show radHomFun (y, 0) = y
  funext j
  apply Subtype.ext
  rw [radHomFun_apply]
  rw [show max (sqRad y) (radC 0) = 1/2 from by
    rw [radC_zero]; exact max_eq_right (sqRad_le_half y)]
  ring

/-- The slices of the radial family fix the boundary of the square pointwise. -/
theorem radHom_fix_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) (s : unitInterval) :
    radHom (y, s) = y := by
  show radHomFun (y, s) = y
  funext j
  apply Subtype.ext
  rw [radHomFun_apply]
  rw [show max (sqRad y) (radC s) = 1/2 from by
    rw [sqRad_eq_half_of_mem_boundary hy]
    exact max_eq_left (radC_le_half s)]
  ring

theorem radHom_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) (s : unitInterval) :
    radHom (y, s) ∈ Cube.boundary (Fin 2) := by
  rw [radHom_fix_boundary hy s]; exact hy

theorem radSqMap_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    radSqMap y ∈ Cube.boundary (Fin 2) := by
  have h := radHom_mem_boundary hy 1
  simpa only [radSqMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk] using h

/-! ## The rotation family `rotHom` -/

/-- The rotation angle `t · π/2`. -/
noncomputable def rotTheta (t : unitInterval) : ℝ := (t : ℝ) * (Real.pi / 2)

theorem continuous_rotTheta : Continuous rotTheta := by unfold rotTheta; fun_prop

theorem rotTheta_zero : rotTheta 0 = 0 := by unfold rotTheta; simp

theorem rotTheta_one : rotTheta 1 = Real.pi / 2 := by unfold rotTheta; simp

/-- The cosine of the rotation angle. -/
noncomputable def rotC (t : unitInterval) : ℝ := Real.cos (rotTheta t)

/-- The sine of the rotation angle. -/
noncomputable def rotS (t : unitInterval) : ℝ := Real.sin (rotTheta t)

theorem continuous_rotC : Continuous rotC := Real.continuous_cos.comp continuous_rotTheta

theorem continuous_rotS : Continuous rotS := Real.continuous_sin.comp continuous_rotTheta

/-- The first centred coordinate of the rotated point `Rot_{tπ/2}(y - c)`. -/
noncomputable def rotAX (p : IC 2 × unitInterval) : ℝ :=
  ((p.1 0 : ℝ) - 1/2) * rotC p.2 - ((p.1 1 : ℝ) - 1/2) * rotS p.2

/-- The second centred coordinate of the rotated point `Rot_{tπ/2}(y - c)`. -/
noncomputable def rotAY (p : IC 2 × unitInterval) : ℝ :=
  ((p.1 0 : ℝ) - 1/2) * rotS p.2 + ((p.1 1 : ℝ) - 1/2) * rotC p.2

/-- The `ℓ∞`-norm of the rotated centred coordinates. -/
noncomputable def rotN (p : IC 2 × unitInterval) : ℝ := max |rotAX p| |rotAY p|

/-- The rotated centred coordinates, indexed by `Fin 2`. -/
noncomputable def rotV (p : IC 2 × unitInterval) (j : Fin 2) : ℝ :=
  if j = 0 then rotAX p else rotAY p

theorem rotV_zero (p : IC 2 × unitInterval) : rotV p 0 = rotAX p := by simp [rotV]

theorem rotV_one (p : IC 2 × unitInterval) : rotV p 1 = rotAY p := by simp [rotV]

theorem rotAX_le_rotN (p : IC 2 × unitInterval) : |rotAX p| ≤ rotN p := by
  unfold rotN; exact le_max_left _ _

theorem rotAY_le_rotN (p : IC 2 × unitInterval) : |rotAY p| ≤ rotN p := by
  unfold rotN; exact le_max_right _ _

theorem rotN_nonneg (p : IC 2 × unitInterval) : 0 ≤ rotN p :=
  le_trans (abs_nonneg _) (rotAX_le_rotN p)

theorem rotAX_sq_le (p : IC 2 × unitInterval) : rotAX p ^ 2 ≤ rotN p ^ 2 := by
  have h := mul_self_le_mul_self (abs_nonneg (rotAX p)) (rotAX_le_rotN p)
  rwa [abs_mul_abs_self, ← pow_two, ← pow_two] at h

theorem rotAY_sq_le (p : IC 2 × unitInterval) : rotAY p ^ 2 ≤ rotN p ^ 2 := by
  have h := mul_self_le_mul_self (abs_nonneg (rotAY p)) (rotAY_le_rotN p)
  rwa [abs_mul_abs_self, ← pow_two, ← pow_two] at h

theorem continuous_rotAX : Continuous rotAX := by
  have hc : Continuous fun p : IC 2 × unitInterval => rotC p.2 :=
    continuous_rotC.comp continuous_snd
  have hs : Continuous fun p : IC 2 × unitInterval => rotS p.2 :=
    continuous_rotS.comp continuous_snd
  have h0 : Continuous fun p : IC 2 × unitInterval => (((p.1 0 : unitInterval)) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply 0).comp continuous_fst)
  have h1 : Continuous fun p : IC 2 × unitInterval => (((p.1 1 : unitInterval)) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply 1).comp continuous_fst)
  exact ((h0.sub continuous_const).mul hc).sub ((h1.sub continuous_const).mul hs)

theorem continuous_rotAY : Continuous rotAY := by
  have hc : Continuous fun p : IC 2 × unitInterval => rotC p.2 :=
    continuous_rotC.comp continuous_snd
  have hs : Continuous fun p : IC 2 × unitInterval => rotS p.2 :=
    continuous_rotS.comp continuous_snd
  have h0 : Continuous fun p : IC 2 × unitInterval => (((p.1 0 : unitInterval)) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply 0).comp continuous_fst)
  have h1 : Continuous fun p : IC 2 × unitInterval => (((p.1 1 : unitInterval)) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply 1).comp continuous_fst)
  exact ((h0.sub continuous_const).mul hs).add ((h1.sub continuous_const).mul hc)

theorem continuous_rotN : Continuous rotN := by
  unfold rotN
  exact continuous_rotAX.abs.max continuous_rotAY.abs

theorem continuous_rotV (j : Fin 2) : Continuous fun p : IC 2 × unitInterval => rotV p j := by
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with h | h
  · rw [h, show (fun p : IC 2 × unitInterval => rotV p 0) = rotAX from
      funext fun p => rotV_zero p]
    exact continuous_rotAX
  · rw [h, show (fun p : IC 2 × unitInterval => rotV p 1) = rotAY from
      funext fun p => rotV_one p]
    exact continuous_rotAY

theorem rotV_le_rotN (p : IC 2 × unitInterval) (j : Fin 2) : |rotV p j| ≤ rotN p := by
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with h | h
  · rw [h, rotV_zero]; exact rotAX_le_rotN p
  · rw [h, rotV_one]; exact rotAY_le_rotN p

/-- The rotation family of the square: the rotated centred coordinates renormalised by
`2 · max (rotN (y,t)) (1/4)`. -/
noncomputable def rotHomFun (p : IC 2 × unitInterval) : IC 2 :=
  fun j => ⟨1/2 + rotV p j / (2 * max (rotN p) (1/4)),
    Set.mem_Icc.mp (coord_mem (by norm_num) (rotV_le_rotN p j))⟩

theorem continuous_rotHomFun : Continuous rotHomFun := by
  unfold rotHomFun
  apply continuous_pi
  intro j
  apply Continuous.subtype_mk
  have hden : Continuous fun p : IC 2 × unitInterval => 2 * max (rotN p) (1/4) :=
    continuous_const.mul (continuous_rotN.max continuous_const)
  exact continuous_const.add ((continuous_rotV j).div hden (fun p => by
    have h := le_max_right (rotN p) ((1:ℝ)/4)
    have : (0:ℝ) < 2 * max (rotN p) (1/4) := by linarith
    linarith))

/-- The rotation family, as a continuous map. -/
noncomputable def rotHom : C(IC 2 × unitInterval, IC 2) :=
  ⟨rotHomFun, continuous_rotHomFun⟩

theorem rotHom_apply (p : IC 2 × unitInterval) (j : Fin 2) :
    ((rotHom p j : unitInterval) : ℝ) = 1/2 + rotV p j / (2 * max (rotN p) (1/4)) := rfl

/-! ### The values of the rotation at the endpoints -/

theorem rotAX_zero_coord (y : IC 2) : rotAX (y, 0) = (y 0 : ℝ) - 1/2 := by
  have h1 : rotC (0 : unitInterval) = 1 := by simp [rotC, rotTheta_zero]
  have h2 : rotS (0 : unitInterval) = 0 := by simp [rotS, rotTheta_zero]
  unfold rotAX
  rw [h1, h2]; ring

theorem rotAY_zero_coord (y : IC 2) : rotAY (y, 0) = (y 1 : ℝ) - 1/2 := by
  have h1 : rotC (0 : unitInterval) = 1 := by simp [rotC, rotTheta_zero]
  have h2 : rotS (0 : unitInterval) = 0 := by simp [rotS, rotTheta_zero]
  unfold rotAY
  rw [h1, h2]; ring

theorem rotAX_one_coord (y : IC 2) : rotAX (y, 1) = -((y 1 : ℝ) - 1/2) := by
  have h1 : rotC (1 : unitInterval) = 0 := by simp [rotC, rotTheta_one]
  have h2 : rotS (1 : unitInterval) = 1 := by simp [rotS, rotTheta_one]
  unfold rotAX
  rw [h1, h2]; ring

theorem rotAY_one_coord (y : IC 2) : rotAY (y, 1) = (y 0 : ℝ) - 1/2 := by
  have h1 : rotC (1 : unitInterval) = 0 := by simp [rotC, rotTheta_one]
  have h2 : rotS (1 : unitInterval) = 1 := by simp [rotS, rotTheta_one]
  unfold rotAY
  rw [h1, h2]; ring

theorem rotN_zero (y : IC 2) : rotN (y, 0) = sqRad y := by
  unfold rotN sqRad
  rw [rotAX_zero_coord, rotAY_zero_coord]

theorem rotN_one (y : IC 2) : rotN (y, 1) = sqRad y := by
  unfold rotN sqRad
  rw [rotAX_one_coord, rotAY_one_coord, abs_neg, max_comm]

/-- The quarter turn `(y₀,y₁) ↦ (σ y₁, y₀)` of the square. -/
noncomputable def rotMapFun (y : IC 2) : IC 2 := pair2 (σ (y 1)) (y 0)

/-- The quarter turn of the square, as a continuous map. -/
noncomputable def rotMap : C(IC 2, IC 2) :=
  ⟨rotMapFun, continuous_pair2 (unitInterval.continuous_symm.comp (continuous_apply 1))
    (continuous_apply 0)⟩

theorem rotMap_apply (y : IC 2) : rotMap y = pair2 (σ (y 1)) (y 0) := rfl

theorem rotMap_zero_coord (y : IC 2) : ((rotMap y) 0 : ℝ) = 1 - (y 1 : ℝ) := by
  rw [rotMap_apply, pair2_zero, unitInterval.coe_symm_eq]

theorem rotMap_one_coord (y : IC 2) : ((rotMap y) 1 : ℝ) = (y 0 : ℝ) := by
  rw [rotMap_apply, pair2_one]

theorem sqRad_rotMap (y : IC 2) : sqRad (rotMap y) = sqRad y := by
  unfold sqRad
  rw [rotMap_zero_coord, rotMap_one_coord,
    show (1:ℝ) - (y 1 : ℝ) - 1/2 = -((y 1 : ℝ) - 1/2) from by ring, abs_neg, max_comm]

theorem rotMap_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    rotMap y ∈ Cube.boundary (Fin 2) := by
  obtain ⟨i, hi⟩ := hy
  have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi01 with h | h
  · rw [h] at hi
    refine ⟨1, ?_⟩
    rw [rotMap_apply, pair2_one]; exact hi
  · rw [h] at hi
    refine ⟨0, ?_⟩
    rw [rotMap_apply, pair2_zero]
    rcases hi with hi | hi
    · right; rw [hi, unitInterval.symm_zero]
    · left; rw [hi, unitInterval.symm_one]

theorem rotHom_zero (y : IC 2) : rotHom (y, 0) = radSqMap y := by
  funext j
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with h | h
  · rw [h]
    apply Subtype.ext
    rw [rotHom_apply, radSqMap_apply, rotV_zero, rotAX_zero_coord, rotN_zero, radC_one]
  · rw [h]
    apply Subtype.ext
    rw [rotHom_apply, radSqMap_apply, rotV_one, rotAY_zero_coord, rotN_zero, radC_one]

theorem rotHom_one (y : IC 2) : rotHom (y, 1) = radSqMap (rotMap y) := by
  funext j
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with h | h
  · rw [h]
    apply Subtype.ext
    rw [rotHom_apply, radSqMap_apply, rotV_zero, rotAX_one_coord, rotN_one, sqRad_rotMap,
      rotMap_zero_coord, radC_one]
    ring
  · rw [h]
    apply Subtype.ext
    rw [rotHom_apply, radSqMap_apply, rotV_one, rotAY_one_coord, rotN_one, sqRad_rotMap,
      rotMap_one_coord, radC_one]

/-! ### The rotation family preserves the boundary -/

/-- The rotation of the square around its centre preserves the euclidean norm of the centred
coordinates. -/
theorem rotAX_sq_add (p : IC 2 × unitInterval) :
    rotAX p ^ 2 + rotAY p ^ 2
      = ((p.1 0 : ℝ) - 1/2)^2 + ((p.1 1 : ℝ) - 1/2)^2 := by
  simp only [rotAX, rotAY, rotC, rotS]
  nlinarith [Real.cos_sq_add_sin_sq (rotTheta p.2)]

/-- On the boundary of the square the rotated centred vector has `ℓ∞`-norm more than `1/4`, so the
clamp in `rotHomFun` never bites there. -/
theorem le_rotN_of_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) (t : unitInterval) :
    (1/4 : ℝ) ≤ rotN (y, t) := by
  have hu : (1/4 : ℝ) ≤ ((y 0 : ℝ) - 1/2)^2 + ((y 1 : ℝ) - 1/2)^2 := by
    obtain ⟨i, hi⟩ := hy
    have hsq : (1/4 : ℝ) ≤ ((y i : ℝ) - 1/2)^2 := by
      rcases hi with h | h
      · have : ((y i : unitInterval) : ℝ) = 0 := by rw [h]; rfl
        rw [this]; norm_num
      · have : ((y i : unitInterval) : ℝ) = 1 := by rw [h]; rfl
        rw [this]; norm_num
    have hle := Finset.single_le_sum (f := fun j : Fin 2 => ((y j : ℝ) - 1/2)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [Fin.sum_univ_two] at hle
    linarith
  have hv := rotAX_sq_add (y, t)
  have h0 := rotAX_sq_le (y, t)
  have h1 := rotAY_sq_le (y, t)
  have hN := rotN_nonneg (y, t)
  nlinarith [sq_nonneg (rotN (y, t) - 1/4), sq_nonneg (rotN (y, t) + 1/4)]

/-- If `N = |v| ≥ 1/4` then the normalised coordinate `1/2 + v/(2 max N 1/4)` is `0` or `1`. -/
theorem coord_eq_zero_or_one {v N : ℝ} (hN : N = |v|) (hNge : 1/4 ≤ N) :
    1/2 + v / (2 * max N (1/4)) = 0 ∨ 1/2 + v / (2 * max N (1/4)) = 1 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hNge
  have habs : (0:ℝ) < |v| := by rw [← hN]; exact hNpos
  have hden : (2:ℝ) * |v| ≠ 0 := by positivity
  rw [max_eq_left hNge]
  rcases lt_or_ge v 0 with hv | hv
  · left
    have h2 : v / (2 * |v|) = -(1/2) := by
      rw [div_eq_iff hden, abs_of_neg hv]
      ring
    rw [hN, h2]; norm_num
  · right
    have h2 : v / (2 * |v|) = 1/2 := by
      rw [div_eq_iff hden, abs_of_nonneg hv]
      ring
    rw [hN, h2]; norm_num

/-- Every slice of the rotation family maps `∂I²` into `∂I²`. -/
theorem rotHom_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) (t : unitInterval) :
    rotHom (y, t) ∈ Cube.boundary (Fin 2) := by
  have hNge : (1/4 : ℝ) ≤ rotN (y, t) := le_rotN_of_mem_boundary hy t
  rcases le_total |rotAX (y, t)| |rotAY (y, t)| with h | h
  · have hN : rotN (y, t) = |rotAY (y, t)| := by
      unfold rotN; exact max_eq_right h
    refine ⟨1, ?_⟩
    rcases coord_eq_zero_or_one hN hNge with hc | hc
    · left
      apply Subtype.ext
      rw [rotHom_apply, rotV_one]
      exact hc
    · right
      apply Subtype.ext
      rw [rotHom_apply, rotV_one]
      exact hc
  · have hN : rotN (y, t) = |rotAX (y, t)| := by
      unfold rotN; exact max_eq_left h
    refine ⟨0, ?_⟩
    rcases coord_eq_zero_or_one hN hNge with hc | hc
    · left
      apply Subtype.ext
      rw [rotHom_apply, rotV_zero]
      exact hc
    · right
      apply Subtype.ext
      rw [rotHom_apply, rotV_zero]
      exact hc

/-! ## The two-map reparametrisation lemma -/

/-- **Reparametrisation of a based cube by a homotopy of boundary-preserving self-maps.**  If a
homotopy `H` connects two self-maps `φ`, `ψ` of the cube that both preserve `∂I^n` (and all of
whose slices preserve it as well), then the based cubes `p ∘ φ` and `p ∘ ψ` are homotopic relative
to the boundary.  (This is `genLoop_homotopic_comp_of_homotopic_id` with both endpoints kept.) -/
theorem genLoop_homotopic_comp_of_homotopic {n : ℕ} [NeZero n] {Y : Type} [TopologicalSpace Y]
    {y₀ : Y} (φ ψ : C(IC n, IC n))
    (hφ : ∀ y ∈ Cube.boundary (Fin n), φ y ∈ Cube.boundary (Fin n))
    (hψ : ∀ y ∈ Cube.boundary (Fin n), ψ y ∈ Cube.boundary (Fin n))
    (H : C(IC n × unitInterval, IC n))
    (h0 : ∀ y, H (y, 0) = φ y) (h1 : ∀ y, H (y, 1) = ψ y)
    (Hb : ∀ y ∈ Cube.boundary (Fin n), ∀ t, H (y, t) ∈ Cube.boundary (Fin n))
    (p : GenLoop (Fin n) Y y₀)
    (hpφ : ∀ y ∈ Cube.boundary (Fin n), p.1 (φ y) = y₀)
    (hpψ : ∀ y ∈ Cube.boundary (Fin n), p.1 (ψ y) = y₀) :
    GenLoop.Homotopic ⟨p.1.comp φ, hpφ⟩ ⟨p.1.comp ψ, hpψ⟩ := by
  refine ⟨⟨⟨fun z : unitInterval × IC n => p.1 (H (z.2, z.1)), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact p.1.continuous.comp (H.continuous.comp (continuous_snd.prodMk continuous_fst))
  · intro y
    show p.1 (H (y, 0)) = p.1 (φ y)
    rw [h0]
  · intro y
    show p.1 (H (y, 1)) = p.1 (ψ y)
    rw [h1]
  · intro t y hy
    show p.1 (H (y, t)) = p.1 (φ y)
    rw [p.2 (H (y, t)) (Hb y hy t), hpφ y hy]

/-- **Reparametrisation of a based cube by a boundary-preserving self-map homotopic to the
identity.**  Same as above with the second map the identity, so that the endpoint is `p` itself.
(Copy of `Work.Stems.Hur2b.genLoop_homotopic_comp_of_homotopic_id` without the simple connectivity
hypothesis.) -/
theorem genLoop_homotopic_comp_of_id {n : ℕ} [NeZero n] {Y : Type} [TopologicalSpace Y]
    {y₀ : Y} (p : GenLoop (Fin n) Y y₀) (φ : C(IC n, IC n))
    (hφ : ∀ y ∈ Cube.boundary (Fin n), φ y ∈ Cube.boundary (Fin n))
    (H : C(IC n × unitInterval, IC n))
    (h0 : ∀ y, H (y, 0) = φ y) (h1 : ∀ y, H (y, 1) = y)
    (Hb : ∀ y ∈ Cube.boundary (Fin n), ∀ t, H (y, t) ∈ Cube.boundary (Fin n)) :
    GenLoop.Homotopic ⟨p.1.comp φ, fun y hy => p.2 (φ y) (hφ y hy)⟩ p := by
  refine ⟨⟨⟨fun z : unitInterval × IC n => p.1 (H (z.2, z.1)), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact p.1.continuous.comp (H.continuous.comp (continuous_snd.prodMk continuous_fst))
  · intro y
    show p.1 (H (y, 0)) = p.1 (φ y)
    rw [h0]
  · intro y
    show p.1 (H (y, 1)) = p.1 y
    rw [h1]
  · intro t y hy
    show p.1 (H (y, t)) = p.1 (φ y)
    rw [p.2 (H (y, t)) (Hb y hy t), p.2 (φ y) (hφ y hy)]

/-- The class of a based cube depends only on its homotopy class relative to the boundary. -/
theorem cl_eq_of_homotopic {p q : GenLoop (Fin 2) X x₀} (h : GenLoop.Homotopic p q) :
    cl x₀ p = cl x₀ q := Quotient.sound h

/-- The class of a based cube reversed in one coordinate is the inverse of its class. -/
theorem cl_symmAt_coord (i : Fin 2) (p : GenLoop (Fin 2) X x₀) :
    cl x₀ (GenLoop.symmAt i p) = (cl x₀ p)⁻¹ := by
  rw [cl, cl]
  exact (HomotopyGroup.inv_spec (N := Fin 2) (i := i) (p := p)).symm

/-! ## `rot90` is class-preserving -/

/-- The homotopy `(y,s) ↦ radHom (rotMap y, s)`, from `rotMap` to `radSqMap ∘ rotMap`. -/
noncomputable def rotRadHom : C(IC 2 × unitInterval, IC 2) :=
  radHom.comp (rotMap.prodMap (ContinuousMap.id unitInterval))

theorem rotRadHom_zero (y : IC 2) : rotRadHom (y, 0) = rotMap y := by
  show radHom (rotMap y, 0) = rotMap y
  exact radHom_zero (rotMap y)

theorem rotRadHom_one (y : IC 2) : rotRadHom (y, 1) = radSqMap (rotMap y) := by
  show radHom (rotMap y, 1) = radSqMap (rotMap y)
  rfl

theorem rotRadHom_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) (s : unitInterval) :
    rotRadHom (y, s) ∈ Cube.boundary (Fin 2) := by
  show radHom (rotMap y, s) ∈ Cube.boundary (Fin 2)
  exact radHom_mem_boundary (rotMap_mem_boundary hy) s

/-- The radial family run backwards: `(y,s) ↦ radHom (y, σ s)`, from `radSqMap` to `id`. -/
noncomputable def radRev : C(IC 2 × unitInterval, IC 2) :=
  radHom.comp (ContinuousMap.prodMap (ContinuousMap.id (IC 2)) ⟨σ, unitInterval.continuous_symm⟩)

theorem radRev_zero (y : IC 2) : radRev (y, 0) = radSqMap y := by
  show radHom (y, σ 0) = radSqMap y
  rw [show σ (0 : unitInterval) = 1 from unitInterval.symm_zero]
  rfl

theorem radRev_one (y : IC 2) : radRev (y, 1) = y := by
  show radHom (y, σ 1) = y
  rw [show σ (1 : unitInterval) = 0 from unitInterval.symm_one, radHom_zero]

theorem radRev_mem_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) (s : unitInterval) :
    radRev (y, s) ∈ Cube.boundary (Fin 2) := by
  show radHom (y, σ s) ∈ Cube.boundary (Fin 2)
  exact radHom_mem_boundary hy (σ s)

/-- **The quarter turn does not change the class of a based cube.** -/
theorem homotopic_comp_rotMap (q : GenLoop (Fin 2) X x₀) :
    GenLoop.Homotopic
      (compGenLoop (c := q) (φ := rotMap) (fun y hy => q.2 _ (rotMap_mem_boundary hy))) q := by
  -- `rot90 ~ radSqMap ∘ rot90` (the rotation family)
  have hA : GenLoop.Homotopic
      (compGenLoop (c := q) (φ := rotMap) (fun y hy => q.2 _ (rotMap_mem_boundary hy)))
      (compGenLoop (c := q) (φ := radSqMap.comp rotMap)
        (fun y hy => q.2 _ (radSqMap_mem_boundary (rotMap_mem_boundary hy)))) :=
    genLoop_homotopic_comp_of_homotopic rotMap (radSqMap.comp rotMap)
      (fun y hy => rotMap_mem_boundary hy)
      (fun y hy => radSqMap_mem_boundary (rotMap_mem_boundary hy)) rotRadHom
      (fun y => rotRadHom_zero y) (fun y => rotRadHom_one y)
      (fun y hy s => rotRadHom_mem_boundary hy s) q
      (fun y hy => q.2 _ (rotMap_mem_boundary hy))
      (fun y hy => q.2 _ (radSqMap_mem_boundary (rotMap_mem_boundary hy)))
  -- `radSqMap ~ radSqMap ∘ rot90` (the rotation family and the radial family)
  have hB : GenLoop.Homotopic
      (compGenLoop (c := q) (φ := radSqMap) (fun y hy => q.2 _ (radSqMap_mem_boundary hy)))
      (compGenLoop (c := q) (φ := radSqMap.comp rotMap)
        (fun y hy => q.2 _ (radSqMap_mem_boundary (rotMap_mem_boundary hy)))) :=
    genLoop_homotopic_comp_of_homotopic radSqMap (radSqMap.comp rotMap)
      (fun y hy => radSqMap_mem_boundary hy)
      (fun y hy => radSqMap_mem_boundary (rotMap_mem_boundary hy)) rotHom
      (fun y => rotHom_zero y) (fun y => rotHom_one y)
      (fun y hy t => rotHom_mem_boundary hy t) q
      (fun y hy => q.2 _ (radSqMap_mem_boundary hy))
      (fun y hy => q.2 _ (radSqMap_mem_boundary (rotMap_mem_boundary hy)))
  -- `radSqMap ~ id` (the radial family backwards)
  have hC : GenLoop.Homotopic
      (compGenLoop (c := q) (φ := radSqMap) (fun y hy => q.2 _ (radSqMap_mem_boundary hy))) q :=
    genLoop_homotopic_comp_of_id q radSqMap (fun y hy => radSqMap_mem_boundary hy) radRev
      (fun y => radRev_zero y) (fun y => radRev_one y)
      (fun y hy s => radRev_mem_boundary hy s)
  exact (hA.trans hB.symm).trans hC

theorem cl_comp_rotMap (q : GenLoop (Fin 2) X x₀) :
    cl x₀ (compGenLoop (c := q) (φ := rotMap) (fun y hy => q.2 _ (rotMap_mem_boundary hy)))
      = cl x₀ q :=
  cl_eq_of_homotopic (homotopic_comp_rotMap q)

/-! ## The swap -/

/-- The reversal of the second coordinate of the square, as it occurs in Mathlib's `symmAt`. -/
theorem pair2_flip (y : IC 2) :
    pair2 (y 0) (σ (y 1)) = (fun j => if j = 1 then σ (y 1) else y j) := by
  funext j
  fin_cases j <;> simp [pair2]

/-- `swapMap = rotMap ∘ (reversal of the second coordinate)`. -/
theorem swapMap_eq (y : IC 2) :
    swapMap y = rotMap (fun j => if j = 1 then σ (y 1) else y j) := by
  rw [← pair2_flip y, rotMap_apply, pair2_zero, pair2_one, unitInterval.symm_symm]
  rfl

/-- The cube `q ∘ swapMap` is the second-coordinate reversal of the cube `q ∘ rotMap`. -/
theorem compGenLoop_swapMap_eq_symmAt (q : GenLoop (Fin 2) X x₀) :
    (compGenLoop (c := q) (φ := swapMap) (fun y hy => q.2 _ (swapMap_boundary hy))
        : GenLoop (Fin 2) X x₀)
      = GenLoop.symmAt 1
          (compGenLoop (c := q) (φ := rotMap) (fun y hy => q.2 _ (rotMap_mem_boundary hy))) := by
  refine GenLoop.ext _ _ fun y => ?_
  rw [compGenLoop_apply]
  rw [show (GenLoop.symmAt 1 (compGenLoop (c := q) (φ := rotMap)
        (fun y hy => q.2 _ (rotMap_mem_boundary hy)))) y
      = (compGenLoop (c := q) (φ := rotMap) (fun y hy => q.2 _ (rotMap_mem_boundary hy)))
          (fun j => if j = 1 then σ (y 1) else y j) from by
    simp [GenLoop.symmAt, GenLoop.copy]]
  rw [compGenLoop_apply]
  rw [swapMap_eq y]

/-- **The class of a based `2`-cube reparametrised by the coordinate swap is the inverse of its
class.** -/
theorem cl_comp_swapMap {X : Type} [TopologicalSpace X] {x₀ : X} (q : GenLoop (Fin 2) X x₀) :
    Work.Stems.Hur2b.cl x₀
        (Work.Stems.Hur2b.compGenLoop (c := q) (φ := Work.Stems.Hur2b.swapMap)
          (fun y hy => q.2 _ (Work.Stems.Hur2b.swapMap_boundary hy)))
      = (Work.Stems.Hur2b.cl x₀ q)⁻¹ := by
  rw [compGenLoop_swapMap_eq_symmAt q, cl_symmAt_coord 1, cl_comp_rotMap]

end

end Work.Stems.Hur2b
