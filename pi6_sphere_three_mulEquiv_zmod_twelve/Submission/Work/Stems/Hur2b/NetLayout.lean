import Mathlib
import Submission.Work.Stems.Hur2b.GluingModel
import Submission.Work.Stems.Hur2b.Assembly
import Submission.Work.Stems.Hur2b.cl_cut_vertical

/-!
# The T-net layout of the square, and its six face-readings

This file fixes the combinatorial data of the "pinched model" of the gluing of the six faces of a
3-cube: the six content cells of the square `I²` (a T-net: the four belt cells in the middle row
plus the two caps above and below the second belt cell), and the affine `reading` of each cell onto
its face of `∂I³`.

The cells are cells of the uniform `8 × 8` grid: the cell `(i,j)` is
`[i/8,(i+1)/8] × [j/8,(j+1)/8]`.  The six content cells are indexed in the order
`[y=0], [x=0], [y=1], [x=1], [z=0], [z=1]`, sitting at the grid cells `(2,3), (3,3), (4,3), (5,3),
(3,2), (3,4)` and are read onto the faces `{y=1}, {x=0}, {y=0}, {x=1}, {z=0}, {z=1}` respectively.

Each `reading` is affine, rescaled so that the cell maps onto the face's square; the sign of its
linear part is recorded in `netSign`, and `netSign k · (-1)^{i+b} = +1` for all six cells, which is
what makes the alternating product of the six face classes come out as `prod6`.

The `cut` machinery (`cl_cut_vertical`, `cl_transAt_zero/one`) computes the class of a based cube
from the classes of its readings on the cells of such a grid, provided the cube vanishes on the
grid lines (`gLine k = k/8`).
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-! ## The readings -/

/-- A continuous function `t ↦ clamp (α t + a)`. -/
def aff (α a : ℝ) (s : unitInterval) : unitInterval := clamp (α * (s : ℝ) + a)

theorem continuous_aff (α a : ℝ) : Continuous (aff α a) :=
  continuous_clamp.comp (by fun_prop)

/-- A reading `I² → I²` given by `(t₀,t₁) ↦ (α t₀ + a, β t₁ + b)` (clamped). -/
def readMap (α a β b : ℝ) : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (aff α a (y 0)) (aff β b (y 1)),
    continuous_pair2 (continuous_aff α a |>.comp (continuous_apply 0))
      (continuous_aff β b |>.comp (continuous_apply 1))⟩

/-- The swapped reading `(t₀,t₁) ↦ (β t₁ + b, α t₀ + a)` (clamped). -/
def readSwap (α a β b : ℝ) : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (aff β b (y 1)) (aff α a (y 0)),
    continuous_pair2 (continuous_aff β b |>.comp (continuous_apply 1))
      (continuous_aff α a |>.comp (continuous_apply 0))⟩

/-! ## The grid -/

/-- The nine grid lines `k/8` of the square. -/
def gLine (k : Fin 9) : unitInterval :=
  ⟨((k : ℕ) : ℝ) / 8, by
    have h1 : (0:ℝ) ≤ ((k:ℕ):ℝ) := Nat.cast_nonneg _
    have h2 : (k:ℕ) ≤ 8 := by have := k.isLt; omega
    have h3 : ((k:ℕ):ℝ) ≤ 8 := by exact_mod_cast h2
    exact ⟨by linarith, by linarith⟩⟩

@[simp] theorem gLine_coe (k : Fin 9) : ((gLine k : unitInterval) : ℝ) = ((k:ℕ):ℝ)/8 := rfl

theorem gLine8_bound (i : Fin 8) : ((i:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 :=
  ⟨by positivity, by
    have h2 : (i:ℕ) ≤ 7 := by have := i.isLt; omega
    have h3 : ((i:ℕ):ℝ) ≤ 7 := by exact_mod_cast h2
    linarith⟩

/-- The `(i,j)`-cell reading: the affine map of the square onto the cell `(i,j)` of the grid,
`(t₀,t₁) ↦ ((t₀ + i)/8, (t₁ + j)/8)` (clamped, so that it is continuous and total). -/
def cellRead (i j : Fin 8) : C(IC 2, IC 2) :=
  readMap (1/8) (((i : ℕ) : ℝ)/8) (1/8) (((j : ℕ) : ℝ)/8)

theorem cellRead_coord0_zero (i j : Fin 8) (y : IC 2) (hy : y 0 = 0) :
    (cellRead i j y) 0 = gLine i.castSucc := by
  apply Subtype.ext
  have hval : ((cellRead i j y) 0 : ℝ) = clamp ((1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8) := rfl
  rw [hval, show (y 0 : ℝ) = 0 by rw [hy]; rfl, mul_zero, zero_add]
  show ((clamp (((i:ℕ):ℝ)/8) : unitInterval) : ℝ) = ((gLine i.castSucc : unitInterval) : ℝ)
  rw [gLine_coe, Fin.val_castSucc]
  exact congrArg Subtype.val (clamp_coe (⟨((i:ℕ):ℝ)/8, gLine8_bound i⟩ : unitInterval))

theorem cellRead_coord0_one (i j : Fin 8) (y : IC 2) (hy : y 0 = 1) :
    (cellRead i j y) 0 = gLine i.succ := by
  apply Subtype.ext
  have hval : ((cellRead i j y) 0 : ℝ) = clamp ((1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8) := rfl
  have hb : (((i:ℕ):ℝ)+1)/8 ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    have h2 : (i:ℕ) ≤ 7 := by have := i.isLt; omega
    have h3 : ((i:ℕ):ℝ) ≤ 7 := by exact_mod_cast h2
    linarith
  have key : ((clamp ((((i:ℕ):ℝ)+1)/8) : unitInterval) : ℝ) = (((i:ℕ):ℝ)+1)/8 :=
    congrArg Subtype.val (clamp_coe (⟨(((i:ℕ):ℝ)+1)/8, hb⟩ : unitInterval))
  rw [hval, show (y 0 : ℝ) = 1 by rw [hy]; rfl, mul_one,
      show (1:ℝ)/8 + ((i:ℕ):ℝ)/8 = (((i:ℕ):ℝ)+1)/8 by ring]
  rw [show ((gLine i.succ : unitInterval) : ℝ) = (((i:ℕ):ℝ)+1)/8 by
    rw [gLine_coe, Fin.val_succ]; push_cast; ring]
  exact key

theorem cellRead_coord1_zero (i j : Fin 8) (y : IC 2) (hy : y 1 = 0) :
    (cellRead i j y) 1 = gLine j.castSucc := by
  apply Subtype.ext
  have hval : ((cellRead i j y) 1 : ℝ) = clamp ((1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8) := rfl
  rw [hval, show (y 1 : ℝ) = 0 by rw [hy]; rfl, mul_zero, zero_add]
  show ((clamp (((j:ℕ):ℝ)/8) : unitInterval) : ℝ) = ((gLine j.castSucc : unitInterval) : ℝ)
  rw [gLine_coe, Fin.val_castSucc]
  exact congrArg Subtype.val (clamp_coe (⟨((j:ℕ):ℝ)/8, gLine8_bound j⟩ : unitInterval))

theorem cellRead_coord1_one (i j : Fin 8) (y : IC 2) (hy : y 1 = 1) :
    (cellRead i j y) 1 = gLine j.succ := by
  apply Subtype.ext
  have hval : ((cellRead i j y) 1 : ℝ) = clamp ((1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8) := rfl
  have hb : (((j:ℕ):ℝ)+1)/8 ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    have h2 : (j:ℕ) ≤ 7 := by have := j.isLt; omega
    have h3 : ((j:ℕ):ℝ) ≤ 7 := by exact_mod_cast h2
    linarith
  have key : ((clamp ((((j:ℕ):ℝ)+1)/8) : unitInterval) : ℝ) = (((j:ℕ):ℝ)+1)/8 :=
    congrArg Subtype.val (clamp_coe (⟨(((j:ℕ):ℝ)+1)/8, hb⟩ : unitInterval))
  rw [hval, show (y 1 : ℝ) = 1 by rw [hy]; rfl, mul_one,
      show (1:ℝ)/8 + ((j:ℕ):ℝ)/8 = (((j:ℕ):ℝ)+1)/8 by ring]
  rw [show ((gLine j.succ : unitInterval) : ℝ) = (((j:ℕ):ℝ)+1)/8 by
    rw [gLine_coe, Fin.val_succ]; push_cast; ring]
  exact key

/-- A point of `I²` is determined by its two coordinates. -/
theorem eq_pair2 (y : IC 2) : y = pair2 (y 0) (y 1) := by
  funext t; fin_cases t <;> simp [pair2]

/-- **The boundary condition**: if `p` vanishes on the nine grid lines, then each cell reading of
`p` is a based cube. -/
theorem cellRead_boundary {X : Type} [TopologicalSpace X] {x₀ : X} (p : GenLoop (Fin 2) X x₀)
    (hV : ∀ (k : Fin 9) (s : unitInterval), p.1 (pair2 (gLine k) s) = x₀)
    (hH : ∀ (k : Fin 9) (s : unitInterval), p.1 (pair2 s (gLine k)) = x₀)
    (i j : Fin 8) : ∀ y ∈ Cube.boundary (Fin 2), p.1 ((cellRead i j) y) = x₀ := by
  intro y hy
  rcases hy with ⟨c, hc | hc⟩ <;> fin_cases c
  · have h1 : ((cellRead i j) y) 0 = gLine i.castSucc := cellRead_coord0_zero i j y hc
    rw [eq_pair2 ((cellRead i j) y), h1]
    exact hV i.castSucc _
  · have h1 : ((cellRead i j) y) 1 = gLine j.castSucc := cellRead_coord1_zero i j y hc
    rw [eq_pair2 ((cellRead i j) y), h1]
    exact hH j.castSucc _
  · have h1 : ((cellRead i j) y) 0 = gLine i.succ := cellRead_coord0_one i j y hc
    rw [eq_pair2 ((cellRead i j) y), h1]
    exact hV i.succ _
  · have h1 : ((cellRead i j) y) 1 = gLine j.succ := cellRead_coord1_one i j y hc
    rw [eq_pair2 ((cellRead i j) y), h1]
    exact hH j.succ _

/-- The based cube obtained by reading the `(i,j)`-cell with `p` (the boundary condition being
supplied by the caller). -/
noncomputable def cellCube {X : Type} [TopologicalSpace X] {x₀ : X} (p : GenLoop (Fin 2) X x₀)
    (i j : Fin 8) (h : ∀ y ∈ Cube.boundary (Fin 2), p.1 ((cellRead i j) y) = x₀) :
    GenLoop (Fin 2) X x₀ :=
  compGenLoop h

/-- The `(i,j)`-cell of the uniform `8 × 8` grid. -/
def gridCell (i j : ℕ) : Set (IC 2) :=
  {y | (i : ℝ) / 8 ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ ((i : ℝ) + 1) / 8 ∧
       (j : ℝ) / 8 ≤ (y 1 : ℝ) ∧ (y 1 : ℝ) ≤ ((j : ℝ) + 1) / 8}

/-! ## The T-net -/

/-- The six cells of the T-net, indexed by `Fin 6` in the order
`[y=0], [x=0], [y=1], [x=1], [z=0], [z=1]`. -/
def netCell : Fin 6 → Set (IC 2)
  | 0 => gridCell 2 3
  | 1 => gridCell 3 3
  | 2 => gridCell 4 3
  | 3 => gridCell 5 3
  | 4 => gridCell 3 2
  | 5 => gridCell 3 4

/-- The face of `∂I³` carrying the `k`-th cell, as `(i, b)` with `faceIncl i b` the inclusion. -/
def netFace : Fin 6 → Fin 3 × Fin 2
  | 0 => (1, 1)
  | 1 => (0, 0)
  | 2 => (1, 0)
  | 3 => (0, 1)
  | 4 => (2, 0)
  | 5 => (2, 1)

/-- The reading of the `k`-th cell onto its face (as a map into `∂I³`).

The affine data is forced (up to the global dihedral ambiguity) by the requirement that the
readings agree on the shared edges *and* at the shared corners of the T-net; the solution found by
the constraint search in the module notes is used here, and it has the further property that the
sign of each reading times `(-1)^{i+b}` equals `-1`. -/
def netRead : Fin 6 → C(IC 2, Bdy3)
  | 0 => (faceIncl 1 1).comp (readMap (-8) 3 8 (-3))
  | 1 => (faceIncl 0 0).comp (readMap (-8) 4 8 (-3))
  | 2 => (faceIncl 1 0).comp (readMap 8 (-4) 8 (-3))
  | 3 => (faceIncl 0 1).comp (readMap 8 (-5) 8 (-3))
  | 4 => (faceIncl 2 0).comp (readSwap (-8) 4 (-8) 3)
  | 5 => (faceIncl 2 1).comp (readSwap (-8) 4 8 (-4))

/-- The sign (degree) of the reading of the `k`-th cell. -/
def netSign : Fin 6 → ℤ
  | 0 => -1
  | 1 => -1
  | 2 => 1
  | 3 => 1
  | 4 => -1
  | 5 => 1

/-- The swap of the two coordinates of the square. -/
def swapMap : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (y 1) (y 0),
    continuous_pair2 (continuous_apply 1) (continuous_apply 0)⟩

theorem swapMap_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    swapMap y ∈ Cube.boundary (Fin 2) := by
  obtain ⟨i, hi⟩ := hy
  fin_cases i
  · rcases hi with h | h
    · refine ⟨1, Or.inl ?_⟩; show y 0 = 0; exact h
    · refine ⟨1, Or.inr ?_⟩; show y 0 = 1; exact h
  · rcases hi with h | h
    · refine ⟨0, Or.inl ?_⟩; show y 1 = 0; exact h
    · refine ⟨0, Or.inr ?_⟩; show y 1 = 1; exact h

/-- The `1`-skeleton of `∂I³`: the points lying on two faces. -/
def Skel3 (p : Bdy3) : Prop :=
  ∃ (i i' : Fin 3), i ≠ i' ∧ ∃ (b b' : Fin 2), p.1 i = bval b ∧ p.1 i' = bval b'

end

end Work.Stems.Hur2b
