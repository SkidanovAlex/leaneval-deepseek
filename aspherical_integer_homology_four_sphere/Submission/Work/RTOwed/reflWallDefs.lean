/-
# The wall reflection of the upper half space model, as a Lorentz transformation

This is the *setup* layer for `Work.RTOwed.mobius_reflWall`, which computes the interaction of a
Lorentz matrix `A` with the reflection of the upper half space model in a vertical wall.

The wall `{z : z k = c}` of the upper half space model (`k : Fin 3`, `c : ℝ`) is the intersection of
the upper sheet of the hyperboloid `{P : ⟨P,P⟩ = -1, P₄ > 0} ⊂ ℝ^{1,4}` with the linear hyperplane
`{P : ⟨P, n_{k,c}⟩ = 0}` orthogonal to

  `n_{k,c} = e_k + c e_3 + c e_4 ∈ ℝ^{1,4}`   (`wallVec k c`),

because for `P = Π(z) = (z₀/z₃, z₁/z₃, z₂/z₃, (‖z‖²−1)/(2z₃), (‖z‖²+1)/(2z₃))` one has

  `⟨P, n_{k,c}⟩ = P k + c P 3 − c P 4 = z k − c`.

Consequently the reflection `z k ↦ 2c − z k` of the upper half space model is induced by the Lorentz
transformation `wallMat k c = 1 − 2 • (n_{k,c} ⊗ J n_{k,c})` (the reflection in the spacelike
hyperplane `n_{k,c}^⊥`), and the reflection of the `t`-th horizontal coordinate is induced by the
diagonal matrix `diagNeg5 (f3to5 t)`.

The two coordinate systems are related by the *height* `P 4 − P 3 = (z 3)⁻¹` of a chart point; the
map `wallMat k c` preserves it (`wallMat_mulVec_height`), and it fixes the wall and negates its
normal (`wallMat_fix`, `wallMat_mulVec_wallVec`).
-/
import Mathlib
import Submission.Work.RTOwed.CuspRigid
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Matrix
open scoped Matrix

namespace Work.RTOwed

open Work.FoldInst

/-! ### The wall normal vector -/

/-- **The Lorentz vector of the wall `{z k = c}`**: `n_{k,c} = e_k + c e_3 + c e_4 ∈ ℝ^{1,4}`.  Its
(Lorentz) orthogonal complement in the hyperboloid is the wall. -/
def wallVec (k : Fin 3) (c : ℝ) : Work.HypModel.V5 :=
  fun j => if j = 3 then c else if j = 4 then c else if j = f3to5 k then 1 else 0

/-- **The Lorentz dual of the wall normal**: `J n_{k,c} = e_k + c e_3 − c e_4`. -/
def wallDual (k : Fin 3) (c : ℝ) : Work.HypModel.V5 :=
  fun j => if j = 3 then c else if j = 4 then -c else if j = f3to5 k then 1 else 0

@[simp] lemma wallVec_apply (k : Fin 3) (c : ℝ) (j : Fin 5) :
    wallVec k c j = if j = 3 then c else if j = 4 then c
      else if j = f3to5 k then 1 else 0 := rfl

@[simp] lemma wallDual_apply (k : Fin 3) (c : ℝ) (j : Fin 5) :
    wallDual k c j = if j = 3 then c else if j = 4 then -c
      else if j = f3to5 k then 1 else 0 := rfl

/-- The wall normal has Lorentz square `1` (it is spacelike of unit length), so that
`P ↦ P − 2⟨P, n_{k,c}⟩ n_{k,c}` is the reflection in `n_{k,c}^⊥`. -/
lemma lorentz_wallVec_self (k : Fin 3) (c : ℝ) :
    Work.HypModel.lorentz (wallVec k c) (wallVec k c) = 1 := by
  rw [show Work.HypModel.lorentz (wallVec k c) (wallVec k c) =
      wallVec k c (f3to5 k) + c * wallVec k c 3 - c * wallVec k c 4 from by
    fin_cases k <;>
    · simp only [Work.HypModel.lorentz, wallVec, f3to5, Fin.isValue]
      simp]
  fin_cases k <;>
  · simp [wallVec, f3to5]

/-- **The Lorentz pairing with the wall normal** is the defining function of the wall:
`⟨n_{k,c}, P⟩ = P k + c P 3 − c P 4`. -/
lemma lorentz_wallVec (k : Fin 3) (c : ℝ) (P : Work.HypModel.V5) :
    Work.HypModel.lorentz (wallVec k c) P = P (f3to5 k) + c * P 3 - c * P 4 := by
  fin_cases k <;>
  · simp only [Work.HypModel.lorentz, wallVec, f3to5, Fin.isValue]
    simp

lemma lorentz_wallVec_comm (k : Fin 3) (c : ℝ) (P : Work.HypModel.V5) :
    Work.HypModel.lorentz (wallVec k c) P = Work.HypModel.lorentz P (wallVec k c) :=
  Work.HypModel.lorentz_comm _ _

/-- The Lorentz dual is the `J`-image of the wall normal. -/
lemma J_mulVec_wallVec (k : Fin 3) (c : ℝ) :
    Work.HypModel.J *ᵥ wallVec k c = wallDual k c := by
  ext j
  rw [Work.HypModel.J_mulVec]
  fin_cases j <;> simp [wallVec, wallDual, f3to5]

/-- The pairing of a vector with `J v` is the Lorentz pairing with `v`. -/
lemma J_mulVec_dotProduct (v x : Work.HypModel.V5) :
    (Work.HypModel.J *ᵥ v) ⬝ᵥ x = Work.HypModel.lorentz v x := by
  rw [Work.HypModel.J_mulVec]
  simp only [dotProduct, Fin.sum_univ_five, Work.HypModel.lorentz]
  simp
  ring

/-- The Euclidean pairing with the Lorentz dual `J n_{k,c}` is the same wall function. -/
lemma wallDual_dotProduct (k : Fin 3) (c : ℝ) (P : Work.HypModel.V5) :
    wallDual k c ⬝ᵥ P = P (f3to5 k) + c * P 3 - c * P 4 := by
  rw [← J_mulVec_wallVec k c, J_mulVec_dotProduct, lorentz_wallVec]



/-! ### The coordinate inclusions `Fin 3 → Fin 4 → Fin 5` -/

@[simp] lemma f3to4_zero : (f3to4 (0 : Fin 3) : Fin 4) = 0 := rfl
@[simp] lemma f3to4_one : (f3to4 (1 : Fin 3) : Fin 4) = 1 := rfl
@[simp] lemma f3to4_two : (f3to4 (2 : Fin 3) : Fin 4) = 2 := rfl
@[simp] lemma f3to5_zero : (f3to5 (0 : Fin 3) : Fin 5) = 0 := rfl
@[simp] lemma f3to5_one : (f3to5 (1 : Fin 3) : Fin 5) = 1 := rfl
@[simp] lemma f3to5_two : (f3to5 (2 : Fin 3) : Fin 5) = 2 := rfl

/-! ### The wall reflection matrix -/

/-- **The Lorentz matrix of the reflection in the wall `{z k = c}`** of the upper half space model:
the reflection `y ↦ y − 2⟨y, n_{k,c}⟩ n_{k,c}` in the spacelike hyperplane `n_{k,c}^⊥`
(`⟨n_{k,c}, n_{k,c}⟩ = 1`). -/
def wallMat (k : Fin 3) (c : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  1 - (2 : ℝ) • Matrix.vecMulVec (wallVec k c) (wallDual k c)

/-- **The diagonal Lorentz matrix negating the `t`-th coordinate**; the reflection of the `t`-th
horizontal coordinate of the upper half space model is its Möbius action `diagNeg5 (f3to5 t)`. -/
def diagNeg5 (t : Fin 5) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.diagonal (fun i => if i = t then -1 else 1)

/-- Scalar multiplication of a vector of `ℝ⁵` by `MulOpposite.op` is ordinary multiplication. -/
lemma op_smul_V5 (r : ℝ) (u : Work.HypModel.V5) : MulOpposite.op r • u = r • u := by
  ext i
  simp [mul_comm]

/-- **The reflection formula**: `wallMat k c *ᵥ P = P − 2⟨n_{k,c},P⟩ n_{k,c}`, i.e. in coordinates
`P k + c P 3 − c P 4` for the pairing. -/
lemma wallMat_mulVec (k : Fin 3) (c : ℝ) (P : Work.HypModel.V5) :
    wallMat k c *ᵥ P = P - (2 * (P (f3to5 k) + c * P 3 - c * P 4)) • wallVec k c := by
  rw [wallMat, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_V5, smul_smul, wallDual_dotProduct]

/-- The coordinate form of the reflection formula. -/
lemma wallMat_mulVec_apply (k : Fin 3) (c : ℝ) (P : Work.HypModel.V5) (j : Fin 5) :
    (wallMat k c *ᵥ P) j = P j - 2 * (P (f3to5 k) + c * P 3 - c * P 4) * wallVec k c j := by
  rw [wallMat_mulVec]
  rfl

/-- The reflection inverts the wall normal: `wallMat k c *ᵥ n_{k,c} = −n_{k,c}`. -/
lemma wallMat_mulVec_wallVec (k : Fin 3) (c : ℝ) :
    wallMat k c *ᵥ wallVec k c = - wallVec k c := by
  rw [wallMat_mulVec]
  have h : wallVec k c (f3to5 k) + c * wallVec k c 3 - c * wallVec k c 4 = 1 := by
    fin_cases k <;> simp [wallVec]
  rw [h, mul_one]
  module

/-- The reflection fixes its wall pointwise: for `P k = c (P 4 − P 3)` one has
`wallMat k c *ᵥ P = P`. -/
lemma wallMat_fix (k : Fin 3) (c : ℝ) (P : Work.HypModel.V5)
    (h : P (f3to5 k) = c * (P 4 - P 3)) : wallMat k c *ᵥ P = P := by
  rw [wallMat_mulVec, h]
  rw [show 2 * (c * (P 4 - P 3) + c * P 3 - c * P 4) = 0 by ring, zero_smul, sub_zero]

/-- The reflection in a vertical wall preserves the height `P 4 − P 3`. -/
lemma wallMat_mulVec_height (k : Fin 3) (c : ℝ) (P : Work.HypModel.V5) :
    (wallMat k c *ᵥ P) 4 - (wallMat k c *ᵥ P) 3 = P 4 - P 3 := by
  rw [wallMat_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases k <;> simp [wallVec] <;> ring

/-- **The squared norm of the reflected point**: reflecting one coordinate in a wall adds
`4c² − 4c z_k` to the squared norm. -/
lemma norm_sq_reflWall4 (k : Fin 3) (c : ℝ) (z : Work.Cusp.E4) :
    ‖reflWall4 k c z‖ ^ 2 = ‖z‖ ^ 2 + 4 * c ^ 2 - 4 * c * z (f3to4 k) := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [Real.norm_eq_abs, sq_abs, reflWall4_apply]
  fin_cases k <;> simp <;> ring

/-- The Möbius matrix of the coordinate reflection: `diagNeg5 t *ᵥ Q = Q − 2 (Q t) e_t`. -/
lemma diagNeg5_mulVec (t : Fin 5) (Q : Work.HypModel.V5) :
    diagNeg5 t *ᵥ Q = Q - (2 * Q t) • Pi.single t 1 := by
  ext j
  rw [diagNeg5, Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
  by_cases h : j = t
  · subst h; simp; ring
  · simp [h]

end Work.RTOwed
