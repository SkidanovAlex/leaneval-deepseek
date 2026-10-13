/-
  WilG4c — shared vocabulary for `SgnEqMem`: the comparison set `{|∂_s T_a| = |∂_s T_b|}`.

  The whole point of `SgnEqMem` is that the *total* Mathlib function
  `w ↦ fderiv ℝ φ w e` (which is `0` where `φ` is not differentiable) has an `Ω`-definable graph
  whenever the graph of `φ` is `Ω`-definable.  The route is

  * `epsFDerivSet N φ` : the `ε`-`δ` derivative relation, i.e. the set of `(x,c)` of `ℝ^{N+N}`
    with `HasFDerivAt φ (Lin c) x`.  It is `Ω` by `epsFDerivSet_mem`;
  * the graph of the total `fderiv` is then the union of the differentiable piece (a projection of
    `epsFDerivSet` intersected with the linear equality `u = ∑ c i * e i`) and the degenerate
    piece `{not differentiable} × {0}` (`fderivDirGraph_mem`, using
    `fderiv_zero_of_not_differentiableAt` and `HasFDerivAt.fderiv`);
  * combining the two graphs `(w,u)`, `(w,v)` with the condition `|u| = |v|` and projecting gives
    the comparison set (`absEqCombine_mem`).

  This file only fixes the shared vocabulary; the three memberships live in separate modules.

  **Template for the `ε`-`δ` bookkeeping.**  `Submission/Work/WilG1/Plumb/SsetMem.lean`
  (with `DerivDefs.lean` and `SsetCore.lean` in the same directory) already does the *one
  variable* case: `Sset N i f ⊆ ℝ^{N+1}` is the relation `c = ∂_i f (x)` (the *partial* derivative,
  i.e. `y` is forced to agree with `x` off the coordinate `i`).  `EpsFDerivSetMem` is the same
  construction with the `agreeSet` piece replaced by `Set.univ` (no agreement), the scalar
  candidate `c` replaced by the vector block `c : Fin N → ℝ` (so the intermediate spaces gain `N`
  instead of `1` coordinates), and `c * (y i - x i)` replaced by `∑ j, c j * (y j - x j)`.
-/

import Mathlib
import Submission.Work.Wilkies.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesConjecture

/-! ## 1. The linear functional attached to a coefficient vector -/

/-- The continuous linear functional `y ↦ ∑ i, c i * y i` on `ℝ^N`. -/
noncomputable def Lin {N : ℕ} (c : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ i, c i • ContinuousLinearMap.proj i

theorem Lin_apply {N : ℕ} (c : Fin N → ℝ) (y : Fin N → ℝ) :
    Lin c y = ∑ i, c i * y i := by
  simp [Lin, smul_eq_mul]

theorem Lin_single {N : ℕ} (c : Fin N → ℝ) (i : Fin N) :
    Lin c (Pi.single i 1) = c i := by
  rw [Lin_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Every continuous linear functional on `ℝ^N` is `Lin c` for `c i = L (single i 1)`. -/
theorem Lin_eq_of_apply_single {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] ℝ) :
    L = Lin (fun i => L (Pi.single i 1)) := by
  ext y
  rw [Lin_apply]
  have h : y = ∑ i, y i • Pi.single i 1 := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Pi.single_smul' i (y i) (1 : ℝ)]
    congr 1
    rw [smul_eq_mul, mul_one]
  conv_lhs => rw [h]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- The continuous linear functionals on `ℝ^N` are exactly the `Lin c`. -/
theorem exists_Lin_eq {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] ℝ) : ∃ c : Fin N → ℝ, L = Lin c :=
  ⟨_, Lin_eq_of_apply_single L⟩

/-! ## 2. The `ε`-`δ` (Fréchet) derivative relation -/

/-- `epsFDerivSet N φ ⊆ ℝ^{N+N}`: the points `p` read as `(x, c)` with
`x = p ∘ Fin.castAdd N` and `c = p ∘ Fin.natAdd N` for which `c` is the Fréchet derivative of `φ`
at `x`.  This is the set whose `Ω`-membership is `epsFDerivSet_mem`. -/
def epsFDerivSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) : Set (Fin (N + N) → ℝ) :=
  {p | HasFDerivAt φ (Lin (fun i => p (Fin.natAdd N i))) (fun i => p (Fin.castAdd N i))}

theorem mem_epsFDerivSet {N : ℕ} {φ : (Fin N → ℝ) → ℝ} {p : Fin (N + N) → ℝ} :
    p ∈ epsFDerivSet N φ ↔
      HasFDerivAt φ (Lin (fun i => p (Fin.natAdd N i))) (fun i => p (Fin.castAdd N i)) :=
  Iff.rfl

/-! ## 3. Turning a `Polynomial ℕ` degree bound into the `MvPolynomial (Fin 2) ℕ` form of the goal -/

/-- A one-variable natural polynomial, as a two-variable one in the first variable: evaluating at
`![D, 1]` recovers the evaluation at `D`. -/
def toMv2 (p : Polynomial ℕ) : MvPolynomial (Fin 2) ℕ := Polynomial.toMvPolynomial (0 : Fin 2) p

theorem eval_toMv2 (p : Polynomial ℕ) (D : ℕ) :
    MvPolynomial.eval ![D, 1] (toMv2 p) = p.eval D := by
  rw [toMv2, MvPolynomial.eval_toMvPolynomial]
  rfl

end Work.WilG4c
