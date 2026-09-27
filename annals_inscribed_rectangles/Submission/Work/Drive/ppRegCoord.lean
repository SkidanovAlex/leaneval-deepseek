import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.encodedTransverse
import Submission.Work.Drive.TParity.Basic

/-!
# The coordinate dictionary of the `9`-box for the base-collar regularity `PPRegAt` at `s = 0`

`Work.Drive.PPRegAt` is a condition on the `x`-derivative of the *self-centred charted* pair map
`Work.Drive.ppDiff`.  At the base `s = 0` of the radial collapse the pair map degenerates: the first
chart block `E (ftS x) (ftU x)` is the chain `D 0` at the *top face* of its cube
(`E 0 u = D 0 (mk3 u 1)` is an explicit hypothesis of the bridge, where `mk3 u 1` has level
coordinate `1`), so the pair map depends only on the plane parameter `u ∈ ℝ²` and the two sweep
parameters `y, z ∈ ℝ³`.

This file contains the linear algebra of that degeneration, with no manifold in sight:

* `Work.Drive.ins2` — the insertion `ℝ² → ℝ³`, `a ↦ (a 0, a 1, 0)`;
* `Work.Drive.ftUCLM`, `ftYCLM`, `ftZCLM` — the three block projections of the `9`-box as continuous
  linear maps (the functions `ftU`, `ftY`, `ftZ` of `pairMeetDefs.lean`);
* `Work.Drive.rho9` — the projection that kills the first coordinate of the `9`-box;
* `Work.Drive.mkZ9` — the point of the `9`-box with family parameter `0` and prescribed
  `(u, y, z)`-blocks.

They are the input to the derivative computation of `ppRegAt_zero_of_meet3Hyp`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

/-! ## 1. The insertion `ℝ² → ℝ³` -/

/-- The insertion `ℝ² → ℝ³`, `a ↦ (a 0, a 1, 0)`: the plane coordinates at level `0`.  Its image is the
hyperplane `{v | v 2 = 0}`, which is the tangent direction of the *plane* part of the chain `D 0` at
its top face. -/
def ins2 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm :
      (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3))).comp
    (ContinuousLinearMap.pi fun i : Fin 3 =>
      if h : i.val < 2 then PiLp.proj 2 (fun _ : Fin 2 => ℝ) ⟨i.val, h⟩ else 0)

@[simp] lemma ins2_zero (a : EuclideanSpace ℝ (Fin 2)) : ins2 a 0 = a 0 := by
  simp [ins2, PiLp.proj_apply]

@[simp] lemma ins2_one (a : EuclideanSpace ℝ (Fin 2)) : ins2 a 1 = a 1 := by
  simp [ins2, PiLp.proj_apply]

@[simp] lemma ins2_two (a : EuclideanSpace ℝ (Fin 2)) : ins2 a 2 = 0 := by
  simp [ins2, PiLp.proj_apply]

/-- `ins2` is the level-`0` slice of `Work.Drive.mk3`. -/
lemma ins2_eq_mk3 (a : EuclideanSpace ℝ (Fin 2)) : ins2 a = Work.Drive.mk3 a 0 := by
  ext i
  fin_cases i <;> simp [ins2, PiLp.proj_apply, Work.Drive.mk3]

/-- **The insertion is onto the level-`0` hyperplane**: the surjectivity input of the pair-map
cancellation. -/
lemma exists_ins2_eq_of_two_eq_zero {v : EuclideanSpace ℝ (Fin 3)} (hv : v 2 = 0) :
    ∃ a : EuclideanSpace ℝ (Fin 2), ins2 a = v := by
  refine ⟨WithLp.toLp 2 ![(v 0), (v 1)], ?_⟩
  ext i
  fin_cases i <;> simp [ins2, PiLp.proj_apply, hv]

/-- The level-`1` slice of `mk3` is the affine image of `ins2`. -/
lemma mk3_one_eq (a : EuclideanSpace ℝ (Fin 2)) :
    Work.Drive.mk3 a 1 = ins2 a + Work.Drive.mk3 (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  ext i
  fin_cases i <;> simp [ins2, PiLp.proj_apply, Work.Drive.mk3]

/-! ## 2. The block projections of the `9`-box -/

/-- The `u`-block projection of the `9`-box as a continuous linear map. -/
def ftUCLM : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm :
      (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2))).comp
    (ContinuousLinearMap.pi fun i : Fin 2 =>
      PiLp.proj 2 (fun _ : Fin 9 => ℝ) ⟨1 + i.val, by omega⟩)

/-- The `y`-block projection of the `9`-box as a continuous linear map. -/
def ftYCLM : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm :
      (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3))).comp
    (ContinuousLinearMap.pi fun i : Fin 3 =>
      PiLp.proj 2 (fun _ : Fin 9 => ℝ) ⟨3 + i.val, by omega⟩)

/-- The `z`-block projection of the `9`-box as a continuous linear map. -/
def ftZCLM : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm :
      (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3))).comp
    (ContinuousLinearMap.pi fun i : Fin 3 =>
      PiLp.proj 2 (fun _ : Fin 9 => ℝ) ⟨6 + i.val, by omega⟩)

lemma ftUCLM_eq (x : EuclideanSpace ℝ (Fin 9)) : ftUCLM x = ftU x := by
  ext i
  fin_cases i <;> simp [ftUCLM, ftU, PiLp.proj_apply]

lemma ftYCLM_eq (x : EuclideanSpace ℝ (Fin 9)) : ftYCLM x = ftY x := by
  ext i
  fin_cases i <;> simp [ftYCLM, ftY, PiLp.proj_apply]

lemma ftZCLM_eq (x : EuclideanSpace ℝ (Fin 9)) : ftZCLM x = ftZ x := by
  ext i
  fin_cases i <;> simp [ftZCLM, ftZ, PiLp.proj_apply]

/-! ## 3. The projection onto the last eight coordinates -/

/-- **The projection that kills the family parameter**: the point of the `9`-box with the first
coordinate replaced by `0`. -/
def rho9 : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 9 => ℝ)).symm :
      (Fin 9 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 9))).comp
    (ContinuousLinearMap.pi fun i : Fin 9 =>
      if h : i = 0 then 0 else PiLp.proj 2 (fun _ : Fin 9 => ℝ) i)

lemma rho9_apply_of_ne {x : EuclideanSpace ℝ (Fin 9)} {i : Fin 9} (hi : i ≠ 0) :
    rho9 x i = x i := by
  simp [rho9, PiLp.proj_apply, hi]

@[simp] lemma rho9_zero (x : EuclideanSpace ℝ (Fin 9)) : rho9 x 0 = 0 := by
  simp [rho9, PiLp.proj_apply]

@[simp] lemma ftS_rho9 (x : EuclideanSpace ℝ (Fin 9)) : ftS (rho9 x) = 0 := by
  simp [ftS, rho9, PiLp.proj_apply]

lemma ftU_rho9 (x : EuclideanSpace ℝ (Fin 9)) : ftU (rho9 x) = ftU x := by
  ext i
  fin_cases i <;> simp [ftU, rho9, PiLp.proj_apply]

lemma ftY_rho9 (x : EuclideanSpace ℝ (Fin 9)) : ftY (rho9 x) = ftY x := by
  ext i
  fin_cases i <;> simp [ftY, rho9, PiLp.proj_apply]

lemma ftZ_rho9 (x : EuclideanSpace ℝ (Fin 9)) : ftZ (rho9 x) = ftZ x := by
  ext i
  fin_cases i <;> simp [ftZ, rho9, PiLp.proj_apply]

lemma rho9_eq_self {x : EuclideanSpace ℝ (Fin 9)} (hx : ftS x = 0) : rho9 x = x := by
  ext i
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · subst h; simpa [ftS] using hx.symm
  · simp [rho9, PiLp.proj_apply]

lemma rho9_fixed (x : EuclideanSpace ℝ (Fin 9)) (h : x 0 = 0) : rho9 x = x := by
  ext i
  rcases Fin.eq_zero_or_eq_succ i with h' | ⟨j, rfl⟩
  · subst h'; simpa using h.symm
  · simp [rho9, PiLp.proj_apply]

/-! ## 4. The point of the `9`-box with prescribed blocks -/

/-- **The point of the `9`-box with family parameter `0`** and prescribed blocks `u, y, z`. -/
def mkZ9 (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 9) :=
  WithLp.toLp 2 ![(0 : ℝ), u 0, u 1, y 0, y 1, y 2, z 0, z 1, z 2]

@[simp] lemma ftS_mkZ9 (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftS (mkZ9 u y z) = 0 := by simp [mkZ9, ftS]

@[simp] lemma ftUCLM_mkZ9 (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftUCLM (mkZ9 u y z) = u := by
  ext i
  fin_cases i <;> simp [mkZ9, ftUCLM, PiLp.proj_apply]

@[simp] lemma ftYCLM_mkZ9 (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftYCLM (mkZ9 u y z) = y := by
  ext i
  fin_cases i <;> simp [mkZ9, ftYCLM, PiLp.proj_apply]

@[simp] lemma ftZCLM_mkZ9 (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftZCLM (mkZ9 u y z) = z := by
  ext i
  fin_cases i <;> simp [mkZ9, ftZCLM, PiLp.proj_apply]

lemma ftU_mkZ9 (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftU (mkZ9 u y z) = u := by
  rw [← ftUCLM_eq, ftUCLM_mkZ9]

lemma ftY_mkZ9 (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftY (mkZ9 u y z) = y := by
  rw [← ftYCLM_eq, ftYCLM_mkZ9]

lemma ftZ_mkZ9 (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftZ (mkZ9 u y z) = z := by
  rw [← ftZCLM_eq, ftZCLM_mkZ9]

lemma mkZ9_zero (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    mkZ9 u y z 0 = 0 := rfl

lemma rho9_mkZ9 (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    rho9 (mkZ9 u y z) = mkZ9 u y z :=
  rho9_fixed _ (mkZ9_zero u y z)

/-- **Every point of the `9`-box with `ftS = 0` is its own `rho9`-image**, and is `mkZ9` of its three
blocks. -/
lemma mkZ9_blocks {x : EuclideanSpace ℝ (Fin 9)} (hx : ftS x = 0) :
    mkZ9 (ftU x) (ftY x) (ftZ x) = x := by
  ext i
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · subst h; simpa [mkZ9, ftS] using hx.symm
  · fin_cases j <;> simp [mkZ9, ftU, ftY, ftZ, PiLp.proj_apply]

/-! ## 5. The triple point of the base degeneration

At `s = 0` the pair meet `E 0 u = V y = E' 0 u = W z` *is* a triple meet of the three chains
`D 0, D 1, D 2` at the triple point `(mk3 u 1, y, z)`: block `0` sits on the **top face**
(`level = 1`) of its cube, which is what makes the common direction of the face clause point *out* of
the level-`0` hyperplane. -/

/-- **The triple point of the three chains at a pair meet with `s = 0`.** -/
def triPt (x : EuclideanSpace ℝ (Fin 9)) : EuclideanSpace ℝ (Fin 9) :=
  TParity.mk3 ![(Work.Drive.mk3 (ftU x) 1), ftY x, ftZ x]

@[simp] lemma bPartC_triPt_zero (x : EuclideanSpace ℝ (Fin 9)) :
    TParity.bPartC 0 (triPt x) = Work.Drive.mk3 (ftU x) 1 := by
  simp only [triPt, TParity.bPartC_mk3, Matrix.cons_val_zero]

@[simp] lemma bPartC_triPt_one (x : EuclideanSpace ℝ (Fin 9)) :
    TParity.bPartC 1 (triPt x) = ftY x := by
  simp only [triPt, TParity.bPartC_mk3, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_zero]

@[simp] lemma bPartC_triPt_two (x : EuclideanSpace ℝ (Fin 9)) :
    TParity.bPartC 2 (triPt x) = ftZ x := by
  simp only [triPt, TParity.bPartC_mk3, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

end

end Work.Drive
