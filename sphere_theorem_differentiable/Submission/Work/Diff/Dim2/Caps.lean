import Mathlib
import Submission.Work.Diff.Dim2.AmbientD
import Submission.Work.Diff.Dim2.Azim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two polar-cap charts of the sphere (the `d = 2` branch)

For the `d = 2` sphere theorem we need the two *cap charts* of `S²`: the graph of the upper
hemisphere over the open unit disc,

`northCap w = (w₀, w₁, √(1 - ‖w‖²))`,

and its mirror image

`southCap w = (w₀, w₁, -√(1 - ‖w‖²))`.

Both are injections of `ℝ²` into `ℝ³` whose derivative is everywhere injective (the vertical
projection `(u₀,u₁,u₃) ↦ (u₀,u₁)` is a left inverse), and both send the closed unit disc into the
unit sphere.

This file contains the definitions and the componentwise `simp` lemmas; the analytic facts are
proved in `sphereAmbCaps.lean`.
-/

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

noncomputable section

/-- The `i`-th component of the north cap chart `w ↦ (w₀, w₁, √(1 - ‖w‖²))`. -/
def northCapComp (i : Fin 3) (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Fin.cases (w 0)
    (fun j => Fin.cases (w 1) (fun _ => Real.sqrt (1 - ‖w‖ ^ 2)) j) i

/-- The `i`-th component of the south cap chart `w ↦ (w₀, w₁, -√(1 - ‖w‖²))`. -/
def southCapComp (i : Fin 3) (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Fin.cases (w 0)
    (fun j => Fin.cases (w 1) (fun _ => -Real.sqrt (1 - ‖w‖ ^ 2)) j) i

/-- The north cap chart of the unit sphere: the graph of the upper hemisphere over the unit disc. -/
def northCap (w : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm fun i => northCapComp i w

/-- The south cap chart of the unit sphere: the mirror image of `northCap`. -/
def southCap (w : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm fun i => southCapComp i w

@[simp] lemma northCapComp_zero (w : EuclideanSpace ℝ (Fin 2)) :
    northCapComp (0 : Fin 3) w = w 0 := by
  rw [northCapComp, Fin.cases_zero]

@[simp] lemma northCapComp_one (w : EuclideanSpace ℝ (Fin 2)) :
    northCapComp (1 : Fin 3) w = w 1 := by
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl, northCapComp, Fin.cases_succ,
    Fin.cases_zero]

@[simp] lemma northCapComp_two (w : EuclideanSpace ℝ (Fin 2)) :
    northCapComp (2 : Fin 3) w = Real.sqrt (1 - ‖w‖ ^ 2) := by
  rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl, northCapComp, Fin.cases_succ,
    show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, Fin.cases_succ]

@[simp] lemma southCapComp_zero (w : EuclideanSpace ℝ (Fin 2)) :
    southCapComp (0 : Fin 3) w = w 0 := by
  rw [southCapComp, Fin.cases_zero]

@[simp] lemma southCapComp_one (w : EuclideanSpace ℝ (Fin 2)) :
    southCapComp (1 : Fin 3) w = w 1 := by
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl, southCapComp, Fin.cases_succ,
    Fin.cases_zero]

@[simp] lemma southCapComp_two (w : EuclideanSpace ℝ (Fin 2)) :
    southCapComp (2 : Fin 3) w = -Real.sqrt (1 - ‖w‖ ^ 2) := by
  rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl, southCapComp, Fin.cases_succ,
    show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, Fin.cases_succ]

@[simp] lemma proj_northCap (i : Fin 3) (w : EuclideanSpace ℝ (Fin 2)) :
    (EuclideanSpace.proj i) (northCap w) = northCapComp i w := by
  rw [northCap]
  simp [EuclideanSpace.proj, PiLp.proj_apply]

@[simp] lemma proj_southCap (i : Fin 3) (w : EuclideanSpace ℝ (Fin 2)) :
    (EuclideanSpace.proj i) (southCap w) = southCapComp i w := by
  rw [southCap]
  simp [EuclideanSpace.proj, PiLp.proj_apply]


section Facts

@[simp] lemma ofLp_northCap (i : Fin 3) (w : EuclideanSpace ℝ (Fin 2)) :
    (northCap w).ofLp i = northCapComp i w := by
  simpa only [PiLp.proj_apply] using proj_northCap i w

@[simp] lemma ofLp_southCap (i : Fin 3) (w : EuclideanSpace ℝ (Fin 2)) :
    (southCap w).ofLp i = southCapComp i w := by
  simpa only [PiLp.proj_apply] using proj_southCap i w

lemma norm_sq_EuclideanTwo (w : EuclideanSpace ℝ (Fin 2)) :
    ‖w‖ ^ 2 = w.ofLp 0 ^ 2 + w.ofLp 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

lemma one_sub_norm_sq_nonneg (w : EuclideanSpace ℝ (Fin 2)) (hw : ‖w‖ ≤ 1) :
    (0 : ℝ) ≤ 1 - ‖w‖ ^ 2 := by
  have h := norm_sq_EuclideanTwo w
  nlinarith [sq_nonneg (w.ofLp 0), sq_nonneg (w.ofLp 1), norm_nonneg w]

lemma norm_northCap (w : EuclideanSpace ℝ (Fin 2)) (hw : ‖w‖ ≤ 1) :
    ‖northCap w‖ = 1 := by
  have hle := one_sub_norm_sq_nonneg w hw
  have h1 : ‖northCap w‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [ofLp_northCap, northCapComp_zero, northCapComp_one, northCapComp_two,
      Real.norm_eq_abs, sq_abs, Real.sq_sqrt hle]
    have h := norm_sq_EuclideanTwo w
    linarith
  nlinarith [norm_nonneg (northCap w), h1]

lemma norm_southCap (w : EuclideanSpace ℝ (Fin 2)) (hw : ‖w‖ ≤ 1) :
    ‖southCap w‖ = 1 := by
  have hle := one_sub_norm_sq_nonneg w hw
  have h1 : ‖southCap w‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [ofLp_southCap, southCapComp_zero, southCapComp_one, southCapComp_two,
      Real.norm_eq_abs, sq_abs, neg_sq, Real.sq_sqrt hle]
    have h := norm_sq_EuclideanTwo w
    linarith
  nlinarith [norm_nonneg (southCap w), h1]

section Flip

/-- The reflection of the second coordinate `(z₀, z₁) ↦ (z₀, s z₁)` as a continuous linear map. -/
noncomputable def flip2 (s : ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 2 =>
      if i = 0 then EuclideanSpace.proj (0 : Fin 2) else s • EuclideanSpace.proj (1 : Fin 2)))

lemma flip2_apply_zero (s : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : flip2 s z 0 = z 0 := by
  simp [flip2, ContinuousLinearMap.pi_apply]

lemma flip2_apply_one (s : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : flip2 s z 1 = s * z 1 := by
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp [flip2, ContinuousLinearMap.pi_apply, h1, ContinuousLinearMap.smul_apply,
    PiLp.proj_apply, smul_eq_mul]

lemma reflE_eq_flip2 (s : ℝ) : reflE s = flip2 s := by
  funext z
  have h0 : reflE s z 0 = flip2 s z 0 := by rw [reflE_apply_zero, flip2_apply_zero]
  have h1 : reflE s z 1 = flip2 s z 1 := by rw [reflE_apply_one, flip2_apply_one]
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma contDiff_reflE (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (reflE s) := by
  rw [reflE_eq_flip2]
  exact (flip2 s).contDiff

lemma flip2_involutive {s : ℝ} (hs : s * s = 1) (z : EuclideanSpace ℝ (Fin 2)) :
    flip2 s (flip2 s z) = z := by
  have h0 : flip2 s (flip2 s z) 0 = z 0 := by
    rw [flip2_apply_zero, flip2_apply_zero]
  have h1 : flip2 s (flip2 s z) 1 = z 1 := by
    rw [flip2_apply_one, flip2_apply_one, ← mul_assoc, hs, one_mul]
  ext i
  fin_cases i
  · exact h0
  · exact h1

end Flip

lemma reflE_involutive {s : ℝ} (hs : s * s = 1) (z : EuclideanSpace ℝ (Fin 2)) :
    reflE s (reflE s z) = z := by
  have h0 : reflE s (reflE s z) 0 = z 0 := by
    rw [reflE_apply_zero, reflE_apply_zero]
  have h1 : reflE s (reflE s z) 1 = z 1 := by
    rw [reflE_apply_one, reflE_apply_one, ← mul_assoc, hs, one_mul]
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma reflE_injective {s : ℝ} (hs : s * s = 1) : Function.Injective (reflE s) := by
  intro a b hab
  have h := congrArg (reflE s) hab
  rwa [reflE_involutive hs a, reflE_involutive hs b] at h

end Facts
end

end Work.Diff.Dim2
