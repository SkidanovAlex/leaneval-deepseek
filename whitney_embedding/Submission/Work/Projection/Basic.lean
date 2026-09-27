import Mathlib
import Lake.Util.Message
import Lean

/-!
# Elementary linear algebra for the Whitney projection argument

This file sets up the coordinate-wise description of the projection onto a hyperplane
in `ℝ^{k+1}` whose kernel is spanned by the vector `(u, 1)`, together with the
"extraction" map `z ↦ (z_1/z_{k+1}, …, z_k/z_{k+1})`.
-/

open scoped Manifold ContDiff
open Topology

namespace Work.Projection

/-- The vector `(u, 1) ∈ ℝ^{k+1}`, written as the last coordinate `1` and the first `k`
coordinates `u`. -/
noncomputable def vVec {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin (k+1)) :=
  WithLp.toLp 2 (Fin.lastCases (motive := fun _ => ℝ) 1 fun i => u i)

@[simp] lemma vVec_last {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) :
    (vVec u) (Fin.last k) = 1 := by
  simp [vVec]

@[simp] lemma vVec_castSucc {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    (vVec u) (Fin.castSucc i) = u i := by
  simp [vVec]

lemma vVec_ne_zero {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) : vVec u ≠ 0 := by
  intro h
  have := congr_fun (congrArg WithLp.ofLp h) (Fin.last k)
  simpa using this

/-- The linear map `ℝ^{k+1} → ℝ^k`, `z ↦ (z_1 - u_1 z_{k+1}, …, z_k - u_k z_{k+1})`,
on plain function spaces. -/
noncomputable def projAux {k : ℕ} (u : Fin k → ℝ) : (Fin (k+1) → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin k =>
    (ContinuousLinearMap.proj (Fin.castSucc i)) -
      (u i) • (ContinuousLinearMap.proj (Fin.last k))

@[simp] lemma projAux_apply {k : ℕ} (u : Fin k → ℝ) (z : Fin (k+1) → ℝ) (i : Fin k) :
    projAux u z i = z (Fin.castSucc i) - u i * z (Fin.last k) := rfl

/-- The linear map `ℝ^{k+1} → ℝ^k`, `z ↦ (z_1 - u_1 z_{k+1}, …, z_k - u_k z_{k+1})`.
Its kernel is spanned by `(u,1)`. -/
noncomputable def projVec {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  ((EuclideanSpace.equiv (Fin k) ℝ).symm : (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k)) ∘L
    (projAux (fun i => u i) ∘L
      ((EuclideanSpace.equiv (Fin (k+1)) ℝ) : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] (Fin (k+1) → ℝ)))

@[simp] lemma projVec_apply {k : ℕ} (u : EuclideanSpace ℝ (Fin k))
    (z : EuclideanSpace ℝ (Fin (k+1))) (i : Fin k) :
    (projVec u z) i = z (Fin.castSucc i) - u i * z (Fin.last k) := by
  simp [projVec, projAux]

@[simp] lemma projVec_vVec {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) : projVec u (vVec u) = 0 := by
  ext i
  simp [projVec_apply]

/-- Characterization of the kernel of `projVec u`. -/
lemma projVec_eq_zero_iff {k : ℕ} (u : EuclideanSpace ℝ (Fin k))
    (z : EuclideanSpace ℝ (Fin (k+1))) :
    projVec u z = 0 ↔ ∃ c : ℝ, z = c • vVec u := by
  constructor
  · intro h
    refine ⟨z (Fin.last k), ?_⟩
    ext i
    induction i using Fin.lastCases with
    | last => simp
    | cast j =>
        have h' : z (Fin.castSucc j) - u j * z (Fin.last k) = 0 := by
          have := congrArg (fun w : EuclideanSpace ℝ (Fin k) => w.ofLp j) h
          simpa using this
        rw [sub_eq_zero] at h'
        simp [h', mul_comm]
  · rintro ⟨c, rfl⟩
    ext i
    simp [projVec_apply]

/-- The "extraction" map `ℝ^{k+1} → ℝ^k`, `z ↦ (z_1/z_{k+1}, …, z_k/z_{k+1})`.  On the open
set where the last coordinate does not vanish this is a (smooth) inverse to `u ↦ ℝ_{>0}·(u,1)`. -/
noncomputable def extract {k : ℕ} (z : EuclideanSpace ℝ (Fin (k+1))) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun i : Fin k => z (Fin.castSucc i) / z (Fin.last k)

@[simp] lemma extract_apply {k : ℕ} (z : EuclideanSpace ℝ (Fin (k+1))) (i : Fin k) :
    (extract z) i = z (Fin.castSucc i) / z (Fin.last k) := by
  simp [extract]

@[simp] lemma extract_smul_vVec {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) {c : ℝ} (hc : c ≠ 0) :
    extract (c • vVec u) = u := by
  ext i
  simp [extract_apply, hc]

@[simp] lemma last_smul_vVec {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) (c : ℝ) :
    (c • vVec u) (Fin.last k) = c := by
  simp

end Work.Projection
