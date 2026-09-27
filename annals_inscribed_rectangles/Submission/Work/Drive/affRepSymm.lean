import Mathlib
import Submission.Work.Drive.foldRep

/-!
# The affine symmetries of the plane parameter square

The elementary ingredients of the *unrestricted* rows-1/2 producer (`ROW1_ENDTRIPLEREG_STATUS.md` §6):
the signed diagonal `Work.Drive.diagEps`, the affine representative `Work.Drive.affRep`
(`x ↦ (ε i * x i + 2 m i)`), its derivative, and the bijectivity of the diagonal when `ε i = ±1`.

Together with `Work.Drive.exists_foldRep'` (`Drive/foldRep.lean`, an affine representative of any real
number inside `[0,1]`) and `Work.Drive.fderiv_transfer_of_comp_eq` (the invariance of the range and of
the injectivity of a charted class map under an invertible affine change of the plane parameter) these
are *all* the ingredients of the unrestricted producer; what remains is the `simpa`-level assembly
described in §6 of the status file.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIMPCU : IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

/-- The signed diagonal map of the plane parameter. -/
def diagEps (ε : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ({ toFun := fun x => WithLp.toLp 2 (fun i : Fin 2 => ε i * x i),
     map_add' := by
       intro a b
       ext i
       simp only [WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply]
       ring
     map_smul' := by
       intro c a
       ext i
       simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
       ring } : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)).toContinuousLinearMap

@[simp] lemma diagEps_apply (ε : Fin 2 → ℝ) (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    diagEps ε x i = ε i * x i := rfl

/-- The affine representative map `x ↦ (ε i * x i + 2 * m i)`. -/
def affRep (ε : Fin 2 → ℝ) (m : Fin 2 → ℤ) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => ε i * x i + 2 * (m i : ℝ))

@[simp] lemma affRep_apply (ε : Fin 2 → ℝ) (m : Fin 2 → ℤ) (x : EuclideanSpace ℝ (Fin 2))
    (i : Fin 2) : affRep ε m x i = ε i * x i + 2 * (m i : ℝ) := rfl

lemma hasFDerivAt_affRep (ε : Fin 2 → ℝ) (m : Fin 2 → ℤ) (x : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (affRep ε m) (diagEps ε) x := by
  have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) =>
      WithLp.toLp 2 (fun i : Fin 2 => ε i * z i)) (diagEps ε) x := (diagEps ε).hasFDerivAt
  have h2 := h1.add_const (WithLp.toLp 2 (fun i : Fin 2 => 2 * (m i : ℝ)))
  have hfun : affRep ε m = fun z : EuclideanSpace ℝ (Fin 2) =>
      WithLp.toLp 2 (fun i : Fin 2 => ε i * z i) + WithLp.toLp 2 (fun i : Fin 2 => 2 * (m i : ℝ)) := by
    funext z
    ext i
    simp only [affRep_apply, WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply]
  rw [hfun]
  exact h2

lemma diagEps_injective {ε : Fin 2 → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    Function.Injective (diagEps ε) := by
  intro a b hab
  ext i
  have h := congrFun (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => (fun i => z i)) hab) i
  simp only [diagEps_apply] at h
  rcases hε i with h1 | h1 <;> rw [h1] at h <;> linarith

lemma diagEps_surjective {ε : Fin 2 → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    Function.Surjective (diagEps ε) := by
  intro z
  refine ⟨WithLp.toLp 2 (fun i : Fin 2 => ε i * z i), ?_⟩
  ext i
  simp only [diagEps_apply, WithLp.ofLp_toLp]
  rcases hε i with h1 | h1 <;> rw [h1] <;> ring

end

end Work.Drive
