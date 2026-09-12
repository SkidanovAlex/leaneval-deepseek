import Mathlib
import ChallengeDeps
import Submission.GeometryOfNumbers.DiagonalFlow
import Submission.Work.Lattice.MaxNormFlow
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent

/-!
# Integrality of the Plücker coordinates, and the max-norm floor for integer families

The paper's §3 arguments use repeatedly that an integer family's wedge has **integer Plücker
coordinates**: the `I`-coordinate of `⋀v` is the determinant of the matrix
`a c ↦ ⟪e_{I_a}, v_c⟫` (`exteriorPower.inner_ιMulti_ιMulti`), whose entries are the (integer)
coordinates of the `v_c`.  This module records

* `inner_std_eq_coord`, `intPoints_coord_int` (the standard basis is orthonormal; `ℤᵈ` has
  integer coordinates);
* **`exists_int_wcoord`** — the Plücker coordinates of an integer family are integers;
* **`one_le_cnorm_iMulti_of_mem_intPoints`** — the resulting **floor for the paper's max norm**:
  an `ℝ`-independent family of `ℤᵈ` has `1 ≤ cnorm (⋀v)`.

(The Euclidean-norm counterpart `Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one` was
already available; the max-norm floor is what the max-norm data of the flow
(`FlowDataMax.flowMaxData`) needs, e.g. for its boundedness below.)

Module `Submission.Work.Lattice.CnormIntegral`, namespace `Submission.CnormIntegral`.
-/

noncomputable section

open LinearSubspaces Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm

namespace Submission.CnormIntegral

variable {d : ℕ}

/-- The standard basis vectors are orthonormal against coordinates. -/
lemma inner_std_eq_coord (t : Fin d) (v : RD d) : inner ℝ ((B d) t) v = v t := by
  simp [B, EuclideanSpace.basisFun_apply, PiLp.inner_apply]

/-- Elements of `ℤᵈ` have integer coordinates. -/
lemma intPoints_coord_int (n : RD d) (hn : n ∈ intPoints (d := d)) (t : Fin d) :
    ∃ z : ℤ, n t = z := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (M := RD d)
    (v := fun i : Fin d => ((B d) i : RD d)) (x := n)).mp hn
  refine ⟨c t, ?_⟩
  rw [← hc, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single t]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]
    simp [zsmul_eq_mul]
  · intro i _ hi
    rw [WithLp.ofLp_smul, Pi.smul_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      if_neg (Ne.symm hi)]
    simp
  · intro h; exact absurd (Finset.mem_univ t) h

/-- **The Plücker coordinates of an integer wedge are integers.** -/
theorem exists_int_wcoord {k : ℕ} (v : Fin k → RD d) (hv : ∀ i, v i ∈ intPoints (d := d))
    (I : IDX d k) :
    ∃ z : ℤ, wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k v) I = (z : ℝ) := by
  classical
  have hw : wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k v) I =
      inner ℝ (exteriorPower.ιMulti ℝ k
          (fun r : Fin k => (B d) (Set.powersetCard.ofFinEmbEquiv.symm I r)))
        (exteriorPower.ιMulti ℝ k v) := by
    rw [wcoord_eq_inner]
    congr 1
    exact basisWedge_eq_enumWedge (d := d) (k := k) I
  rw [hw, exteriorPower.inner_ιMulti_ιMulti]
  have hentry : ∀ a c : Fin k,
      ∃ z : ℤ, inner ℝ ((B d) (Set.powersetCard.ofFinEmbEquiv.symm I c)) (v a) = (z : ℝ) := by
    intro a c
    rw [inner_std_eq_coord]
    exact intPoints_coord_int (v a) (hv a) _
  choose z hz using hentry
  refine ⟨(Matrix.of (fun a c : Fin k => z a c)).det, ?_⟩
  have hM : (Matrix.of fun (i j : Fin k) =>
        inner ℝ ((B d) (Set.powersetCard.ofFinEmbEquiv.symm I j)) (v i))
      = (Matrix.of (fun a c : Fin k => z a c)).map (Int.castRingHom ℝ) := by
    ext a c
    simp only [Matrix.of_apply, Matrix.map_apply]
    exact hz a c
  rw [hM]
  exact (RingHom.map_det (Int.castRingHom ℝ) (Matrix.of (fun a c : Fin k => z a c))).symm

/-- **The max-norm floor for integer families.**  An `ℝ`-independent family of `ℤᵈ` has
`1 ≤ cnorm (⋀v)`. -/
theorem one_le_cnorm_iMulti_of_mem_intPoints {k : ℕ} (hk : k ≤ d) (v : Fin k → RD d)
    (hv : ∀ i, v i ∈ intPoints (d := d)) (hli : LinearIndependent ℝ v) :
    1 ≤ cnorm hk (exteriorPower.ιMulti ℝ k v) := by
  classical
  have hwne : exteriorPower.ιMulti ℝ k v ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent v hli
  obtain ⟨I, hI⟩ : ∃ I : IDX d k,
      wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k v) I ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    refine hwne ?_
    rw [← sum_wcoord_smul_basis (d := d) (k := k) (exteriorPower.ιMulti ℝ k v)]
    exact Finset.sum_eq_zero (fun J _ => by rw [h J, zero_smul])
  obtain ⟨z, hz⟩ := exists_int_wcoord (d := d) v hv I
  have hz0 : z ≠ 0 := by
    intro h0
    exact hI (by rw [hz, h0]; norm_num)
  have h1 : (1 : ℝ) ≤ |wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k v) I| := by
    rw [hz]
    have h2 : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
    exact_mod_cast h2
  exact le_trans h1 (le_cnorm hk _ I)

end Submission.CnormIntegral

end
