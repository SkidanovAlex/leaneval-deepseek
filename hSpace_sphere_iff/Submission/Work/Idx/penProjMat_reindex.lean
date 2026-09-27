import Mathlib
import Submission.Work.Idx.WPenAppendDefs

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral

set_option linter.style.haveILetI false

/-!
# `Work.Idx.penProjMat_reindex` — reindexing commutes with the pencil projection

The pencil projection `penProjMat X A B = (2πi)⁻¹ ∮_{|z|=1} (z • A + B)⁻¹ A dz` of a matrix
pencil over `C(X, ℂ)` is natural with respect to reindexing the matrix by an equivalence
`e : ι ≃ ι'`: `Matrix.reindex e e` is an isometric `ℂ`-algebra isomorphism of the matrix
algebras with their `L∞` operator norms, hence commutes with `Ring.inverse`, with scalar
multiplication and with the vector-valued circle integral.

The three ingredients are proved first, each for an arbitrary pair of Banach algebras rather
than specifically for matrices:

* `ringEquiv_map_ringInverse` — a *ring equivalence* commutes with `Ring.inverse` (totalized
  inverse; no unit hypothesis, unlike `Work.Idx.ringHom_map_ringInverse`);
* `circleIntegral_linearIsometry` — a linear isometry commutes with circle integrals (no
  integrability hypothesis, because integrability is preserved by an isometry);
* `penProj_map_ringEquiv` — the abstract statement: a norm-preserving `ℂ`-linear ring
  equivalence interchanges `penProj` of a pencil and of the transported pencil.

Only then is the statement instantiated at `Matrix.reindex e e`, where the norm preservation
`‖Matrix.reindex e e A‖ = ‖A‖` for the `L∞` operator norm is checked by hand (`Finset.sup`
over `Finset.univ` and `Finset.sum` are invariant under the bijection `e`).
-/

/-- **A ring equivalence commutes with the totalized inverse.** For `f : R ≃+* S` between
rings, `f (x⁻¹ʳ) = (f x)⁻¹ʳ`, with no unit hypothesis: off the units both sides vanish,
because `IsUnit (f x) ↔ IsUnit x`. -/
theorem ringEquiv_map_ringInverse {R S : Type*} [Ring R] [Ring S] (f : R ≃+* S) (a : R) :
    f (Ring.inverse a) = Ring.inverse (f a) := by
  by_cases ha : IsUnit a
  · have hb : IsUnit (f a) := ha.map f
    have h1 : f (Ring.inverse a) * f a = 1 := by
      rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
    have h4 : f a * Ring.inverse (f a) = 1 := Ring.mul_inverse_cancel _ hb
    calc f (Ring.inverse a)
        = f (Ring.inverse a) * (f a * Ring.inverse (f a)) := by rw [h4, mul_one]
      _ = (f (Ring.inverse a) * f a) * Ring.inverse (f a) := by rw [mul_assoc]
      _ = Ring.inverse (f a) := by rw [h1, one_mul]
  · have hb : ¬ IsUnit (f a) := fun hb => ha (by
      have h := hb.map f.symm
      rwa [RingEquiv.symm_apply_apply] at h)
    rw [Ring.inverse_non_unit _ ha, Ring.inverse_non_unit _ hb, map_zero]

/-- **A linear isometry commutes with circle integrals.** No integrability hypothesis is
needed: a linear isometry preserves integrability, and the Bochner integral of a
non-integrable function is `0`. -/
theorem circleIntegral_linearIsometry {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →ₗᵢ[ℂ] F) (g : ℂ → E) (c : ℂ) (R : ℝ) :
    circleIntegral (fun z => L (g z)) c R = L (circleIntegral g c R) := by
  rw [circleIntegral, circleIntegral]
  rw [← L.intervalIntegral_comp_comm (fun θ : ℝ => deriv (circleMap c R) θ • g (circleMap c R θ))]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [LinearIsometry.map_smul]

/-- **The pencil projection is natural in a norm-preserving `ℂ`-linear ring equivalence.**
If `f : R ≃+* S` between complex Banach algebras is `ℂ`-linear (`hsmul`) and isometric
(`hnorm`), then `penProj (f A) (f B) = f (penProj A B)`. -/
theorem penProj_map_ringEquiv {R S : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    [NormedRing S] [NormedAlgebra ℂ S] [CompleteSpace S]
    (f : R ≃+* S) (hsmul : ∀ (c : ℂ) (x : R), f (c • x) = c • f x)
    (hnorm : ∀ x : R, ‖f x‖ = ‖x‖) (A B : R) :
    Work.KT.Idx.penProj (f A) (f B) = f (Work.KT.Idx.penProj A B) := by
  let L : R →ₗᵢ[ℂ] S :=
    { toLinearMap := { toFun := ⇑f, map_add' := fun x y => map_add f x y, map_smul' := hsmul }
      norm_map' := hnorm }
  have hpResA : ∀ z : ℂ, Work.KT.Idx.pResA (f A) (f B) z = f (Work.KT.Idx.pResA A B z) := by
    intro z
    simp only [Work.KT.Idx.pResA, Work.KT.Idx.pRes]
    have h1 : z • f A + f B = f (z • A + B) := by
      rw [map_add, hsmul]
    rw [h1, map_mul, ringEquiv_map_ringInverse]
  have hB : (∮ z in C(0, 1), Work.KT.Idx.pResA (f A) (f B) z)
      = f (∮ z in C(0, 1), Work.KT.Idx.pResA A B z) := by
    rw [circleIntegral.integral_congr (by norm_num) (fun z _ => hpResA z)]
    exact circleIntegral_linearIsometry L (fun z => Work.KT.Idx.pResA A B z) 0 1
  simp only [Work.KT.Idx.penProj, Work.KT.Idx.pCirc]
  rw [hB, hsmul]

/-- **Reindexing commutes with the pencil projection.** `Matrix.reindex e e` is an isometric ring
isomorphism of matrix rings (`Matrix.linftyOpNormedRing`), hence commutes with `Ring.inverse`,
scalar multiplication and the circle integral.

Route.  `penProjMat X A B` is `(2πi)⁻¹ • ∮_{C(0,1)} Ring.inverse (z • A + B) * A` under the
`linftyOp` instances.  Show that `Matrix.reindex e e` is norm-preserving (`‖Matrix.reindex e e A‖ =
‖A‖` for the `linftyOp` norm `sup_i ∑_j ‖A i j‖`, via `Finset.sup`/`Finset.sum` invariance under the
bijection `e`; Mathlib has no ready-made statement of this), hence a continuous ℂ-linear
equivalence; `Ring.inverse` commutes with ring isomorphisms (a unit is a unit), and continuous
linear maps commute with the Bochner/interval integral (`ContinuousLinearMap.integral_comp_comm`,
or an `intervalIntegral`-level version: unfold `circleIntegral` as
`∫ θ, deriv (circleMap c R) θ • f (circleMap c R θ)` and use that a continuous linear map commutes
with `•` and with `∫`). -/
theorem penProjMat_reindex (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (A B : Matrix ι ι C(X, ℂ)) :
    Work.Idx.penProjMat X (Matrix.reindex e e A) (Matrix.reindex e e B)
      = Matrix.reindex e e (Work.Idx.penProjMat X A B) := by
  letI hR : NormedRing (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI hA : NormedAlgebra ℂ (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI hC : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace ι ι C(X, ℂ)
  letI hR' : NormedRing (Matrix ι' ι' C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI hA' : NormedAlgebra ℂ (Matrix ι' ι' C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI hC' : CompleteSpace (Matrix ι' ι' C(X, ℂ)) := Matrix.instCompleteSpace ι' ι' C(X, ℂ)
  unfold Work.Idx.penProjMat
  -- `‖Matrix.reindex e e A‖ = ‖A‖` for the `L∞` operator norm.
  have hnorm : ∀ x : Matrix ι ι C(X, ℂ), ‖Matrix.reindex e e x‖ = ‖x‖ := by
    intro x
    have h : ‖Matrix.reindex e e x‖₊ = ‖x‖₊ := by
      rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
      have hsum : ∀ i : ι', (∑ j : ι', ‖Matrix.reindex e e x i j‖₊) = ∑ j : ι, ‖x (e.symm i) j‖₊ := by
        intro i
        refine (Fintype.sum_equiv e.symm (fun j : ι' => ‖(Matrix.reindex e e) x i j‖₊)
          (fun j : ι => ‖x (e.symm i) j‖₊) (fun j => ?_)).trans rfl
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      apply le_antisymm
      · refine Finset.sup_le fun i _ => ?_
        exact (hsum i).le.trans
          (Finset.le_sup (f := fun i : ι => ∑ j, ‖x i j‖₊) (Finset.mem_univ (e.symm i)))
      · refine Finset.sup_le fun i _ => ?_
        refine (le_of_eq ?_).trans
          (Finset.le_sup (f := fun i : ι' => ∑ j, ‖(Matrix.reindex e e) x i j‖₊)
            (Finset.mem_univ (e i)))
        simpa using (hsum (e i)).symm
    exact congrArg (fun r : NNReal => (r : ℝ)) h
  have hsmul : ∀ (c : ℂ) (x : Matrix ι ι C(X, ℂ)),
      Matrix.reindex e e (c • x) = c • Matrix.reindex e e x := by
    intro c x
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  exact @penProj_map_ringEquiv (Matrix ι ι C(X, ℂ)) (Matrix ι' ι' C(X, ℂ)) hR hA hC hR' hA' hC'
    (Matrix.reindexRingEquiv (C(X, ℂ)) e) hsmul hnorm A B

end Work.Idx
