import Mathlib
import Submission.Work.SG.Defs

/-! ## Coordinate model for the affine group of `E 3`

This file sets up the bridge between the abstract affine group `AffineGroup 3 = E 3 ≃ᵃ[ℝ] E 3`
and its coordinate description `x ↦ M *ᵥ x.ofLp + v`, together with the
integer-matrix ↔ real-matrix dictionary used by `Work.SG.conj_sgSet_integral`. -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

noncomputable section

/-- The standard orthonormal basis of `E 3`, as a plain basis. -/
noncomputable def stdB : Module.Basis (Fin 3) ℝ (E 3) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

theorem stdB_repr_apply (x : E 3) (i : Fin 3) : stdB.repr x i = x.ofLp i := rfl

theorem stdB_repr (x : E 3) : (⇑(stdB.repr x) : Fin 3 → ℝ) = x.ofLp :=
  funext fun i => stdB_repr_apply x i

theorem stdB_apply (i : Fin 3) : stdB i = WithLp.toLp 2 (Pi.single i (1 : ℝ)) := by
  simp [stdB, EuclideanSpace.basisFun_apply, EuclideanSpace.single]

/-- The real matrix of an integer matrix. -/
def matR (A : IMat) : Matrix (Fin 3) (Fin 3) ℝ := A.map fun x => (x : ℝ)

@[simp] theorem matR_apply (A : IMat) (i j : Fin 3) : matR A i j = (A i j : ℝ) := rfl

theorem matR_injective : Function.Injective matR := fun _ _ h =>
  Matrix.map_injective (fun _ _ hx => Int.cast_injective hx) h

@[simp] theorem matR_inj {A B : IMat} : matR A = matR B ↔ A = B :=
  matR_injective.eq_iff

theorem matR_eq_mapCast (A : IMat) : matR A = A.map (Int.cast : ℤ → ℝ) := rfl

theorem matR_mul (A B : IMat) : matR (A * B) = matR A * matR B := by
  show ((A * B).map (Int.castRingHom ℝ)) =
    (A.map (Int.castRingHom ℝ)) * (B.map (Int.castRingHom ℝ))
  exact Matrix.map_mul

theorem matR_one : matR (1 : IMat) = 1 := by
  show ((1 : IMat).map (Int.castRingHom ℝ)) = 1
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem matR_mulVec_intVec (A : IMat) (n : Fin 3 → ℤ) : matR A *ᵥ intVec n = intVec (A *ᵥ n) := by
  show (A.map (Int.castRingHom ℝ)) *ᵥ (fun i => ((n i : ℤ) : ℝ)) =
    fun i => ((((A *ᵥ n) i : ℤ)) : ℝ)
  funext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) A n i).symm

theorem isUnit_matR_det {A : IMat} (hA : IsUnit A.det) : IsUnit (matR A).det := by
  show IsUnit ((A.map fun x => (x : ℝ)).det)
  rw [← Int.cast_det A]
  exact hA.map (Int.castRingHom ℝ)

/-- A real coordinate vector with integer coordinates.  (This is `intVec`'s range.) -/
def IsIntVec (v : Fin 3 → ℝ) : Prop := ∃ n : Fin 3 → ℤ, v = intVec n

theorem isIntVec_iff {v : Fin 3 → ℝ} : IsIntVec v ↔ ∃ n : Fin 3 → ℤ, v = intVec n := Iff.rfl

theorem intVec_add (n m : Fin 3 → ℤ) : intVec (n + m) = intVec n + intVec m := by
  ext i; simp [intVec]

theorem intVec_neg (n : Fin 3 → ℤ) : intVec (-n) = -intVec n := by
  ext i; simp [intVec]

theorem intVec_sub (n m : Fin 3 → ℤ) : intVec (n - m) = intVec n - intVec m := by
  ext i; simp [intVec]

theorem intVec_zero : intVec (0 : Fin 3 → ℤ) = 0 := by ext i; simp [intVec]

theorem intVec_smul (c : ℤ) (n : Fin 3 → ℤ) : intVec (c • n) = (c : ℝ) • intVec n := by
  ext i; simp [intVec]

theorem intVec_injective : Function.Injective intVec := fun n m h =>
  funext fun i => Int.cast_injective (congrFun h i)

theorem intVec_single (j : Fin 3) : intVec (Pi.single j (1 : ℤ)) = Pi.single j (1 : ℝ) := by
  ext i
  by_cases h : i = j <;> simp [intVec, Pi.single_eq_same, Pi.single_eq_of_ne, h]

theorem IsIntVec.add {v w : Fin 3 → ℝ} (hv : IsIntVec v) (hw : IsIntVec w) : IsIntVec (v + w) := by
  obtain ⟨n, rfl⟩ := hv; obtain ⟨m, rfl⟩ := hw
  exact ⟨n + m, (intVec_add n m).symm⟩

theorem IsIntVec.neg {v : Fin 3 → ℝ} (hv : IsIntVec v) : IsIntVec (-v) := by
  obtain ⟨n, rfl⟩ := hv; exact ⟨-n, (intVec_neg n).symm⟩

theorem IsIntVec.sub {v w : Fin 3 → ℝ} (hv : IsIntVec v) (hw : IsIntVec w) : IsIntVec (v - w) := by
  obtain ⟨n, rfl⟩ := hv; obtain ⟨m, rfl⟩ := hw
  exact ⟨n - m, (intVec_sub n m).symm⟩

/-- The matrix of an affine equivalence `E 3 ≃ᵃ[ℝ] E 3` in the standard basis. -/
noncomputable def matOf (g : AffineGroup 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix stdB stdB g.linear.toLinearMap

theorem matOf_eq_toMatrix (g : AffineGroup 3) :
    matOf g = LinearMap.toMatrix stdB stdB (g.linear : E 3 →ₗ[ℝ] E 3) := rfl

/-- The linear equivalence of `E 3` given by a real matrix of invertible determinant. -/
noncomputable def linOfMat (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det) : E 3 ≃ₗ[ℝ] E 3 :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).trans
    ((Matrix.toLin'OfInv (M := M⁻¹) (M' := M) (Matrix.nonsing_inv_mul M hM)
      (Matrix.mul_nonsing_inv M hM)).trans (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm)

theorem linOfMat_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det) (x : E 3) :
    linOfMat M hM x = WithLp.toLp 2 (M *ᵥ x.ofLp) := rfl

/-- The affine equivalence `x ↦ M x + v` of `E 3`, for `M` of invertible determinant. -/
noncomputable def affOfMat (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det) (v : Fin 3 → ℝ) :
    AffineGroup 3 :=
  AffineEquiv.mk' (fun x : E 3 => WithLp.toLp 2 (M *ᵥ x.ofLp + v)) (linOfMat M hM) 0
    (by intro x; rw [linOfMat_apply]; simp)

theorem affOfMat_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det) (v : Fin 3 → ℝ)
    (x : E 3) : affOfMat M hM v x = WithLp.toLp 2 (M *ᵥ x.ofLp + v) := rfl

theorem affOfMat_linear (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det) (v : Fin 3 → ℝ) :
    (affOfMat M hM v).linear = linOfMat M hM := rfl

theorem affOfMat_apply_zero (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det)
    (v : Fin 3 → ℝ) : affOfMat M hM v 0 = WithLp.toLp 2 v := by
  rw [affOfMat_apply]; simp

/-- The affine equivalence `x ↦ A x + v`, for an integer matrix `A` with invertible
determinant. -/
noncomputable def affOfInt (A : IMat) (hA : IsUnit A.det) (v : Fin 3 → ℝ) : AffineGroup 3 :=
  affOfMat (matR A) (isUnit_matR_det hA) v

theorem affOfInt_apply (A : IMat) (hA : IsUnit A.det) (v : Fin 3 → ℝ) (x : E 3) :
    affOfInt A hA v x = WithLp.toLp 2 (matR A *ᵥ x.ofLp + v) := rfl

theorem affOfInt_apply_zero (A : IMat) (hA : IsUnit A.det) (v : Fin 3 → ℝ) :
    affOfInt A hA v 0 = WithLp.toLp 2 v := by
  show affOfMat (matR A) (isUnit_matR_det hA) v 0 = WithLp.toLp 2 v
  rw [affOfMat_apply_zero]

theorem affOfInt_mem_sgSet {P : Set IMat} (hP : IsIntPointGroup P) {τ : IMat → Fin 3 → ℝ}
    {A : IMat} (hA : A ∈ P) (n : Fin 3 → ℤ) :
    affOfInt A (hP.2.2.2 A hA) (τ A + intVec n) ∈ sgSet P τ := by
  refine ⟨A, hA, n, fun x => ?_⟩
  rw [affOfInt_apply, matR_eq_mapCast, add_assoc]

end

end Work.SG
